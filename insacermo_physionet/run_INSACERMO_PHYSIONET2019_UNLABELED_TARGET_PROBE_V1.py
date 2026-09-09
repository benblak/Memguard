#!/usr/bin/env python3
from __future__ import annotations
import io, json, math, zipfile, hashlib
from collections import Counter
from pathlib import Path
import numpy as np
import pandas as pd
from sklearn.cluster import MiniBatchKMeans
from sklearn.preprocessing import StandardScaler
from sklearn.tree import DecisionTreeClassifier

SEED=20260909; H_TRAIN=6; H_MAX=12; K=32
PHYS=["HR","O2Sat","Temp","SBP","MAP","DBP","Resp","Glucose","Lactate","Creatinine","WBC","Platelets"]
STATIC=["Age","Gender"]; REQUIRED=PHYS+STATIC+["SepsisLabel"]

def iter_frames(source):
    with zipfile.ZipFile(source) as z:
        for n in sorted(x for x in z.namelist() if x.endswith('.psv')):
            yield Path(n).stem,pd.read_csv(io.BytesIO(z.read(n)),sep='|')

def sig(labels,t,H):
    out=0
    for j in range(H+1): out|=(int(labels[t+j])&1)<<j
    return out

def patient_bucket(pid):
    return int(hashlib.sha256(pid.encode()).hexdigest(),16)%5

def build(source):
    Xs=[]; y6=[]; sigs={h:[] for h in range(1,H_MAX+1)}; pids=[]
    for pid,df in iter_frames(source):
        df=df.reset_index(drop=True)
        if any(c not in df.columns for c in REQUIRED) or len(df)<=H_MAX+1: continue
        lab=pd.to_numeric(df.SepsisLabel,errors='coerce').fillna(0).astype(int).to_numpy()
        raw=df[PHYS].apply(pd.to_numeric,errors='coerce'); miss=raw.isna().astype(np.float32); ff=raw.ffill(); lag=ff.shift(1); diff=ff-lag
        age=pd.to_numeric(df.Age,errors='coerce'); gender=pd.to_numeric(df.Gender,errors='coerce')
        parts=[]
        for c in PHYS: parts.extend([ff[c].to_numpy(np.float32),lag[c].to_numpy(np.float32),diff[c].to_numpy(np.float32),miss[c].to_numpy(np.float32)])
        parts.extend([age.to_numpy(np.float32),gender.to_numpy(np.float32)])
        Xall=np.column_stack(parts).astype(np.float32); prior=np.maximum.accumulate(lab)
        idx=[t for t in range(1,len(df)-H_MAX) if lab[t]==0 and prior[t]==0]
        if not idx: continue
        Xs.append(Xall[idx]); y6.extend(sig(lab,t,H_TRAIN) for t in idx); pids.extend([pid]*len(idx))
        for h in range(1,H_MAX+1): sigs[h].extend(sig(lab,t,h) for t in idx)
    return {'X':np.vstack(Xs).astype(np.float32),'y6':np.array(y6,dtype=np.int16),'sigs':{h:np.array(v,dtype=np.int16) for h,v in sigs.items()},'pids':np.array(pids,dtype=object)}

def prep_fit(X):
    med=np.nanmedian(X,axis=0).astype(np.float32); med=np.where(np.isnan(med),0,med); Xi=np.where(np.isnan(X),med,X); sc=StandardScaler().fit(Xi); return med,sc

def prep(X,med,sc): return sc.transform(np.where(np.isnan(X),med,X)).astype(np.float32)
def comb2(n): return n*(n-1)//2

def metrics(codes,sigs):
    n=len(codes); total=comb2(n); cc=Counter(codes.tolist()); jc=Counter(zip(codes.tolist(),sigs.tolist())); merged=sum(comb2(v) for v in cc.values()); same=sum(comb2(v) for v in jc.values()); bad=merged-same
    M=merged/total if total else 0.; V=bad/merged if merged else 0.; L=bad/total if total else 0.; p2=(1+(n-1)*M)/n if n else 1.; Keff=1/p2 if p2 else math.inf
    return {'M':M,'V':V,'Lambda':L,'Keff':Keff,'merged_pairs':merged,'bad_pairs':bad,'n':n}

def apply_ops(X,codes,ops):
    codes=codes.copy()
    for op in ops:
        parent,new,feat,thr=op['parent'],op['new'],op['feature'],op['threshold']
        idx=np.where(codes==parent)[0]
        if len(idx): codes[idx[X[idx,feat]>thr]]=new
    return codes

def refine_cal(Xcal,pre_cal,targetM,max_codes=256):
    codes=pre_cal.copy(); next_code=int(codes.max())+1; ops=[]
    def M(c): return metrics(c,np.zeros(len(c),dtype=np.int8))['M']
    while M(codes)>targetM and len(np.unique(codes))<max_codes:
        cnt=Counter(codes.tolist()); parent=max(cnt,key=cnt.get); idx=np.where(codes==parent)[0]
        if len(idx)<2: break
        var=np.nanvar(Xcal[idx],axis=0); feat=int(np.nanargmax(var)); vals=Xcal[idx,feat]; thr=float(np.median(vals)); hi=idx[vals>thr]
        if len(hi)==0 or len(hi)==len(idx):
            order=idx[np.argsort(vals,kind='mergesort')]; hi=order[len(order)//2:]
            thr=float(Xcal[order[max(0,len(order)//2-1)],feat])
        new=next_code; next_code+=1; codes[hi]=new
        ops.append({'parent':int(parent),'new':int(new),'feature':feat,'threshold':thr,'cal_parent_n':int(len(idx)),'cal_new_n':int(len(hi))})
    return codes,ops

def run_fold(train,target,name):
    med,sc=prep_fit(train['X']); Xtr=prep(train['X'],med,sc); Xtg=prep(target['X'],med,sc)
    cur=MiniBatchKMeans(n_clusters=K,random_state=SEED,batch_size=4096,n_init=10,max_iter=100,reassignment_ratio=.01).fit(Xtr)
    pre=DecisionTreeClassifier(max_leaf_nodes=K,min_samples_leaf=50,criterion='entropy',random_state=SEED).fit(Xtr,train['y6'])
    cur_all=cur.predict(Xtg); pre_all=pre.apply(Xtg)
    buckets=np.array([patient_bucket(p) for p in target['pids']]); cal=(buckets==0); ev=~cal
    Xcal,Xev=Xtg[cal],Xtg[ev]; cur_cal,cur_ev=cur_all[cal],cur_all[ev]; pre_cal,pre_ev=pre_all[cal],pre_all[ev]
    targetM=metrics(cur_cal,np.zeros(cal.sum(),dtype=np.int8))['M']
    rep_cal,ops=refine_cal(Xcal,pre_cal,targetM)
    rep_ev=apply_ops(Xev,pre_ev,ops)
    rows=[]
    for h in range(1,H_MAX+1):
        a=metrics(cur_ev,target['sigs'][h][ev]); b=metrics(pre_ev,target['sigs'][h][ev]); c=metrics(rep_ev,target['sigs'][h][ev])
        rows.append({'fold':name,'H':h,'current':a,'preserve':b,'repaired':c,'dV_cur_minus_rep':a['V']-c['V'],'dL_cur_minus_rep':a['Lambda']-c['Lambda']})
    return {
      'fold':name,'n_cal':int(cal.sum()),'n_eval':int(ev.sum()),
      'cal_M_current':targetM,'cal_M_preserve':metrics(pre_cal,np.zeros(cal.sum(),dtype=np.int8))['M'],'cal_M_repaired':metrics(rep_cal,np.zeros(cal.sum(),dtype=np.int8))['M'],
      'eval_M_current':metrics(cur_ev,np.zeros(ev.sum(),dtype=np.int8))['M'],'eval_M_preserve':metrics(pre_ev,np.zeros(ev.sum(),dtype=np.int8))['M'],'eval_M_repaired':metrics(rep_ev,np.zeros(ev.sum(),dtype=np.int8))['M'],
      'codes_current':len(np.unique(cur_cal)),'codes_preserve':len(np.unique(pre_cal)),'codes_repaired':len(np.unique(rep_cal)),
      'ops':ops,'rows':rows}

def main():
    A=build('training_setA.zip'); B=build('training_setB.zip')
    out=[run_fold(A,B,'A→B'),run_fold(B,A,'B→A')]
    flat=[]
    for f in out:
      for r in f['rows']:
        q={'fold':r['fold'],'H':r['H'],'dV_cur_minus_rep':r['dV_cur_minus_rep'],'dL_cur_minus_rep':r['dL_cur_minus_rep']}
        for rep in ['current','preserve','repaired']:
          for k,v in r[rep].items(): q[f'{rep}_{k}']=v
        flat.append(q)
    df=pd.DataFrame(flat); df.to_csv('INSACERMO_PHYSIONET2019_UNLABELED_TARGET_PROBE_V1_METRICS.csv',index=False)
    summary={'name':'INSACERMO PHYSIONET2019 UNLABELED TARGET PROBE V1','status':'POST_PRIMARY_EXPLORATORY','folds':[],'overall':{}}
    for f in out:
      rr=pd.DataFrame([{'dV':x['dV_cur_minus_rep'],'dL':x['dL_cur_minus_rep']} for x in f['rows']])
      summary['folds'].append({k:v for k,v in f.items() if k!='rows'} | {
        'n_refinement_splits':len(f['ops']),
        'mean_delta_V_current_minus_repaired':float(rr.dV.mean()),
        'mean_delta_Lambda_current_minus_repaired':float(rr.dL.mean()),
        'pointwise_V_repaired_lower':int((rr.dV>0).sum()),
        'pointwise_Lambda_repaired_lower':int((rr.dL>0).sum())})
    summary['overall']={
      'mean_delta_V_current_minus_repaired':float(df.dV_cur_minus_rep.mean()),
      'mean_delta_Lambda_current_minus_repaired':float(df.dL_cur_minus_rep.mean()),
      'V_repaired_lower_pointwise':f"{int((df.dV_cur_minus_rep>0).sum())}/24",
      'Lambda_repaired_lower_pointwise':f"{int((df.dL_cur_minus_rep>0).sum())}/24"}
    Path('INSACERMO_PHYSIONET2019_UNLABELED_TARGET_PROBE_V1_RECEIPT.json').write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary['overall'],indent=2))
if __name__=='__main__': main()
