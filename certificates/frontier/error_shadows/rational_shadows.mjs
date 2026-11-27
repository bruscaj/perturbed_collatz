// Standalone exact replay. Node.js 18+; no third-party packages.
import fs from "node:fs";
const H=[0,0,0,1,0,0,1],DIMP=[0,0,1,-1,0,1,-1],T=[[0,1,2],[0,1,3],[0,2,3],[1,2,3]];
function need(b,m){if(!b)throw Error(m);}

function mod(a,b){return ((a%b)+b)%b;}

function gcd(a,b){while(b){[a,b]=[b,a%b]}return a<0n?-a:a;}

function inv(a,m){let u=mod(a,m),v=m,s=1n,t=0n;while(v){const q=u/v;[u,v]=[v,u-q*v];[s,t]=[t,s-q*t]}need(u===1n,"nonunit inverse");return mod(s,m);}

function lcm(a,b){return a/gcd(a,b)*b;}

function toggle(s,k){if(s.has(k))s.delete(k);else s.add(k);}

function makeTable(data){
 let S=0n,B=0n,table={};
 for(let q=0;q<4;q++)for(let d=0;d<3;d++){
  const key=q+","+d,rr=data.digit_error_supports[key];need(Array.isArray(rr),"missing dependency row");
  let sa=0n,sb=0n;table[key]=rr.map(([a,b])=>{const A=BigInt(a),B=BigInt(b);need(A>0n&&B>0n,"nonpositive dependency");sa+=A;sb+=B;return [A,B]});
  S=S>sa?S:sa;B=B>sb?B:sb;
 }
 return {S,B,table};
}

function tick(z,p,D=1n){
 const s=z%2n,m=s===BigInt(H[p])?3n:1n;need(z>0n&&(m*z+D*s)%2n===0n,"nonpositive or nonintegral rational tick");
 const N=z-D+BigInt(H[p])*D,sphys=mod(N,2n),Nnext=(sphys===1n?3n*N+D:N)/2n+BigInt(DIMP[p])*D;
 const pp=(p+1)%7,w=(m*z+D*s)/2n;
 need(Nnext+D-BigInt(H[pp])*D===w&&w>0n,"signed numerator step mismatch");
 return [w,pp,m===3n?1:0];
}

function orbit(N,D,cap=6000){
 let p=2,g=0;const path=[],seen=new Map();
 for(let i=0;i<cap;i++){
  if(N<=0n||N.toString(2).length>2000)return null;
  const key=N+","+p;
  if(seen.has(key)){
   const pre=seen.get(key),period=i-pre,cg=g-path[pre].g;
   return {pre,period,cg,path,cycleKeys:path.slice(pre).map(x=>x.N+","+x.p).sort()};
  }
  seen.set(key,i);path.push({N,p,g});
  let inc;[N,p,inc]=tick(N,p,D);g+=inc;
 }
 return null;
}

function at(o,L){if(L<o.pre)return o.path[L];const k=Math.floor((L-o.pre)/o.period),i=o.pre+(L-o.pre)%o.period,x=o.path[i];return {N:x.N,p:x.p,g:x.g+k*o.cg};}

function affine(A,b,p,L){
 let B=b-1n+BigInt(H[p]),g=0;
 for(let k=0;k<L;k++){
  need(A%2n===0n&&B>=BigInt(H[p]),"nonuniform or unsafe integer affine replay");
  if(B%2n){A=3n*A/2n;B=(3n*B+1n)/2n+BigInt(DIMP[p]);g++}
  else {A/=2n;B=B/2n+BigInt(DIMP[p])}
  p=(p+1)%7;
 }
 need(B>=BigInt(H[p]),"unsafe endpoint");
 return [A,B+1n-BigInt(H[p]),p,g];
}

function digitAffine(A,b,d,table){
 let q=0,S=new Set();need(A===3n**BigInt(d)&&b>=0n&&b<A,"not canonical ternary affine suffix");
 const raw=b,a0=A;
 for(let j=0;j<d;j++){
  const t=Number(b%3n);b/=3n;A/=3n;
  for(const [u,v] of table[q+","+t])toggle(S,(u*A)+","+(u*b+v));
  q=T[q][t];
 }
 need(A===1n&&b===0n&&BigInt(q)===4n*raw/a0,"quarter formula mismatch");
 return {q,S};
}

function verifyQuantizer(){
 let cases=0;
 for(let d=0;d<=8;d++){const M=3**d;for(let b=0;b<M;b++)for(let q0=0;q0<4;q0++){
  let q=q0,v=b;for(let j=0;j<d;j++){q=T[q][v%3];v=Math.floor(v/3);}
  need(q===Math.floor((4*b+q0)/M),"finite digit check");cases++;
 }}
 return cases;
}

function shadow(a,D,dep){
 need(D>1n&&gcd(D,6n)===1n&&gcd(a,D)===1n&&27n*a-22n*D>0n,"bad center");
 const o1=orbit(a,D),o2=orbit(27n*a-22n*D,D);need(o1&&o2,"cycle search not completed");
 for(const o of [o1,o2])need(o.cg>0&&3n**BigInt(o.cg)<2n**BigInt(o.period)&&o.period%7===0,"no contracting positive-grow cycle");
 const period=Number(lcm(BigInt(o1.period),BigInt(o2.period)));
 let peak=0n;for(const o of [o1,o2])for(const x of o.path)if(x.N>peak)peak=x.N;
 const K=2n+peak/D;
 const make=(L)=>{const M=2n**BigInt(L),x=at(o1,L),y=at(o2,L),j=mod(-a*inv(M,D),D),r=(a+j*M)/D,A=3n**BigInt(x.g),B=27n*3n**BigInt(y.g);
  need(j>0n&&(a+j*M)%D===0n&&x.p===2&&y.p===2,"invalid common ray");
  return {M,x,y,j,r,A,B,good:r>=1n&&r<=M&&A>4n*D*K&&B>4n*D*K&&100n*D*(dep.S+dep.B)*(A+B)<2n*M};
 };
 let L0=7*Math.ceil(Math.max(o1.pre,o2.pre,7)/7);for(;L0<20000;L0+=7){let ok=true;for(let L=L0;L<L0+period;L+=7)if(!make(L).good){ok=false;break;}if(ok)break;}
 need(L0<20000,"threshold not found");
 const samples=[];
 for(const L of [...new Set([L0,L0+period,L0+10*period,L0+30*period])]){
  const {M,x,y,j,r,A,B,good}=make(L);need(good,"threshold condition");
  const a1=(A*j+x.N)/D,b1=(B*j+y.N)/D;need((A*j+x.N)%D===0n&&(B*j+y.N)%D===0n,"nonintegral intercept");
  const w1=affine(M,r,2,L),w2=affine(27n*M,27n*r-22n,2,L);
  need(w1[0]===A&&w1[1]===a1&&w1[2]===2&&w2[0]===B&&w2[1]===b1&&w2[2]===2,"whole-ray replay mismatch");
  const s1=digitAffine(A,a1-1n,x.g,dep.table),s2=digitAffine(B,b1-1n,y.g+3,dep.table);
  need(s1.q===s2.q&&BigInt(s1.q)===4n*j/D,"shadow mantissa did not synchronize");
  const s=new Set(s1.S);for(const k of s2.S)toggle(s,k);
  let num=0n,maxA=0n,maxB=0n;for(const k of s){const [u,v]=k.split(",").map(BigInt);need(u>0n&&v>0n&&u<M&&v<r,"not strict lower root");num+=(u*r>v*M?u*r:v*M);if(u>maxA)maxA=u;if(v>maxB)maxB=v;}
  need(100n*num<M*r&&2n*num*M<=D*(dep.S+dep.B)*(A+B)*M*r,"sum cost exceeds theorem bound");
  const gg=gcd(num,M*r);samples.push({L,source_modulus:M.toString(),source_residue:r.toString(),slope1:A.toString(),intercept1:a1.toString(),slope2:B.toString(),intercept2:b1.toString(),state:s1.q,dependencies:s.size,maximum_dependency_slope:maxA.toString(),maximum_dependency_offset:maxB.toString(),weight_sum_num:(num/gg).toString(),weight_sum_den:(M*r/gg).toString()});
 }
 return {a:a.toString(),D:D.toString(),L0,period,base_checks:period/7,orbits:[o1,o2].map(o=>({pre:o.pre,period:o.period,grows:o.cg,cycle:o.cycleKeys})),different_rational_cycles:o1.cycleKeys.join(";")!==o2.cycleKeys.join(";"),K:K.toString(),samples};
}

function report(data){
 const dep=makeTable(data);
 const centers=[[14n,17n],[15n,17n],[16n,17n],[18n,17n],[61n,71n],[72n,47n],[166n,47n]].map(([a,d])=>shadow(a,d,dep));
 return {status:"PASS",scope:"conditional on the pinned exact digit-error identities and captured bases; exact finite arithmetic of seven all-depth shadow certificates, not global capture",all_seed_capture_proved:false,quantizer_checks:verifyQuantizer(),max_sum_slopes:dep.S.toString(),max_sum_offsets:dep.B.toString(),centers};
}
const data=JSON.parse(fs.readFileSync(new URL("./xor_recursion_report.json",import.meta.url),"utf8"));
console.log(JSON.stringify(report(data),null,2));
