// Alpha path rooted at its middle: determine attainable zero/max positions.
const k=+(process.argv[2]||7), target=+(process.argv[3]||2), mode=process.argv[4]||'zero';
const budget=+(process.argv[5]||10000000), direction=+(process.argv[6]||-1), q=2*k, alpha=k-(k%2);
const a=Array(q+1).fill(-1); a[k]=alpha;
const zi=mode==='zero'?k-target:k-target+direction, mi=mode==='zero'?zi+direction:k-target;
if(zi<0||mi<0||zi>q||mi>q)throw Error('index');
if(zi===k||mi===k)throw Error('would overwrite center');
a[zi]=0;a[mi]=q;
let nodes=0,cut=false,found=null;
function dfs(vm,em){
 if(++nodes>budget){cut=true;return false;}
 let best=-1,opts=null;
 for(let i=0;i<=q;i++)if(a[i]<0 && ((i&&a[i-1]>=0)||(i<q&&a[i+1]>=0))){
  const os=[];for(let x=0;x<=q;x++)if(!(vm&(1<<x))&&((x<=alpha)===((i-k)%2===0))){
   let eb=0,ok=true;
   for(const j of [i-1,i+1])if(j>=0&&j<=q&&a[j]>=0){let d=Math.abs(x-a[j]),b=1<<d;if(!d||(em&b)||(eb&b)){ok=false;break;}eb|=b;}
   if(ok)os.push([x,eb]);
  }
  if(!opts||os.length<opts.length){best=i;opts=os;if(!os.length)return false;}
 }
 if(best<0){found=[...a];return true;}
 for(const [x,e]of opts){a[best]=x;if(dfs(vm|(1<<x),em|e))return true;if(cut)break;}a[best]=-1;return false;
}
let vm=0,em=0,valid=true;
for(let i=0;i<=q;i++)if(a[i]>=0){if(vm&(1<<a[i]))valid=false;vm|=1<<a[i];if((a[i]<=alpha)!==((i-k)%2===0))valid=false;if(i&&a[i-1]>=0){let d=Math.abs(a[i]-a[i-1]);if(em&(1<<d))valid=false;em|=1<<d;}}
if(valid)dfs(vm,em);
console.log(JSON.stringify({k,target,mode,direction,alpha,zi,mi,status:found?'FOUND':cut?'UNKNOWN':'EXHAUSTED',nodes,path:found}));
