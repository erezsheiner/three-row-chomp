"""Independent exact Horner interval verification (not the author's Bernstein checker)."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json
class P:
 def __init__(self,x):
  self.c=[F(t) for t in (x if isinstance(x,list) else [x])]
  while len(self.c)>1 and not self.c[-1]:self.c.pop()
 def __add__(self,y):
  y=as_p(y);return P([(self.c[i] if i<len(self.c) else 0)+(y.c[i] if i<len(y.c) else 0) for i in range(max(len(self.c),len(y.c)))])
 __radd__=__add__
 def __neg__(self):return P([-t for t in self.c])
 def __sub__(self,y):return self+-as_p(y)
 def __rsub__(self,y):return as_p(y)+-self
 def __mul__(self,y):
  y=as_p(y);r=[F(0)]*(len(self.c)+len(y.c)-1)
  for i,s in enumerate(self.c):
   for j,t in enumerate(y.c):r[i+j]+=s*t
  return P(r)
 __rmul__=__mul__
 def __pow__(self,n):
  r=P(1)
  for _ in range(n):r=r*self
  return r
 def derivative(self):return P([i*self.c[i] for i in range(1,len(self.c))])
 def at(self,x):
  r=0
  for c in reversed(self.c):r=r*x+c
  return r
 def interval(self,l,r):
  lower=upper=F(0)
  for c in reversed(self.c):
   products=[lower*l,lower*r,upper*l,upper*r]
   lower,upper=min(products)+c,max(products)+c
  return lower,upper
def as_p(x):return x if isinstance(x,P) else P(x)
results={}
def identity(name,p):
 assert p.c==[0],(name,p.c);results[name]={'result':'passed','method':'exact coefficient identity'}
def positive(name,p,l=F(469,1000),r=F(471,1000)):
 n=10
 while n<=100000:
  bounds=[p.interval(l+(r-l)*i/n,l+(r-l)*(i+1)/n)[0] for i in range(n)]
  if min(bounds)>0:
   results[name]={'result':'passed','method':'rational interval Horner over complete subdivision','interval':[str(l),str(r)],'subintervals':n,'strictLowerBound':str(min(bounds))};return
  n*=10
 raise AssertionError(name)
a=P([0,1]);h=1+2*a;g=1+a;lam=1-a;kk=1-2*a*a;ww=h-a*a
D=4+15*a+17*a*a+2*a**3-6*a**4
V=3+7*a+a*a-5*a**3-2*a**4+2*a**5
Nv=2*g*ww-kk*a*lam
old=P([1,9,-2,-42,-19,20,7,-8,2])
new=P([12496,112497,-24984,-524992,-237524,249993,87520,-100006,25000])
identity('vertex denominator',4*g*g*ww-kk*a*lam-D)
identity('minimum formula',a*a*lam*D*D+a*lam*kk*(2*Nv*D-Nv*Nv)+ww*(D-2*g*Nv)**2-V*a*h*lam*D)
identity('baseline polynomial',(1-2*a)*D-lam**3*V-old)
identity('improved polynomial',12500*old-lam**3*D-new)
positive('baseline denominator',D,F(2,5),F(1,2))
positive('baseline strict convexity',D,F(2,5),F(1,2))
positive('baseline positive vertex',Nv,F(2,5),F(1,2))
positive('baseline monotonicity',-old.derivative(),F(2,5),F(1,2))
for name,p in {
 'vertex left':Nv-F(332,1000)*D,'vertex right':F(336,1000)*D-Nv,
 'breakpoint beyond rectangle':1-2*g*F(336,1000),
 'inside improvement':5*a-h,
 'source earlier than target':F(24,100)*h-F(62,100)*a*g-a*F(1,20),
 'disjoint source ranks':h*F(30,100)-F(58,100),
 'ramp vanishes before target upper rank':-a+(1+3*a)*F(332,1000)-F(58,100)*lam,
 'ramp height positive':1-2*g*F(336,1000),
 'source missing-rank coefficient':2*g*F(354,1000)-1,
 'target missing-rank coefficient':F(41,10)*2*g*F(84,1000)-1,
 'positive improved q coefficient':h-2*a*a,
 'upper branch monotonicity':kk,
 'improved strict monotonicity':-new.derivative(),
}.items():positive(name,p)
for name,v in [('left',F(332,1000)),('right',F(336,1000))]:
 Jnum=a*a*lam+a*lam*kk*(2*v-v*v)+ww*(1-2*g*v)**2
 positive(name+' outer improvement',Jnum*D-V*a*h*lam-F(2,25000)*a*h*lam*D)
assert F(969,500)*F(539,1000)-1==F(22291,500000)
for name,p,l,r in [('baseline',old,F('0.46995152763789'),F('0.46995152763790')),('improved',new,F('0.4699439942048370'),F('0.4699439942048372'))]:
 assert p.at(l)>0>p.at(r)
 results[name+' root']={'result':'passed','rationalBracket':[str(l),str(r)],'diagonalBracket':[str(1/(1-l)),str(1/(1-r))]}
 if name=='baseline':assert F('1.88661990769183')<1/(1-l)<1/(1-r)<F('1.88661990769187')
 else:assert 1/(1-r)<F('1.886593095')
HERE=Path(__file__).resolve().parent
out={'result':'passed','method':'Independent exact polynomial identities and rational interval Horner; no Bernstein code imported and no floating-point proof decisions.','checks':results,'scriptSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'counting-independent-algebra.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print('PASSED',len(results),'independent exact algebra checks')
