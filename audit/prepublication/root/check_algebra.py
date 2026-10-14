from pathlib import Path
from fractions import Fraction as F
from math import comb
import json
HERE=Path(__file__).resolve().parent
def trim(v):
 while len(v)>1 and v[-1]==0:v.pop()
 return v
class Poly:
 def __init__(self,c):self.c=trim([F(v) for v in (c if isinstance(c,list) else [c])])
 def __add__(self,v):
  v=P(v);return Poly([(self.c[i] if i<len(self.c) else 0)+(v.c[i] if i<len(v.c) else 0) for i in range(max(len(self.c),len(v.c)))])
 __radd__=__add__
 def __neg__(self):return Poly([-v for v in self.c])
 def __sub__(self,v):return self+-P(v)
 def __rsub__(self,v):return P(v)+-self
 def __mul__(self,v):
  v=P(v);cs=[F(0)]*(len(self.c)+len(v.c)-1)
  for i,a in enumerate(self.c):
   for j,b in enumerate(v.c):cs[i+j]+=a*b
  return Poly(cs)
 __rmul__=__mul__
 def __pow__(self,n):
  ans=Poly(1)
  for _ in range(n):ans=ans*self
  return ans
 def at(self,x):
  value=0
  for a in self.c[::-1]:value=value*x+a
  return value
 def derivative(self):return Poly([i*v for i,v in enumerate(self.c)][1:] or [0])
def P(v):return v if isinstance(v,Poly) else Poly(v)
checks={}
def positive(name,p,lo=F(469,1000),hi=F(471,1000)):
 p=P(p);n=len(p.c)-1
 # First affine transform coefficients by direct binomial expansion; then
 # express powers using t^j=sum_{i>=j} C(i,j)/C(n,j) B_i^n.
 shifted=[sum(p.c[k]*comb(k,j)*lo**(k-j)*(hi-lo)**j for k in range(j,n+1)) for j in range(n+1)]
 bern=[sum(shifted[j]*F(comb(i,j),comb(n,j)) for j in range(i+1)) for i in range(n+1)]
 assert min(bern)>0,(name,bern);checks[name]={'domain':[str(lo),str(hi)],'minimumBernstein':str(min(bern))}
x=Poly([0,1]);a=x;h=1+2*a;g=1+a;lam=1-a;kk=1-2*a*a;ww=h-a*a
D=4+15*a+17*a*a+2*a**3-6*a**4;V=3+7*a+a*a-5*a**3-2*a**4+2*a**5;Nv=2*g*ww-kk*a*lam
old=Poly([1,9,-2,-42,-19,20,7,-8,2]);new=12500*old-lam**3*D
assert (4*g*g*ww-kk*a*lam-D).c==[0]
assert ((1-2*a)*D-lam**3*V-old).c==[0]
assert new.c==list(map(F,[12496,112497,-24984,-524992,-237524,249993,87520,-100006,25000]))
assert (a*a*lam*D*D+a*lam*kk*(2*Nv*D-Nv*Nv)+ww*(D-2*g*Nv)**2-V*a*h*lam*D).c==[0]
for name,p in [('denominator',D),('vertex_low',Nv-F(332,1000)*D),('vertex_high',F(336,1000)*D-Nv),('breakpoint',1-2*g*F(336,1000)),('inside_gain',5*a-h),('source_time_margin',F(24,100)*h-F(62,100)*a*g-F(1,20)*a),('baseline_disjointness',F(30,100)*h-F(58,100)),('ramp_support',-a+(1+3*a)*F(332,1000)-F(58,100)*lam),('ramp_positive',1-2*g*F(336,1000)),('source_missing',2*g*(F(664,1000)-F(31,100))-1),('target_missing',F(41,10)*2*g*(F(664,1000)-F(58,100))-1),('objective_gain',h-2*a*a),('upper_branch',kk),('root_monotone',-new.derivative())]:positive(name,p)
for name,v in [('left',F(332,1000)),('right',F(336,1000))]:
 Jnum=a*a*lam+a*lam*kk*(2*v-v*v)+ww*(1-2*g*v)**2
 positive(name+'_outer_gain',Jnum*D-V*a*h*lam-F(2,25000)*a*h*lam*D)
assert F(969,500)*(1-F(461,1000))-1>0
def bracket(p,lo,hi,increasing=False):
 assert (p.at(lo)<0<p.at(hi)) if increasing else (p.at(lo)>0>p.at(hi))
 for _ in range(90):
  mid=(lo+hi)/2
  if (p.at(mid)<0)==increasing:lo=mid
  else:hi=mid
 return lo,hi
br=bracket(new,F(469,1000),F(471,1000));assert 1/(1-br[1])<F(1886593095,10**9)

# Independent expansion of the latest union/chord inequality.
c=x;B=c*c-3*c+3
union=B**2*(c**3+4*c*c+c-1)-(2-c)*c*c*(3*c+2)*(2*c-1)*(c*c-2*c+2)
assert union.c==list(map(F,[-9,27,11,-58,25,22,-25,7]))
positive('union_derivative',union.derivative(),F(9,5),F(15,8))
ub=bracket(union,F(9,5),F(15,8),True);assert ub[1]<F(1868565865679,10**12)
cm=F(15,8);DD=cm*cm+cm-1
assert 1/(cm*DD)+(cm-1)**3*(cm*cm-3)**2/(cm**3*DD)-(2-cm)==F(159327,60696000)

result={'status':'PASS','method':'Independently implemented Fraction polynomial expansion, affine transformation, Bernstein positivity and90-step rational brackets; no floating-point proof decisions.','temporalPolynomial':list(map(str,new.c)),'temporalRootBracket':list(map(str,br)),'temporalSlopeUpper':str(1/(1-br[1])),'unionPolynomial':list(map(str,union.c)),'unionRootBracket':list(map(str,ub)),'certificates':checks}
(HERE/'exact-algebra-checks.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print('PASS',len(checks),'exact positivity checks')
