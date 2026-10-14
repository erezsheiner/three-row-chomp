from pathlib import Path
import sympy as sp
import hashlib,json
checks={}
# Exact symbolic/rational check of the strict-gap budget and local finite area.
a,w,c=sp.symbols('a w c',positive=True)
D=6*a*a+9*a+2
k=(2*a+1)*(3*a+2)/(3*D)
ca=(30*a*a+35*a+6)/(6*D)
gamma=(1+4*a)/(1+2*a); eta=1/(3*gamma*a*a)
lam=6*a/((2*a+1)*(3*a+1));chi=3/((2*a+1)*(3*a+1)*(4*a+3))
Theta=lam*(11*k/(15*a*a)+eta)+chi*eta
theta_expected=(444*a**3+734*a*a+327*a+30)/(15*a*a*(3*a+1)*(4*a+3)*D)
assert sp.factor(Theta-theta_expected)==0
G=1/(3*a+1)+lam*(1-ca-sp.Rational(1,3))
assert sp.factor(G-(3*a*a+11*a+2)/((3*a+1)*D))==0
P=3*a**4-34*a**3-70*a*a+27*a+6
budget=a*P/((1-a)*(3*a+1)*D)
assert sp.factor((2-1/(1-a))-(1-a)**2*G-budget)==0
Q=18*a**3*w-36*a**3+12*a*a*w*w-9*a*a*w-42*a*a+14*a*w*w-29*a*w+6*a+4*w*w-6*w+4
F1=w-1-1/(1+w-sp.Rational(3,2)*(1-a))
F2=w-1-1/(1+2*a)
assert sp.factor(ca-k*F1-1/w+(2*w-3)*Q/(6*w*(3*a+2*w-1)*D))==0
B=(12*a*a+14*a+4)*w-18*a*a-27*a-6
assert sp.factor(ca-k*F2-1/w+(w-2)*B/(6*w*D))==0
L=sp.Rational(467,1000);U=sp.Rational(469,1000)
assert P.subs(a,L)>0 and P.subs(a,U)<0
assert 12*U**3-102*L**2-140*L+27<0
num,den=sp.fraction(theta_expected)
theta_up=num.subs(a,U)/den.subs(a,L)
kappa_low=1/(1-L)**2-3-(1-L)**2*theta_up
assert kappa_low>sp.Rational(1336,10000)
assert 18*L**3+57*L**2+12*L-8>0 and 6*L**2+7*L-4>0
area=(c*c-3*c+3)**2/(2*c*(3*c-2))+(c-1)*(2-c)**2/(2*c)
assert sp.factor(area-(2-c)/2-(c-1)*(4*c**3-16*c*c+25*c-17)/(2*c*(3*c-2)))==0
c0=sp.Rational(1877,1000);c1=sp.Rational(939,500)
assert (4*c0**3-16*c0*c0+25*c0-17)>sp.Rational(1,160)
assert 2*c1*(3*c1-2)<14 and c0-1>sp.Rational(7,8)
assert P.subs(a,1-1/c0)>0 and P.subs(a,1-1/c1)<0 # c_dagger bracket
checks['strict_gap_algebra']={'identities':'all symbolic rational identities reduced to zero',
    'kappa_lower':str(kappa_low),'root_bracket':['0.467','0.469'],
    'c_dagger_bracket':['1.877','1.878'],'local_area_gap_gt':'1/2560',
    'limits':'No symbolic computation validates the analytic uniformity arguments; those are in the independent derivation.'}

checks['checkerSha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
checks['result']='PASS'
Path(__file__).with_name('strict-gap-algebra.json').write_text(json.dumps(checks,indent=2)+'\n',encoding='utf-8')
print(json.dumps(checks))
