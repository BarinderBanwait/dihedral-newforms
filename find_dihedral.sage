"""find_dihedral.sage

For a given bound B and prime l, this script will search through dimension 2, 
weight 2 newforms f up to level B such that, for a prime ideal lambda over l, 
the mod-lambda Galois representation attached to f has projective dihedral
image. The algorithm can be found in Section 10.1 of Samuele Anni's thesis.

To run this in a local sage session, use the "load" function.

"""


def does_this_alpha_work(f, lam, alpha):    
    """Carries out the check on the Fourier coefficients of f

    Args:
        f : newform
        lam : prime ideal
        alpha : Quadratic Dirichlet character

    Returns:
        (bool) depending on whether or not this alpha works
    """

    B = sturm_bound(f.level(),2) + 2  # the two is for good measure :)
    fourier_coeffs = f.coefficients(B)
    # zero_and_infinity = [0, +Infinity]
    for p in primes(B):
        if (fourier_coeffs[p-1].valuation(lam) == 0) and (alpha(p) == -1):
            return False
    return True


def has_proj_dihedral_image(f, lam):
    """Returns False if rho(f,lam) doesn't have projective dihedral image,
       else returns the quadratic character alpha s.t. rho = rho x alpha.
       This assumes the representation is irreducible.

    Args:
        f : newform
        lam : prime ideal over l
        l : characteristic of base field

    Returns:
        (bool) depending on whether or not f has projective dihedral image at lam
    """

    n = f.level()
    q = prod([p for p,i in n.factor() if i > 1])

    if q == 1:
        return False

    D = [g for g in DirichletGroup(q, QQ) if g.order() == 2]  # all but one of them have order 2, so this could be optimised

    for alpha in D:
        if does_this_alpha_work(f, lam, alpha):
            return alpha
    
    return False


def check_reducible_mod(f,p):
    """This is Peter Bruin's method (slightly edited) - Hartelijk bedankt Peter! :)

    Check whether the Galois representation attached to f mod p is
    reducible.

    We do this by checking that f is congruent to an Eisenstein series
    modulo p.

    Args:
        f : newform
        p : prime ideal

    Returns:
        (bool) depending on whether or not representation is reducible
    """
    M = f.parent().ambient()
    E = M.eisenstein_series()
    B = M.sturm_bound() + 10  # to be sure
    F = p.residue_field()
    f_red = f.q_expansion(B).change_ring(F)

    for e in E:
        try:
            e_red = e.q_expansion(B).change_ring(F)
            if e_red == f_red:
                chi1, chi2, _ = e.parameters()
                print('congruent to Eisenstein series {} with characters {}'.format(e, e.parameters()))
                return
        except ZeroDivisionError:
            pass

    print("irreducible")


def find_dihedral(level_bound, l):
    """Main calling function
    Args:
        level_bound (int): Search levels up to this bound
        l (int): The prime we're looking at

    Returns:
        None (output printed to stdout)
    """    
    if level_bound < 11:
        return "No forms to check"
    for N in range(11, level_bound + 1):
        newforms = Newforms(Gamma1(N),names='a')
        two_dim_newforms = [f for f in newforms if f.base_ring().degree() == 2]
        for f in two_dim_newforms:
            K = f.base_ring()  # A quadratic field
            OK = K.ring_of_integers()
            primes_over_l = OK.ideal(l).prime_factors()
            prime_type = "split" if len(primes_over_l) > 1 else "inert"
            if prime_type == "split":  # Currently only dealing with split primes
                has_possible_dihedral_image = has_proj_dihedral_image(f,primes_over_l[0])
                if has_possible_dihedral_image:
                    output_msg = "Level: {}  Field disc: {}  Prime type: {}  Is dihedral or reducible: {}".format(N,
                                                                                K.discriminant(),
                                                                                prime_type,
                                                                                has_possible_dihedral_image)
                    print(output_msg)


# Do it:
find_dihedral(90, 7)

"""
This returns three forms, of levels 49, 63, 81. To check irreducibility, we 
use Peter Bruin's method `is_reducible_mod' above. Unfortunately taking 
Eisenstein series over a general number field is not yet implemented in Sage. To
get around this, we need forms that are defined over a CyclotomicField. So for
our purposes we can do this by hand, constructing each of the newforms individually.
When sage can compute these Eisenstein series, then this check on irreducibility
can be plumbed in directly into `find_dihedral'. Until then, the following will
suffice.
"""


print("Doing level 49...")
K.<s> = CyclotomicField(6)
D = DirichletGroup(49, K)
eps = [d for d in D if d(3) == -s][0]
f_49 = Newforms(eps, 2)[0]

for p in K.primes_above(7):
    print('above {}:'.format(p))
    check_reducible_mod(f_49, p)


print("\nDoing level 63...")
D = DirichletGroup(63, K)
eps = [d for d in D if d(29) == 1 and d(10) == s-1][0]
f_63 = Newforms(eps, 2)[0]

for p in K.primes_above(7):
    print('above {}:'.format(p))
    check_reducible_mod(f_63, p)


print("\nDoing level 81...")
D = DirichletGroup(81, K)
eps = [d for d in D if d(2) == s^2][0]
N = Newforms(eps, 2, names='a')
f_81 = [j for j in N if j.base_ring().absolute_degree() == 2][0]

for p in K.primes_above(7):
    print('above {}:'.format(p))
    check_reducible_mod(f_81, p)


"""
We may use Corollary 2.2 from Dieulefait's papper "Newforms, Inner twists, and 
the Inverse Galois problem for projective linear groups" (suitably tweaked for 
non-trivial character) to sanity check this last example, since it has level prime
to 7
"""

print("Sanity check the level 81 form using Dieulefait...")
B = 200  # a big number
F = p.residue_field()
f_81_red = f_81.q_expansion(B).change_ring(F).change_ring(GF(7))
list_of_chis = []
for chi in D:
    this_chi_works = True
    for p in prime_range(10,B):
        RHS = GF(7)(F((chi(p) + p*eps(p)/chi(p))))
        if f_81_red[p] != RHS:
            this_chi_works = False
            break
    if this_chi_works:
        list_of_chis.append(chi)
if not list_of_chis:
    print("No character found, so this level 81 form has irreducible representation at this prime ideal")
