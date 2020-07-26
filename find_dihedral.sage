"""find_dihedral.sage

For a given bound B and prime l, this script will search through dimension 2,
weight 2 newforms f up to level B such that, for a prime ideal lambda over l,
the mod-lambda Galois representation attached to f has projective dihedral
image. The algorithm can be found in Section 10.1 of Samuele Anni's thesis.

To run this in a local sage session, use the "load" function.

"""

### GLOBALS
R.<T> = GF(7)[]


def get_root_quotient(my_roots):
    """helper method for compute_projective_orders"""

    if len(my_roots) == 2:
        return my_roots[0][0]/my_roots[1][0]
    elif len(my_roots) == 1:
        return my_roots[0][0]/my_roots[0][0]
    else:
        raise IndexError


def compute_projective_orders_verbose(f, eps, D, F, OK):
    """raw version of observing char polys of Frobenius"""
    N = f.level()
    running_set = set()
    print("split:")
    for p in prime_range(10,300):
        if N%p != 0:
            p_splits = (legendre_symbol(D,p) == 1)
            if p_splits:
                pol_p = T^2 - GF(7)(F(OK(f[p])))*T + GF(7)(p*F(OK(eps(p))))
                pol_p_roots = pol_p.roots(GF(49,'a'))  # should be two of them
                root_quotient = get_root_quotient(pol_p_roots)
                p_order = root_quotient.multiplicative_order()
                running_set = running_set.union({p_order})
                msg_p = "prime: {}   poly: {}   is_irred:{}   p_order: {}"
                print(msg_p.format(p, pol_p, pol_p.is_irreducible(), p_order))

    print("inert:")
    for p in prime_range(10,170):
        if N%p != 0:
            p_splits = (legendre_symbol(D,p) == 1)
            if not p_splits:
                pol_p = T^2 - GF(7)(F(OK(f[p])))*T + GF(7)(p*F(OK(eps(p))))
                pol_p_roots = pol_p.roots(GF(49,'a'))  # should be two of them
                root_quotient = get_root_quotient(pol_p_roots)
                p_order = root_quotient.multiplicative_order()
                running_set = running_set.union({p_order})
                msg_p = "prime: {}   poly: {}   is_irred:{}    p_order: {}"
                print(msg_p.format(p, pol_p, pol_p.is_irreducible(), p_order))
    return running_set


def compute_projective_orders(f, eps, D, F, OK, verbose=False):

    if verbose:
        return compute_projective_orders_verbose(f, eps, D, F, OK)

    N = f.level()
    running_set = set()
    for p in prime_range(10,300):
        if N%p != 0:
            pol_p = T^2 - GF(7)(F(OK(f[p])))*T + GF(7)(p*F(OK(eps(p))))
            pol_p_roots = pol_p.roots(GF(49,'a'))  # should be two of them
            root_quotient = get_root_quotient(pol_p_roots)
            p_order = root_quotient.multiplicative_order()
            running_set = running_set.union({p_order})
    return running_set


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


def is_reducible_mod(f,p):
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

    try:
        E = M.eisenstein_series()
    except NotImplementedError:
        # If we can't compute this space, then assume it is irreducible for now;
        # irreducibility or otherwise can be checked later
        return False

    B = M.sturm_bound() + 10  # to be sure
    F = p.residue_field()
    f_red = f.q_expansion(B).change_ring(F)

    for e in E:
        try:
            e_red = e.q_expansion(B).change_ring(F)
            if e_red == f_red:
                chi1, chi2, _ = e.parameters()
                print('congruent to Eisenstein series {} with characters {}'.format(e, e.parameters()))
                return True
        except ZeroDivisionError:
            pass

    return False


def get_forms_to_check(characters, K):
    """Speeds up computing a list of candidate newforms to check, starting from
    a list of Dirichlet characters.

    Args:
        characters ([list]): list of Dirichlet characters
        K ([field]): base field
    """

    newforms_spaces = [Newforms(eps, base_ring=K, names='a') for eps in characters]

    preforms = [j for N in newforms_spaces for j in N if j.base_ring().absolute_degree() == 2]

    lam = K.primes_above(7)[0]

    filtered_forms = []
    for f in preforms:
        is_red = is_reducible_mod(f,lam)
        is_dihedral = has_proj_dihedral_image(f,lam)
        if (not is_red) and is_dihedral:
            filtered_forms.append(f)
    return filtered_forms


def get_irreducibility_and_orders(f,integer_ring):
    """top-level wrapper for other methods"""
    for p in K.primes_above(7):
        print('above {}:'.format(p))
        is_red = is_reducible_mod(f, p)
        if not is_red:
                #
                # This is irreducible, and hence dihedral. To determine its size, we may
                # compute the orders of the matrices in the projective image to determine
                # the group. The raw version of this - which I used - is with verbose set to
                # True, which the reader is welcome to try.
                #
                print("irreducible")
                orders_of_elements = compute_projective_orders(f, f.character(), f.cm_discriminant(), p.residue_field(), integer_ring, verbose=False)
                print("Projective orders are: {}".format(orders_of_elements))
        else:
            print("reducible")


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
find_dihedral(189, 7)

"""
This (eventually) prints to screen the forms in the paper, of levels 49, 63, 81,
117, 189. To check irreducibility, we use Peter Bruin's method `is_reducible_mod'
above. Unfortunately taking Eisenstein series over a general number field is not
yet implemented in Sage. To get around this, we need forms that are defined over
a CyclotomicField. So for our purposes we can do this by hand, constructing
each of the newforms individually. When sage can compute these Eisenstein series,
then this check on irreducibility can be plumbed in directly into `find_dihedral'.
"""

print("Doing level 49...")
K.<s> = CyclotomicField(6)
OK = K.ring_of_integers()
D = DirichletGroup(49, K)
eps = [d for d in D if d(3) == -s][0]
f_49 = Newforms(eps, 2)[0]
get_irreducibility_and_orders(f_49,OK)


print("\nDoing level 63...")
D = DirichletGroup(63, K)
eps = [d for d in D if d(29) == 1 and d(10) == s-1][0]
f_63 = Newforms(eps, 2)[0]
get_irreducibility_and_orders(f_63,OK)


print("\nDoing level 81...")
D = DirichletGroup(81, K)
eps = [d for d in D if d(2) == s^2][0]
N = Newforms(eps, 2, names='a')
f_81 = [j for j in N if j.base_ring().absolute_degree() == 2][0]
get_irreducibility_and_orders(f_81,OK)


"""
We may use Corollary 2.2 from Dieulefait's papper "Newforms, Inner twists, and
the Inverse Galois problem for projective linear groups" (suitably tweaked for
non-trivial character) to sanity check this last example, since it has level prime
to 7
"""

print("Sanity check the level 81 form using Dieulefait...")
B = 200  # a big number
p = K.primes_above(7)[0]
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


print("\nDoing level 117...")
level = 117
gens = [92,28]
D = DirichletGroup(level, K)
eps_g = [d for d in D if [d(i) for i in gens] == [1,s^2]][0]
eps_q = [d for d in D if [d(i) for i in gens] == [1,s^5]][0]
characters = [eps_g, eps_q]
forms_to_check = get_forms_to_check(characters, K)
for f in forms_to_check:
    get_irreducibility_and_orders(f,OK)


print("\nDoing level 189...")
level = 189
gens = [29,136]
D = DirichletGroup(level, K)
eps_c = [d for d in D if [d(i) for i in gens] == [-1,-1]][0]
eps_e = [d for d in D if [d(i) for i in gens] == [1,s^4]][0]
eps_p = [d for d in D if [d(i) for i in gens] == [-1,s^5]][0]
characters = [eps_c, eps_e, eps_p]
forms_to_check = get_forms_to_check(characters, K)
for f in forms_to_check:
    get_irreducibility_and_orders(f,OK)
