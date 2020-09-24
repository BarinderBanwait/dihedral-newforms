"""find_simple_dihedral_with_api.py

This is a version of find_dihedral.sage which works with lists of
Fourier coefficients as opposed to computing Newform objects, the latter
of which takes prohibitively long for large levels. The main loop below
obtains the required coefficients via a call to the LMFDB API.

Loading this file directly into the sage shell will fail, because it doesn't know
what '__file__' is. Therefore this file needs to be run from the command line
with 'sage path/to/your/find_simple_dihedral_with_api.sage'.

"""

# The following is needed to read the labels we want to search
import os
os.chdir(os.path.dirname(__file__))

import requests  # for accessing LMFDB API
import json
from filtered_labels import labels  # the labels downloaded from LMFDB


# Globals

R = PolynomialRing(QQ,"x")
S = PolynomialRing(GF(7),"T")
T = S.gen()
CHARACTERISTIC = 7
B = 1000  # big number, used for verifying size of dihedral image and Frob stats

# The URL containing the data we want. The labels will be put into this URL trunk.
URL_TRUNK = ('https://www.lmfdb.org/api/mf_hecke_nf/?_format=json&weight=2&'
             'hecke_ring_rank=2&_fields=label,ap,hecke_ring_power_basis,'
             'field_poly,maxp,hecke_ring_numerators,hecke_ring_denominators'
             '&label={}')


def get_root_quotient(my_roots):
    """helper method for compute_projective_orders"""

    if len(my_roots) == 2:
        return my_roots[0][0]/my_roots[1][0]
    elif len(my_roots) == 1:
        return my_roots[0][0]/my_roots[0][0]
    else:
        raise IndexError


def does_this_alpha_work(aps, level, maxp, lam, alpha):
    """Carries out the check on the Fourier coefficients of f

    Args:
        aps : a_p values of newform
        level : level of the form
        maxp : Biggest prime value of a_p we have
        lam : the prime ideal
        alpha : Dirichlet character

    Returns:
        (bool) depending on whether or not this alpha works
    """
    B = min(sturm_bound(level,2) + 2, maxp )

    unpack_B = list(enumerate(prime_range(B)))

    for i,p in unpack_B:
        if (aps[i].valuation(lam) == 0) and (alpha(p) == -1):
            return False
    return True


def is_dihedral(row, K, aps, characteristic, lam):
    """Main function to check for dihedral image. Assumes lam is a split
    prime in K.

    Args:
        row ([dict]): dict of important data for the form, comes from the API
        K ([NumberField]): The Hecke field of Fourier coefficients
        aps ([list]): list of a_p values of modular form
        characteristic ([int]): the characteristic we're considering
        lam ([FractionalIdeal]): a prime ideal in OK above characteristic

    Returns:
        [bool]: Yes/No depending on whether image is dihedral or not
    """
    # Transcribe from 'find_dihedral.sage'
    n = Integer(row['label'].split(".")[0])
    q = prod([p for p,i in n.factor() if i > 1])

    if q == 1:
        return False

    # all but one of the following have order 2, so this could be optimised
    D = [g for g in DirichletGroup(q, QQ) if g.order() == 2]

    for alpha in D:
        if does_this_alpha_work(aps, n, row['maxp'], lam, alpha):
            return True
    return False


def get_aps(row):
    """Having gathered the data from the LMFDB, we need to unpack the a_p
    values from it. This method does that.

    Args:
        row (dict): a data 'row' corresponding to a newform

    Returns:
        pair of NumberField, list: the Fourier coefficient field, and a list
        of the a_p values
    """

    f = R(row['field_poly'])
    K = NumberField(f, "a")

    if row['hecke_ring_power_basis']:
        betas = [K.gens()[0]**i for i in range(3)]
    else:
        basis_data = [(a,b) for a,b in zip(row['hecke_ring_numerators'],
                       row['hecke_ring_denominators'])]
        betas = [K([c/ZZ(den) for c in num]) for num, den in basis_data]

    convert_elt_to_field = lambda elt: sum(c*beta for c, beta in zip(elt, betas))
    return K, list(map(convert_elt_to_field, row['ap']))


def get_stats(B, lam, OK, aps, is_dihedral_lam):
    """Carries out checks and prints the info we need to the screen"""
    res_field = lam.residue_field()
    running_set = set()
    proportion_dict = {}
    all_red = True
    unpack_B = list(enumerate(prime_range(B)))
    for i,p in unpack_B:
        if p != CHARACTERISTIC:
            pol_p = (T ** 2 - GF(CHARACTERISTIC)(res_field(OK(aps[i])))*T +
                    GF(CHARACTERISTIC)(p))
            pol_p_roots = pol_p.roots(GF(CHARACTERISTIC ** 2,'a'))
            root_quotient = get_root_quotient(pol_p_roots)
            p_order = root_quotient.multiplicative_order()

            if p_order not in proportion_dict:
                proportion_dict[p_order] = 1
            else:
                proportion_dict[p_order] += 1

            running_set = running_set.union({p_order})
            if all_red:
                    all_red = all_red and not pol_p.is_irreducible()
    # The following is used to rule out image contained in Borel
    print("\nall reducible: {}".format(all_red))

    if is_dihedral_lam:
        print("\nProjective orders: {}".format(running_set))
        total_hits = sum(proportion_dict.values())
        proportion_dict_normalised = {k:RR(v/total_hits) for k,v in
                                      proportion_dict.items()}
        print("\nProportions: {}".format(proportion_dict_normalised))


# Do it:
for label in labels:
    the_url = URL_TRUNK.format(label)
    data_this_label = requests.get(url=the_url).json()
    assert(len(data_this_label['data']) == 1)
    data_this_label = data_this_label['data'][0]

    K, aps = get_aps(data_this_label)
    OK = K.ring_of_integers()

    primes_above_l = K.primes_above(CHARACTERISTIC)

    if len(primes_above_l) == 2:
        lam_1, lam_2 = primes_above_l
        is_dihedral_lam_1 = is_dihedral(data_this_label, K, aps,
                                        CHARACTERISTIC, lam_1)
        is_dihedral_lam_2 = is_dihedral(data_this_label, K, aps,
                                        CHARACTERISTIC, lam_2)
        is_dihedral_either_lam = is_dihedral_lam_1 or is_dihedral_lam_2

        if is_dihedral_either_lam:
            print("Checking {} ...".format(label))

            print("Form is dihedral at {}: {}".format(lam_1,is_dihedral_lam_1))
            get_stats(B, lam_1, OK, aps, is_dihedral_lam_1)

            print("Form is dihedral at {}: {}".format(lam_2, is_dihedral_lam_2))
            get_stats(B, lam_2, OK, aps, is_dihedral_lam_2)
