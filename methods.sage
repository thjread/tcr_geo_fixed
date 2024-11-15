from sage.libs.gap.libgap import libgap as lg

# For some GAP functions, there is a slow version that does more consistency checks on
# the input, and a fast "NC" version that skips these checks. Here we set a global flag
# to toggle between these, so that we can run the code on small cases and check it
# doesn't fail any of these checks, but also run the code faster on large cases.
NC = True
lgGroupHomomorphismByImagesCNC = lg.GroupHomomorphismByImagesNC if NC\
    else lg.GroupHomomorphismByImages
lgSubgroupCNC = lg.SubgroupNC if NC else lg.Subgroup
lgNaturalHomomorphismByNormalSubgroupCNC = lg.NaturalHomomorphismByNormalSubgroupNC if NC\
    else lg.NaturalHomomorphismByNormalSubgroup

# We make a class to represent a connective chain complex of abelian groups
# For efficiency we use memoization: the  class is initialised with a
# function `group_func(i)` that computes the ith term, and a function
# `hom_images_func(i, ith_group, i_minus_1st_group)` that computes the
# images of the generating set of the ith term under the differential. The class
# uses this to produce a GAP group homomorphism representing the differential.
# The class saves the results of calling these functions to avoid unnecessary
# re-computation later.
#
# More precisely, `group_func(i)` takes a natural number `i`, and should return
# a tuple `(G, b)` where `G` is a GAP group representing the ith term of the chain
# complex and `b` is a generating set.
# `hom_images_func(i, ith_group, i_minus_1st_group)` takes a natural number `i` and
# the results of calling `group_func(i)` and `group_func(i-1)`; it outputs a list
# of elements of `i_minus_1st_group[0]` describing the images of the generators
# `ith_group[1]` under the degree `i` differential.
class ConnectiveChainComplex:
    def __init__(self, group_func, hom_images_func):
        self.group_func = group_func
        self.hom_images_func = hom_images_func

        self.groups_dict = {}
        self.hom_images_dict = {}
        self.homs_dict = {}

    def group(self, i):
        if not i in self.groups_dict.keys():
            if i < 0:
                self.groups_dict[i] = (lg.TrivialGroup(), {})
            else:
                self.groups_dict[i] = self.group_func(i)
        return self.groups_dict[i]

    def hom_images(self, i):
        if not i in self.hom_images_dict.keys():
            if i <= 0:
                basis_len = len(self.group(i)[1].keys())
                self.hom_images_dict[i] = [self.group(i-1)[0].One()]*basis_len
            else:
                self.hom_images_dict[i] = self.hom_images_func(
                    i,
                    self.group(i),
                    self.group(i-1)
                )
        return self.hom_images_dict[i]

    def hom(self, i):
        if not i in self.homs_dict.keys():
            self.homs_dict[i] = lgGroupHomomorphismByImagesCNC(
                self.group(i)[0],
                self.group(i-1)[0],
                self.hom_images(i)
            )
        return self.homs_dict[i]

# For a chain complex C, computes the quotient C_i ->> H_i(C) of the ith term onto
# the degree i homology
def homology_quot(C, i):
    kernel = lg.KernelOfMultiplicativeGeneralMapping(C.hom(i))
    image = lgSubgroupCNC(C.group(i)[0], C.hom_images(i+1))

    return lgNaturalHomomorphismByNormalSubgroupCNC(kernel, image)

# For a chain complex C, computes the degree i homology H_i(C)
def homology(C, i):
    return lg.ImagesSource(homology_quot(C, i))

# A class to represent a map of connective chain complexes. Again we use memoization: the
# class is initialised with the two chain complexes `A` and `B`, and a function
# `hom_func(i, g, B_i)` that takes as input the degree `i` and the outputs of `A.group(i)`
# and `B.group(i)`, and outputs a list of the images of basis elements of `A.group(i)`
# under the map of chain complexes.
class ChainComplexMap:
    def __init__(self, A, B, hom_func):
        self.A = A
        self.B = B
        self.hom_func = hom_func
        self.homs_dict = {}

    def hom(self, i):
        if i not in self.homs_dict.keys():
            gen_images = self.hom_func(i, self.A.group(i), self.B.group(i))
            self.homs_dict[i] = lgGroupHomomorphismByImagesCNC(
                self.A.group(i)[0],
                self.B.group(i)[0],
                gen_images
            )
        return self.homs_dict[i]

# Given a natural number `i`, outputs a list of non-decreasing surjective
# functions [i] ->> [k] for all k
def inc_surj_list(i):
    assert(i >= 0)

    if i == 0:
       return [(0,)]

    # compute recursively
    old_seqs = inc_surj_list(i-1)
    seqs = []
    for seq in old_seqs:
        seqs.append(seq+(seq[-1],))
        seqs.append(seq+(seq[-1]+1,))

    return seqs

# Arguments are natural numbers `i`, `n`. Let M be the chain complex resolving
# a copy of Z/2 in degree `n`, given by copies of Z/4 in all degrees >= `n`
# with differential multiplication by 2. Let sM be the simplicial abelian group
# corresponding to M under Dold-Kan, and let F(sM) be the chain complex produced by
# (degreewise) taking the C_2-fixed points of the tensor square of sM. Then the present
# function computes the ith term F(sM)_i.
def FsM_simp_ab(i, n):
    maps = [m for m in inc_surj_list(i) if m[-1] >= n]
    map_distinct_pairs = []
    for x in range(len(maps)):
        for y in range(x+1, len(maps)):
            map_distinct_pairs.append((maps[x], maps[y]))

    C = lg.AbelianGroup([4]*(len(maps)+len(map_distinct_pairs)))
    basis = dict(zip([(m, m) for m in maps]+map_distinct_pairs, C.GeneratorsOfGroup()))
    return (C, basis)

# A helper function for computing face maps in sM. Inputs are a natural number `i`,
# a natural number j <= i, and a list `mp` describing a non-decreasing
# surjection [i] -> [k] (for some k). Outputs `(b, mp_)` indicating that
# the basis element indexed by `mp` goes to `b` times the basis element `mp_` under
# the d_j face map, or `(0, None)` if the image is zero.
def map_dj_dest(i, j, mp):
    # remove jth term of mp
    mp_ = tuple(a for (k, a) in enumerate(mp) if k != j)

    if (j < i and mp[j] == mp[j+1]) or (j > 0 and mp[j] == mp[j-1]):
        return (1, mp_)
    elif j == i and mp[j] != mp[j-1]:
        return (2, mp_)
    else:
        return (0, None)

# Computes the differential of the Moore complex of the simplicial abelian group
# F(sM) described above in `FsM_simp_ab`.
def FsM_Moore_diff_images(i, n, FsM_simp_ab_i, FsM_simp_ab_i_minus):
    C_i, basis_i = FsM_simp_ab_i
    C_i_minus, basis_i_minus = FsM_simp_ab_i_minus

    gen_images = []
    for (m1, m2) in basis_i.keys():
        image = C_i_minus.One()
        for j in range(0, i+1):
            (mult1, m11) = map_dj_dest(i, j, m1)
            (mult2, m22) = map_dj_dest(i, j, m2)
            mult = mult1*mult2
            mult *= (-1)**j
            if mult != 0:
                if m1 != m2 and m11 == m22:
                    mult *= 2
                m11, m22 = sorted((m11, m22))
                if m11[-1] >= n and m22[-1] >= n:
                    image *= basis_i_minus[(m11, m22)]**mult
        gen_images.append(image)

    return gen_images

# Outputs a `ConnectiveChainComplex` object representing the Moore complex of F(sM)
def FsM_Moore_complex(n):
    return ConnectiveChainComplex(lambda i: FsM_simp_ab(i, n), lambda i, ab_i, ab_i_minus: FsM_Moore_diff_images(i, n, ab_i, ab_i_minus))

# Let `M` be a free resolution (as a chain complex of Z/4-modules) of Z/2 in degree
# `offset`. Let Tensor2(sM) be the simplicial abelian group obtained by taking the
# (degreewise) tensor square of the simplicial abelian group corresponding to M under
# Dold-Kan. Then this function computes Tensor2(sM)_i.
def Tensor2sM_simp_ab(i, n):
    maps = [m for m in inc_surj_list(i) if m[-1] >= n]
    map_pairs = []
    for x in range(len(maps)):
        for y in range(len(maps)):
            map_pairs.append((maps[x], maps[y]))

    C = lg.AbelianGroup([4]*(len(map_pairs)))
    basis = dict(zip(map_pairs, C.GeneratorsOfGroup()))
    return (C, basis)

# Computes the differential of the Moore complex of Tensor2(sM)
def Tensor2sM_Moore_diff_images(i, n, Tensor2sM_simp_ab_i, Tensor2sM_simp_ab_i_minus):
    C_i, basis_i = Tensor2sM_simp_ab_i
    C_i_minus, basis_i_minus = Tensor2sM_simp_ab_i_minus

    gen_images = []
    for (m1, m2) in basis_i.keys():
        image = C_i_minus.One()
        for j in range(0, i+1):
            (mult1, m11) = map_dj_dest(i, j, m1)
            (mult2, m22) = map_dj_dest(i, j, m2)
            mult = mult1*mult2
            mult *= (-1)**j
            if mult != 0:
                if m11[-1] >= n and m22[-1] >= n:
                    image *= basis_i_minus[(m11, m22)]**mult
        gen_images.append(image)

    return gen_images

# Computes the Moore complex of Tensor2(sM)
def Tensor2sM_Moore_complex(n):
    return ConnectiveChainComplex(
        lambda i: Tensor2sM_simp_ab(i, n),
        lambda i, ab_i, ab_i_minus: Tensor2sM_Moore_diff_images(i, n, ab_i, ab_i_minus)
    )

# Sanity check: the geometric realisation of Tensor2(sM) should be homotopy equivalent
# to \Sigma^n HZ/2 \otimes_{HZ/4} \Sigma^n HZ/2 \cong \bigoplus_{k \ge 0} \Sigma^{2n+k} HZ/2
def Tensor2sM_test(n, max_i):
    Tensor2sM = Tensor2sM_Moore_complex(n)
    print(f"n={n}, checking pi_i(|Tensor2(sM)|) for i from 0 to {max_i}")
    for i in range(0, max_i+1):
        h_i = homology(Tensor2sM, i)
        if i < 2*n:
            assert(lg.Order(h_i) == 1)
        else:
            assert(lg.Order(h_i) == 2)
    print("Success")

# Outputs a `ChainComplexMap` object representing the above map F(sM) -> Tensor2(sM)
def FsM_include_Tensor2sM(FsM, Tensor2sM):
    # Inclusion of C_2-fixed points induces a canonical map F(sM) -> Tensor2(sM);
    # this function computes this map.
    def FsM_include_Tensor2sM_images(i, FsM_simp_ab_i, Tensor2sM_simp_ab_i):
        gen_images = []
        for m1, m2 in FsM_simp_ab_i[1].keys():
            if m1 == m2:
                gen_images.append(Tensor2sM_simp_ab_i[1][(m1, m2)])
            else:
                gen_images.append(
                    Tensor2sM_simp_ab_i[1][(m1, m2)] * Tensor2sM_simp_ab_i[1][(m2, m1)]
                )
        return gen_images

    return ChainComplexMap(
        FsM,
        Tensor2sM,
        FsM_include_Tensor2sM_images
    )

# Outputs the group homomorphism F(sM)_i ->> Z/2 defined as follows: given an element of
# F(sM)_i, the homomorphism extracts the coefficient (in Z/4) of the basis element
# indexed by (id_i, id_i) and returns it reduced modulo 2
def FsM_extract_leading_coeff_mod_2(FsM_i, i):
    id_i = tuple(range(0, i+1))
    Z2 = lg.CyclicGroup(2)
    Z2_generator = lg.GeneratorsOfGroup(Z2)[0]
    gen_images = []
    for k in FsM_i[1].keys():
        if k == (id_i, id_i):
            gen_images.append(Z2_generator)
        else:
            gen_images.append(Z2.One())
    quot = lgGroupHomomorphismByImagesCNC(FsM_i[0], Z2, gen_images)
    return quot

# Helper function to compute the action of the map f on degree i homotopy of the
# n-indexed diagonal component of (THR(Z/4)^{\\phi Z/2})^{C_2}
def f_basis_images_on_diagonal(i, n, FsM, FsM_quot, Tensor2sM, Tensor2sM_quot, rhs, rhs_basis):
    f_basis_images = []
    if i < 2*n:
        f_basis_images += [rhs.One()]*len(lg.AbelianInvariants(lg.ImagesSource(FsM_quot)))
    else:
        c_map = FsM_include_Tensor2sM(FsM, Tensor2sM)
        hom = c_map.hom(i)
        for g in lg.IndependentGeneratorsOfAbelianGroup(lg.ImagesSource(FsM_quot)):
            gg = lg.PreImagesRepresentative(FsM_quot, g)
            h = lg.Image(Tensor2sM_quot, lg.Image(hom, gg))
            exps = lg.IndependentGeneratorExponents(lg.ImagesSource(Tensor2sM_quot), h)
            assert(len(exps) == 1) # note lg.ImagesSource(Tensor2sM_quot) is iso to C2
            f_basis_images.append(rhs_basis[(n, n, i-2*n)]**exps[0])
    return f_basis_images

# Helper function to compute the action of the map r on degree i homotopy of the
# n-indexed diagonal component of (THR(Z/4)^{\\phi Z/2})^{C_2}
def r_basis_images_on_diagonal(i, n, FsM, FsM_quot, rhs, rhs_basis):
    r_basis_images = []
    quot_to_Z2 = FsM_extract_leading_coeff_mod_2(FsM.group(i), i)
    for g in lg.IndependentGeneratorsOfAbelianGroup(lg.ImagesSource(FsM_quot)):
        gg = lg.PreImagesRepresentative(FsM_quot, g)
        im = lg.Image(quot_to_Z2, gg)
        if lg.IsOne(im):
            r_basis_images.append(rhs.One())
        else:
            r_basis_images.append(rhs_basis[(n, 0, i-n)])
    return r_basis_images

# Computes the map r_\ast - f_\ast on \pi_i -- in particular outputs the
# kernel and cokernel
def r_minus_f(i):
    rhs_basis_labels = []
    for n in range(0, i+1):
        for m in range(0, i+1-n):
            if i-n-m >= 0:
                k = i-n-m
                rhs_basis_labels.append((n, m, k))
    rhs = lg.AbelianGroup([2]*len(rhs_basis_labels))
    rhs_basis = dict(zip(rhs_basis_labels, rhs.GeneratorsOfGroup()))

    lhs_basis_labels = []
    lhs_invars = []
    f_basis_images = []
    r_basis_images = []
    # Compute diagonal terms of LHS, and calculate images
    for n in range(0, i+1):
        FsM = FsM_Moore_complex(n)
        FsM_quot = homology_quot(FsM, i)
        print(f"L_{i}^({n})F_{{Z/4}}(Z/2)")
        print(lg.StructureDescription(lg.ImagesSource(FsM_quot)))
        invars = lg.AbelianInvariants(lg.ImagesSource(FsM_quot))
        for (ii, inv) in enumerate(invars):
            lhs_basis_labels.append((n, ii))
            lhs_invars.append(inv)

        # Tensor2sM is only used for i <= floor(i/2), so we economise by only computing
        # it in this case
        if n <= floor(i/2):
            Tensor2sM = Tensor2sM_Moore_complex(n)
            Tensor2sM_quot = homology_quot(Tensor2sM, i)
        else:
            Tensor2sM = None
            Tensor2sM_quot = None

        f_basis_images += f_basis_images_on_diagonal(
            i, n,
            FsM, FsM_quot,
            Tensor2sM, Tensor2sM_quot,
            rhs, rhs_basis
        )
        r_basis_images += r_basis_images_on_diagonal(
            i, n,
            FsM, FsM_quot,
            rhs, rhs_basis
        )
        # Ensure memory is reclaimed
        del FsM, FsM_quot, Tensor2sM, Tensor2sM_quot

    # Specify non-diagonal terms of LHS
    for n in range(0, i+1):
        for m in range(n+1, i+1-n):
            k = i-n-m
            lhs_basis_labels.append((n, m, k))
            lhs_invars.append(2)

    # Images of off-diagonal (n, m) terms of LHS
    for n in range(0, i+1):
        for m in range(n+1, i+1-n):
            k = i-n-m
            f_basis_images.append(rhs_basis[(n, m, k)]*rhs_basis[(m, n, k)])
            r_basis_images.append(rhs.One())

    lhs = lg.AbelianGroup(lhs_invars)
    lhs_basis = dict(zip(lhs_basis_labels, lhs.GeneratorsOfGroup()))

    print(f"pi_{i}((THR(Z/4)^{{\\phi Z/2}})^{{C_2}}):")
    print(lg.StructureDescription(lhs))
    # On-diagonal basis elements are labeled (n, i) where i is an arbitrary index
    # Off-diagonal basis elements labelled by (n, m, k)
    print("Basis labels:")
    print(lhs_basis)
    print("Abelian group invariants corresponding to basis labels:")
    print(lhs_invars)

    print(f"pi_{i}(THR(Z/4)^{{\\phi Z/2}}):")
    print(f"C2^{len(rhs_basis_labels)}")
    # Basis elements labelled by (n, m, k)
    print("Basis labels:")
    print(rhs_basis)

    print("Images of basis elements under f map:")
    print(f_basis_images)
    print("Images of basis elements under r map:")
    print(r_basis_images)

    r_minus_f = lgGroupHomomorphismByImagesCNC(
        lhs,
        rhs,
        [r/f for f, r in zip(f_basis_images, r_basis_images)]
    )
    print("ker(r-f):")
    print(lg.StructureDescription(lg.KernelOfMultiplicativeGeneralMapping(r_minus_f)))
    print("coker(r-f):")
    print(lg.StructureDescription(lg.ImagesSource(lgNaturalHomomorphismByNormalSubgroupCNC(
        rhs,
        lg.ImagesSource(r_minus_f)
    ))))

# Compute r-f map with domain restricted to the diagonal term indexed by `n`,
# and the codomain restricted to terms indexed by `n`
def r_minus_f_fixed_n(i, n):
    assert(n <= i) # Otherwise map is definitely zero on homotopy

    FsM = FsM_Moore_complex(n)
    Tensor2sM = Tensor2sM_Moore_complex(n)

    FsM_quot = homology_quot(FsM, i)
    print(f"L_{i}^({n})F_{{Z/4}}(Z/2)")
    print(lg.StructureDescription(lg.ImagesSource(FsM_quot)))
    Tensor2sM_quot = homology_quot(Tensor2sM, i)

    lhs_invars = list(lg.AbelianInvariants(lg.ImagesSource(FsM_quot)))
    lhs_basis_labels = [(n, ii) for ii in range(len(lhs_invars))]

    lhs = lg.AbelianGroup(lhs_invars)
    lhs_basis = dict(zip(lhs_basis_labels, lhs.GeneratorsOfGroup()))

    rhs_basis_labels = []
    for m in range(0, i+1-n):
        if i-n-m >= 0:
            k = i-n-m
            rhs_basis_labels.append((n, m, k))
    rhs = lg.AbelianGroup([2]*len(rhs_basis_labels))
    rhs_basis = dict(zip(rhs_basis_labels, rhs.GeneratorsOfGroup()))

    # On-diagonal basis elements are labeled (n, i) where i is an arbitrary index
    # Off-diagonal basis elements labelled by (n, m, k)
    print("Basis labels:")
    print(lhs_basis)
    print("Abelian group invariants corresponding to basis labels:")
    print(lhs_invars)

    print(f"pi_{i}(({n}, m)-indexed part of THR(Z/4)^{{\\phi Z/2}}):")
    print(f"C2^{len(rhs_basis_labels)}")
    # Basis elements labelled by (n, m, k)
    print("Basis labels:")
    print(rhs_basis)

    f_basis_images = f_basis_images_on_diagonal(
        i, n,
        FsM, FsM_quot,
        Tensor2sM, Tensor2sM_quot,
        rhs, rhs_basis
    )
    r_basis_images = r_basis_images_on_diagonal(
        i, n,
        FsM, FsM_quot,
        rhs, rhs_basis
    )

    print("Images of basis elements under f map:")
    print(f_basis_images)
    print("Images of basis elements under r map:")
    print(r_basis_images)

    r_minus_f = lgGroupHomomorphismByImagesCNC(
        lhs,
        rhs,
        [r/f for f, r in zip(f_basis_images, r_basis_images)]
    )
    print(f"ker(pi_{i}(gamma_{n})):")
    print(lg.StructureDescription(lg.KernelOfMultiplicativeGeneralMapping(r_minus_f)))
    print(f"coker(pi_{i}(gamma_{n})):")
    print(lg.StructureDescription(lg.ImagesSource(lgNaturalHomomorphismByNormalSubgroupCNC(
        rhs,
        lg.ImagesSource(r_minus_f)
    ))))

# Procedure to verify lemma claiming that
# ker(delta_{i})/(im(delta_{i+1}) + ker(delta_{i}) \\cap off_diag_part + 2ker(delta_{i}))
# \cong Z/2 via projecting the coefficient of e_(id_[i], id_[i])
def check_quotient_lemma(i, n):
    assert(i >= n)

    FsM = FsM_Moore_complex(n)
    maps = [m for m in inc_surj_list(i) if m[-1] >= n]
    map_distinct_pairs = []
    for ii in range(len(maps)):
        for jj in range(ii+1, len(maps)):
            map_distinct_pairs.append((maps[ii], maps[jj]))
    G = FsM.group(i)[0]
    G_basis = FsM.group(i)[1]

    diag_part = lgSubgroupCNC(G, [G_basis[(m, m)] for m in maps])
    off_diag_part = lgSubgroupCNC(G, [G_basis[mm] for mm in map_distinct_pairs])
    kernel = lg.KernelOfMultiplicativeGeneralMapping(FsM.hom(i))
    image = lgSubgroupCNC(G, FsM.hom_images(i+1))
    ker_off_diag = lg.Intersection(kernel, off_diag_part)
    image_plus_off_diag_plus_2_ker = lgSubgroupCNC(
        G,
        list(lg.GeneratorsOfGroup(ker_off_diag))
        + list(lg.GeneratorsOfGroup(image))
        + [g*g for g in lg.GeneratorsOfGroup(kernel)]
    )
    quot_hom = lgNaturalHomomorphismByNormalSubgroupCNC(
        kernel,
        image_plus_off_diag_plus_2_ker
    )
    quot = lg.ImagesSource(quot_hom)
    print(f"ker(delta_{i})/(im(delta_{i+1}) + ker(delta_{i}) \\cap off_diag_part + 2ker(delta_{i})):")
    print(lg.StructureDescription(quot))
    assert(lg.Order(quot) == 2)

    # Check that quotient does agree with projecting onto (id_[i], id_[i]) component
    quot_non_zero = lg.IndependentGeneratorsOfAbelianGroup(quot)[0]
    zero_to_i = tuple(range(0, i+1))
    gen_images = []
    for (k, b) in G_basis.items():
        if k == (zero_to_i, zero_to_i):
            gen_images.append(quot_non_zero)
        else:
            gen_images.append(quot.One())
    quot_manual_def = lgGroupHomomorphismByImagesCNC(G, quot, gen_images)

    for g in lg.GeneratorsOfGroup(kernel):
        assert(lg.Image(quot_hom, g) == lg.Image(quot_manual_def, g))
    print(f"Confirmed that quotient agrees with projecting onto (id_[{i}], id_[{i}]) component")
