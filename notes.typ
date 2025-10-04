#import "template/preamble.typ": *

#show: lecture_notes.with(
  lecture: [Representation Theory],
  lecture_id: [401-4202-11L],
  lecturer: [Emmanuel Kowalski],
  authors: (
    (
      name: "Dominique Garmier",
      affiliation: "ETH Zurich",
      email: "dgarmier@ethz.ch",
    ),
  ),
  semester: [Fall 2025],
)

#let link_box(
  doc,
) = box(
  stroke: 0.1pt,
  outset: 1pt,
  doc,
)

#show link: link_box

= Introduction
== History

- Symmetries of various goemetric objects (approx. 1830)
- Dirichlet / Weber (finite abelian groups)
- Dedekind / Frobenius / Schur (late 1800's)
- Burnside (approx. 1900s)
- Artin (1920s)
- Peter-Weyl (1920s)
- Baugman, Gelfand, Harish-Chandra (1940s-50s)
- Langlands (1960s-70s)

Representation theory interacts with:
- Group Theory
- Linear Algebra
- Number Theory
- Harmonic Analysis
- (Mathematical Physics)

== Some Statements

#theorem[Burnside][
  If $G$ is a finite group and $|G| = p q r$ for some pairwise different primes $p, q, r$,
  then $G$ is solvable.
]

#remark[
  A group is solveable if there exists a descending chain of (relatively) normal
  subgroups with abelian quotients.
]

#remark[
  This is in some sense the best possible result as $A_5$ is not solvable
  and has order
  $
    60 = 2^2 dot 3 dot 5.
  $
]

#example[Product-free or Sum-free Sets][
  Let $G = ZZ slash n ZZ$. Then we ask the question: how large can a
  subset $A subset G$ be such that:
  $
    (A + A) inter A = emptyset.
  $
  In this case we can have
  $
    |A| tilde (|G|) / 3 = n / 3.
  $
]

#example[Babai-Sos][
  What about non-abelian groups? Does there exist a $c > 0$ s.t.
  any $G$ has a product free set of size $>= c |G|$?
]
#theorem[Gowers 2008][
  Let $G = "SL"_2(FF_p)$. Then any subset $A subset G$ with $|A| >= p^(8/9)$.
  Is not a product field. But now we notice that $|G| approx p^3$.
  Thus the conjecture is false.
]

Next we consider a theorem of Delign and Katz (1988):

For $p$ prime take $a in FF_p^times$ let
$
  B(a,p) = 1 / (sqrt(p))sum_{x in FF_p} e^(2i pi (a x + x^3) / p).
$
Then $B(a,p) in RR$ (easy). Moreover, $|B(a,p)| <= 2$ (hard, Weil 1948).

If we let $p$ get large how are the $B(a,p)$ distributed in $[-2, 2]$
for the $p-1$ values of $a$.

#theorem[Deligne, Katz][
  For any $phi: [-2, 2] -> CC$ continous we have
  $
    integral_(-2)^2 phi(x) 1 / pi sqrt(1 - x^2 / 4) dif x =
    lim_(p -> oo) 1 / (p-1) sum_(a in FF_p^times) phi(B(a,p)).
  $
  Where the integral on the left is the "semi-circle distribution".
]

#theorem[Wiles, Taylor-Wiles, 1994][
  if $n >= 3$ and $a,b,c in ZZ$ then
  $
    a^n + b^n = c^n => a b c = 0.
  $
]

#remark[
  The proof of Fermat's last theorem uses representation theory multiple
  different ways.
]

= Basic Language

== Definitions and Examples

#definition[
  $G$ a group, $k$ a field, $V$ a $k$-vector space. A ($k$-linear) representation
  of $G$ on $V$ is a group homomorphism
  $
    rho: G -> "GL"(V).
  $
]

#remark[
  Often we think of $G, k$ as fixed and $V$ varies.
]

#remark[
  Concretely - a represetnation of $G$ on $V$ is an action of $G$ on $V$.
  Such that $G$ acts by $k$-linear transformations.
]

#example[Examples][
  1. trivial representation: $rho(g) = id_V$ for all $g in G$, denoted $1_V$.

  2. #[
      Suppose $G subset "GL"(V)$ then the inclusion map is a representation,
      called the tautological representation.
    ]

  3. #[
      $G = RR$ (with addition) then we can define
      $
        rho: G -> "GL"(CC) = CC^times, t |-> e^(i t).
      $
      is a 1-dimensional representation of $RR$.
    ]
  4. #[
      $G = S_n$
      - we can consider the representation $rho$ induced by the
        permutation matrices. I.e. $G$ permutes the dimensions of $V = k^n$.
        Note that this representation is injective, we way its faithful.

      - we can also consider the representation $epsilon$ induced
        by the signature
        of the permutation. I.e. we have
        $
          epsilon = det(rho) id_V.
        $
    ]
  5. #[
      $G = "GL"_(2, k)$ and let $n >= 0$. Consider
      $
        V_n = { p in k[X,y]: p "is homogeneous of degree n" }
      $
      (I.e. the polynomials spanned by $X^n, X^(n-1)Y, ..., X Y^(n-1), Y^n$)
      notice that $dim(V_n) = n + 1$ and we can define the representation
      $
        rho_n: G -> "GL"(V_n)
      $
      where for $rho_n (g) P = P((X,Y) dot g)$.
    ]
  6. #[
      $G$ be a group, $k$ a field. And $V = {f: G -> k}$ then we can consider
      the *left-regular representation*:
      $
        lambda_G(g) f(x) = f(g^(-1) x)
      $
      or *right-regular representation*:
      $
        rho_G (g) f(x) = f(x g).
      $
      (Note that both of these are left group actions, this is just confusing.
      But generally all group actions are assumed to be *left*.)
    ]
  7. #[
      $G = G_1 times G_2$ we can compose the left and right regular
      representations.
    ]
  8. #[
      $G$ a free group on generators $S$ then a representation
      $
        rho: G -> "GL"(V)
      $
      is uniquely determined by an element of $"GL"(V)^S$.
      If $G$ has generators $S$ and relation $R$ then
      $
        {rho: G -> "GL"(V)}
        isom
        { (u_s)_(s in S) in "GL"(V) | r((u_s)_(s in S)) = id_V forall r in R }.
      $
    ]
]

#definition[
  $G$ fixed and $k$ fixed given two representations $rho_1, rho_2$
  on $V_1, V_2$. A $G$-morphism (or intertwining operator)
  denoted $rho_1 -> rho_2$ is a $k$-linear map
  $
    u: V_1 -> V_2
  $
  such that $u dot rho_1(g) = rho_2(g) dot u$ for all $g in G$.

  The set of such operators is denoted by
  $
    "Hom"_G (rho_1, rho_2) = "Hom"_G (V_1, V_2).
  $
]

#remark[
  We use the notation
  $
    "End"_G (rho) = "Hom"_G (rho, rho).
  $
]

#remark[
  1. we have $
      "Hom"_G (V,W) subset "Hom"_k (V,W).
    $

  2. composition is well defined, i.e. we have a map
    $
      "Hom"_G (W, U) times "Hom"_G (V, W) -> "Hom"_G (V, U).
    $

  3. this composition is associative (as its the composition of linear maps).

  4. we have the identity map $id_V in "End"_G (V)$.

  I.e. representations of $G$ over $k$ form a sub category of the category
  of $k$-vector spaces.
]

#definition[
  A $G$-morphism with an inverse which is a $G$-morphism is called an
  isomorphism.
]

#remark[
  A $G$-morphism is an isomorphism iff it is a $k$-vector space isomorphism.
]

#example[
  1. #[
      $rho$ arbitary on $V$ and if $1_G$ denotes the trivial one-dim rep.
      of $G$ on $k$ by $g v = v$, then
      $
        "Hom"_G (1_G, rho) = { v in V | rho(g) v = v " " forall g in G } =: V^G
      $
      where the bijection is given by evaluating the morphism at $1 in k$.
    ]

  2. #[
      $rho$ arbitrary and $
    chi: G -> "GL"(k) = k^times
      $
      a one-dimensional representation (often called a character).
      $
        "Hom"_G (chi, rho) isom { v in V | rho(g) v = chi(g) v " "
          forall g in G }.
      $
      which are called the common eigenvectors of $chi$.

      For instance the right-regular representation $rho_G$ on
      $
        V = {phi: G -> k}
      $
      (by right multiplcation of the argument).
      Then we claim that
      $
        "Hom"_G (chi, rho_G) isom chi dot k
      $
      Indeed $chi in "Hom"_G(chi, rho_G)$ iff
      $
        forall g in G, forall x in G: (rho_G (g) phi)(x) = chi(g) phi(x) \
        <=> forall g in G, forall x in G:
        phi(x g) = chi(g) phi(x)
      $
      if this holds then for $x = e_G$ we get
      $
        phi(g) = chi(g) phi(e_G)
      $
      so in particular $phi in chi dot k$. The converse can be checked.
    ]
  3. #[
      $rho$ representation of $G$ on $V$. Let
      $
        W = "End"_k (V)
      $
      Then $G$ acts on $W$ by conjugation:
      $
        g dot u = rho(g) dot u dot rho(g)^(-1).
      $
      This is a representation.

      #remark[
        A nice fact:
        $
          "Hom"_G (1_G, "End"_k (V))
          isom { u: V -> V | forall g in G, g dot u = u} \
          = {u: V -> V | forall g in G, rho(g) dot u = u dot rho(g)} = "End"_G (V).
        $
      ]
    ]

  4. #[
      $G, rho_G, lambda_G$ the right, and left regular representations then
      there exists and explicit isomorphism
      $
        rho_G -> lambda_G
      $
      Indeed define
      $
        u(phi)(x) = phi(x^(-1)).
      $
      #remark[
        this is related to the fact that taking the inverse is an involution
        "converting" (bruh idk the proper way to say this in breavity) left
        and right haar measures.
      ]
    ]
]

== Subrepresentations, Irreducibility, Semi-simplicity

#definition[
  Let $k, G$ be fixed.

  1. #[
      A subrepresentation of
      $
        rho: G -> "GL"(V)
      $
      is a representation of the form
      $
        g |-> rho(g)|_W
      $
      for some $G$ invariant subspace $W$.
    ]

  2. #[
      The direct sum
      $
        plus.circle.big_(i in I) rho_i
      $
      is the representation on
      $
        plus.circle.big_(i in I) V_i
      $
      defined by
      $
        plus.circle.big_(i in I) rho_i (g) ((v_i)_(i in I)) =
        (rho_i (g) v_i)_(i in I).
      $
    ]

  3. #[
      Given $rho$ and a subrepresentation $rho'$ of $rho$ on $W$ there is
      a representation $rho slash rho'$ on $V slash W$ defined by
      $
        (rho slash rho') (g) (v + W) = rho(g) v + W.
      $
    ]
]

#example[
  If $V$ is finite dimensional the decoposition in the previous definition
  corresponds to the block matrix
  $
    mat(rho(g), *; , rho slash rho'(g)) ,
  $
]


#example[
  $G = CC$, $k = CC$ and $V = CC^2$ and
  $
    rho(z) = mat(1, z; , 1).
  $
]


#definition[
  $k, G$ fixed.

  1. #[
      A repr. $rho$ of $G$ on $V != {0}$ is irreducible if $V$ has no non-trivial
      $G$-invariant subspaces.
    ]

  2. #[
      $rho$ is called semisimple if and only if it is a
      direct sum of irreducible representations.
    ]

  3. #[
      $rho$ is called $pi$-isotypic for some irreducible representation $pi$
      if it is semisiple with all summands isomorphic to $pi$
      (e.g: $rho = pi plus.circle pi plus.circle pi$...).
    ]
]


#example[
  $G = CC, k = CC$ and $V=CC^2$ and

  1. #[
      $
        rho(z) = mat(1, z; , 1)
      $
      is not semisimple. If it were it would have to be
      - irreducible (no because $CC e_1$ is invariant / stable)
      - or a direct sum of two one-dim subrepresentations, so there is a
        basis which diagonalizes this matrix, but $rho(z)$ is not
        diagonalizable for any $z != 0$.
    ]

  4. #[
      $G = "SL"_n (CC), n >= 1$, $k = CC$ and
      $
        V = M_(n times n) (CC)
      $
      consider the adjoin representation
      $
        rho(g) (X) = g X g^(-1)
      $
      In this case $CC I_n$ is a stable subspace, and spans a
      trivial subrepresentation of dimension $1$.
      $
        M_(n times n) (CC) = CC I_n times M_(n times n)^0 (CC)
      $
      where $M_(n times n)^0(CC)$ are the matrices with trace zero.
    ]

  5. #[
      Warning. A representation of $G$ does not always contain an
      irreducible subrepresentation.

      In particular if $v$ is a non-zero vector in $V$, then the span
      of
      $
        {rho(g) v | g in G}
      $
      is a subrepresentation, but not always
      irreducible (e.g. see the action of $S_n$ on $k^n$).
    ]
]

#theorem[Maschke 1899][
  For $k$ of char. zero e.g $k = CC$ or $RR$, $G$ finite, every repr. is
  semisimple.
]


#theorem[Schur's Lemma][
  $G, k$

  1. #[
      If $rho$ is a repr. $pi$ is an irred. repr then any
      $u in "Hom"_G (pi, rho)$ is either $0$ or injective.
      And any $u in "Hom"_G (rho, pi)$ then is either $0$ or surjective.
    ]

  2. #[
      If $k$ is alg. closed and $pi$ is finite-dim then
      $
        "End"_G (pi) = k id_pi.
      $
    ]
]

#proofidea[
  For the first part we need to use the fact that $ker(u), im(u)$ are subrepresentations.

  For the finite dimensional part we use that any endomorphism has an eigenvalue.
]

#remark[
  When we talk about subreprsentations we sometimes abuse subspace notation. I.e. we identify
  subrepresentation with invariant subspaces.

  The reason why this makes sense, is that we can think of representations as vector spaces with extra structure.
  As opposed to a group homomorphism into a general linear group.
  Of course the two notions are equivalent.
]


#lemma[
  $G, k$ fixed, A representation $rho$ of $G$ on $V$ is semisimple if and only if
  every subrepresentation $W subset V$ there exists a complement $W' subset V$ such that
  $
    V = W plus.circle W'
  $
]

#proof[
  Look at lecture notes, not covered in class @Kowalski2011.
]

#proofidea[if $dim V < oo$][
  #[
    ($==>$):
    Assume $V = plus.circle.big_(i in I) W_i$ with $V_i$ irreducible.
    Let now $W subset V$ be a subrepresentation.

    *Warning*: in general we dont have $W = plus.circle.big_(i in J) W_i$ for some $J subset I$.

    #example[
      trivial group $G = {e}$, $V = k^2$ then the semisimple decomposition
      is $V = k e_1 plus.circle k e_2$ but any one-dim subspace $W$ is a subrepresentation.
    ]

    For each $i in I$ we have $W inter W_i subset W_i$ is a subrepresentation, so either
    ${0}$ or $W_i$ by irreducibility. Moreover unless $W=V$ it cant be $W_i$ for all $i$.

    So we have $i in I$ such that $W inter W_i = {0}$. Then $W plus.circle W_i subset V$ is a direct sum.
    We do induction and we can find $J subset I$ such that
    $
      plus.circle.big_(j in J) W_j
    $
    complements $W$.
  ]

  #[
    ($<==$): find $W_i subset V$ irred. find complements, decompose and repeat inductively.

    In infinite dimension we use Zorn's lemma to do this induction (like in the other direction). However it is not trivial to find
    non-trivial irreducible subrepresentations in infinite dimensions.

    In general, there are repr. without any irreducible subrepresentations (see exercise sheet 2).
  ]
]

#corollary[
  $G, k$ fixed.
  if $rho$ is semsimple, then any subrepr is semisimple, any quotient is semisimple. Any sum (not necessarily direct) of semisimple
  repr. is semisimple.
]

#proof[
  Let $W subset V$ be a subrep. We use the criterion of the lemma.
  Let $W_1 subset W$ be a subrep, but then its also a subrep of $V$ so by the lemma there eixsts a complement $W_1' subset V$ in $V$.
  Then $W_2 = W_1' inter W$ is a complement of $W_1$ in $W$.

  simlarly for quotients and sums @Kowalski2011.
]

#proposition[
  $G,k$ fixed. Let $rho = plus.circle.big_(i in I) rho_i$ be semismple with $rho_i$ pairwise non-isom and irred.

  Then any subrepresentation of $rho$ is the representation on
  $
    plus.circle.big_(i in J) V_i
  $
  for some $J subset I$.
]

#remark[
  The assumption, pairwise non-isom and irred is sometimes called *multiplicity free*.
]

#proof[
  Let $W' subset V$ be a subrep. By corollary we have that $W'$ is semisimple so
  its a direct sum of irreducible subrepresentations.

  So it is enough to prove that if $W$ is irreducible then $W = V_i$ for some $i in I$.

  Denote by $pi$ the representation on $W$. Let
  $
    p_i: rho -> rho_i
  $
  be the projection $V -> V_i$ given by the direct sum decomposition.

  We can check that since $V_i$ is a subrep. of $V$, $p_i in "Hom"_G (rho, rho_i)$.
  For $i in I$ we have $p_i|_W in "Hom"_G (pi, rho_i)$ so by Schur's lemma either $p_i|_W = 0$ or $p_i|_W$ is an isomorphism
  (since $rho_i$ is also irreducible).

  If $p_i|_W = 0$ for all $i$ then $W = {0}$. So some $p_i|_W$ is an isomorphism, so $W isom V_i$. This $i$ must be unique
  by multiplicity free assumption.
  So for $j != i$ $p_j|_W = 0$. This means
  $
    W subset V_i
  $
  so $W = V_i$ by irreducibility.
]

#example[Application][
  What integral linear relations may exist between complex roots of $f in ZZ[X]$ for $f != 0$?

  There is no restriction unless we assume someting about $f$, say $f$ is irreducible over $QQ$.

  We know that one relation occurs somewhat freqeuntly, namely:

  $
    alpha_1 + ... + alpha_d = 0
  $
  where $alpha_i$ are the distinct roots of $f$ and $d = deg(f)$.
  (if and only if the coefficient of $X^(d-1)$ is $0$).
]

#proposition[Girstmair, 1999][
  Assume that the Galois group $G$ of the splitting field $K = QQ(alpha_1, ..., alpha_d)$ of $f$ in $CC$ is $S_d$
  (acitng by permuting the roots).

  The only possible non-trivial integral linear relation between the roots of $f$ is that
  $
    alpha_1 + ... + alpha_d = 0.
  $
]

#proof[
  Let
  $
    R_f = {(n_1, ..., n_d) in QQ^d | n_1 alpha_1 + ... + n_d alpha_d = 0}
  $
  be the space of linear relations between the roots.
  This is a vector subspace of $QQ^d$.

  *Fact*:
  $R_f subset QQ^d$ is a subrepresentation of the representation of $G$ on $QQ^d$ by permuting the indices.

  I.e. for $sigma in G$ we have
  $
    sigma dot (n_i)_i = (n_(tilde(sigma)^(-1)(i)))_i
  $
  where $sigma(alpha_i) = alpha_(tilde(sigma)(i))$. Its a simple computation to check this.

  Moreover this repr. on $QQ^d$ is the same as permuting the canonical basis of $QQ^d$ that is
  $
    sigma dot e_i = e_(tilde(sigma)(i)).
  $
  (notice how here we dont have the inverse but it can be check that its infact the same.)

  Assume now that $G = S_d$ then we have already seen this representation as an example, moreover its semisimple
  and we have
  $
    QQ^d = QQ 1 plus.circle {(n_i) in QQ^d | sum n_i = 0}
  $
  and claimed that $W_d = {(n_i) in QQ^d | sum n_i = 0}$ is irreducible (if $d >= 2$).

  For $d >= 2$ these two are not isomorphic. Thus $QQ^d$ has a multiplicity free decomposition.
  For $d >= 3$ this is trivially true by dimensionality. For $d=2$ we can check directly that $W_2$
  is given by
  $
    W_2 = {(a, -a) | a in QQ}
  $
  which is not the trivial representation.

  The repr. on $QQ^d$ is multiplicity free.
  By the last proposition we have the following properties.

  We have few cases:

  1. $R_f = {0}$ no relations.

  2. $R_f = QQ 1$ which happens iff $alpha_1 = ... = alpha_d = 0$.

  3. $R_f supset W_d$ but then for $i != j$ we have $alpha_i - alpha_j = 0$ thus all roots are equal which
    cant be the case if $f$ is irreducible and $d >= 2$.

  Thus the only possible non-trivial relation is $R_f = QQ 1$ which concludes the proof.
]

== Multilinear Operations

#remark[Recall][
  Given a vector space $V$ and $W$ over $k$ then the tensorproduct
  $
    V times.circle_k W
  $
  of $V$ and $W$ is a vector space with a $k$-blinear map
  $
    b: V times W -> V times.circle_k W
  $
  such that for $k$ vector space $E$ and any $k$-bilinear map
  $
    beta: V times W -> E
  $
  there exists a unique linear map $u: V times.circle_k W -> E$ such that
  $
    beta = u dot b.
  $
  Moreover such a vector space exists and is unique up to unique isomorphism.
]

Given
$
  u_1: V_1 -> V_2 \
  u_2: W_1 -> W_2
$
there is a unique linear map
$
  u_1 times.circle u_2: V_1 times.circle W_1 -> V_2 times.circle W_2
$
such that
$
  (u_1 times.circle u_2) (v times.circle w) = u_1(v) times.circle u_2(w).
$

#definition[
  If $V$ and $W$ are given repr. $rho, tau$ of a group $G$ then defining
  $
    g |-> rho(g) times.circle tau(g)
  $
  gives a representation on $V times.circle W$ called the tensor product
  representation and denoted by
  $
    rho times.circle tau.
  $
]

#remark[
  We will see: if $G$ is finite and $k = CC$ and we start with
  $
    rho: G -> "GL"(V)
  $
  is faithful then decomposing
  $
    rho, rho times.circle rho, rho times.circle rho times.circle rho, ...
  $ you get
  all irreducible representations of $G$.
]

#remark[
  This extends to all other multilinear operations like symmetric and
  alternating.
]

#remark[
  it turns out that "in some sense" representations of $G$ on $CC$-v.s. allows
  you to recover $G$ up to isomorphism provided one also has
  extra data, the most important of which is the tensor operation.

  This is known as Tannaka-Krein duality.
]

#example[
  1. #[
      One uses tensor products to construct "new" representations e.g.
      $
        G = S_n, n >= 1
      $
      $rho_n$ the rep. on $V = CC^n$ given by permuting the coordinates.
      Then we have
      $
        rho = 1_(S_n) plus.circle tau_n
      $
      if we took direct sums we would not get anything new. However if we
      take tensor product we get e.g.:
      $
        rho times.circle rho =
        underbrace(1_(S_n) times.circle 1_(S_n), 1_(S_n))
        plus.circle underbrace(1_(S_n) times.circle tau_n, tau_n)
        plus.circle underbrace(tau_n times.circle 1_(S_n), tau_n)
        plus.circle (tau_n times.circle tau_n).
      $
      and we get
      $
        tau_n times.circle tau_n = "Sym"^2 tau_n plus.circle Lambda^2 tau_n
      $
      one can show that
      $
        Lambda^2 tau_n
      $
      is irreducible of dimension $((n-1)(n-2))/2$ so is different
      from $1_(S_n)$ and $tau_n$ if $n >= 4$.
      In general $"Sym"^m tau_n$ is not irreducible in general.
    ]
  2. #[
      $G = "SL"_2(CC)$ with $d >= 0$. $rho_d$ on
      $
        V_d = {f in CC[X, Y] : "hom. of " deg d}
      $
      by restricting the left-regular representation.
      One can show that
      $
        rho_d isom "Sym"^d rho_1
      $
      and $rho_1$ is given by the tautological representation
      $"SL"_2(CC) arrow.hook "GL"_2(CC)$.
    ]
]

#definition[
  Given $G, k, rho$. The contragradient (dual) of $rho$ is the representation
  $
    rho^vee: G -> "GL"(V^*)
  $
  by $(rho^vee (g) lambda)(v) = lambda(rho(g^(-1)) v)$ for $lambda in V'$ and
  $v in V$.
]

#remark[
  $rho$ is said to be self-dual if there is an isomorphism
  $
    rho --> rho^vee.
  $
]

== Changing $G$

"Changing" $G$ means relating repr. of $G$, $G$ given a morphism
$
  H --> G.
$

*Two Operations*

1. #[
    *restriction* to a subgroup $H subset G$.
    This is often used to study rep. of $G$ by exploiting what
    we know about repr. of $H$.
  ]

2. #[
    *induction* from a subgroup $H subset G$ to define/study
    repr. of $G$ using those of $H$.
  ]

#proposition[
  Let $H lt.tri G$ be a normal subgroup of $G$, $K = G slash H$. Then
  $
    {K -> "GL"(V)} &-> {"repr. " tilde(rho) " of " G " s.t. "
      H subset ker(tilde(rho))} \
    (rho: K -> "GL"(V)) &|-> (tilde(rho) := rho compose pi)
  $
  where $pi: G -> K$ is the quotient map.
]

#proofidea[
  The proof of this relies on the universal property of quotients and
  uses the representations are just group homomorphisms.
]

=== Restriction

#definition[
  $G, k, H < G$ fixed. Given $rho: G -> "GL"(V)$ we write
  $"Res"_H^G (rho)$ for $rho|_H$.
]

#remark[
  Note obvious compatibilities like
  - direct sums commute with restriction
  - tensor products commute with restriction
  - duals commute with restriction

  It is however not true in general that restrictions preserve properties such
  as irreducibility or semisimplicity (e.g. restriction to the trivial group).

  On the otherhand if a restriction is irreducible then the
  original representation is irreducible.
]

#example[
  $G = "SL"_2(CC), k = CC$.

  #proposition[2.7.12 @Kowalski2011][
    For $d >= 0$, $rho_d$ is irreducible.
  ]

  #proofidea[
    Restrict to
    $
      A = {a_t = mat(t, ; , t^(-1)) | t in CC^times} isom CC^times
    $

    *Claim*:
    $
      "Res"_A^("SL"_2(CC)) (rho_d) isom
      plus.circle.big_(i=0)^d CC X^i Y^(d-i)
    $
    where $CC X^i Y^(d-i)$ is an $A$-sub given by
    $
      a_t |-> t^(2i - d)
    $

    Indeed by def.
    $
      rho_d (a_t) (alpha X^i Y^(d-i)) =
      alpha (t X)^i (t^(-1) Y)^(d-i) = alpha t^(2i - d) X^i Y^(d-i).
    $
    Thus the restriction is multiplicity free. Indeed note that the characters
    $
      a_t |-> t^(2i - d)
    $
    for $i = 0, ..., d$ are pairwise different on $CC^times$, hence
    they are pairwise non-isomorphic as repr. of $A$.

    Let $W subset V_d$ be an $"SL"_2(CC)$-subrep. $W$ is also a subrep.
    of $"Res"_A^("SL"_2(CC)) (rho_d)$ so by one of the previous propositions
    $
      W = plus.circle.big_(i in I) CC X^i Y^(d-i)
    $
    for some $I subset {0, ..., d}$. Assume $I != emptyset$, and let
    $i_0 in I$. So let
    $
      e_0 = X^(i_0) Y^(d-i_0) in W.
    $
    Now we use
    $
      u^+ = mat(1, 1; , 1) in "SL"_2(CC).
    $
    Then
    $
      rho_d(u^+) e_0 = X^(i_0) (X + Y)^(d-i_0) = \
      X^d + (d-i_0) X^(d-1) Y + ... + X^(i_0) Y^(d-i_0) \
      in W = plus.circle.big_(i in I) CC X^i Y^(d-i).
    $
    but then $X^i Y^(d-i) in W$ for all $i >= i_0$ by linear independence.
    So if $i >= i_0$ then $i in I$. The same argument applied to
    $
      u^- = mat(1, ; 1, 1)
    $
    we get $I = {0, ..., d}$. Thus $W = V_d$ and $rho_d$ is irreducible.
  ]
]

#remark[Rewords][
  - $A$: cartan subgroup
  - $u^+, u^-$: unipotent elements
  - decomp. of restriction: weight space decomposition
]

=== Induction

Given $H < G$ induction constructs a repr. of $G$ out of a repr. of $H$;
this is related to restriction.

*Abstractly*, one defines a representation
$
  "Ind"_H^G rho
$
for $rho: H -> "GL"(V)$ such that frobenius reciprocity holds:

For $rho_1$ repr. of $G$ and $rho_2$ repr. of $H$ there is a $k$-linear
isomorphism
$
  "Hom"_G (rho_1, "Ind"_H^G rho_2) isom "Hom"_H ("Res"_H^G rho_1, rho_2).
$
We will make this more concrete.

#definition[
  $k, H<G$ fixed. Let $rho: H -> "GL"(V)$. Let
  $
    W = {f: G -> V: f(h g) = rho(h) f(g) " " forall h in H, g in G}
  $
  (the space of $rho$ equivariant functions.
  and let $G$ act on $W$ by right translation:
  $
    (g dot f)(x) = f(x g) in W.
  $
  for $f in W, g in G, x in G$. Then the resulting repr. of $G$ is denoted
  $
    "Ind"_H^G rho
  $
  and is called the representation of $G$ induced by $rho$.
]

#example[
  H = ${e_G}$ and $rho = 1$ then $W = {f: G -> k}$
  and
  $
    rho_G = "Ind"_H^G 1
  $
  is the right-regular representation.
]

#proposition[Frobenius Reciprocity][
  $k, H < G$ fixed. For any repr.
  $
    rho_1: G -> "GL"(V_1),\
    rho_2: H -> "GL"(V_2),
  $
  there are natural isomorphisms ($k$-vector spaces)
  $
    "Hom"_G (rho_1, "Ind"_H^G rho_2) isom "Hom"_H ("Res"_H^G rho_1, rho_2).
  $
]

#remark[
  For finite dimensions and (or?) finite groups the ordering above does not
  matter. However in generality this matters.
]

#proof[
  Given $H < G$ let
  $
    rho_1: G &-> "GL"(V_1),\
    rho_2: H &-> "GL"(V_2),\
    "Res"_H^G rho_1: H &-> "GL"(V_1),\
    "Ind"_H^G rho_2: G &-> "GL"(W_2)
  $
  Be as in the theorem. We will start by constructing the isomorphims in the
  obvious way. That is

  #set enum(numbering: "i")
  1. #[
      Given $V_1 -->^u &W_2 = {f: G -> V_2 :f " " rho_2"-equivariant"}$ we define
      $
        tilde(u): V_1 -> V_2
      $
      by $tilde(u)(v) = u(v)(e_G)$.
    ]

  2. #[
      Given $V_1 ->^u V_2$ we define
      $
        hat(u): V_1 -> W_2 = {f: G -> V_2 : f " " rho_2"-equivariant"}
      $
      by $hat(u)(v)(g) = u(rho_1(g) v)$.
    ]
  *Clear*:
  $
    u -> tilde(u),\
    u -> hat(u)
  $
  are $k$-linear maps.

  *We need to check*:

  1. #[
      $u -> tilde(u)$ sends $G$-maps to $H$-maps,
      $u -> hat(u)$ sends $H$-maps to $G$-maps,
      and the image of $hat(u)$ is $W_2$.
    ]

  2. $hat(u) isom u$

  3. $tilde(u) isom u$

  See @Kowalski2011[Prop.~2.3.9] for more details.

  1. #[
      We check that $hat(u)(v) in W_2$. Let $h in H$ consider
      $
        hat(u)(v) (h x) = u(rho_1(h x) v) = u(rho_1(h) rho_1(x) v)
        = rho_2(h) u(rho_1(x) v) = rho_2(h) hat(u)(v)(x).
      $
      thus $hat(u)(v) in W_2$. The remainder of this part can be done
      as an exercise.
    ]

  2. #[
      For this we compute
      $
        hat(tilde(u))
      $
      take $v in V_1$ then
      $
        tilde(u)(v) = u(v)(e_G)
      $
      then
      $
        hat(tilde(u))(v)(x) = tilde(u)(rho_1(x) v)
        = u(rho_1(x) v)(e_G)
        = ("Ind" rho_2)(x) u(v) (e_G) \
        = u(v)(e_G x) = u(v)(x)
      $
      thus
      $
        hat(tilde(u)) = u
      $
      for all $v$.
    ]
]

#example[
  $k$ a field, $G$ a group we saw that
  $
    rho_G = "Ind"_({e_G})^G (1).
  $
  Let $pi$ be any representation of $G$ on $V$ then Frobenius reciprocity
  gives reciprocal isomorphisms
  $
    "Hom"_G (pi, rho_G) <-->^tilde "Hom"_({e_G}) (V, k) = "Hom"_k (V, k) = V'.
  $
  What are the $pi -> rho_G$? Let $lambda in V'$ Then the construction above
  associates to $lambda$ the $G$-morphism
  $
    u_lambda: pi -> rho_G
  $
  defined by
  $
    u_lambda (v) (g) = lambda(pi(g) v).
  $
]

#definition[
  Given $k, G, rho$ A *matrix coefficient* of $rho$ is a function
  $f: G -> k$ of the form
  $
    f(x) = lambda(rho(x) v)
  $
  for some $lambda in V'$ and $v in V$.
]

#remark[
  $V$ finite dimensional let $e_i$ be a basis of $V$ and $lambda_i$ the
  associated dual basis. Then the matrix coefficients
  $
    lambda_i (rho(x) e_j)
  $
  is the coefficient in the $i$-th row and $j$-th column of the matrix
  representing $rho(x)$ in the basis $e_i$.

  $
    rho(x) = mat(lambda_i (rho(x) e_j))_(i, j).
  $
]

#remark[
  Many (if not most) special functions of classical analysis
  are matrix coefficients of suitable representation of certain groups.
]

#example[
  $k = RR, G = RR$
  and
  $
    R &-> "GL"_2 (RR), \
    t &-> mat(cos t, -sin t; sin t, cos t)
  $
  is a repr of $RR$, and the matrix coefficients we get from
  the standard basis are $sin$ and $cos$. From this fact we also
  get all the addition formulas for $sin$ and $cos$.
]

== Further Properties of $"Res"$ and $"Ind"$

1. *Functoriality*
  #[
    Given $H subset G$ and $rho_i: G -> "GL"(V_i)$
    and $rho_1 -->^u rho_2$ a $G$-morphism. We get
    $
      "Res" rho_1 -->^u "Res" rho_2
    $
    Similarly for $pi_i: H -> "GL" (V_i)$
    and $pi_1 ->^u pi_2$ an $H$-moprhism there is a $G$-morphism
    $
      "Ind"(u): "Ind" pi_1 -> "Ind" pi_2.
    $
    given by
    $
      "Ind"(u)(f)(g) = u(f(g)).
    $
    moreover we also have
    $
      "Ind"(u compose v) = "Ind"(u) compose "Ind"(v),
      "Ind"(id_pi) = id_("Ind"(pi)).
    $
    (the same clearly also holds for $"Res"$).
  ]

2. *Dimension*
  #[
    $
      dim "Res"_H^G (rho) = dim rho
    $
    and if $G$ is finite
    $
      dim "Ind"_H^G (pi) = [G:H] dim pi
    $
    otherwise both are infinite (not necessarily the same cardinality).
  ]

3. *Projection Formula* @Kowalski2011[2.3.18]:
  #[
    Given
    $
      rho_1: G -> "GL" (V_1)\
      rho_2: H -> "GL" (V_2)
    $
    there are "natural" isomorphisms
    $
      "Ind"_H^G (rho_2) times.circle rho_1 -->^u
      "Ind"_H^G (rho_2 times.circle "Res"_H^G rho_1)
    $
    *Interpretation*:
    The class of representations of $G$ optained by inducing representations
    of $H$ are stable under $plus.circle$ and $times.circle$
    (indeed direct sum commutes with induction (exercise))
    In that sense this class is an ideal (stable under external
    multiplication).

    To get this define $u$ by
    $
      u(f times.circle v)(x) = f(x) times.circle rho_1(x) v
    $
  ]

4. *Transitivity* @Kowalski2011[2.3.20]
  #[
    Given $H_2 subset H_1 subset G$ then you have natural isomorphisms
    $
      "Res"_(H_2)^G rho = "Res"_(H_2)^(H_1) ("Res"_(H_1)^G rho)
    $
    and
    $
      "Ind"_(H_2)^G (rho) isom "Ind"_(H_2)^(H_1) ("Ind"_(H_1)^G rho)
    $
  ]

#remark[
  One can recover / prove abstractly some of these facts using only
  Frobenius Reciprocity as a characterization of the induced representation.

  See recording of 02.10.2025 for more details
]


#bibliography("bib.bib", full: true)
