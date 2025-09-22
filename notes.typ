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
      A repr. $rho$ of $G$ on $V != {0}$ is irreducizible if $V$ has no non-trivial
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

#theorem[Blaschhe][
  For $k$ of char. zero e.g $k = CC$ or $RR$, $G$ finite, every repr. is
  semisimple.
]


#theorem[Schur's Lemma][
  $G, k$

  1. #[
      If $rho$ is a repr. $pi$ is an irred. repr then any
      $u in "Hom"_G(phi, rho)$ is either $0$ or injective.
      And any $u in "Hom"_G(rho, pi)$ then is either $0$ or surjective.
    ]

  2. #[
      If $k$ is alg. closed and $pi$ is finite-dim then
      $
        "End"_G (pi) = k id_pi.
      $
    ]
]



#bibliography("bib.bib", full: true)
