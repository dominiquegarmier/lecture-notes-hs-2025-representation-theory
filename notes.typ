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
  If $G$ is a finite group and $|G| = p^a q^b$ for some primes $p, q$,
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

]

#bibliography("bib.bib", full: true)
