# Kakeya

### Core Proof DAG

> Each section below begins with the Blueprint roadmap card statement in a blockquote (`>`), followed by the dependency tree (`✔` indicates a verified Lean declaration) and the exact mathematical translation of the Lean definitions and theorems.

#### WZ2 Definition 2.12

> The tubes are essentially distinct. For every $\rho_0 \in [\delta, 1]$, there are $\rho \in [\rho_0, A \rho_0)$ and $\rho$-tubes $\mathcal T_\rho$ such that:
> 1. $\mathcal T_\rho$ is an $A$-uniform partitioning cover of $\mathcal T$
> 2. for each parent, the unit-rescaled child family satisfies the convex Wolff axiom with error $A$.
> 
> This is the root hypothesis; neither a direction-separated cover nor self-similar child counts is stipulated.

##### tags: `Kakeya.Assouad.WZ2PaperPureCWAAtNearbyScales`

```
WZ2PaperPureCWAAtNearbyScales ✔
├─ WZ2PaperFiniteErrorConstant ✔
├─ WZ2PaperOrdinaryIsEssentiallyDistinct ✔
│  └─ wz2PaperCenteredDilatedCarrier ✔
│     └─ wz2PaperTubeMidpoint ✔
├─ WZ2PaperRequestedScale ✔
└─ WZ2PaperPureNearbyScaleCoverData ✔
   └─ WZ2PaperPureScaleCoverData ✔
      ├─ WZ2PaperPurePartitioningCover ✔
      │  ├─ wz2PaperOrdinaryFullFiberIndices ✔
      │  └─ wz2PaperOrdinaryDilatedFiberIndices ✔
      │     └─ wz2PaperCenteredDilatedCarrier ✔
      ├─ WZ2PaperPureFullFibersAreCUniform ✔
      │  └─ wz2PaperOrdinaryFullFiberCount ✔
      │     └─ wz2PaperOrdinaryFullFiberIndices ✔
      └─ WZ2PaperPureUnitRescaledFullFiberData ✔
         ├─ WZ2PaperAssouadUnitRescalingData ✔
         ├─ wz2PaperPureUnitRescaledFullFiberBodyFamily ✔
         │  ├─ wz2PaperOrdinaryFullFiberIndices ✔
         │  ├─ wz2PaperOrdinaryFullFiberIndexEquiv ✔
         │  └─ WZ2PaperAssouadUnitRescalingData.map ✔
         └─ WZ2PaperBodyConvexWolffBound ✔
```

Basic Definitions:
1. **$\delta$-tube**: closed $\delta$-neighbourhood of a unit line segment (`Kakeya.Streamlined.TubeFamily`)
2. **Essentially distinct**: $\mathbb T$ is essentially distinct if $T_i \nsubseteq 2 \cdot T_j$ and $T_j \nsubseteq 2 \cdot T_i$ for every $i \neq j$. Here $2 \cdot T$ means dilation about the center of $T$  factor of $2$. (`Kakeya.Assouad.wz2PaperCenteredDilatedCarrier`, `Kakeya.Assouad.WZ2PaperOrdinaryIsEssentiallyDistinct`)
3. **$\mathbb T[T_\rho]$**: $\{T \in \mathbb T : T \subseteq T_\rho\}$ (`Kakeya.Assouad.wz2PaperOrdinaryFullFiberIndices`)
4. **Unit rescaling**:
	- Ellipsoid (centered at $\hbf c$ under linear equivalence $A$): $\thbf c + A(\overline{B(0, 1)})$ (`JohnEllipsoid.ellipsoid`)
	- Outer John ellipsoid of a set $K$: an ellipsoid of minimum volume containing $K$ (`JohnEllipsoid.IsOuterJohnEllipsoid`)
	- Unit rescaling relative to $T_\rho$: choose an outer John ellipsoid of $T_\rho$, centered at $\mathbf c$ under linear equivalence $A$. Then  unit rescaling relative to $T_\rho$ is the affine equivalence $\phi_{T_\rho}: \thbf x \mapsto A^{-1} (\thbf x - \mathbf c)$ h which sends the outer John ellipsoid of $T_\rho$ to the unit ball centered at $\thbf 0$. (`Kakeya.Assouad.WZ2PaperAssouadUnitRescalingData.map`)
5. **Convex Wolff Axiom**: a multi-set $\mathcal S$ of sets in $\mathbb R^3$ satisfies the CWA with error $C$ if for all convex sets $W \subseteq \mathbb R^3$, we have $\# \mathcal S[W] \leq C|W|(\# \mathcal S)$ (`Kakeya.Assouad.WZ2PaperBodyConvexWolffBound`, $C \in [0, +\infty]$)
6. **$C$-uniform**: $\mathbb T_\rho$  $C$-uniform over $\mathbb T$ if $\# \mathbb T[T_\rho] \leq C (\# \mathbb T[T_\rho'])$ for every $T_\rho, T_\rho' \in \mathbb T_\rho$ (`Kakeya.Assouad.WZ2PaperPureFullFibersAreCUniform`, $C \in [0, +\infty]$)
7. **Partitioning cover**: $\mathbb T_\rho$ is a partitioning cover of $\mathbb T$ if:
	- $\forall T \in \mathbb T, \exists T_\rho \in \mathbb T_\rho, T \in \mathbb T[T_\rho]$
	- $\forall i \neq j, \mathbb T[2 \cdot T_{\rho, i}]$ and $\mathbb T[2 \cdot T_{\rho,j}]$ are disjoint
	- (`Kakeya.Assouad.WZ2PaperPurePartitioningCover`)

- `Kakeya.Assouad.WZ2PaperPureUnitRescaledFullFiberData`: he unit rescaling $\phi_{T_\rho}(\mathbb T[T_\rho])$ relative to $T_\rho$ satisfies the CWA with error $C$ ($C \in [0, +\infty]$)

8. **CWA at scale**: Let $C \in [0, + \infty], \delta > 0, \rho > 0$.  ammathbb T$ of $\delta$-tubes satisfies the CWA at scale $\rho$ with error $C$ if there exists a  of $\rho$-tubes $\mathbb T_\rho$ such that:
	- $\mathbb T_\rho$ is a $C$-uniform partitioning cover of $\mathbb T$
	- For each $T_\rho \in \mathbb T_\rho$, the unit rescaling o\mathbb T[T_\rho]$ relative to $T_\rho$with error $$
	- (`Kakeya.Assouad.WZ2PaperPureScaleCoverData`)

- `Kakeya.Assouad.WZ2PaperPureNearbyScaleCoverData`: given a requested scale $\rho_0 \in [\delta, 1]$, this packages a scale $\rho \in [\rho_0, C\rho_0)$ together with a witness that $\mathbb T$ satisfies the CWA at cae $\rho$ with error $C$. (Note: only $\rho_0 \leq 1$ is stipulated; $\rho$ itself may exceed $1$.)

**CWA at nearby scales (WZ2 Def 2.12 / CWA at every scale)**:

Let $C \in [1, + \infty), \delta > 0$. A family $\mathbb T$ of $\delta$-tubes satisfies the CWA at nearby scales with error $C$ if the tubes in $\mathbb T$ are essentially distinct, and for every $\rho_0 \in [\delta, 1]$, there exists $\rho \in [\rho_0, C \rho_0)$ such that $\mathbb T$ satisfies the CWA at cale $\rho$ with error $C$. (`Kakeya.Assouad.WZ2PaperPureCWAAtNearbyScales`)

---

#### WZ2 Lemma 2.13

> If $\mathcal T$ satisfies the multi-scale convex Wolff axiom with error $A$, then for every $\rho_0 \in [\delta, 1]$ one can choose $\rho \in [\rho_0, A\rho_0]$ and a $\rho$-cover whose coarse family and every unit-rescaled child family satisfy the same multi-scale condition with error $O(A)$.
> Partitioning forces the child-incidence clusters at successive scales to form a nested tree.

##### tags: *(no standalone Lean declaration)*

There is no standalone Lean theorem corresponding to general multi-scale inheritance. Instead, the Proposition 6.2 construction directly builds the nearby-scale covers and unit-rescaled fiber certificates for the specific coarse and fine families it produces.

---

#### WZ2 Section 6.2

> Let $Bad(s)$ mean: for every $\eta, \delta_0 > 0$, some $0 < \delta \leq \delta_0$ has multi-scale convex Wolff error $\delta^{-\eta}$, shading density $\delta^\eta$, and $|E_C| \leq \delta^s$. Define $\sigma = \sigma_{CW}=\sup(\{0\} \cup \{s > 0 : Bad(s)\})$. Failure of Theorem 5.2 gives $\sigma > 0$. This is a new deficit for a different admissible class, not WZ1's $\sigma_3$.

##### tags: `Kakeya.Assouad.PureWZ2Admissible`, `Kakeya.Assouad.pure_wz2_node02_critical_extraction` (`Kakeya.Assouad.PureWZ2CriticalExtractionStatement`)

```
PureWZ2CriticalExtractionStatement ✔
├── PureWZ2SubunitPackageStatement ✔
│   ├── PureWZ2FullFiberAssertionDRefinementStatement ✔
│   │   ├── PureWZ2FullFiberAssertionDRefinementData ✔
│   │   │   ├── WZ2PaperPureOneScaleRescalingBridge ✔
│   │   │   │   ├── wz2PaperPureFullFiberSubfamily ✔
│   │   │   │   │   ├── Kakeya.Streamlined.TubeSubfamily ✔
│   │   │   │   │   └── Kakeya.Streamlined.TubeSubfamily.fromFinset ✔
│   │   │   │   ├── WZ2PaperLiteralUnitRescaledFamilyData ✔
│   │   │   │   │   ├── WZ1PaperIsLineClass ✔
│   │   │   │   │   │   └── WZ1PaperTubeInLineClass ✔
│   │   │   │   │   │       ├── wz1PaperDirection ✔
│   │   │   │   │   │       │   └── Point3 ✔
│   │   │   │   │   │       └── wz1TubeAxisZeroPoint ✔
│   │   │   │   │   ├── tubeAxisLine ✔
│   │   │   │   │   └── wz2PaperLiteralUnitRescalingMap ✔
│   │   │   │   │       └── unitRescalingMap ✔
│   │   │   │   │           ├── householderToE3 ✔
│   │   │   │   │           │   └── e3 ✔
│   │   │   │   │           └── transverseScaleLin ✔
│   │   │   │   │               └── point3 ✔
│   │   │   │   ├── WZ2PaperAssouadUnitRescalingData.ofTube ✔
│   │   │   │   ├── WZ2PaperAssouadToLiteralRescalingCertificate ✔
│   │   │   │   └── Kakeya.Streamlined.TubeFamily.toBodyFamily ✔
│   │   │   │       └── Kakeya.Streamlined.tubeBody ✔
│   │   │   ├── Kakeya.FrostmanSlabWolffBound ✔
│   │   │   │   ├── Kakeya.Slab ✔
│   │   │   │   ├── Kakeya.Slab.carrier ✔
│   │   │   │   │   ├── Kakeya.DeltaTube.unitBall ✔
│   │   │   │   │   └── Kakeya.Slab.hyperplane ✔
│   │   │   │   ├── Kakeya.TubeFamily ✔
│   │   │   │   ├── Kakeya.TubeFamily.containedCount ✔
│   │   │   │   └── Kakeya.TubeFamily.enncard ✔
│   │   │   ├── Kakeya.KatzTaoConvexWolffBound ✔
│   │   │   │   └── Kakeya.deltaTubeVolume ✔
│   │   │   ├── Kakeya.Shading ✔
│   │   │   ├── Kakeya.Shading.IsLambdaDense ✔
│   │   │   │   ├── Kakeya.Shading.mass ✔
│   │   │   │   └── Kakeya.TubeFamily.mass ✔
│   │   │   │       └── Kakeya.DeltaTube.volume ✔
│   │   │   ├── Kakeya.Shading.union ✔
│   │   │   ├── Kakeya.Streamlined.Shading ✔
│   │   │   ├── Kakeya.Streamlined.Shading.mass ✔
│   │   │   ├── Kakeya.Streamlined.Shading.union ✔
│   │   │   ├── Kakeya.Streamlined.TubeFamily.Nonempty ✔
│   │   │   ├── Kakeya.Streamlined.TubeFamily.enncard ✔
│   │   │   ├── Kakeya.Streamlined.TubeShading ✔
│   │   │   ├── Kakeya.TubeFamily.IsEssentiallyDistinct ✔
│   │   │   │   └── Kakeya.DeltaTube.EssentiallyDistinct ✔
│   │   │   ├── Kakeya.TubeFamily.IsInUnitBall ✔
│   │   │   │   └── Kakeya.DeltaTube.IsInUnitBall ✔
│   │   │   └── Kakeya.realRpowENN ✔
│   │   └── Kakeya.Streamlined.Shading.IsLambdaDense ✔
│   │       └── Kakeya.Streamlined.BodyFamily.mass ✔
│   │           └── Kakeya.Streamlined.Body.volume ✔
│   ├── PureWZ2WolffFloorFromAssertionDStatement ✔
│   │   ├── Kakeya.AssertionD ✔
│   │   │   └── Kakeya.AssertionDLowerBound ✔
│   │   └── PureWZ2WolffVolumeFloor ✔
│   └── PureWZ2WolffFloorImpliesSubunitCeilingStatement ✔
│       └── PureWZ2Admissible ✔
├── PureWZ2Theorem5_2Statement ✔
└── PureWZ2CriticalPackage ✔
    ├── PureWZ2ExtremalConfiguration ✔
    │   └── WZ2PaperPureIsExtremal ✔
    └── PureWZ2CriticalVolumeFloor ✔
```

Basic Definitions:

> A remark on tube families in the formalization:
>
> There are two representations: the indexed tube family (`Kakeya.Streamlined.TubeFamily`) and the de-duplicated tube family (`Kakeya.TubeFamily`, a `Finset` of `DeltaTube`).
>
> By default, $\mathbb T$ refers to an indexed tube family; we explicitly write **de-duplicated** whenever `Kakeya.TubeFamily` is used. For an indexed family, writing $T \in \mathbb T$ refers to the index, though we often abuse notation and write $T$ for its carrier when clear from context. Note also that `DeltaTube` stores a basepoint and unit direction vector, so reversing the segment orientation yields a distinct `DeltaTube` record even in a de-duplicated family.

1. **Shading**: A shading of $\mathbb T$ is an indexed family of measurable subsets $Y(T) \subseteq T$ for each $T \in \mathbb T$; we write $E_Y = \bigcup_{T \in \mathbb T} Y(T)$ (`Kakeya.Streamlined.Shading`; `Kakeya.Shading` is the counterpart for de-duplicated families)
2. **Essentially distinct (2025)**: A **de-duplicated** family $\mathbb T$ is essentially distinct (2025) if $|T \cap T'| \leq \frac{1}{2}\max(|T|, |T'|)$ for every $T \neq T' \in \mathbb T$ (`Kakeya.TubeFamily.IsEssentiallyDistinct`)
3. **$\lambda$-dense**: Let $\lambda \in [0, +\infty]$. A pair $(\mathbb T, Y)$ is $\lambda$-dense if $\lambda \sum_{T \in \mathbb T}|T| \leq \sum_{T \in \mathbb T}|Y(T)|$ (`Kakeya.Streamlined.Shading.IsLambdaDense`; `Kakeya.Shading.IsLambdaDense` for de-duplicated families)
4. **Katz–Tao convex Wolff bound with constant $C$**: For a **de-duplicated** family $\mathbb T$ of $\delta$-tubes, $\# \mathbb T[W] \leq C |W| / |T|$ for every convex set $W \subseteq \mathbb R^3$, where $|T| = v_\delta$ is the common volume of a $\delta$-tube (`Kakeya.KatzTaoConvexWolffBound`)
5. **Slab**: Given a unit normal $\mathbf n \in \mathbb R^3$, offset $a \in \mathbb R$, and thickness $r \geq 0$, the slab is the intersection of $\overline{B(0,1)}$ with the closed $r$-neighbourhood of the hyperplane $\{\mathbf x \in \mathbb R^3 : \langle \mathbf x, \mathbf n \rangle = a\}$ (`Kakeya.Slab.carrier`)
6. **Frostman slab Wolff bound with constant $C$**: For a **de-duplicated** family $\mathbb T$, $\# \mathbb T[W] \leq C |W| (\# \mathbb T)$ for every slab $W$ (`Kakeya.FrostmanSlabWolffBound`)
7. **Fixed-constant unit rescaling relative to $T_\rho$** (`Kakeya.Assouad.wz2PaperLiteralUnitRescalingMap`):
	- Let $l = l(T_\rho)$ be the coaxial line of $T_\rho$, meeting the plane $\{z = 0\}$ at $A$ (`Kakeya.Assouad.wz1TubeAxisZeroPoint`).
	- Let $\mathbf d$ be the unit direction vector of $T_\rho$, and orient it upward by setting $\tilde{\mathbf d} = \mathbf d$ if $d_3 \geq 0$ and $\tilde{\mathbf d} = -\mathbf d$ otherwise.
	- Let $R$ be the reflection across the plane through the origin with normal $\tilde{\mathbf d} - \mathbf e_3$ (or $R = \mathrm{id}$ when $\tilde{\mathbf d} = \mathbf e_3$).
	- Let $D(x, y, z) = (x/\rho, y/\rho, z)$ be the transverse scaling map.
	- The fixed-constant unit rescaling map is $\varphi_{T_\rho}(\mathbf x) = \frac{1}{100} D(R(\mathbf x - A))$.
8. **Line class $\mathcal L_3$**: A $\delta$-tube $T$ belongs to $\mathcal L_3$ if its upward-oriented direction $\tilde{\mathbf d}$ and $\{z = 0\}$ intercept $A = (A_1, A_2, 0)$ satisfy $\tilde{d}_3 \geq 1/2$, $|A_1| \leq 1/3$, and $|A_2| \leq 1/3$ (`Kakeya.Assouad.WZ1PaperTubeInLineClass`, family version `Kakeya.Assouad.WZ1PaperIsLineClass`)
- `Kakeya.Assouad.WZ2PaperLiteralUnitRescaledFamilyData`: For a family $\mathbb T$ of $\delta$-tubes and a $\rho$-tube $T_\rho$ ($\rho > 0$), this structure gives a family $\mathbb T_q$ of $q$-tubes ($q = \delta/\rho$) in $\mathcal L_3$ and a bijection $f : \mathbb T_q \to \mathbb T$ such that $l(T) = \varphi_{T_\rho}(l(f(T)))$ for all $T \in \mathbb T_q$.
- `Kakeya.Assouad.WZ2PaperAssouadToLiteralRescalingCertificate`: Given $\mathbb T$, $T_\rho$ ($\rho > 0$), a `WZ2PaperLiteralUnitRescaledFamilyData` with target family $\mathbb T_q$ and bijection $f : \mathbb T_q \to \mathbb T$, and a constant $C_j \in [0, +\infty]$, this structure gives an ordinary family $\mathbb P_q$ of $q$-tubes, bijections $g_1 : \mathbb P_q \to \mathbb TT$ and $g_2 : \mathbb T_q \to \mathbb P_q$, and an affine automorphism $h$ of $\mathbb R^3$ such that:
	- $g_1 \circ g_2 = f$
	- $l(g_2(T)) = l(T)$ for all $T \in \mathbb T_q$
	- $h(\phi_{T_\rho}(f(T))) = \varphi_{T_\rho}(f(T))$ for all $T \in \mathbb T_q$
	- $\varphi_{T_\rho}(f(T)) \subbseteq g_2(T)$ for all $T \in \mathbb T_q$
	- $W$ is convex $\Rightarrow h^{-1}(W)$ is convex
	- $\forall S \subseteq \mathbb R^3, |h^{-1}(S)| \leq C_j |S|$
- `Kakeya.Assouad.WZ2PaperPureOneScaleRescalingBridge`: Given a family $\mathbb T$ of $\delta$-tubes, a family $\mathbb T_\rho$ of $\rho$-tubes ($\rho > 0$), a parent $T_\rho \in \mathbb T_\rho$, and $C \in [0, +\infty]$, this structure packages:
	- a `WZ2PaperLiteralUnitRescaledFamilyData` on $(\mathbb T[T_\rho], T_\rho)$, with target family $\mathbb T_q$,
	- a `WZ2PaperAssouadToLiteralRescalingCertificate` on that data with $C_j = 4000000$, producing the ordinary $q$-tube family $\mathbb P_q$ and bijection $g_1 : \mathbb P_q \to \mathbb T[T_\rho]$,
	- a witness that $\mathbb P_q$ satisfies the CWA with error $4000000 C$.
- `Kakeya.Assouad.PureWZ2FullFiberAssertionDRefinementData`: Fix real parameters $\varepsilon_o, \varepsilon_a, \kappa, \eta_a, \delta$, a constant $C \in [0, +\infty]$, and a shaded configuration $(\mathbb T, Y)$ at scale $\delta$. This structure consists of:
	- a `WZ2PaperPureNearbyScaleCoverData` for $\mathbb T$ at some requested scale $\rho_0 \in [\delta, 1]$ with error $C$, giving an actual selected scale $\rho \in [\rho_0, C\rho_0)$ with $q = \delta/\rho \in (0, 1]$ and coarse family $\mathbb T_\rho$,
	- a parent $T_\rho \in \mathbb T_\rho$ with $\mathbb T[T_\rho] \neq \varnothing$, together with a witness (`WZ2PaperPureUnitRescaledFullFiberData`) that $\phi_{T_\rho}(\mathbb T[T_\rho])$ satisfies the CWA with error $C$,
	- a `WZ2PaperPureOneScaleRescalingBridge` on $(\mathbb T, \mathbb T_\rho, T_\rho, C)$, giving the family $\mathbb P_q$ of $q$-tubes, the bijection $g_1 : \mathbb P_q \to \mathbb T[T_\rho]$, and the affine coordinate change $h$,
	- a shading $Y_{\mathbb P_q}$ on $\mathbb P_q$ satisfying $Y_{\mathbb P_q}(P) \subseteq (h \circ \phi_{T_\rho})(Y(g_1(P)))$ for every $P \in \mathbb P_q$,
	- a nonempty subfamily $\mathbb S_q \subseteq \mathbb P_q$ (with index embedding $\iota : \mathbb S_q \hookrightarrow \mathbb P_q$) and a subshading $Y_{\mathbb S_q}(S) \subseteq Y_{\mathbb P_q}(\iota(S))$ retaining cardinality and mass up to $q^{\varepsilon_a}$:
	  $$q^{\varepsilon_a} \#\mathbb P_q \leq \#\mathbb S_q, \qquad q^{\varepsilon_a} \sum_{P \in \mathbb P_q} |Y_{\mathbb P_q}(P)| \leq \sum_{S \in \mathbb S_q} |Y_{\mathbb S_q}(S)|,$$
	- a **de-duplicated** family $\mathbb F_q$ of $q$-tubes and a bijection $j : \mathbb F_q \to \mathbb S_q$ such that each $T \in \mathbb F_q$ equals $\mathbb S_q(j(T))$ and contains the rescaled source tube $(h \circ \phi_{T_\rho})(g_1(\iota(j(T))))$,
	- a shading $Y_{\mathbb F_q}$ on $\mathbb F_q$ given by $Y_{\mathbb F_q}(T) = Y_{\mathbb S_q}(j(T))$, satisfying $\bigcup_{T \in \mathbb F_q} Y_{\mathbb F_q}(T) \subseteq (h \circ \phi_{T_\rho})(\bigcup_{T \in \mathbb T} Y(T))$,
	- the Assertion D hypotheses on $(\mathbb F_q, Y_{\mathbb F_q})$ at scale $q$:
		- every tube in $\mathbb F_q$ is contained in $\overline{B(0,1)}$,
		- $\mathbb F_q$ is essentially distinct **(2025)**,
		- $(\mathbb F_q, Y_{\mathbb F_q})$ is $q^{\eta_a}$-dense,
		- $\mathbb F_q$ satisfies the Katz–Tao convex Wolff bound and the Frostman slab Wolff bound with constant $q^{-\eta_a}$,
		- $\#\mathbb F_q \geq q^{-2+\varepsilon_a}$,
	- a finite factor $\beta > 0$ transferring the Assertion D lower bound from $\mathbb F_q$ back to $\mathbb T$:
		- $\delta^{1/2+\varepsilon_o} \leq \beta \, \kappa \, q^{\varepsilon_a} (\#\mathbb F_q) v_q \bigl((\#\mathbb F_q) v_q^{1/2}\bigr)^{-1/2}$
		- $\beta \bigl|\bigcup_{T \in \mathbb F_q} Y_{\mathbb F_q}(T)\bigr| \leq \bigl|\bigcup_{T \in \mathbb T} Y(T)\bigr|$, where $v_q$ is the volume of a $q$-tube.
- `Kakeya.Assouad.PureWZ2FullFiberAssertionDRefinementStatement`: For every $0 < \varepsilon_a < \varepsilon_o$, $\kappa > 0$, and $\eta_a > 0$, there exist $\eta > 0$ and $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$ and every nonempty $\delta$-tube configuration $(\mathbb T, Y)$ where $\mathbb T$ satisfies the CWA at nearby scales with error $\delta^{-\eta}$ and $(\mathbb T, Y)$ is $\delta^\eta$-dense, either
  $$\delta^{1/2+\varepsilon_o} \leq \Bigl|\bigcup_{T \in \mathbb T} Y(T)\Bigr|,$$
  or there exists a `PureWZ2FullFiberAssertionDRefinementData` for $(\mathbb T, Y)$ with parameters $(\varepsilon_o, \varepsilon_a, \kappa, \eta_a, \delta)$ and $C = \delta^{-\eta}$.
9. **Assertion D lower bound**: For a **de-duplicated** family $\mathbb F$ of $\delta$-tubes, a shading $Y$, and real parameters $\kappa, \sigma, \omega, \varepsilon$, the Assertion D lower bound is
   $$\Bigl|\bigcup_{T \in \mathbb F} Y(T)\Bigr| \geq \kappa \, \delta^{\omega+\varepsilon} (\#\mathbb F) \, v_\delta \bigl((\#\mathbb F) v_\delta^{1/2}\bigr)^{-\sigma},$$
   where $v_\delta$ is the volume of a $\delta$-tube (`Kakeya.AssertionDLowerBound`).
10. **Assertion $D(\sigma, \omega)$**: We have $\sigma, \omega \geq 0$, and for every $\varepsilon > 0$, there exist $\kappa, \eta > 0$ such that for every $\delta > 0$ and every **de-duplicated** configuration $(\mathbb F, Y)$ at scale $\delta$ whose tubes lie in $\overline{B(0, 1)}$, are essentially distinct **(2025)**, are $\delta^\eta$-dense, and satisfy both the Katz–Tao convex Wolff bound and the Frostman slab Wolff bound with constant $\delta^{-\eta}$, the Assertion D lower bound holds with parameters $(\kappa, \sigma, \omega, \varepsilon)$ (`Kakeya.AssertionD`).
11. **Wolff volume floor**: For every $\varepsilon > 0$, there exist $\eta > 0$ and $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$ and every nonempty $\delta$-tube configuration $(\mathbb T, Y)$ satisfying the CWA at nearby scales with error $\delta^{-\eta}$ and $\delta^\eta$-density,
    $$\delta^{1/2+\varepsilon} \leq \Bigl|\bigcup_{T \in \mathbb T} Y(T)\Bigr|$$
    (`Kakeya.Assouad.PureWZ2WolffVolumeFloor`).
- `Kakeya.Assouad.PureWZ2WolffFloorFromAssertionDStatement`: Assertion $D(1/2, 0)$ and `PureWZ2FullFiberAssertionDRefinementStatement` together imply `PureWZ2WolffVolumeFloor`.
12. **WZ2 Theorem 5.2 statement**: For every $\varepsilon > 0$, there exist $\eta > 0$ and $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$ and every nonempty $\delta$-tube configuration $(\mathbb T, Y)$ satisfying the CWA at nearby scales with error $\delta^{-\eta}$ and $\delta^\eta$-density,
    $$\delta^\varepsilon \leq \Bigl|\bigcup_{T \in \mathbb T} Y(T)\Bigr|$$
    (`Kakeya.Assouad.PureWZ2Theorem5_2Statement`).
13. **Admissible exponent / $\mathsf{Bad}(s)$**: A real exponent $s$ is admissible if for every $\eta > 0$ and $\delta_0 > 0$, there exist $\delta \in (0, \min(\delta_0, 1)]$ and a nonempty $\delta$-tube configuration $(\mathbb T, Y)$ satisfying the CWA at nearby scales with error $\delta^{-\eta}$ and $\delta^\eta$-density such that
    $$\Bigl|\bigcup_{T \in \mathbb T} Y(T)\Bigr| \leq \delta^s$$
    (`Kakeya.Assouad.PureWZ2Admissible`).
- `Kakeya.Assouad.PureWZ2WolffFloorImpliesSubunitCeilingStatement`: `PureWZ2WolffVolumeFloor` implies the existence of $a < 1$ such that $\mathsf{Bad}(a)$ fails.
- `Kakeya.Assouad.PureWZ2SubunitPackageStatement`: The conjunction of `PureWZ2FullFiberAssertionDRefinementStatement`, `PureWZ2WolffFloorFromAssertionDStatement`, `PureWZ2WolffFloorImpliesSubunitCeilingStatement`, `PureWZ2WolffVolumeFloor`, and the existence of $a < 1$ for which $\mathsf{Bad}(a)$ fails.
14. **$\varepsilon$-extremal configuration (WZ2 Def 6.1)**: Given $\sigma, \varepsilon \in \mathbb R$ and $\delta \in (0, 1]$, a nonempty $\delta$-tube configuration $(\mathbb T, Y)$ is $\varepsilon$-extremal (with respect to $\sigma$) if $\mathbb T$ satisfies the CWA at nearby scales with error $\delta^{-\varepsilon}$, $(\mathbb T, Y)$ is $\delta^\varepsilon$-dense, and $\bigl|\bigcup_{T \in \mathbb T} Y(T)\bigr| \leq \delta^{\sigma - \varepsilon}$ (`Kakeya.Assouad.WZ2PaperPureIsExtremal`, bundled as `Kakeya.Assouad.PureWZ2ExtremalConfiguration`).
15. **Critical volume floor**: For $\sigma \in \mathbb R$, the critical volume floor holds at $\sigma$ if for every $\alpha > 0$ and every structural budget $\eta_0 > 0$, there exist $\eta \in (0, \eta_0]$ and $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$ and every nonempty $\delta$-tube configuration $(\mathbb T, Y)$ satisfying the CWA at nearby scales with error $\delta^{-\eta}$ and $\delta^\eta$-density,
    $$\delta^{\sigma + \alpha} \leq \Bigl|\bigcup_{T \in \mathbb T} Y(T)\Bigr|$$
    (`Kakeya.Assouad.PureWZ2CriticalVolumeFloor`).
- `Kakeya.Assouad.PureWZ2CriticalPackage`: For $\sigma \in \mathbb R$, this package records that $0 < \sigma < 1$, that for every $\varepsilon, \delta_0 > 0$ there exists $\delta \in (0, \delta_0]$ and an $\varepsilon$-extremal configuration at scale $\delta$ with respect to $\sigma$, and that `PureWZ2CriticalVolumeFloor` holds at $\sigma$.
- `Kakeya.Assouad.PureWZ2CriticalExtractionStatement` (proved as `pure_wz2_node02_critical_extraction`): If `PureWZ2SubunitPackageStatement` holds and `PureWZ2Theorem5_2Statement` fails, then there exists $\sigma \in (0, 1)$ satisfying `PureWZ2CriticalPackage` (constructed in the proof as $\sigma = \sup \{s : \mathsf{Bad}(s)\}$).

---

#### WZ2 Definition 6.1

> Write $E_C = \bigcup_T Y(T)$ and $\sigma = \sigma_{\mathrm{CW}}$. The pair $C = (\mathcal T, Y)_\delta$ is *$\varepsilon$-CW-extremal* precisely when
> $$\begin{aligned}
> &\mathcal T \text{ satisfies multi-scale convex Wolff with error } \delta^{-\varepsilon},\\
> &\sum_T |Y(T)| \geq \delta^\varepsilon \sum_T |T|,\\
> &|E_C| \leq \delta^{\sigma - \varepsilon}.
> \end{aligned}$$
> This is WZ2 Definition 6.1, where it is called $\varepsilon$-extremal. The added CW label distinguishes it from WZ1's different extremal class.

##### tags: `Kakeya.Assouad.WZ2PaperPureIsExtremal`

```
WZ2PaperPureIsExtremal ✔
├─ Kakeya.Streamlined.TubeFamily.Nonempty ✔
├─ WZ2PaperPureCWAAtNearbyScales ✔
├─ Kakeya.Streamlined.Shading.IsLambdaDense ✔
├─ Kakeya.Streamlined.Shading.union ✔
└─ Kakeya.realRpowENN ✔
```

This is item 14 in WZ2 Section 6.2 above: for $\sigma, \varepsilon \in \mathbb R$ and $0 < \delta \leq 1$, a nonempty $\delta$-tube configuration $(\mathbb T, Y)$ satisfies `WZ2PaperPureIsExtremal` when $\mathbb T$ satisfies the CWA at nearby scales with error $\delta^{-\varepsilon}$, $(\mathbb T, Y)$ is $\delta^\varepsilon$-dense, and $|E_Y| \leq \delta^{\sigma - \varepsilon}$. Note that $\sigma$ is supplied as an explicit real parameter rather than referring to a global constant $\sigma_{\mathrm{CW}}$.

---

#### WZ2 Proposition 6.2

> For every $\varepsilon > 0$ choose $\eta, \delta_0 > 0$.
> If $C$ is $\eta$-extremal and $\delta^{1-\varepsilon} \leq \rho \leq \delta^\varepsilon$, there are a refinement $C'$ and a balanced $\rho$-cover $D$ such that $D$ and each unit-rescaled child family are $\varepsilon$-extremal.
> For every point $p$,
> $$\begin{split}
> \#\mathcal T_D(p) &\leq \rho^{2-\sigma-\varepsilon} \#\mathcal T_D,\\
> \#\mathcal T_{C'}[U](p) &\leq (\delta/\rho)^{2-\sigma-\varepsilon} \#\mathcal T_{C'}[U].
> \end{split}$$
> The fine/coarse product comparison also supplies matching lower multiplicity estimates with a reserved small loss.

##### tags: `Kakeya.Assouad.pure_wz2_node03_rich_prop62_kernel` (`Kakeya.Assouad.PureWZ2RichProp62KernelStatement`), `Kakeya.Assouad.pure_wz2_node03_prop_sticky` (`Kakeya.Assouad.PureWZ2PropStickyStatement`)

```
PureWZ2RichProp62KernelStatement ✔
├─ PureWZ2CriticalPackage ✔
└─ PureWZ2.Proposition63RichStickyKernelScheduleData ✔
   ├─ PureWZ2PropStickyReentryData ✔
   │  ├─ PureWZ2ExtremalConfiguration ✔
   │  ├─ PureWZ2PropStickyReentryGeometry ✔
   │  │  ├─ wz2PaperPureRefinementFraction ✔
   │  │  ├─ pureWZ2DenseCubicalization ✔
   │  │  ├─ WZ1PaperIsCubicalShading ✔
   │  │  ├─ WZ1PaperIsLineClass ✔
   │  │  ├─ wz1PaperTubeCarrier ✔
   │  │  └─ HasBoundedBase ✔
   │  ├─ WZ2PaperConvexWolffBound ✔
   │  └─ WZ2PaperCroppedIsExtremal ✔
   └─ PureWZ2.Proposition63RichTerminalStickyData ✔
      ├─ PureWZ2PropStickyData ✔
      │  ├─ PureWZ2Section6Cover ✔
      │  │  ├─ WZ1PaperTubeCovers ✔
      │  │  │  └─ wz1PaperLineDistance ✔
      │  │  └─ WZ1PaperIsEssentiallyDistinct ✔
      │  ├─ wz2PaperFullFiberIndices ✔
      │  ├─ wz2PaperFullFiberCount ✔
      │  ├─ PureWZ2BalancedCoverData ✔
      │  │  └─ wz1PaperGridCube ✔
      │  ├─ WZ2PaperCroppedIsExtremal ✔
      │  └─ WZ2PaperPureRescaledFullFiberOutput ✔
      │     ├─ WZ2PaperLiteralUnitRescaledFamilyData ✔
      │     ├─ WZ2PaperLiteralUnitRescaledShadingData ✔
      │     └─ WZ2PaperAssouadToLiteralRescalingCertificate ✔
      └─ PureWZ2.Proposition63TerminalMultiplicityCertificate ✔
```

Basic Definitions (Section 6 cropped-tube model):
1. **Line metric and line-metric full fibers**: For two tubes $T, T'$ with coaxial lines $l, l'$ havmeeting $\{z = 0\}$ anchorst $A, A'$ and upward-oriented unit directions $\tilde{\mathbf d}, \tilde{\mathbf d}'$, their line distance is $d(T, T') = \|A - A'\| + \angle(\tilde{\mathbf d}, \tilde{\mathbf d}')$. A $\rho$-tube $T_\rho$ covers a $\delta$-tube $T$ in the WZ1 sense if $d(T, T_\rho) \leq \rho / 2$ (`Kakeya.Assouad.wz1PaperLineDistance`, `Kakeya.Assouad.WZ1PaperTubeCovers`). In the Section 6 cropped model, the full fiber over $T_\rho$ is defined by this line-cover relation,
   $$\mathbb T[T_\rho]_{\mathrm{line}} := \{T \in \mathbb T : d(T, T_\rho) \leq \rho/2\}$$
   (`Kakeya.Assouad.wz2PaperFullFiberIndices`, cardinality `wz2PaperFullFiberCount`), rather than the ordinary carrier containment $\mathbb T[T_\rho] = \{T \in \mathbb T : T \subseteq T_\rho\}$ of Definition 2.12. A family $\mathbb T$ is line-metric essentially distinct if $d(T_i, T_j) > \delta$ for $i \neq j$ (`Kakeya.Assouad.WZ1PaperIsEssentiallyDistinct`).
2. **Cropped tube and cubical shading**: For a $\delta$-tube $T$, its cropped tube body is the closed $6\delta$-neighbourhood of its coaxial line $l(T)$ intersected with $[-1, 1]^3$ (`Kakeya.Assouad.wz1PaperTubeCarrier`). A cropped shading $Y$ assigns a measurable subset of each cropped tube body (`Kakeya.Assouad.WZ1PaperTubeShading`). It is cubical if each $Y(T)$ is a union of standard $\delta$-grid cubes $Q \in \mathcal Q_\delta$ (`Kakeya.Assouad.WZ1PaperIsCubicalShading`, `Kakeya.Assouad.wz1PaperGridCube`).
3. **Cropped CWA and cropped $\varepsilon$-extremality**: A family $\mathbb T$ satisfies the cropped CWA with error $C$ if $\#\{T \in \mathbb T : \text{cropped body of } T \subseteq W\} \leq C |W| (\#\mathbb T)$ for every convex $W \subseteq \mathbb R^3$ (`Kakeya.Assouad.WZ2PaperConvexWolffBound`). For $\sigma, \varepsilon \in \mathbb R$ and $\delta \in (0, 1]$, a nonempty pair $(\mathbb T, Y)$ with a cropped cubical shading $Y$ is cropped $\varepsilon$-extremal if the underlying ordinary family $\mathbb T$ satisfies the CWA at nearby scales with error $\delta^{-\varepsilon}$, $(\mathbb T, Y)$ is $\delta^\varepsilon$-dense (with respect to cropped tube volumes), and $|E_Y| \leq \delta^{\sigma - \varepsilon}$ (`Kakeya.Assouad.WZ2PaperCroppedIsExtremal`).
4. **Bounded base**: $\mathbb T$ has $R$-bounded bases if $\|p_T\| \leq R$ for the basepoint $p_T$ of every $T \in \mathbb T$ (`Kakeya.Assouad.HasBoundedBase`).
5. **Section 6 cover and balanced cover**: For a fine family $\mathbb T$ of $\delta$-tubes and a coarse family $\mathbb T_\rho$ of $\rho$-tubes, a Section 6 cover requires $\mathbb T, \mathbb T_\rho \subseteq \mathcal L_3$, $\mathbb T_\rho$ line-metric essentially distinct, every $T \in \mathbb T$ covered by some $T_\rho \in \mathbb T_\rho$ in the line metric ($d(T, T_\rho) \leq \rho/2$), and every $T_\rho \in \mathbb T_\rho$ covering at least one $T \in \mathbb T$ (`Kakeya.Assouad.PureWZ2Section6Cover`). For a fine cropped shading $Y$ and a coarse cubical shading $Y_\rho$, the cover is balanced if:
	- $Y(T) \subseteq Y_\rho(T_\rho)$ whenever $T_\rho$ covers $T$,
	- $E_{Y_\rho}$ is a union of active $\rho$-grid cubes $Q \in \mathcal Q_\rho$, and $|E_Y \cap Q|$ takes a constant positive value across all active $Q$ (`Kakeya.Assouad.PureWZ2BalancedCoverData`).

- `Kakeya.Assouad.PureWZ2PropStickyReentryData`: Links an ordinary $\eta_{\mathrm{src}}$-extremal configuration $(\mathbb T_{\mathrm{ord}}, Y_{\mathrm{ord}})$ at scale $\delta$ to a cropped $\eta_{\mathrm{norm}}$-extremal configuration $(\mathbb T, Y)$ ($0 < \eta_{\mathrm{src}} \leq \eta_{\mathrm{norm}} / 2$) via a nonempty subfamily $\mathbb T_{\mathrm{sel}} \subseteq \mathbb T_{\mathrm{ord}}$, an ordinary subshading $Y_{\mathrm{ord}}' \subseteq Y_{\mathrm{ord}}|_{\mathbb T_{\mathrm{sel}}}$, and a rigid isometry $\Phi : \mathbb R^3 \to \mathbb R^3$: $Y_{\mathrm{ord}}'$ and a subfamily selection retainsing at least $(\log(1/\delta))^{-N_0}$ of the mass of $Y_{\mathrm{ord}}$ and has per-tube density $|Y_{\mathrm{ord}}'(T)| \geq \frac{1}{2}\delta^{\eta_{\mathrm{src}}}|T|$,: the tubes of $\mathbb T \subseteq \mathcal L_3$ are the $\Phi$-images of $\mathbb T_{\mathrm{sel}}$the selected ordinary tubes (with bases bounded by $4$), the $\Phi(Y_{\mathrm{ord}}'(T)) \subseteq $-image of the ordinary shading lies in $\{|z| \leq 1/4\}$, $Y(T)$ is the dense cubicalization ofobtained by replacing each $\Phi(Y_{\mathrm{ord}}'(T))$ with its dense $\delta$-grid cubes (`pureWZ2DenseCubicalization`), and $\mathbb T$ satisfies the cropped CWA with error $\delta^{-\eta_{\mathrm{norm}}}$.
- `Kakeya.Assouad.PureWZ2PropStickyData`: Given a cropped configuration $(\mathbb T, Y)$ at scale $\delta$, a scale $\rho \in [\delta, 1]$, and a logarithmic exponent $N$, this records:
	- a nonempty subfamily $\mathbb T' \subseteq \mathbb T$ and cubical subshading $Y'$ retaining at least $(\log(1/\delta))^{-N}$ of the mass of $Y$,
	- a coarse family $\mathbb T_\rho$ of $\rho$-tubes, a Section 6 cover of $\mathbb T'$ by $\mathbb T_\rho$, and a coarse cubical shading $Y_\rho$ forming a balanced cover with $Y'$ such that $(\mathbb T_\rho, Y_\rho)$ is cropped $\varepsilon$-extremal,
	- for each parent $T_\rho \in \mathbb T_\rho$, a unit-rescaled full-fiber output (`WZ2PaperPureRescaledFullFiberOutput`) showing that the rescaled child family of $\mathbb T'[T_\rho]_{\mathrm{line}}$ at scale $\delta/\rho$ is cropped $\varepsilon$-extremal,
	- the pointwise multiplicity upper bounds for every $p \in \mathbb R^3$ and every $T_\rho \in \mathbb T_\rho$:
	  $$\#\{U \in \mathbb T_\rho : p \in Y_\rho(U)\} \leq \rho^{2 - \sigma - \varepsilon} \#\mathbb T_\rho, \qquad \#\{T \in \mathbb T'[T_\rho]_{\mathrm{line}} : p \in Y'(T)\} \leq (\delta/\rho)^{2 - \sigma - \varepsilon} \#\mathbb T'[T_\rho]_{\mathrm{line}}.$$
- `Kakeya.Assouad.PureWZ2.Proposition63RichTerminalStickyData`: Strengthens `PureWZ2PropStickyData` (with $N = 61$) on the same families $(\mathbb T', Y')$ and $(\mathbb T_\rho, Y_\rho)$ by also retaining:
	- a coarse re-entry certificate (`PureWZ2PropStickyReentryData`) on $(\mathbb T_\rho, Y_\rho)$ (when the input ordinary subshading lies in the tighter axial window $\{|z| \leq 1/8\}$), so that Proposition 6.2 can be applied a second time to the coarse configuration,
	- uniform constant packet multiplicity $\mu_{\mathrm{fine}}$ on active parent-cell pairs, two-sided coarse multiplicity bands $\mu_{\mathrm{coarse}} \leq \mu_{Y_\rho}(p) \leq r_{\mathrm{reg}} \mu_{\mathrm{coarse}}$ on $p \in E_{Y_\rho}$ with $r_{\mathrm{reg}} \lesssimq (\log(1/\delta))^{10}$, and the matching lower multiplicity bounds $\mu_{\mathrm{fine}} \gtrsim (\delta/\rho)^{2 - \sigma + \varepsilon'} \#\mathbb T'[T_\rho]_{\mathrm{line}}$ and $\mu_{\mathrm{coarse}} \gtrsim \rho^{2 - \sigma + \varepsilon'} \#\mathbb T_\rho$ (`Proposition63TerminalMultiplicityCertificate`).
- `Kakeya.Assouad.PureWZ2RichProp62KernelStatement` (proved as `pure_wz2_node03_rich_prop62_kernel`): Given $\sigma$ with `PureWZ2CriticalPackage` and any output loss $\varepsilon \in (0, 1]$, there exist pre-selected losses $0 < \eta_{\mathrm{src}} \leq \eta_{\mathrm{norm}}/2$ with $\eta_{\mathrm{norm}} < \varepsilon$ and a threshold $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$, every cropped configuration $(\mathbb T, Y)$ with a `PureWZ2PropStickyReentryData` at $(\eta_{\mathrm{src}}, \eta_{\mathrm{norm}})$, and every scale $\rho \in [\delta^{1-\varepsilon}, \delta^\varepsilon]$, there exists a `Proposition63RichTerminalStickyData` with output loss $\varepsilon$.

---

#### WZ2 Proposition 6.3

> For every $\varepsilon, \delta_0 > 0$, some $\varepsilon$-extremal pair at $0 < \delta \leq \delta_0$ has:
> 1. a $1$-Lipschitz $f: [-1, 1] \to \mathbb R$ with each fixed-$z$ image $\{x + f(z)y : (x, y, z) \in E_C\}$ an $(\delta, 1-\sigma, \delta^{-\varepsilon})_1$-ADset;
> 2. a $1$-Lipschitz plane map $V$ with $V(p) \cdot (E_C \cap B(p, \sqrt{\rho}))$ an $(\rho, 1-\sigma, \delta^{-\varepsilon})_1$-ADset for all $p$ and $\rho \in [\delta, 1]$.

##### tags: `Kakeya.Assouad.pure_wz2_node04_reentrant_grains` (`Kakeya.Assouad.PureWZ2ReentrantGrainsStatement`), `Kakeya.Assouad.PureWZ2GrainsFromCriticalStatement`

```
PureWZ2ReentrantGrainsStatement ✔
├─ PureWZ2PropStickyCapability ✔
├─ PureWZ2CriticalPackage ✔
└─ PureWZ2HierarchyInitialReentrantSourceAt ✔
   └─ PureWZ2HierarchyInitialReentrantSourceConclusion ✔
      └─ PureWZ2ReentrantGrainSource ✔
         ├─ PureWZ2QuantitativeGrainConfiguration ✔
         │  ├─ WZ1PaperIsLineClass ✔
         │  ├─ WZ1PaperIsCubicalShading ✔
         │  ├─ WZ2PaperCroppedIsExtremal ✔
         │  ├─ WZ2PaperConvexWolffBound ✔
         │  ├─ PureWZ2BoundedLipschitzGlobalGrainData ✔
         │  │  └─ PureWZ2LipschitzGlobalGrainData ✔
         │  │     └─ PureWZ2PaperADSet1 ✔
         │  └─ PureWZ2LocalGrainData ✔
         │     └─ PureWZ2PaperADSet1 ✔
         └─ PureWZ2PropStickyReentryData ✔
```

Basic Definitions:
1. **$1$-dimensional $(\delta, \alpha, C)_1$-ADset**: For $\delta > 0$, $\alpha \in (0, 1]$, and $C \in [1, +\infty)$, a subset $A \subseteq \mathbb R$ is a $(\delta, \alpha, C)_1$-ADset if for every $\rho \geq \delta$ and every closed interval $I \subseteq \mathbb R$ of length $|I| \geq \rho$,
   $$\mathcal N_\rho(A \cap I) \leq C (|I|/\rho)^\alpha,$$
   where $\mathcal N_\rho(\cdot)$ denotes the external covering number by closed intervals (balls in $\mathbb R$) of radius $\rho$ (`Kakeya.Assouad.PureWZ2PaperADSet1`). Note that this is an upper-regularity condition only.
2. **Lipschitz global grains**: Given a cropped configuration $(\mathbb T, Y)$ at scale $\delta$, an exponent $\sigma$, and constant $C$, this consists of a $1$-Lipschitz function $f : [-1, 1] \to \mathbb R$ such that for every $z \in [-1, 1]$, the projected slice
   $$\Bigl\{\frac{x + f(z)y}{\sqrt{1 + f(z)^2}} : (x, y, z) \in E_Y\Bigr\}$$
   is a $(\delta, 1-\sigma, C)_1$-ADset (`Kakeya.Assouad.PureWZ2LipschitzGlobalGrainData`; `PureWZ2BoundedLipschitzGlobalGrainData` additionally records $|f(z)| \leq 3$ on $[-1, 1]$).
3. **Local grains and plane map**: Given $(\mathbb T, Y)$, $\sigma$, and $C$, this consists of a $1$-Lipschitz unit normal field $V : E_Y \to S^2$ (defined on the shaded union $E_Y$, not on all of $\mathbb R^3$) such that:
	- for every $T \in \mathbb T$ with unit direction $\mathbf d_T$ and every $p \in Y(T)$, $|\langle \mathbf d_T, V(p) \rangle| \leq \delta$,
	- for every $\rho \in [\delta, 1]$ and every $p \in E_Y$, the orthogonal projection $\{\langle V(p), q \rangle : q \in E_Y \cap \overline{B(p, \sqrt{\rho})}\}$ is a $(\rho, 1-\sigma, C)_1$-ADset (`Kakeya.Assouad.PureWZ2LocalGrainData`).

- `Kakeya.Assouad.PureWZ2GrainConfiguration`: At scale $\delta$ with exponent $\sigma$ and loss $\varepsilon$, this packages a cropped $\varepsilon$-extremal configuration $(\mathbb T, Y)$ with $\mathbb T \subseteq \mathcal L_3$, cubical shading $Y$, top-level cropped CWA with error $\delta^{-\varepsilon}$, Lipschitz global grains (`PureWZ2LipschitzGlobalGrainData`), and local grains (`PureWZ2LocalGrainData`) with constant $C = \delta^{-\varepsilon}$. (`PureWZ2QuantitativeGrainConfiguration` additionally records $|E_Y| \geq \delta^{\sigma + \varepsilon}$, $|f(z)| \leq 3$, and $|V_3(p)| \leq 1/2$ for $p \in E_Y$.)
- `Kakeya.Assouad.PureWZ2GrainsFromCriticalStatement`: Given $\sigma$ with `PureWZ2CriticalPackage`, for every $\varepsilon, \delta_0 > 0$ there exists $\delta \in (0, \delta_0]$ and a `PureWZ2GrainConfiguration` at scale $\delta$ with loss $\varepsilon$.
- `Kakeya.Assouad.PureWZ2ReentrantGrainSource`: Bundles a `PureWZ2QuantitativeGrainConfiguration` at scale $\delta$ and loss $\eta$ together with a `PureWZ2PropStickyReentryData` on the same family and shading (with axial window $|z| \leq 1/8$), so that the C² hierarchy in Proposition 6.4 can repeatedly apply Proposition 6.2 to this configuration.
- `Kakeya.Assouad.PureWZ2ReentrantGrainsStatement` (proved as `pure_wz2_node04_reentrant_grains`, which consumes `pure_wz2_node03_rich_prop62_kernel`): Given `PureWZ2PropStickyCapability` and $\sigma$ with `PureWZ2CriticalPackage`, for every $\varepsilon, \delta_0 > 0$ there exist $0 < \eta < \varepsilon$, $0 < \delta \leq \delta_0$, and a `PureWZ2ReentrantGrainSource` at scale $\delta$ with loss $\eta$. Forgetting the re-entry certificate and weakening $\eta$ to $\varepsilon$ recovers `PureWZ2GrainsFromCriticalStatement` on the exact same family, shading, global slope, and plane map.

---

#### WZ2 Proposition 6.4

> For every $\varepsilon, \delta_0 > 0$, an $\varepsilon$-extremal pair at some $0 < \delta \leq \delta_0$ has global grains with $\|f\|_{C^2([-1,1])} \leq 1$ and retains the same local grains with a $1$-Lipschitz plane map.
> The WZ1 Section 5 construction uses its Section 8 dot-product projection theorem; that entire internal branch remains in this atlas.

##### tags: `Kakeya.Assouad.pure_wz2_left_line_c2_grains` (`Kakeya.Assouad.PureWZ2C2GrainsFromCriticalStatement`)

```
PureWZ2C2GrainsFromCriticalStatement ✔
├─ PureWZ2CriticalPackage ✔
└─ PureWZ2C2GrainConfiguration ✔
   ├─ WZ1PaperIsLineClass ✔
   ├─ HasBoundedBase ✔
   ├─ WZ1PaperIsCubicalShading ✔
   ├─ WZ2PaperCroppedIsExtremal ✔
   ├─ WZ2PaperConvexWolffBound ✔
   ├─ PureWZ2C2GlobalGrainData ✔
   │  ├─ PureWZ2C2SlopeIsNormalized ✔
   │  └─ PureWZ2PaperADSet1 ✔
   └─ PureWZ2LocalGrainData ✔
```

Basic Definitions:
1. **Normalized $C^2$ slope**: A function $f \in C^2([-1, 1]): [-1, 1] \to \mathbb R$ is a normalized $C^2$ slope if it admits a $C^2$ extension to $[-1, 1]$ satisfying
   $$|f(z)| \leq 1, \qquad |f'(z)| \leq 1, \qquad |f''(z)| \leq 1 \qquad \forall z \in [-1, 1]$$
   (`Kakeya.Assouad.PureWZ2C2SlopeIsNormalized`; for globally defined $C^2$ functions `SlopeFunction`, the same bound on $[-1, 1]$ is `Kakeya.Assouad.SlopeFunction.IsNormalized`).

- `Kakeya.Assouad.PureWZ2C2GlobalGrainData`: Same as `PureWZ2LipschitzGlobalGrainData`, except that $f : [-1, 1] \to \mathbb R$ is required to be a normalized $C^2$ slope rather than merely $1$-Lipschitz.
- `Kakeya.Assouad.PureWZ2C2GrainConfiguration`: At scale $\delta$ with exponent $\sigma$ and loss $\varepsilon$, this packages a cropped $\varepsilon$-extremal configuration $(\mathbb T, Y)$ with $\mathbb T \subseteq \mathcal L_3$, $4$-bounded bases, cubical shading $Y$, top-level cropped CWA with error $\delta^{-\varepsilon}$, normalized $C^2$ global grains (`PureWZ2C2GlobalGrainData`), and local grains (`PureWZ2LocalGrainData`) with constant $\delta^{-\varepsilon}$, all on the same $(\mathbb T, Y)$.
- `Kakeya.Assouad.PureWZ2C2GrainsFromCriticalStatement` (proved as `pure_wz2_left_line_c2_grains`): Given $\sigma$ with `PureWZ2CriticalPackage`, for every $\varepsilon, \delta_0 > 0$ there exists $\delta \in (0, \delta_0]$ and a `PureWZ2C2GrainConfiguration` at scale $\delta$ with loss $\varepsilon$.

---

#### WZ1 Theorem 5.2

> For every $\varepsilon > 0$, choose $\eta, \delta_0 > 0$.
> For $(\delta, 1, \delta^{-\eta})$-ADsets $F, G \subset [0, 1]^2$, either
> (A) an affine line $\ell$ and the orthogonal line $\ell^\perp$ through the origin have $\mathcal E_\delta(F \cap N_\delta \ell), \mathcal E_\delta(G \cap N_\delta \ell^\perp) \geq \delta^{\varepsilon - 1}$; or
> (B) for every $H \subset F \times G \times G$ with $\mathcal E_\delta(H) \geq \delta^{\eta - 3}$, some $\rho \geq \delta$ and interval $I$, $|I| \geq \delta^{-\eta}\rho$, satisfy $\mathcal E_\rho(I \cap \{a \cdot (b_1 - b_2) : (a, b_1, b_2) \in H\}) \geq (|I|/\rho)^{1-\varepsilon}$.

##### tags: `Kakeya.Assouad.WZ1ProjectionDichotomyConclusion` (unused interface), `Kakeya.Assouad.wz1_well_separated_projection_union` (`Kakeya.Assouad.WZ1WellSeparatedProjectionUnionConclusion`, used in the $C^2$ proof)

```
WZ1ProjectionDichotomyConclusion ✔
├─ DiscreteSet ✔
├─ DiscreteSet.IsInUnitBall ✔
├─ DiscreteSet.IsDeltaSeparated ✔
├─ DiscreteSet.IsKatzTao ✔
├─ wz1DiscreteLineCount ✔
├─ wz1Perp2 ✔
└─ wz1DotDifferenceSet ✔

wz1_well_separated_projection_union (WZ1WellSeparatedProjectionUnionConclusion) ✔
├─ DiscreteSet.IsFrostman ✔
├─ WZ1StandardSeparation ✔
├─ WZ1UniformTripleDensity ✔
├─ wz1DiscreteLineCount ✔
└─ WZ1StripLocalizationLongProjection ✔
```

Basic Definitions:
1. **Discrete point set in $\mathbb R^n$**: A finite subset $A \subseteq \mathbb R^n$ (`Kakeya.Assouad.DiscreteSet`). It is $\delta$-separated if $\|x - y\| \geq \delta$ for all $x \neq y \in A$ (`DiscreteSet.IsDeltaSeparated`), and lies in the unit ball if $\|x\| \leq 1$ for all $x \in A$ (`DiscreteSet.IsInUnitBall`).
2. **$s$-dimensional Katz–Tao and Frostman bounds for discrete sets**: For $A \subseteq \mathbb R^n$, $\delta > 0$, $s \in \mathbb R$, and $C \in [0, +\infty]$:
	- $A$ satisfies the $(\delta, s, C)$-Katz–Tao bound if $\#(A \cap \overline{B(x, r)}) \leq C (r/\delta)^s$ for all $x \in \mathbb R^n$ and $r \in [\delta, 1]$ (`DiscreteSet.IsKatzTao`),
	- $A$ satisfies the $(\delta, s, C)$-Frostman bound if $\#(A \cap \overline{B(x, r)}) \leq C r^s (\# A)$ for all $x \in \mathbb R^n$ and $r \in [\delta, 1]$ (`DiscreteSet.IsFrostman`).
3. **Discrete line count**: For $A \subseteq \mathbb R^2$, basepoint $b \in \mathbb R^2$, direction $v \in \mathbb R^2$, and width $\delta$, `wz1DiscreteLineCount A b v delta` is $\#\{p \in A : |\langle p - b, v^\perp \rangle| \leq \delta\}$; when $\|v\| = 1$, this is the number of points of $A$ within distance $\delta$ of the affine line $b + \mathbb R v$.

- `Kakeya.Assouad.WZ1ProjectionDichotomyConclusion`: For every $\varepsilon > 0$, there exist $\eta > 0$ and $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$ and any nonempty $\delta$-separated finite sets $F, G_1, G_2 \subseteq \overline{B(0, 1)} \subset \mathbb R^2$, each satisfying the $(\delta, 1, \delta^{-\eta})$-Katz–Tao bound, one of the following holds:
	- **(Line concentration)** There exist a unit vector $v \in S^1$ and $b \in \mathbb R^2$ such that $F$ has at least $\delta^{\varepsilon - 1}$ points within $\delta$ of the line $\mathbb R v^\perp$ through the origin, and *both* $G_1$ and $G_2$ have at least $\delta^{\varepsilon - 1}$ points within $\delta$ of the affine line $b + \mathbb R v$. (Note the orientation compared to the roadmap card: since the dot-difference is $a \cdot (b_1 - b_2)$ with $a \in F$ and $b_1, b_2 \in G_i$, the coefficient set $F$ concentrates near the line $\mathbb R v^\perp$ through the origin, while the endpoint sets $G_1, G_2$ concentrate near an affine line parallel to $v$.)
	- **(Dot-product expansion)** For every $H \subseteq F \times G_1 \times G_2$ with $\# H \geq \delta^{\eta - 3}$, there exist $\rho \in [\delta, 1]$ and a closed interval $I = [c - R, c + R]$ ($R > 0$) of length $|I| = 2R \geq \delta^{-\eta}\rho$ such that
	  $$\mathcal N_\rho\bigl(I \cap \{a \cdot (b_1 - b_2) : (a, b_1, b_2) \in H\}\bigr) \geq (|I|/\rho)^{1 - \varepsilon}.$$
- **Actual $C^2$ dependency (`Kakeya.Assouad.wz1_well_separated_projection_union` / `WZ1WellSeparatedProjectionUnionConclusion`)**: `WZ1ProjectionDichotomyConclusion` is an unproved standalone proposition interface and is not proved in its full generality. Instead, Proposition 6.4 invokes the proved theorem `wz1_well_separated_projection_union`: given nonempty $\delta$-separated sets $F, G_1, G_2 \subseteq \overline{B(0, 1)}$ satisfying the relative $(\delta, 1, \delta^{-\eta})$-Frostman bound (`IsFrostman`), standard separation `WZ1StandardSeparation` ($\mathrm{diam}(F), \mathrm{diam}(G_1), \mathrm{diam}(G_2) \leq 1/10$, $\mathrm{dist}(G_1, G_2) \geq 1/2$, and $\mathrm{dist}(0, F) \geq 1/2$), and a triple set $H \subseteq F \times G_1 \times G_2$ with $\# H \geq \delta^\eta (\# F)(\# G_1)(\# G_2)$ and uniform fiber-density lower bounds across all coordinate projections (`WZ1UniformTripleDensity`), either $F$ concentrates near $\mathbb R v^\perp$ and $G_1$ *or* $G_2$ has at least $\delta^\varepsilon (\# G_i)$ points within $\delta$ of $b + \mathbb R v$, or the dot-difference set of $H$ satisfies `WZ1StripLocalizationLongProjection` (an interval $I$ of length $\geq \delta^{-\eta}\rho$ at scale $\rho \in [\delta, 1]$ with $\mathcal N_\rho(I \cap \{a \cdot (b_1 - b_2)\}) \geq (|I|/\rho)^{1-\varepsilon}$) (`WZ1WellSeparatedProjectionUnionConclusion`), which applies to a triple set $H \subseteq F \times G_1 \times G_2$ already regularised to have uniform degree and standard separation between $G_1$ and $G_2$, and whose line-concentration alternative requires only $G_1$ *or* $G_2$ (which come from the same ambient local chart) to concentrate near $b + \mathbb R v$.

---

#### WZ2 Lemma 6.6

> Let $C, f, V$ satisfy Proposition 6.4 with loss $\eta$. Let $\delta^{1/2} \leq |J| \leq \delta^\varepsilon$.
> Assume $\sum_T |Y(T) \cap (\mathbb R^2 \times J)| \geq \delta^\eta |J|$ and that the shaded union in this slab is covered by at most $\delta^{-\eta}|J|^{-2+\sigma}$ cubes of side $|J|$.
> For sufficiently small $\eta, \delta_0$ one has $|f'(z)| \geq |J|$ for every $z \in J$.

##### tags: `Kakeya.Assouad.pure_wz2_lemma66_prepared_interval` (`Kakeya.Assouad.PureWZ2Lemma66PreparedInterval`)

```
pure_wz2_lemma66_prepared_interval ✔
└─ PureWZ2Lemma66PreparedInterval ✔
   ├─ PureWZ2C2GrainConfiguration ✔
   ├─ WZ2PaperRequestedScale ✔
   ├─ SlopeFunction.IsNormalized ✔
   ├─ PureWZ2Section6ScaleData ✔
   │  ├─ horizontalSlab ✔
   │  └─ CanCoverByBalls ✔
   └─ PureWZ2FrameNormalCompatibility ✔
      └─ pureWZ2FrameProjectedNormal ✔
```

Basic Definitions:
1. **Horizontal slab**: For $a \leq b$, `horizontalSlab a b` is the slab $\mathbb R^2 \times [a, b] = \{(x, y, z) \in \mathbb R^3 : a \leq z \leq b\}$.
2. **Frame-normal compatibility**: For a reference slope $s_0 \in \mathbb R$, let $R_{s_0}(x, y, z) = \bigl(\frac{x + s_0 y}{\sqrt{1+s_0^2}}, \frac{-s_0 x + y}{\sqrt{1+s_0^2}}, z\bigr)$ be the horizontal rotation aligning $(1, s_0, 0)$ with the $x$-axis, and let $P_{xz}(u, v, w) = (u, 0, w)$ drop the rotated $y$-component. For a configuration `cfg` of type `PureWZ2C2GrainConfiguration` with global slope $f$ and local plane map $V : E_Y \to S^2$, `PureWZ2FrameNormalCompatibility cfg` requires that for every reference slope $s_0 \in \mathbb R$ and every $p = (x, y, z) \in E_Y$ with $|f(z) - s_0| \leq 1/50$, the projected normal $R_{s_0}^{-1} P_{xz} R_{s_0} V(p)$ (`pureWZ2FrameProjectedNormal`)ion of $V(p)$ onto the horizontal plane in the sheared frame associated to $s_0$ has norm at least $1/16$ (`PureWZ2FrameNormalCompatibilityOn` restricts this conditionrequirement to $p$ in the slab shading union).

- `Kakeya.Assouad.PureWZ2Section6ScaleData`: Given a cropped shading $Y$ on $\mathbb T$ at scale $\delta$, exponent $\sigma$, loss $\eta_{\mathrm{slab}}$, and scale $r \in [\delta, 1]$, this records an interval $J = [a, b] \subseteq [-1, 1]$ of length $r = b - a$ and a cubical subshading $Y_J \subseteq Y$ supported in $\mathbb R^2 \times J$ such that:
	- **Normalized slab mass**: $\sum_{T \in \mathbb T} |Y_J(T)| \geq \frac{\pi}{4} \delta^{\eta_{\mathrm{slab}} + 2} (\#\mathbb T) r$,
	- **Spatial cover**: $\mathcal N_r(E_{Y_J}) \leq \delta^{-\eta_{\mathrm{slab}}} r^{-2+\sigma}$,
	- **Coarse-ratio multiplicity cap**: $\mu_{Y_J}(p) = \#\{T \in \mathbb T : p \in Y_J(T)\} \leq (\delta/r)^{2 - \sigma - \eta_{\mathrm{slab}}} \#\mathbb T$ for all $p \in \mathbb R^3$.
- `Kakeya.Assouad.PureWZ2Lemma66PreparedInterval`: For $(\sigma, \eta, \delta)$, this bundles:
	- a `PureWZ2C2GrainConfiguration` at scale $\delta$ with loss $\eta/8$, together with a globally defined $C^2$ representative $f$ of its global slope satisfying $|f|, |f'|, |f''| \leq 1$ on $[-1, 1]$,
	- a scale $r \in [\delta, 1]$ and `PureWZ2Section6ScaleData` on $Y$ with loss $\eta/8$ over an interval $J = [a, b]$ of length $r$,
	- `PureWZ2FrameNormalCompatibility` on the configuration,
	- **Fine multiplicity cap**: $\mu_{Y_J}(p) \leq \delta^{2 - \sigma - \eta/4096} r^{-\eta/4096} \#\mathbb T$ for all $p \in \mathbb R^3$.
- `Kakeya.Assouad.pure_wz2_lemma66_prepared_interval`: Fix $0 < \sigma < 1$, $0 < \varepsilon \leq 1/2$, and $\eta > 0$ with $1000\eta \leq \varepsilon \sigma^2$. There exists $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$ and every `PureWZ2Lemma66PreparedInterval` at $(\sigma, \eta, \delta)$ whose interval length $r = |J|$ satisfies $\delta^{1/2} \leq r \leq \delta^\varepsilon$,
  $$|f'(z)| \geq |J| \qquad \forall z \in J.$$
  *(Remark: Compared to the roadmap card's absolute mass assumption $\sum_T |Y(T) \cap (\mathbb R^2 \times J)| \geq \delta^\eta |J|$, the Lean lemma uses the normalized mass $\frac{\pi}{4}\delta^{\eta/8+2}(\#\mathbb T)|J|$ together with the pointwise multiplicity caps, which are supplied by the Proposition 6.5 slab selection. A newer theorem `pure_wz2_lemma66_normalized_interval` removes the external frame-compatibility hypothesis by proving frame nondegeneracy internally on each slab, while still taking the normalized slab mass and fine multiplicity cap.)*

---

#### WZ2 Proposition 6.5

> For every $\varepsilon, \delta_0 > 0$, an $\varepsilon$-extremal pair at some $0 < \delta \leq \delta_0$ has global grains for a $C^2$ slope satisfying
> $$1 \leq |f'(z)| \leq 2, \qquad |f''(z)| \leq 1/100 \quad (-1 \leq z \leq 1).$$
> The local grains and $1$-Lipschitz plane map are retained.
> Use the transferred comparable-slope slab lemma, WZ2 Lemma 6.6 and mild anisotropic normalization.

##### tags: `Kakeya.Assouad.pure_wz2_left_line_large_slope_retained` (`Kakeya.Assouad.PureWZ2LargeSlopeRetainedStatement`), `Kakeya.Assouad.PureWZ2LargeSlopeFromCriticalStatement`

```
PureWZ2LargeSlopeRetainedStatement ✔
├─ PureWZ2CriticalPackage ✔
└─ PureWZ2LargeSlopeConstruction ✔
   ├─ PureWZ2DirectCommonYSourceAssembly ✔
   ├─ PureWZ2HalfOffsetTerminalDistinctCleanupData ✔
   ├─ PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData ✔
   ├─ DirectHalfOffsetTerminalRequestedCWAData ✔
   └─ PureWZ2HorizontalTerminalData ✔
      └─ PureWZ2HorizontalTerminalData.toLargeSlopeConfiguration ✔
         └─ PureWZ2LargeSlopeConfiguration ✔
            ├─ WZ1PaperIsLineClass ✔
            ├─ WZ1PaperIsCubicalShading ✔
            ├─ WZ2PaperCroppedIsExtremal ✔
            ├─ WZ2PaperConvexWolffBound ✔
            ├─ SlopeFunction.IsNonsingular ✔
            ├─ PureWZ2PaperADSet1 ✔
            ├─ twistedProjection ✔
            └─ PureWZ2LocalGrainData ✔
```

Basic Definitions:
1. **Nonsingular $C^2$ slope**: A $C^2$ function $f : \mathbb R \to \mathbb R$ (`Kakeya.Assouad.SlopeFunction`) is nonsingular if for every $z \in [-1, 1]$,
   $$1 \leq |f'(z)| \leq 2, \qquad |f''(z)| \leq \frac{1}{100}$$
   (`Kakeya.Assouad.SlopeFunction.IsNonsingular`). Note that this condition does not restrict $|f(0)|$.
2. **Twisted projection**: For a slope function $f$, the twisted projection $\pi_f : \mathbb R^3 \to \mathbb R^2$ is defined by
   $$\pi_f(x, y, z) = (x + f(z)y, z),$$
   and for a shading $Y$ we write $X_f(Y) = \pi_f(E_Y) = \bigcup_{T \in \mathbb T} \pi_f(Y(T)) \subseteq \mathbb R^2$ (`Kakeya.Assouad.twistedProjection`, `Kakeya.Assouad.twistedUnion`).

- `Kakeya.Assouad.PureWZ2LargeSlopeConfiguration`: At scale $\delta$ with exponent $\sigma$ and loss $\varepsilon$, this packages a cropped $\varepsilon$-extremal configuration $(\mathbb T, Y)$ with $\mathbb T \subseteq \mathcal L_3$, cubical shading $Y$, top-level cropped CWA with error $\delta^{-\varepsilon}$, local grains (`PureWZ2LocalGrainData`) with constant $\delta^{-\varepsilon}$, and a nonsingular $C^2$ slope $f$ such that:
	- for every $z \in [-1, 1]$, the slice projection along $(1, f(z))/\sqrt{1+f(z)^2}$ is a $(\delta, 1-\sigma, \delta^{-\varepsilon})_1$-ADset,
	- the twisted projection satisfies $|X_f(Y)| \leq \delta^{\sigma - \varepsilon}$.
- `Kakeya.Assouad.PureWZ2LargeSlopeFromCriticalStatement`: Given $\sigma$ with `PureWZ2CriticalPackage`, for every $\varepsilon, \delta_0 > 0$ there exists $\delta \in (0, \delta_0]$ and a `PureWZ2LargeSlopeConfiguration` at scale $\delta$ with loss $\varepsilon$.
- `Kakeya.Assouad.PureWZ2LargeSlopeConstruction` and `PureWZ2LargeSlopeRetainedStatement` (proved as `pure_wz2_left_line_large_slope_retained`): Given $\sigma$ with `PureWZ2CriticalPackage`, an output loss $\varepsilon > 0$, a target scale ceiling $\delta_{\mathrm{out}} > 0$, and a source scale ceiling $\delta_{\mathrm{src}} > 0$, there exist $N \in \mathbb N$, a source scale $\delta_{\mathrm{source}} \in (0, \delta_{\mathrm{src}}]$, and a complete construction record `PureWZ2LargeSlopeConstruction` whose target scale $\delta = \delta_{\mathrm{target}}$ satisfies $0 < \delta \leq \delta_{\mathrm{out}}$ and whose terminal field projects to `PureWZ2LargeSlopeConfiguration`. Retaining the full construction record (including the source scale $\delta_{\mathrm{source}}$ before the slab rescaling) allows Lemma 6.7 to bound the slope offset $|f(0)|$ in terms of $\delta_{\mathrm{source}}$ and normalize the exact terminal family constructed here.

---

#### WZ2 Lemma 6.7

> For every small loss $\varepsilon > 0$ and cutoff $\delta_0 > 0$, obtain a convex-Wolff family with error $\delta^{-\varepsilon}$, shading density $\delta^\varepsilon$, and a nonsingular slope such that
> $$|X_f(C)| \lesssim \delta^{\sigma-\varepsilon}, \qquad X_f(C) = \bigcup_T \pi_f(Y(T)).$$
> Indeed, the global AD slice bound gives $\mathcal E_\delta(X_f(C) \cap \{z=t\}) \leq \delta^{-\varepsilon}\delta^{-(1-\sigma)}$; multiply by $O(\delta)$ and integrate in $t$.

##### tags: `Kakeya.Assouad.pure_wz2_left_line_normalized_projection` (`Kakeya.Assouad.PureWZ2NormalizedProjectionStatement`)

```
PureWZ2NormalizedProjectionStatement ✔
├─ PureWZ2CriticalPackage ✔
└─ PureWZ2NormalizedProjectionData ✔
   ├─ PureWZ2ParameterFrostmanPreparationData ✔
   │  ├─ Kakeya.Streamlined.TubeFamily.Nonempty ✔
   │  ├─ Kakeya.Streamlined.Shading.IsLambdaDense ✔
   │  ├─ HasBoundedBase ✔
   │  ├─ Kakeya.Streamlined.TubeFamily.IsEssentiallyDistinct ✔
   │  ├─ IsInVerticalChart ✔
   │  ├─ TubeWolffBound ✔
   │  ├─ TubeParameterFrostmanBound ✔
   │  │  └─ tubeParams ✔
   │  ├─ HasExtremalCardinalityUpper ✔
   │  ├─ IsInSlopeWindow ✔
   │  ├─ SlopeFunction.IsNonsingular ✔
   │  └─ twistedUnion ✔
   └─ ConvexWolffBound ✔
```

Basic Definitions:
1. **Essentially distinct (indexed analytic form)**: An indexed family $\mathbb T$ of $\delta$-tubes is analytically essentially distinct if $|T_i \cap T_j| \leq \frac{1}{2}\max(|T_i|, |T_j|)$ for all $i \neq j$ (`Kakeya.Streamlined.TubeFamily.IsEssentiallyDistinct`).
2. **Vertical chart and line parameters**: A family $\mathbb T$ lies in the vertical chart if every tube direction $\mathbf d_T = (d_1, d_2, d_3)$ satisfies $|d_3| \geq 1/2$ (`Kakeya.Assouad.IsInVerticalChart`). Each tube axis can then be written as
   $$(x, y, z) = (a_T + c_T z, \, b_T + d_T z, \, z), \qquad p_T = (a_T, b_T, c_T, d_T) \in \mathbb R^4$$
   (`Kakeya.Assouad.tubeParams`).
3. **Parameter Frostman bound**: $\mathbb T$ satisfies the parameter Frostman bound with constant $C$ if for every $r \in [\delta, 1]$ and every reference tube $T_0 \in \mathbb T$,
   $$\#\{T \in \mathbb T : \|p_T - p_{T_0}\|_\infty \leq r\} \leq C r^2 (\#\mathbb T)$$
   (`Kakeya.Assouad.TubeParameterFrostmanBound`).
4. **Ordinary Tube Wolff bound**: $\mathbb T$ satisfies the Tube Wolff bound with constant $C$ if for every $\rho \in [\delta, 1]$ and every $\rho$-tube $T_\rho$, $\#\mathbb T[T_\rho] \leq C \rho^2 (\#\mathbb T)$ (`Kakeya.Assouad.TubeWolffBound`).
5. **Normalized Convex Wolff bound**: $\mathbb T$ satisfies the normalized CWA with constant $C$ if for every convex set $W \subseteq \mathbb R^3$,
   $$v_1 \cdot (\#\mathbb T[W]) \leq C |W| (\#\mathbb T),$$
   where $v_1 \geq 1$ is the volume of a unit-radius tube (`Kakeya.Assouad.ConvexWolffBound`).
6. **Slope window**: A shading $Y$ lies in the slope window if $E_Y \subseteq \mathbb R^2 \times [-1, 1]$ (`Kakeya.Assouad.IsInSlopeWindow`).

- `Kakeya.Assouad.PureWZ2NormalizedProjectionData`: At scale $\delta \in (0, 1)$ with exponent $\sigma$ and loss $\varepsilon$, this packages an ordinary $\delta$-tube family $\mathbb T$, a shading $Y$, and a $C^2$ slope function $f$ satisfying:
	- $\mathbb T$ is nonempty, analytically essentially distinct, has $4$-bounded bases, and lies in the vertical chart,
	- $\mathbb T$ satisfies the normalized CWA (`ConvexWolffBound`), the Tube Wolff bound (`TubeWolffBound`), and the parameter Frostman bound (`TubeParameterFrostmanBound`), each with constant $\delta^{-\varepsilon}$, as well as $\#\mathbb T \leq \delta^{-2 - \varepsilon/10}$ (`HasExtremalCardinalityUpper`),
	- $(\mathbb T, Y)$ is $\delta^\varepsilon$-dense and $Y$ is supported in $\mathbb R^2 \times [-1, 1]$,
	- $f$ is nonsingular on $[-1, 1]$ and satisfies $f(0) = 0$,
	- $|X_f(Y)| \leq \delta^{\sigma - \varepsilon}$.
  *(Note: To achieve $f(0) = 0$ from the Proposition 6.5 output slope $f_0$ with $s = f_0(0)$, the proof uses the quantitative offset bound $1 + |s| \leq \delta_{\mathrm{source}}^{-a}$ from the retained construction and applies the shear-scaling map $A_s(x, y, z) = (k(x + sy), ky, z)$ with $k = \frac{1}{4(1+|s|)}$, which replaces $f_0$ by $\tilde{f} = f_0 - s$ (so $|\tilde{f}(z)| \leq 2$ on $[-1, 1]$) and scales projected area by $k$ since $\pi_{\tilde{f}}(A_s(x,y,z)) = (k(x+f_0(z)y), z)$. Note also that both the roadmap card and Lean use the exponent $\sigma - \varepsilon$, whereas WZ2 Equation (6.11) prints $\sigma + \varepsilon$.)*
- `Kakeya.Assouad.PureWZ2NormalizedProjectionStatement` (proved as `pure_wz2_left_line_normalized_projection`): Given $\sigma$ with `PureWZ2CriticalPackage`, for every $\varepsilon \in (0, \sigma)$ and every $\delta_0 > 0$, there exists $\delta$ with $0 < \delta \leq \delta_0$ and $\delta < 1$ together with \in (0, \min(\delta_0, 1))$ and a `PureWZ2NormalizedProjectionData` at $(\sigma, \varepsilon, \delta)$.

---

#### WZ2 Lemma 7.12: cinematic assembly

> Zoom the uniform triple set to a $q$-cube, extract Katz-Tao triples at $h = \delta/q$, and replicate them back at mesh $\delta$.
> For fixed $c$ the functions $g(t) = a + bf(t) + dtf(t) + ct$ are cinematic; their parameter metric and $C^2$ metric are comparable.
> A $(\delta, 1-\tau, O(1))$-Katz-Tao parameter set therefore gives a $\delta$-separated curve family obeying $\#(G \cap B_r) \lesssim (r/\delta)$.
> All cardinality and shading deficits from extraction remain explicit small powers of $h$.

##### tags: `Kakeya.Assouad.parameter_block_representative_cinematic_pullback` (`Kakeya.Assouad.ParameterBlockRepresentativeCinematicPullbackStatement`)

```
ParameterBlockRepresentativeCinematicPullbackStatement ✔
├─ HalfParameterCinematicPYZGeneralStatement ✔
├─ CompactSubshadingSelectionStatement ✔
├─ CompactTubeTwistedProjectionAreaStatement ✔
├─ AssignedCurveProjectionContainmentFromVerticalChartStatement ✔
├─ IsInVerticalChart ✔
├─ TubeParameterClusterFrostmanData ✔
├─ ParameterLocalFullBlockData ✔
├─ ParameterLocalRepresentativeBlockData ✔
├─ ParameterBlockAmplificationData ✔
├─ HasPerTubeMass ✔
├─ SlopeFunction.IsNonsingular ✔
└─ ParameterBlockRepresentativeCinematicPullbackData ✔
   └─ parameterBlockRepresentativeCopiedFiberCap ✔
```

Basic Definitions:
1. **Collapsed parameter triples**: In the vertical chart $(x, y, z) = (a_T + c_T z, b_T + d_T z, z)$, the twisted projection of a tube's axis is $\pi_f(a_T + c_T z, b_T + d_T z, z) = (a_T + b_T f(z) + d_T z f(z) + c_T z, z)$. Aafter restricting $c_T$ to an interval of width $\delta$ around $c_0$, each tube's twisted projection $\pi_f(x, y, z) = (a_T + b_T f(z) + d_T z f(z) + c_T z, z)$ is governed by its three-dimensional parameter point $(a_T, b_T, d_T) \in \mathbb R^3$, rescaled by $(1/24, 1/24, 1/4)$ so that bounded chart parameters lie in $\overline{B(0, 1)}$ (`Kakeya.Assouad.tubeParameterPoint3`).
2. **Per-tube mass lower bound**: A shading $Y$ has per-tube mass $\theta$ if $|Y(T)| \geq \theta$ for every active $T \in \mathbb T$, i.e. whenever $Y(T) \neq \varnothing$ (`Kakeya.Assouad.HasPerTubeMass`).

- `Kakeya.Assouad.TubeParameterClusterFrostmanData`: Given $(\mathbb T, Y)$ at scale $\delta$ with parameter Frostman constant $C$ and density $\lambda$, this records a whole-tube subshading $Y_{\mathrm{cl}} \subseteq Y$ retaining mass up to a logarithmic factor $R_{\mathrm{reg}}$ in $C \lambda^{-1} \delta^{-1}$, together with a $\delta$-separated finite set $P_{\mathrm{cl}} \subseteq \overline{B(0, 1)} \subset \mathbb R^3$ of collapsed $(a, b, d)$ cluster centers satisfying the $(\delta, 1, C_{\mathrm{cl}})$-Frostman bound with $C_{\mathrm{cl}} = 10^5 C R_{\mathrm{reg}} \lambda^{-1}$, and an assignment map $\mathrm{assign} : \mathbb T \to P_{\mathrm{cl}}$ with comparable cluster weights $\mu_{\mathrm{cl}} \leq \sum_{\mathrm{assign}(T) = p} |Y_{\mathrm{cl}}(T)| \leq 2\mu_{\mathrm{cl}}$ for every $p \in P_{\mathrm{cl}}$.
- `Kakeya.Assouad.ParameterLocalFullBlockData`: Selects a block scale $q \in [\delta, 1/100]$ with $(\delta^{1-\varepsilon^2} < q, 1/100]$, a center $p_0 \in \mathbb R^3$, and a nonempty local parameter subset $P \subseteq P_{\mathrm{cl}} \cap \overline{B(p_0, q/10)}$ (with recentered copy $P_0 = P - p_0 \subseteq \overline{B(0, q/10)}$) such that all active tubes in the block have $|c_T - c_0| \leq \delta/2$, the block shading mass is at least $(\# P)\mu_{\mathrm{cl}}$, $P_0$ satisfies the $(\delta, 1-\varepsilon^2, 100)$-Katz–Tao bound, and and $(P_0) / q$ satisfies the $(h, 1, O(1))$-Katz–Tao bound at scale $h = \delta/q$ with cardinality $\# P \gtrsim (q/\delta)^{1 - 20\varepsilon^2}$.
- `Kakeya.Assouad.ParameterLocalRepresentativeBlockData`: Selects an injective map `sourceIndex` assigning to each parameter point $p \in P$ a single active representative tube $T_p \in \mathbb T$ whose rescaled $(a, b, d)$ parameter equalsith $(a_{T_p}, b_{T_p}, d_{T_p})$ assigned to $p$, forming the representative family $\mathbb T_{\mathrm{rep}}$ of cardinality $\# P$ and shading $Y_{\mathrm{rep}}$. (Selecting one tube per collapsed parameter ensures that the replicated family has a bounded number of tubes per cinematic curve, avoiding unbounded multiplicity from duplicate indexed tubes.)
- `Kakeya.Assouad.ParameterBlockAmplificationData`: Translates $P_0$ by a finite set $\Lambda \subseteq \mathbb R^3$ of $m = \#\Lambda \sim q^{-1}$ translation vectors so that the translates $P_0 + v$ ($v \in \Lambda$) are pairwise disjoint, their union $\widetilde P = \bigcup_{v \in \Lambda} (P_0 + v) \subseteq [-1/2, 1/2]^3$ has cardinality $m (\# P)$, and $\widetilde P$ satisfies the $(\delta, 1, 10^5)$-Katz–Tao bound at scale $\delta$.
- `Kakeya.Assouad.ParameterBlockRepresentativeCinematicPullbackData`: Records a subshading $Z \subseteq Y_{\mathrm{rep}}$ on $\mathbb T_{\mathrm{rep}}$ satisfying the two mass boundsuch that:
  $$\sum_{T \in \mathbb T_{\mathrm{rep}}} |Z(T)| \geq \frac{1}{2} \sum_{T \in \mathbb T_{\mathrm{rep}}} |Y_{\mathrm{rep}}(T)|, \qquad \sum_{T \in \mathbb T_{\mathrm{rep}}} |Z(T)| \geq \frac{1}{2} \theta (\# P),$$
  and, with $m = \#\Lambda$ and $B = 12500000$ (`parameterBlockRepresentativeCopiedFiberCap`), the area lower bound
  $$|X_f(Z)| \geq \frac{1}{m} \left(\frac{m \sum_{T \in \mathbb T_{\mathrm{rep}}} |Z(T)|}{20\delta \cdot B \delta^{-\beta}}\right)^3.$$
- `Kakeya.Assouad.ParameterBlockRepresentativeCinematicPullbackStatement` (proved as `parameter_block_representative_cinematic_pullback`): Given the four auxiliary geometric/cinematic statements (`HalfParameterCinematicPYZGeneralStatement`, `CompactSubshadingSelectionStatement`, `CompactTubeTwistedProjectionAreaStatement`, `AssignedCurveProjectionContainmentFromVerticalChartStatement`), for every $\varepsilon \in (0, 1/10)$ and $\beta > 0$, there exists $\delta_0 \in (0, 1)$ such that for every $\delta \in (0, \delta_0]$, every vertical-chart configuration $(\mathbb T, Y)$ with clustered data supported in $\mathbb R^2 \times [0, 1]$, local block $P$, representative family $\mathbb T_{\mathrm{rep}}$, amplification $\Lambda$, per-tube mass $\theta \in (0, +\infty)$, and nonsingular slope $f$ with $f(0) = 0$, there exists a `ParameterBlockRepresentativeCinematicPullbackData`.

---

#### WZ1 Thm. 7.2 = WZ2 Thm. 7.13

> For a cinematic family on a compact interval and every $\varepsilon > 0$, sufficiently small $\delta$ has the following property.
> A $\delta$-separated finite subfamily $F$ satisfying $\#(F \cap B) \leq \delta^{-\varepsilon}(r/\delta)$ for every $C^2$-ball of diameter $r$ obeys $\|\sum_{g \in F} 1_{N_\delta(\operatorname{graph} g)}\|_{L^{3/2}} \leq \delta^{-\varepsilon}$.
> The small-scale threshold depends on the cinematic and doubling constants. The ball condition here is absolute one-dimensional Katz-Tao control. Relative Frostman control would instead contain $r\#G$ on the right.

##### tags: `Kakeya.Cinematic.wz2_uniformC2_input` (`Kakeya.Cinematic.WZ2UniformC2Input`)

```
WZ2UniformC2Input ✔
├─ Kakeya.Cinematic.C2Function ✔
├─ Kakeya.Cinematic.IsCinematicFamily ✔
│  ├─ Kakeya.Cinematic.c2Distance ✔
│  └─ Kakeya.Cinematic.jetGap ✔
├─ Kakeya.Cinematic.HasUniformC2Bound ✔
├─ Kakeya.Cinematic.FiniteFunctionFamily ✔
│  ├─ Kakeya.Cinematic.FiniteFunctionFamily.IsDeltaSeparated ✔
│  └─ Kakeya.Cinematic.FiniteFunctionFamily.HasKatzTaoBound ✔
└─ Kakeya.Cinematic.multiplicity ✔
   └─ Kakeya.Cinematic.graphNeighborhood ✔
```

Basic Definitions:
1. **$C^2([0, 1])$ metric and jet gap**: For $f, g \in C^2([0, 1])$ (`Kakeya.Cinematic.C2Function`), let
   $$d_{C^2}(f, g) = \max\Bigl\{\|f - g\|_{C^2} = \sup_{t \in [0, 1]} |f(t) - g(t)|, \, + \sup_{t \in [0, 1]} |f'(t) - g'(t)|, \, + \sup_{t \in [0, 1]} |f''(t) - g''(t)|\Bigr\}$$
   (`c2Distance`), and at each $t \in [0, 1]$ define the jet gap $\mathrm{jetGap}(f, g, t) = |f(t) - g(t)| + |f'(t) - g'(t)| + |f''(t) - g''(t)|$.
2. **Cinematic family**: A family $\mathcal F \subseteq C^2([0, 1])$ is cinematic with constants $K, D \geq 1$ (`Kakeya.Cinematic.IsCinematicFamily`) if:
	- $d_{C^2}(f, g) \leq K$ for all $f, g \in \mathrm{diam}_{C^2}(\mathcal F) \leq K$,
	- every $C^2$-ball in $\mathcal F$ of radius $r > 0$ can be covered by at most $D$ balls of radius $r/2$ centered in $\mathcal F$,
	- for all $f, g \in \mathcal F$ and all $t \in [0, 1]$, $\mathrm{jetGap}(f, g, t) \geq K^{-1} d_{C^2}(f, g)\|f - g\|_{C^2}$.
3. **Uniform $C^2$ bound**: $\mathcal F$ has uniform $C^2$ bound $M \geq 0$ if $|f(t)|, |f'(t)|, |f''(t)| \leq M$ for all $f \in \mathcal F$ and $t \in [0, 1]$ (`Kakeya.Cinematic.HasUniformC2Bound`).
4. **Katz–Tao bound for curve families**: A finite family $F \subseteq C^2([0, 1])$ satisfies the $(\delta, C_{\mathrm{KT}})$-Katz–Tao bound if $\# F \leq C_{\mathrm{KT}} / \delta$ and $\#(F \cap B_{C^2}(g, r)) \leq C_{\mathrm{KT}} (r/\delta)$ for every $g \in C^2([0, 1])$ and $r \in [\delta, 1]$ (`Kakeya.Cinematic.FiniteFunctionFamily.HasKatzTaoBound`).

- `Kakeya.Cinematic.WZ2UniformC2Input` (proved as `wz2_uniformC2_input`): Fix $K, D, C_{\mathrm{KT}}, \lambda \geq 1$ and $M \geq 0$. For every $\varepsilon > 0$, there exists $\delta_0 \in (0, 1/\lambda]$ such that for every $\delta \in (0, \delta_0]$, every cinematic family $\mathcal F \subseteq C^2([0, 1])$ with constants $(K, D)$ and uniform $C^2$ bound $M$, and every $\delta$-separated finite subfamily $F \subseteq \mathcal F$ satisfying the $(\delta, C_{\mathrm{KT}})$-Katz–Tao bound,
  $$\Biggl\|\sum_{g \in F} \mathbf 1_{N_{\lambda\delta}(\operatorname{graph} g)}\Biggr\|_{L^{3/2}(\mathbb R^2)} \leq \delta^{-\varepsilon}.$$
  *(Note: The domain is $[0, 1]$, and the constants $C_{\mathrm{KT}}, \lambda, M$ are fixed before the threshold $\delta_0$.)*

---

#### WZ2 Lemma 7.12

> For every $\varepsilon > 0$ choose $\eta, \delta_0 > 0$.
> For a Tube-Wolff family with error $\delta^{-\eta}$, $\delta^\eta$-dense shading and nonsingular slope, there are $r \in (\delta^{1-\varepsilon^2}, 1)$ and a sub-shading $Y'$ that is $\delta^{4\eta}$-dense such that
> $$\left|\bigcup_T \pi_f(Y'(T))\right| \geq (\delta/r)^\varepsilon \left|N_r\!\left(\bigcup_T \pi_f(Y'(T))\right)\right|.$$
> The exact mesh can be rounded to the sparse scale set with bounded losses.

##### tags: `Kakeya.Assouad.pure_wz2_lemma7_12_parameter_frostman_sharp_density` (`Kakeya.Assouad.GridOSBoundedOneScaleSharpInput`)

```
GridOSBoundedOneScaleSharpInput ✔
├─ Kakeya.Streamlined.TubeFamily.Nonempty ✔
├─ IsInVerticalChart ✔
├─ tubeParams ✔
├─ TubeParameterFrostmanBound ✔
├─ Kakeya.Streamlined.Shading.IsLambdaDense ✔
├─ IsInSlopeWindow ✔
├─ SlopeFunction.IsNonsingular ✔
├─ IsSubshading ✔
└─ twistedUnion ✔
```

- `Kakeya.Assouad.GridOSBoundedOneScaleSharpInput` (proved as `pure_wz2_lemma7_12_parameter_frostman_sharp_density`): For every $\varepsilon \in (0, 1/100)$ and $\rho_{\max} \in [1/100, 1]$, there exists $\eta_{\max} \in (0, \varepsilon]$ such that for every $\eta \in (0, \eta_{\max}]$, there exists $\delta_0 \in (0, 1)$ with the following property. For every $\delta \in (0, \delta_0]$, every nonempty $\delta$-tube family $\mathbb T$ in the vertical chart whose line parameters satisfy $|a_T|, |b_T| \leq 12$ and $|c_T|, |d_T| \leq 2$ and which obeys the parameter Frostman bound with constant $C \in [1, \delta^{-\eta}]$, every $\delta^\eta$-dense shading $Y$ supported in $\mathbb R^2 \times [-1, 1]$, and every nonsingular $C^2$ slope $f$ with $f(0) = 0$, there exist a scale $\rho \in (\delta^{1-\varepsilon^2}, \rho_{\max}]$ and a subshading $Z \subseteq Y$ such that $(\mathbb T, Z)$ is $\delta^{4\eta}$-dense and
  $$|X_f(Z)| \geq (\delta/\rho)^\varepsilon |N_\rho(X_f(Z))|,$$
  where $N_\rho(\cdot)$ denotes the closed $\rho$-neighbourhood in $\mathbb R^2$.

---

#### WZ2 Proposition 7.1

> For every $\varepsilon > 0$ choose $\eta, \delta_0 > 0$.
> For $0 < \delta \leq \delta_0$, Tube-Wolff error $\delta^{-\eta}$, $\delta^\eta$-dense shading and a nonsingular slope imply $|\bigcup_T \pi_f(Y(T))| \geq \delta^\varepsilon$.
> This is the stronger Section 7 statement that proves Proposition 6.8.

##### tags: `Kakeya.Assouad.pure_wz2_proposition7_1_dilated_tube_wolff`, `Kakeya.Assouad.pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart`

```
pure_wz2_proposition7_1_dilated_tube_wolff ✔
├─ Kakeya.Streamlined.TubeFamily.Nonempty ✔
├─ HasBoundedBase ✔
├─ IsInVerticalChart ✔
├─ Kakeya.Streamlined.TubeFamily.enncard ✔
├─ DilatedTubeWolffVolumeBound ✔
│  └─ wz2PaperCenteredDilatedCarrier ✔
├─ Kakeya.Streamlined.Shading.IsLambdaDense ✔
├─ IsInSlopeWindow ✔
├─ SlopeFunction.IsNonsingular ✔
└─ twistedUnion ✔
```

Basic Definitions:
1. **Dilated Tube Wolff volume bound**: For a factor $L > 0$ and constant $C \in [0, +\infty]$, a $\delta$-tube family $\mathbb T$ satisfies the $L$-dilated Tube Wolff volume bound with constant $C$ if for every $r > 0$ and every ordinary unit-segment $r$-tube $T_r$, its centered $L$-dilation $L \cdot T_r$ (which has axis length $L$ and physical radius $L r$) obeys
   $$\#\mathbb T[L \cdot T_r] \leq C |L \cdot T_r| (\#\mathbb T)$$
   (`Kakeya.Assouad.DilatedTubeWolffVolumeBound`).

- `Kakeya.Assouad.pure_wz2_proposition7_1_dilated_tube_wolff`: Fix any cardinality exponent $q > 0$ and any $\varepsilon > 0$. There exist $\eta \in (0, \min(\varepsilon, 1)]$ and $\delta_0 \in (0, 1)$ such that for every $\delta \in (0, \delta_0]$, every nonempty $\delta$-tube family $\mathbb T$ in the vertical chart with $4$-bounded bases, $\#\mathbb T \leq \delta^{-q}$, and $32$-dilated Tube Wolff volume bound with constant $\delta^{-\eta}$, every $\delta^\eta$-dense shading $Y$ supported in $\mathbb R^2 \times [-1, 1]$, and every nonsingular $C^2$ slope $f$ with $f(0) = 0$,
  $$|X_f(Y)| \geq \delta^\varepsilon.$$
- `Kakeya.Assouad.pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart`: Removes the explicit cardinality hypothesis $\#\mathbb T \leq \delta^{-q}$ by assuming instead that $\mathbb T$ is analytically essentially distinct (`IsEssentiallyDistinct`), which implies $\#\mathbb T \leq \delta^{-7}$ for small $\delta$ by a parameter-space packing argument in the bounded chart.
  *(Remark: Why $32$-dilated coarse tubes? Two unit-length fine tubes sharing the same supporting line can have different longitudinal positions along that line, so proximity in the four-parameter chart $(a, b, c, d)$ does not force containment in a unit-length coarse tube. In a $4$-bounded vertical chart, however, any fine tube within parameter distance $r \leq 1/20$ of a reference tube is contained in a centered $32$-dilated coarse tube of physical radius $20r$, yielding the parameter Frostman bound with constant $128000 C = 320 \cdot 20^2 C$ via `tubeParameterFrostmanBound_of_dilatedTubeWolffBound`.)*

---

#### WZ2 Proposition 6.8

> For every $\varepsilon > 0$, convex-Wolff error $\delta^{-\eta}$ and $\delta^\eta$-dense shading imply $|\bigcup_T \pi_f(Y(T))| \geq \delta^\varepsilon$ for any nonsingular $C^2$ slope and all sufficiently small $\delta$.
> The required $\eta, \delta_0$ depend on $\varepsilon$.
> Use convex Wolff $\Rightarrow$ Tube Wolff, then Proposition 7.1.

##### tags: `Kakeya.Assouad.pure_wz2_convex_wolff_lower_bound_via_dilated_tubes`

```
pure_wz2_convex_wolff_lower_bound_via_dilated_tubes ✔
├─ Kakeya.Streamlined.TubeFamily.Nonempty ✔
├─ HasBoundedBase ✔
├─ Kakeya.Streamlined.TubeFamily.IsEssentiallyDistinct ✔
├─ IsInVerticalChart ✔
├─ ConvexWolffBound ✔
├─ Kakeya.Streamlined.Shading.IsLambdaDense ✔
├─ IsInSlopeWindow ✔
├─ SlopeFunction.IsNonsingular ✔
└─ twistedUnion ✔
```

- `Kakeya.Assouad.pure_wz2_convex_wolff_lower_bound_via_dilated_tubes`: For every $\varepsilon > 0$, there exist $\eta \in (0, \varepsilon]$ and $\delta_0 \in (0, 1)$ such that for every $\delta \in (0, \delta_0]$, every nonempty, analytically essentially distinct $\delta$-tube family $\mathbb T$ in the vertical chart with $4$-bounded bases satisfying the normalized CWA (`ConvexWolffBound`) with constant $\delta^{-\eta}$, every $\delta^\eta$-dense shading $Y$ supported in $\mathbb R^2 \times [-1, 1]$, and every nonsingular $C^2$ slope $f$ with $f(0) = 0$,
  $$|X_f(Y)| \geq \delta^\varepsilon.$$
  *(The proof notes that every $32$-dilated coarse tube $32 \cdot T_r$ is convex, so `ConvexWolffBound` immediately implies `DilatedTubeWolffVolumeBound` with factor $32$, and then applies `pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart`.)*

---

#### WZ2 Section 6.5: contradiction

> If $\sigma > 0$, apply the lower bound with exponent $\sigma/4$.
> Choose the small-image construction with loss $\kappa < \sigma/4$ and $\kappa$ smaller than the lower-bound admissibility threshold.
> At arbitrarily small mesh the same pair obeys $\delta^{\sigma/4} \leq |X_f(C)| \lesssim \delta^{\sigma-\kappa}$, which is impossible. Therefore $\sigma_{\mathrm{CW}} = 0$.

##### tags: `Kakeya.Assouad.pure_wz2_no_critical_package`

```
pure_wz2_no_critical_package ✔
└─ PureWZ2CriticalPackage ✔
```

- `Kakeya.Assouad.pure_wz2_no_critical_package`: For every $\sigma \in \mathbb R$, `PureWZ2CriticalPackage sigma` implies `False`.
  *(In the proof, given `PureWZ2CriticalPackage sigma` with $0 < \sigma < 1$, one first applies Proposition 6.8 (`pure_wz2_convex_wolff_lower_bound_via_dilated_tubes`) with $\varepsilon = \sigma/4$ to obtain $\eta \in (0, \sigma/4]$ and $\delta_0 \in (0, 1)$. One then invokes Lemma 6.7 (`pure_wz2_left_line_normalized_projection`) with loss $\eta$ and scale ceiling $\delta_0$ to obtain a configuration $(\mathbb T, Y)$ and slope $f$ at scale $\delta \in (0, \delta_0]$ ($\delta < 1$)$ satisfying both $|X_f(Y)| \geq \delta^{\sigma/4}$ and $|X_f(Y)| \leq \delta^{\sigma - \eta}$, a contradiction since $0 < \delta < 1$ and $\sigma - \eta \geq \frac{3}{4}\sigma > \sigma/4$.)*

---

#### WZ2 Theorem 5.2

> For every $\varepsilon > 0$ there exist $\eta, \delta_0 > 0$ such that for every $0 < \delta \leq \delta_0$:
> if $\mathcal T$ satisfies the convex Wolff axioms at every scale with error $\delta^{-\eta}$ and $Y$ is $\delta^\eta$-dense, then
> $$\left|\bigcup_{T \in \mathcal T} Y(T)\right| \geq \delta^\varepsilon.$$
> This is the sole root theorem. No Hausdorff/Assouad-dimension deduction is part of the graph.

##### tags: `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional` (`Kakeya.Assouad.PureWZ2Theorem5_2Statement`)

```
PureWZ2Theorem5_2Unconditional ✔
└─ PureWZ2Theorem5_2Statement ✔
   ├─ Kakeya.Streamlined.TubeFamily.Nonempty ✔
   ├─ WZ2PaperPureCWAAtNearbyScales ✔
   ├─ Kakeya.Streamlined.Shading.IsLambdaDense ✔
   ├─ Kakeya.Streamlined.Shading.union ✔
   └─ Kakeya.realRpowENN ✔
```

- `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional`: Proves `PureWZ2Theorem5_2Statement` unconditionally: for every $\varepsilon > 0$, there exist $\eta > 0$ and $\delta_0 \in (0, 1]$ such that for every $\delta \in (0, \delta_0]$, every nonempty $\delta$-tube family $\mathbb T$ satisfying the CWA at nearby scales (`WZ2PaperPureCWAAtNearbyScales`) with error $\delta^{-\eta}$, and every $\delta^\eta$-dense shading $Y$ of $\mathbb T$,
  $$\Bigl|\bigcup_{T \in \mathbb T} Y(T)\Bigr| \geq \delta^\varepsilon.$$
<!--stackedit_data:
eyJoaXN0b3J5IjpbLTExMTk5MDI2NTRdfQ==
-->