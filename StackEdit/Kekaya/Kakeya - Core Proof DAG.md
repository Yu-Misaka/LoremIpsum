# Kakeya

### Core Proof DAG

#### WZ2 Definition 2.12

> The tubes are essentially distinct. For every $\rho_0 \in [\delta, 1]$, there are $\rho \in [\rho_0, A \rho_0)$ and $\rho$-tubes $\mathcal T_\rho$ such that:
> 1. $\mathcal T_\rho$ is an $A$-uniform partitioning cover of $\mathcal T$
> 2. for each parent, the unit-rescaled child family satisfies the convex Wolff axiom with error $A$.
> 
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
2. **Essentially distinct**: $\mathbb T$ is essentially distinct if $T_i \nsubseteq 2 \cdot T_j$ and $T_j \nsubseteq 2 \cdot T_i$ for every $i \neq j$. Here $2 \cdot T$ means dilation about the center of $T$ with factor 2. (`Kakeya.Assouad.wz2PaperCenteredDilatedCarrier`, `Kakeya.Assouad.WZ2PaperOrdinaryIsEssentiallyDistinct`)
3. **$\mathbb T[T_\rho]$**: $\{T \in \mathbb T : T \subseteq T_\rho\}$ (`Kakeya.Assouad.wz2PaperOrdinaryFullFiberIndices`)
4. **Unit rescaling**: 
	- Ellipsoid (centered at $\textbf c$ under linear equivalence $A$): $\textbf c + A(\overline{B(0, 1)})$ (`JohnEllipsoid.ellipsoid`)
	- Outer John ellipsoid of set $K$: an ellipsoid of minimum volume containing $K$ (`JohnEllipsoid.IsOuterJohnEllipsoid`)
	- Unit rescaling relative to $T_\rho$: choose an outer John ellipsoid of $T_\rho$, suppose it is centered at $\textbf c$ under linear equivalence $A$. Then a unit rescaling relative to $T_\rho$ is affine equivalence $\phi_{T_\rho}: \textbf x \mapsto A^{-1} (\textbf x - \textbf c)$. 
	- In short, send the outer John ellipsoid of $T_\rho$ back to unit ball at $\textbf 0$. (`Kakeya.Assouad.WZ2PaperAssouadUnitRescalingData.map`)
5. **Convex Wolff Axioms**: a multi-set $\mathcal S$ of sets in $\mathbb R^3$ satisfies the CWA with error $C$ if for all convex sets $W \subseteq \mathbb R^3$, we have $\# \mathcal S[W] \leq C|W|(\# \mathcal S)$ (`Kakeya.Assouad.WZ2PaperBodyConvexWolffBound`, $C \in [0, +\infty]$)
6. **$C$-uniform**: $\mathbb T_\rho$ are $C$-uniform over $\mathbb T$ if $\# \mathbb T[T_\rho] \leq C (\# \mathbb T[T_\rho'])$ for every $T_\rho, T_\rho' \in \mathbb T_\rho$ (`Kakeya.Assouad.WZ2PaperPureFullFibersAreCUniform`, $C \in [0, +\infty]$)
7. **Partitioning cover**: $\mathbb T_\rho$ is a partitioning cover of $\mathbb T$ if:
	- $\forall T \in \mathbb T, \exists T_\rho \in \mathbb T_\rho, T \in \mathbb T[T_\rho]$
	- $\forall i \neq j, \mathbb T[2 \cdot T_{\rho, i}]$ and $\mathbb T[2 \cdot T_{\rho,j}]$ are disjoint
	- (`Kakeya.Assouad.WZ2PaperPurePartitioningCover`)

- `Kakeya.Assouad.WZ2PaperPureUnitRescaledFullFiberData`: The unit rescaling of $\mathbb T[T_\rho]$ relative to $T_\rho$ satisfies the CWA with error $C$ ($C \in [0, +\infty]$)

8. **CWA at actual selected scale**: Let $C \in [0, + \infty], \delta > 0, \rho > 0$. We say that a set $\mathbb T$ of $\delta$-tubes satisfies CWA at actual selected scale $\rho$ with error $C$ if there exists a set of $\rho$-tubes $\mathbb T_\rho$ that satisfies the following property:
	- $\mathbb T_\rho$ is a $C$-uniform partitioning cover of $\mathbb T$
	- For each $T_\rho \in \mathbb T_\rho$, the unit rescaling of $\mathbb T[T_\rho]$ relative to $T_\rho$ satisfies the CWA with error $C$
	- (`Kakeya.Assouad.WZ2PaperPureScaleCoverData`)

**CWA at nearby scales (WZ2 Def 2.12 / CWA at every scale)**: 

Let $C \in [1, + \infty), \delta > 0$. We say that a set $\mathbb T$ of $\delta$-tubes satisfies CWA at nearby scales if the tubes in $\mathbb T$ are essentially distinct, and for every $\rho_0 \in [\delta, 1]$, there exists $\rho \in [\rho_0, C \rho_0)$ such that $\mathbb T$ satisfies CWA at actual selected scale $\rho$ with error $C$

---

#### WZ2 Section 6.2

> Let $Bad(s)$ mean: for every $\eta, \delta_0 > 0$, some $0 < \delta \leq \delta_0$ has multi-scale convex Wolff error $\delta^{-\eta}$, shading density $\delta^\eta$, and $|E_C| \leq \delta^s$. Define $\sigma = \sigma_{CW}=\sup(\{0\} \cup \{s > 0 : Bad(s)\})$. Failure of Theorem 5.2 gives $\sigma > 0$. This is a new deficit for a different admissible class, not WZ1's $\sigma_3$.

##### tags: `Kakeya.Assouad.PureWZ2CriticalExtractionStatement`

```
PureWZ2CriticalExtractionStatement
├── PureWZ2SubunitPackageStatement
│   ├── PureWZ2FullFiberAssertionDRefinementStatement
│   │   ├── PureWZ2FullFiberAssertionDRefinementData
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
│   ├── PureWZ2WolffFloorFromAssertionDStatement
│   │   ├── Kakeya.AssertionD
│   │   │   └── Kakeya.AssertionDLowerBound
│   │   └── PureWZ2WolffVolumeFloor
│   └── PureWZ2WolffFloorImpliesSubunitCeilingStatement
│       └── PureWZ2Admissible
├── PureWZ2Theorem5_2Statement
└── PureWZ2CriticalPackage
    ├── PureWZ2ExtremalConfiguration
    │   └── WZ2PaperPureIsExtremal
    └── PureWZ2CriticalVolumeFloor
```

Basic Definitions:

> Here is a very annoying remark on tube families: 
>
> We have indexed tube family (`Kakeya.Streamlined.TubeFamily`) and de-duplicated tube family (`Kakeya.TubeFamily`). 
> 
> We are always referring to indexed tube family by default - I'll mark it out when de-duped family is in use.
>
> When we write $T$ for an indexed family, we mostly mean the index, not the underlying geometric object.
> 
> Also, "de-dup" here does not mean de-duplicating according to the underlying geometric object, it basically says nothing useful mathematically. Tubes dilated from $(0, 0, 1) \rightarrow (0, 0, 0)$ and $(0,0,0) \rightarrow (0, 0, 1)$ are considered distinct.


1. **Shading**: A shading of $\mathbb T$ is an indexed family of measurable subsets $Y(T)$ of $T$ for every $T \in \mathbb T$ (`Kakeya.Streamlined.Shading`)
	- note that `Kakeya.Shading` is for de-duplicated tube families
2. **Essentially distinct (2025)**: **$\mathbb T$** is essentially distinct (2025) if $|T \cap T'| \leq 2^{-1}\max(|T|, |T'|)$ for every $T \neq T' \in \mathbb T$ (`Kakeya.TubeFamily.IsEssentiallyDistinct`)
	- note that $\mathbb T$ here is de-duplicated
3. **$\lambda$-dense**: Let $\lambda \in [0, +\infty], (\mathbb T, Y)$ is $\lambda$-dense if $\lambda \sum_{T \in \mathbb T}|T| \leq \sum_{T \in \mathbb T}|Y(T)|$ (`Kakeya.Streamlined.Shading.IsLambdaDense`)
	- note that `Kakeya.Shading.IsLambdaDense` is for de-duplicated tube families
4. **Katz-Tao convex Wolff bound with constant $C$**: $\# \mathbb T[W] \leq C |W| (|T|^{-1})$ for every convex set $W$ (`Kakeya.KatzTaoConvexWolffBound`)
	- Tubes in $\mathbb T$ have same size so it doesn't matter which $T$ is chosen. $\mathbb T$ here is de-duplicated
5. **Slab with norm $\textbf n$, offset $a$ and radius $r$**: $\|\textbf n\| = 1, 0 \leq r$, then the corresponding slab is $\overline{B(0,1)} \cap r$-closed neighbourhood of hyperplane $\{x : \langle \textbf x, \textbf n \rangle = a\}$ (`Kakeya.Slab.carrier`)
6. **Frostman slab Wolff bound with constant $C$**: $\# \mathbb T[W] \leq C |W| (\# \mathbb T)$ for every slab $W$ (`Kakeya.FrostmanSlabWolffBound`)
	- $\mathbb T$ here is de-duplicated
7.   **Fixed-constant unit rescaling relative to $T_\rho$**: (`Kakeya.Assouad.wz2PaperLiteralUnitRescalingMap`)
		- First consider the coaxial line of $T_\rho$, written as $l$, which meets the plane $z=0$ at $A$
		- Next, consider axial vector of $T_\rho$, denoted as $\textbf d$. We write $\tilde {\textbf d} = \textbf d$ when $\textbf d_3 \geq 0$ and $\tilde {\textbf d} = - \textbf d$ otherwise
		- Let $R$ denote the reflection across the plane through the origin with norm vector $\tilde {\textbf d} - \textbf e_3$ (when $\textbf d = \textbf e_3,$ set $R=id$)
		- Let $D$ be transverse anisotropic scaling linear map $(x, y, z) \mapsto (x/\rho, y / \rho, z)$
		- ... is $\varphi_{T_\rho} : x \mapsto \frac1{100} D(R(x - A))$
8. **$\mathcal L_3$**: a $\delta$-tube $T$ is in $\mathcal L_3$ if $1/2 \leq \tilde {\textbf d_3}, |A_1| \leq 1/3$ and $|A_2| \leq 1/3$ (`Kakeya.Assouad.WZ1PaperTubeInLineClass`)
- `Kakeya.Assouad.WZ2PaperLiteralUnitRescaledFamilyData`: Let $\mathbb T$ be a family of $\delta$-tubes, $\rho > 0, T_\rho$ be a $\rho$-tube. This structure admits a target family of $\delta/\rho$-tubes (write $q=\delta/\rho$) $\mathbb T_q$ in $\mathcal L_3$ and a bijection $f : \mathbb T_q \rightarrow \mathbb T$ satisfying:
	- $l=\varphi_{T_\rho}\circ l \circ f$
- `Kakeya.Assouad.WZ2PaperAssouadToLiteralRescalingCertificate`: Let $\mathbb T$ be a family of $\delta$-tubes, $\rho > 0, T_\rho$ be a $\rho$-tube. Suppose there is a `WZ2PaperLiteralUnitRescaledFamilyData` on this setting. And set $C_j$ a constant in $[0, +\infty]$. Then this structure admits another family of $\delta/\rho$-tube $\mathbb P_q$ together with two bijections: $g_1 : \mathbb P_q \rightarrow \mathbb T, g_2 : \mathbb T_q \rightarrow \mathbb P_q$ and an affine automorphism $h$ of $\mathbb R^3$  satisfying:
	- $g_1 \circ g_2 =f$
	- $l \circ g_2 =l$
	- $h \circ \phi_{T_\rho} \circ f= \varphi_{T_\rho} \circ f$
	- $\varphi_{T_\rho} \circ f\subseteq g_2$
	- $W$ is convex $\Rightarrow h^{-1}(W)$ is convex
	- $\forall S \subseteq \mathbb R^3, |h^{-1}(S)| \leq C_j |S|$
- `Kakeya.Assouad.WZ2PaperPureOneScaleRescalingBridge`: Let $\mathbb T$ be a family of $\delta$-tubes, $\mathbb T_\rho$ be a family of $\rho$-tubes with $0 < \rho$. Fix a $T_\rho \in \mathbb T_\rho$ and a constant $C \in [0, +\infty]$. Then this structure admits:
	- a `WZ2PaperLiteralUnitRescaledFamilyData` on $(\mathbb T[T_\rho], T_\rho)$, public indexed family is written as $\mathbb P_q$
	- a `WZ2PaperAssouadToLiteralRescalingCertificate` on the aforementioned data with $C_j = 4000000$
	- $\mathbb P_q$ satisfies CWA with error $4000000C$
-  `Kakeya.Assouad.PureWZ2FullFiberAssertionDRefinementData`: Fix $\epsilon_o,\epsilon_a,\kappa,\eta_a,\delta\in\mathbb R$, a constant $C\in[0,+\infty]$, and $(\mathbb T,Y)_\delta$. This structure bundles:
	- a requested scale $\rho_0\in[\delta,1]$ and an actual selected scale $\rho\in[\rho_0,C\rho_0)$, together with a witness that $\mathbb T$ satisfies CWA at actual selected scale $\rho$ with error $C$. Write $\mathbb T_\rho$ for its coarse family
	- a parent $T_\rho\in\mathbb T_\rho$ whose full fiber $\mathbb T[T_\rho]$ is nonempty
	- a John unit rescaling $\phi_{T_\rho}$ under which $\mathbb T[T_\rho]$ satisfies CWA with error $C$
	- a `WZ2PaperPureOneScaleRescalingBridge` on $(\mathbb T,\mathbb T_\rho,T_\rho,C)$. Write $\mathbb P_q$ for its public indexed family of $\delta/\rho$-tubes, and let $g_1$ be its bijection to $\mathbb T$
	- the restriction $0<q\leq1$
	- a shading $Y^{pub}$ on $\mathbb P_q$ satisfying $Y^{pub}(P) \subseteq \Psi\bigl(Y(b(P))\bigr), P\in\mathbb P_q$ where $\Psi=h\circ\phi_{T_\rho}$ and $h$ is the affine coordinate change recorded by the bridge
	- a nonempty indexed subfamily $\mathbb S_q$ of $\mathbb P_q$, with index embedding $\iota$, and a shading $Y^{sel}$ satisfying $Y^{sel}(S)\subseteq Y^{pub}(\iota(S)), S\in\mathbb S_q$
	- $q^{\epsilon_a}\#\mathbb P_q\leq\#\mathbb S_q$ and $q^{\epsilon_a}\sum_T Y^{pub}(T)\leq \sum_T Y^{sel}(T)$
	- a **de-duplicated** family $\mathbb F_q$ of $q$-tubes and a bijection $j$ from its members to the indices of $\mathbb S_q$, satisfying $T=\mathbb S_q(j(T)), T\in\mathbb F_q$
	- $\Psi\bigl(\mathbb T(b(\iota(j(T))))\bigr) \subseteq T, T\in\mathbb F_q$
	- a shading $Y^{tar}$ on $\mathbb F_q$ satisfying $Y^{tar}(T)=Y^{sel}(j(T))$, together with $\bigcup_T Y^{tar}(T) \subseteq \Psi(\bigcup_TY(Y))$
	- the following properties of the target configuration:
		- every tube in $\mathbb F_q$ is contained in $\overline{B(0,1)}$
		- $\mathbb F_q$ is essentially distinct **(2025)**
		- $(\mathbb F_q,Y^{tar})$ is $q^{\eta_a}$-dense
		- $\mathbb F_q$ satisfies the Katz–Tao convex Wolff bound with constant $q^{-\eta_a}$
		- 
----
- `Kakeya.Assouad.PureWZ2FullFiberAssertionDRefinementData`: Fix $\epsilon_o, \epsilon_a, \kappa, \eta_a, \delta$, fix constant $C \in [0, +\infty]$ and $(\mathbb T, Y)_\delta$. This structure bundles:
	- a $\rho_0 \in [\delta, 1]$, a $\rho \in [\rho_0, C \rho_0)$ s.t., $\mathbb T$ satisfies CWA at actual selected scale $\rho$ with error $C$ (this gives a $\mathbb T_\rho$)
	- a $T_\rho \in \mathbb T_\rho$ satisfying:
		- $\mathbb T[T_\rho] \neq \empty$
		-  The unit rescaling of $\mathbb T[T_\rho]$ relative to $T_\rho$ satisfies the CWA with error $C$
	- a `WZ2PaperPureOneScaleRescalingBridge` on $(\mathbb T, \mathbb T_\rho, T_\rho, C)$
	- a restriction that $0 < \delta / \rho \leq 1$
	- a shading $Y_{\delta/\rho}'$ on $\mathbb T_{\delta/\rho}'$


<!--stackedit_data:
eyJoaXN0b3J5IjpbLTI1OTQyNzQ2NiwxMTQ4NzM0NjM4LDU4Nz
E4NDU0MywtNTQ3MzY3NDQzLC01NDczNjc0NDMsLTM0MTc4MDM0
MCwtMTgzNTI3NDU2MCwtMTY5NDY4OTg0NiwtODU4MjIyMTUsLT
MyODc0MDU1LDExNTUwNzMwMjNdfQ==
-->