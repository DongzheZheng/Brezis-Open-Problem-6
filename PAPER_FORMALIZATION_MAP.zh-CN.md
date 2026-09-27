# 论文命题与 Lean 陈述的对应关系

本索引对照单位球、任意正参数的数学主定理与 Lean 陈述。每个端点的显示前提共同规定了形式化验证的准确范围；文献输入和经典分析输入另列于 [`EXTERNAL_INPUTS.md`](EXTERNAL_INPUTS.md)。

| 论文环节 | Lean 对象 | 当前状态 |
| --- | --- | --- |
| $n\ge3$、$\varepsilon=1$、$R>0$ 的光滑固定迹比较和等号 | `physical_smooth_ball_minimum_and_ae_equality` | 在下列剖面、球面与整空间输入下已证明；能量用经典 `fderiv`，仅用于光滑场。 |
| 径向有限球与整空间轮廓的存在和正则性 | `PhysicalRadialDataCore` | 具体轮廓满足这些条件仍是前提；`y` 的构造、排序、余项正性等本文步骤已在 Lean 中证明。 |
| 接触余量在外端点的符号 | `physical_profile_contact_coercivity_certificate` | 在 `(0,R)` 严格为正，在 `R` 非负；正文命题已按此陈述。环域定量稳定性只在 `[δ,ρ]` 且 `ρ<R` 上需要严格正性。 |
| 零模的环域定量控制 | `profilePicone_remainder_annular_le_full_density_sharp`、`PhysicalRadialData.annular_remainder_constant`、`PhysicalRadialData.zero_mode_annular_l2_fixed`、`PhysicalRadialData.bridgeMean_annular_l2_fixed` | 从 ODE、Picone 恒等式和原点通量推出：每个 $0<\delta\le\rho<R$ 均有只依赖剖面与环带的 $\lambda_{\delta,\rho}>0$，**在选择竞争者和球面坐标前**固定，并满足 $\lambda_{\delta,\rho}\int_\delta^\rho b^2\le Q_0[b]$。四个固定系数模块已在远程服务器编译；对公开的 `PhysicalRadialData`，接触正性、原点通量因子衰减，以及 Picone 平方项和接触余项的穿孔区间可积性均已自动推出。实际光滑场提供径向均值的导数、原点右极限、原始密度可积性和穿孔通量正则性。 |
| 非零球谐的环域径向定量控制 | `PhysicalRadialData.annular_angular_constant`、`bridgeQuadratic_controls_meanZero_radial_derivative_on_annulus_fixed` | 从球面桥的精确非负余项和剖面间隙推出：在固定 $[\delta,R]$ 上选定只依赖剖面的 $\kappa_{\delta,R}>0$，对所有球面切片有 $\kappa_{\delta,R}\int_\delta^R\|\partial_r(v-ce)\|^2\le Q_{\mathrm{bridge}}$。这两个模块已在远程服务器编译。Hilbert 值估计覆盖一阶与全部更高球谐；它控制径向导数，实际球面切片的可积性由后续实例化提供。 |
| 外迹与整条环带的定量桥 | `annular_trace_l2_with_fixed_remainder_constants`、`actual_smooth_annular_coordinate_stability_uniform`、`actual_smooth_annular_distance_le_vector_bridge_uniform`、`actual_smooth_annular_energy_gap_uniform` | 已在远程服务器编译。Picone 零模、mean-zero 径向导数、固定外迹、有限坐标求和、极坐标公式和能量桥共同给出 $\int_{A_{\delta,\rho}}\|u-f e_r\|^2\le C_{\delta,\rho}(E(u)-E(fe_r))$。常数只依赖剖面与环带，**在任意光滑固定迹竞争者及目标坐标之前**选定；实际场的均值、导数、通量、可积性和球面谱隙接口均已接入。 |
| 整空间径向涡旋极小性 | `PublishedC1VortexMinimality` | 明确的外部文献结果，按所有紧支 $C^1$ 扰动陈述；Lean 没有证明该专项分析定理。 |
| 同迹场的零延拓与逼近 | `StandardC1FixedTraceZeroExtensionBridge`、`publishedC1_and_standardTrace_to_ballMinimality` | 前者是尚未在 Lean 内实例化的经典 Sobolev 迹/密度定理；它给出真实弱梯度及强 $H^1\cap L^4$ 内支近似。后者已在 Lean 中从此桥和文献紧支扰动不等式推出内部球比较，能量收敛也已形式化证明。 |
| 球面尖锐谱隙 | `SharpUnitSpherePoincareLocal` | 仍是明确的球面解析前提；球面坐标均值零已在独立模块证明。 |
| 真正的 $H^1(B_R;\mathbb R^n)\cap L^4$ 场及其能量 | `WeakH1L4BallField`、`HasWeakGradientOnBall`、`weakBallEnergy` | 弱梯度按分布积分分部定义，要求实际的 $L^2,L^4$ 可积性；能量从该弱梯度计算。 |
| 固定径向边值的弱竞争者 | `WeakFixedTraceCompetitor` | 差映射的零延拓在整个欧氏空间具有分布弱梯度且属于 $H^1\cap L^4$。这是本形式化采用的固定迹定义；它与论文通常 Sobolev 球面迹相等的等价性尚未形式化，需作为标准外部桥梁说明或在论文中明确采用零延拓定义。 |
| $C^1$ 场的经典梯度、弱梯度及能量一致 | `hasWeakGradientOnBall_of_globalC1`、`WeakH1L4BallField.ofGlobalC1`、`weakBallEnergy_classical_gradient` | 已证明全局 $C^1$ 场在有限球上的分布积分分部；有限球可积性、弱场构造和经典／弱能量一致也已形式化。 |
| 径向基场的真实弱代表 | `radialRegularField_weak_energy_eq_vortex`、`physical_weak_ball_minimum_and_ae_equality` | 由 $H_f(\|x\|^2)x$ 在球内构造基涡旋的弱梯度、$H^1\cap L^4$ 代表和真实能量；主端点不再有额外的密度、稳定性或等号正则性前提。 |
| $H_0^1\cap L^4$ 的固定迹光滑密度与能量收敛 | `physical_weak_fixed_trace_strong_closure`、`weakBallEnergy_tendsto_of_strongH1L4` | 已由零延拓弱梯度数据构造共同的光滑紧支撑扰动序列，强 $H^1$ 与强 $L^4$ 收敛，并推出真实弱能量收敛；在本文选定的零延拓固定迹定义下，不再把强近似的存在作为前提。 |
| 等号情形的弱极限 | `weak_ae_eq_of_strong_closure_and_smooth_annular_stability`、`physical_weak_ball_minimum_and_ae_equality` | 对光滑近似应用统一环带能量间隙估计，以强 $H^1\cap L^4$ 收敛传递能量和环带 $L^2$ 距离，取可数环带耗尽球并利用原点零测度，得到弱等号场几乎处处唯一；无需弱极小元的 Euler–Lagrange 方程或 $W^{2,p}$ 正则性。 |
| $n=m+3\ge3$ 的真实弱能量最小性与等号 | `physical_weak_ball_minimum_and_ae_equality_from_core` | 已在远程服务器编译。对任意本形式化定义的固定迹弱竞争者，直接证明最小性和等号唯一性；明示剖面、文献整空间极小性、标准零迹桥和球面谱隙四项输入。 |
| 任意 $\varepsilon>0$ 的单位球版本 | `physical_weak_unit_epsilon_minimum_and_ae_equality_from_core`、`physical_weak_unit_base_from_core_ae_eq_vortex` | 已在远程服务器编译。弱梯度、零延拓固定迹和能量在正尺度伸缩下转移；单位球基场几乎处处等于论文的 $f_\varepsilon(r)=f_{1/\varepsilon}(r/\varepsilon)$ 径向涡旋。无额外大球极小性前提。 |

形式化结论是：以径向剖面定理、已发表整空间涡旋紧支扰动极小性、标准零迹延拓与强逼近桥、球面尖锐谱隙为四项分别显示的输入，Lean 4 已验证 $n\ge3$ 的任意正参数弱能量最小性与等号唯一性。顶层有限球与单位球端点的 `#print axioms` 均只报告 `propext`、`Classical.choice` 和 `Quot.sound`。这些输出审计 Lean 证明项；四项数学输入的证明及具体实例化属于外部依赖范围。

`PhysicalRadialData` 已经不再要求分别给出二阶导数见证、导数的 $C^1$ 正则性、重复的 ODE 条件、$\eta$ 在闭球上的连续性或外端接触余量的左极限；这些由 `PhysicalRadialRegularity`、`PhysicalProfileOrder` 和顶层组装证明。剩余剖面前提与论文“既有径向轮廓定理”之间仍有以下接口差异：

- 论文给出 $f_R$ 在自然区间 $[0,R]$、$F$ 在 $[0,\infty)$ 上的正光滑解。Lean 目前使用定义在整条实线上的全局 $C^2$ 扩张。有限球剖面越过 $R$ 的扩张及两剖面跨过原点的扩张尚未在 Lean 中构造。
- 论文在原点使用局部光滑分解 $p(r)=rH(r^2)$；对本文多项式势，正文已简述由解析椭圆正则性和 $O(n)$ 等变性得到它。Ignat--Nguyen 定理 2.1 的印刷陈述只直接给出 $f(r)/r\in C^2$，所以这一加强不能误称为该定理的逐字结论。`OriginFactorTaylor` 已从正半径上的 $C^2$ 因子导出 `RadialOriginTaylorInterior` 的**函数、一阶导数、二阶导数三条五次 Peano 展开**，并结合已形式化的径向 ODE 系数抽取给出三次、五次项的具体公式。公开 `PhysicalRadialDataCore` 入口已调用该定理，因而不再独立要求 Taylor 系数或余项。仍未形式化的是从文献的半轴剖面构造此入口所用的全实线 $C^2$ 代表及因子；原点局部解析正则性也是所引用剖面事实的一部分。
- 辅助函数 $y$ 现在由 `PhysicalProfileYExtension` 在 Lean 中定义为正半径上的 $1-rF'(r)/F(r)$，在非正半径置零。原点因子分解推出导数为零，因而全实线可微。公开 `PhysicalRadialDataCore` 接口不再要求 `y`、`hyDiff`、`hyMatch`，并以文献自然形式的 $F'>0$ 推出内部使用的 `hyFlt`。`profile_logSlope_lt_one` 则证明相反方向的 $1-rF'/F>0$，两者不可混淆。

剖面的存在、正性、单调性、边值、整空间远场极限与 ODE 本身是论文引用的既有结果；形式化它们将涉及奇异径向边值问题和整空间射击／极限分析，不能由上述接口清理代替。若尚未完成这些构造，论文的形式化验证声明应把“径向剖面定理作为文献输入”写明。

形式化的弱等号路线把环域稳定性只用于**光滑近似场** $u_j$。逐坐标桥、Picone 定量余量、极坐标求和与能量桥已给出每个紧环带上的 $\|u_j-fe_r\|_{L^2}^2\le C_{\delta,\rho}(\En(u_j)-\En(fe_r))$；固定迹强 $H^1\cap L^4$ 近似使右侧趋零且 $u_j\to u$ 在环带上强 $L^2$ 收敛，于是 $u=fe_r$ 几乎处处。论文正文现已采用这一等号证明路线。

依赖项分属两个层次：球面尖锐谱隙与 Sobolev 迹等价属于经典背景；径向 Ginzburg--Landau 剖面存在性及任意幅度整空间涡旋极小性属于本问题已有的专项结果。它们在数学证明中按原始文献准确引用，在本仓主定理中以明确前提出现。读者可以据此区分已机证的新推导与所采用的成熟分析定理。
