# 臂长为95条边的蜘蛛树的零可旋转性

**Beedbyte — 源码包v1**

Jordi Gartner 通过 Beedbyte 发布这项工作。[English](README.md) · [Deutsch](README.de.md)

## 定理

对所有整数 `n ≥ 2`、`m ≥ 0`，以及 `S(95^n,1^m)` 的每个实际顶点v，都存在一个使v标签为零的优美标号。图由一个中心、n条各含恰好95条边的具名长臂，以及中心处m个原有短叶组成。每个目标使用独立的标号；顶点标签恰为 `0,…,95n+m`，边的绝对差恰为 `1,…,95n+m`。结论包括中心、每条具名臂上实际深度1..95的全部顶点，以及每个实际存在的短叶。m=0时没有短叶目标。这里不声称其他奇数臂长的定理。

Lean入口定理为 `GracefulBoundary.K95Full.all_vertices`；`unique_zero` 还证明所选顶点是唯一零点。见 [K95Full.lean](source/K95Full.lean)、[完整深度对应表](coverage.md) 和 [精确目录](data/lean-catalog.json)。

## 证明与验证

51个具有中点条件的P191路径α标号覆盖臂深度1..94。Lean检查完整的标签和边差集合、分界94、实际中点索引95上的标签94，以及指定极值位置。已有的α合并方法配合显式根标零剩余树，将每个路径证书转移到所有n、m和每条具名臂。最大值目标通过全图取补得到零。中心、原有短叶和实际端点95由显式构造处理。

状态：**独立任务的内部数学QA为GO；Lean作者构建为GO；另行复制源码的Lean重放为GO。** 作者使用Lean4.34.0并将警告视为错误，编译了35个源码模块；检查了1678个仅依赖标准公理的定理公理闭包、671个具名实例和12个语义反例控制。后续的[独立重放](evidence/separate-lean-replay.md)重新编译了全部35个模块，检查了八个指定定理的公理闭包、13个实例和八个语义控制。数学汇总核查采用独立实现和全参数转移证明。这些核查属于内部验证，不是外部审查或同行评审。

本包仅含源码，不含编译对象。信任边界包括Lean内核、可执行程序及标准库，以及图定义和其数学解释。[evidence](evidence/) 中保留了选定的冻结报告与原始清单；原始清单描述各自的审计目录，而不是本包的文件集合。证据报告记录各自冻结日期的状态；上面的当前验证状态包含后续记录。[provenance.json](provenance.json) 记录复制来源和哈希。

## 既有成果与限制

本工作明确归功于已有的α合并、优美排列插入和连接方法，包括 [Hicks–Ollis–Schmitt引理4.5的证明](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf)、[Adamaszek引理1](https://arxiv.org/pdf/math/0608513) 和 [Ollis引理5.5/定理5.6](https://ajc.maths.uq.edu.au/pdf/78/ajc_v78_p035.pdf)。H1分支使用已有的连接操作。[Luiz–Campos–Richter引理4/定理14](https://ic.unicamp.br/~reltech/2017/17-12.pdf) 已覆盖 `n=2,m=0/1` 子族的每个顶点。其引理5是单个指定点的普通优美标号自由性，并非同时满足中点、α分界和极值位置的条件。

全球优先权仍为 **UNKNOWN**。[有限范围比较](evidence/bounded-priority.md) 记录其他重叠结果，以及 [Cattell2007](https://doi.org/10.1016/j.disc.2007.03.046) 原文全文仍未获得的缺口。访问缺失或新的项目目录都不能证明新颖性。

## 复现与贡献

需要Python3.10+和Lean4.34.0，无需求解器：

```
python build.py --check
python verify_catalog.py
python -O verify_catalog.py
python build.py --lean /path/to/lean --output /new/directory/outside/this/package
```

构建脚本检查SHA256SUMS.txt中的全部文件哈希，按依赖顺序编译，并仅将新输出目录放入LEAN_PATH。AI工具协助了已记录的源构造、证明开发、编程、Lean形式化、文献比较和内部核查；这些贡献与Jordi Gartner的发布责任分开说明。本组译文经过内部一致性检查，没有声称外部语言审校。

版本1提供固定k95定理、完整内部深度目录、边界及端点源码、复现工具和选定证据。
