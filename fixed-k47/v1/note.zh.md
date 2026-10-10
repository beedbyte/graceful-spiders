# 47 条边长臂蜘蛛树的零可旋转性

> **草稿：简体中文译文，尚未经过语言审校。**

Jordi Gartner 通过 Beedbyte 发布这项工作。

设 `S(47^n,1^m)` 为一棵树，含有一个中心、`n` 条分别命名且各有 47 条边的长臂，以及中心相连的 `m` 个分别命名的原始叶顶点。对于每个 `n ≥ 2` 和 `m ≥ 0`，每个实际存在的顶点——中心、每条命名长臂上深度 1 至 47 的所有顶点，以及实际存在的 `m` 个叶顶点——都可以在一个优美标号中取值 0。标号可以随选定顶点而不同。该图有 `N=47n+m` 条边；优美标号将顶点双射到 `0,…,N`，并将边的端点差绝对值双射到 `1,…,N`。

构造使用 95 个顶点的有限 alpha 路径证书处理长臂深度 1–38，以混合 q24 构造处理深度 39–42，以 q30 构造处理深度 43–44，以直接路径证书处理深度 45，并以端点构造处理深度 46–47。另有专门的零根构造处理中心和每个原始中心叶顶点。该源码只证明固定臂长 47；它没有证明所有奇数臂长的结论，也没有证明无界的 q24/q30 递增族。

Luiz、Campos 和 Richter 的 [*Some families of 0-rotatable graceful caterpillars* (2017), 技术报告 IC-17-12](https://ic.unicamp.br/~reltech/2017/17-12.pdf) 已覆盖完整路径情形 `n=2,m=0` 和 `n=2,m=1`；后一情形是在路径中心连接一个叶顶点。零根蜘蛛树、alpha 拼接、图补标号，以及等长臂蜘蛛树通常优美可标号的结果也都是已有工具。[Patterson 于 2017 年完成的学位论文](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content)讨论了相关的拼接方法，并提出关于蜘蛛树零可旋转性的广义猜想。有限范围的比较尚不能确定早期路径构造是否提供了这里所需的联合源条件，因此历史优先权仍为**未确定**。另见 Cattell 的 [*Graceful labellings of paths* (2007)](https://doi.org/10.1016/j.disc.2007.03.046)，以及 Bahls、Lake 和 Wertheim 的 [*Gracefulness of families of spiders* (2010)](https://msp.org/involve/2010/3-3/involve-v3-n3-p01-s.pdf)。

Lean 声明 `GracefulBoundary.K47Full.all_vertices` 和 `GracefulBoundary.K47Full.all_vertices_unique_zero` 形式化了对所有实际存在顶点的普遍结论及其唯一零点加强版本。可复现的软件包含 42 个逐字节固定的 Lean 模块。一次单独的复制源码重放以警告视为错误的设置编译了全部 42 个模块，依据 Lean 标准公理检查了 2,201 个定理依赖（含 111 个私有声明），检查了 `n=2,m=0/1` 的 191 个实际命名顶点实例，并拒绝了六个语义负控制。这些都属于项目内部检查，并非外部评审或学术同行评审。

## 方法

AI 工具实质性地协助了源码构造、检查程序、数学综合、部分文献比较，以及德文和中文翻译草稿的准备。Lean 构建和单独完成的检查属于项目内部验证，并非外部学术评审。Jordi Gartner 通过 Beedbyte 承担发布责任。

本源码包不含 PDF。
