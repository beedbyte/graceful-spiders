# Beedbyte — 在 graceful 根图上添加两条 95 边臂

英文说明为原文；德文和简体中文版本为翻译草稿。Jordi Gartner 拥有这项工作，并通过 Beedbyte 发布。

## 精确定理

设 H 为任意有限索引图，有 Q 条边、指定顶点 r，以及给定的通常意义下的 graceful 标号 g。此处要求顶点标号单射到 0..Q，边的绝对差值双射到 1..Q，并且 g(r)=0。

将 r 与新建的 190 边路径中点合并，添加两条分别命名、各有 95 条边的臂，并保留 H 的所有旧顶点和旧边。对任一新臂及每个实际深度 d=1..94，所得图都存在依目标而定的通常 graceful 标号，使该实际选定的新顶点标为零。不同臂或深度可使用不同标号。输出顶点标号单射到 0..Q+190，边权恰为 1..Q+190。

H 不必是树、连通图、具有 alpha 标号的图或顶点标号满射的图。标号为 0,1,3 的非满射三角形也满足条件。定理要求给定的标号在选定根处为零，并不证明任意指定根都允许这样的标号。它不包含深度 95 的新臂端点、H 的旧目标顶点，或更强的顶点标号满射谓词。

精确 Lean 声明为 [source/K95Rooted.lean](source/K95Rooted.lean) 中的 `GracefulBoundary.K95Rooted.interior`。其合取结论分别给出路径索引 95-d 和 95+d 处实际拼接顶点的存在性证据。

## 证据与方法

包内包含数学作者证明、另行实现的内部数学检查、Lean 作者报告，以及另行执行的内部复制源代码重建检查。数学检查披露曾有限阅读作者文字，因此不称为完全盲审；它未使用作者检查程序。

复制源代码检查从空对象目录开始，以 Lean 4.34.0、将警告视为错误，重新编译了全部 59 个传递依赖项目模块。检查了按来源模块识别的 2,239 个定理公理依赖闭包，均仅使用标准公理 `propext`、`Classical.choice`、`Quot.sound`；精确定理类型；非满射三角形在两臂全部 94 个深度的实例；196 个具名目标断言；以及四个有效的根、臂端点、旧顶点和满射语义对照。未导入作者或前序对象。编译器及其标准库属于明确的信任边界，标准库未重新编译。这些属于项目内部检查，并非外部学术同行评审。

AI 工具协助了已记录的构造和证明代码工作、字面数据及图检查、另行分派的内部源代码重建检查，以及这些读者说明的翻译。发布责任仍由 Jordi Gartner 通过 Beedbyte 承担。精确文件哈希和检查边界见 [evidence-pins.json](evidence-pins.json) 及保留的证据报告。

高侧 d-graceful 平移、整体平移、标号取补和顶点合并都是已有操作。Panpa、Imnang 和 Wasuanankul（2025，定理 2.5，转述 Huang–Kotzig–Rosa）以及 Shan 和 Zhong（2026，引理 1）都陈述了 alpha 标号图与在合并顶点处标为 0 的 graceful 图之间的一般顶点合并操作。本文构造将此操作用于带 graceful 标号的根图 H 和一条 alpha 标号路径。Barrientos（2020）《Alpha graphs with different pendent paths》第 302–303 页描述了相关子变换及一种以两个 alpha 图为输入的较窄合并；见[出版社 PDF](https://www.ejgta.org/index.php/ejgta/article/download/1036/pdf_143)。这是操作层面的重合，并非适用于任意 H 的原文定理。本包不主张新的基本操作。这个精确位置图族结论的优先权为 **UNKNOWN**；不声称已完成穷尽的全球文献比较或外部评审。参见 [Panpa–Imnang–Wasuanankul，定理 2.5](https://onlinelibrary.wiley.com/doi/10.1155/jama/5826777) 和 [Shan–Zhong，引理 1](https://arxiv.org/html/2605.14295v2)。

## 复现

包内提供完整的 59 源文件项目导入依赖闭包、另行编写的检查、模块顺序，以及源代码和证据清单。证明源文件与冻结的重建检查输入逐字节相同。使用 Python 3、精确验证过的 Windows Lean 可执行文件，以及新的或空的构建目录运行：

```text
python -B build.py --lean "path/to/lean.exe" --build-dir "new-empty-build-folder"
```

可执行文件须匹配 SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`（Lean 4.34.0，提交 `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`）。此脚本不安装软件，也不验证其他编译器或平台。它核对包清单，生成全新对象，重复类型、三角形和公理检查，并要求四个语义变异用例被拒绝。它不删除文件。`SHA256SUMS.txt` 包含全部包文件，但排除其自身精确根路径。

英文：[README.md](README.md)。德文：[README.de.md](README.de.md)。三种说明保持相同的数学范围和验证边界。
