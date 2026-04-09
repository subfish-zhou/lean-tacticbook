# Lean 4 自动化内幕

从 tactic 编写到决策过程自动化 / Lean 4 Automation Internals: From Tactic Writing to Decision Process Automation

## 目录

### Part I: Foundations — How Tactics Work
- Ch0: 环境与运行约定
- Ch1: Lean 4 元编程模型
- Ch2: Expr：Lean 4 的内部表示
- Ch3: 编写你的第一个 Tactic

_(更多章节持续更新中)_

## 构建

需要 Lean 4 v4.30.0-rc1（通过 elan 安装）。

```bash
lake build           # 编译
lake exe lean-auto-book  # 生成 HTML 到 _out/
```

## Authors
- Ziyu Zhou (子鱼) — primary author
- Yachiyo (八千代) — writing assistant
- Noi (乃依) — reviewer & editor
