# TNumbersLean — guia rápido em português

Este projeto contém uma formalização **seletiva** em Lean 4 de cálculos sensíveis do artigo

> *Normality in Mahler's Class of T-Numbers*

de Diego Marques.

O objetivo não é formalizar todo o artigo, mas verificar no kernel do Lean os budgets de expoentes, identidades numéricas e passos lógicos mais sujeitos a erros de sinal ou de escala.

## 1. Estrutura do projeto

| Arquivo | Conteúdo |
| --- | --- |
| `TNumbersLean/DiophantineBudget.lean` | Expoentes da Proposição 3.2 e overlap dos height ranges |
| `TNumbersLean/FourierBudget.lean` | Budget da perturbação de Fourier |
| `TNumbersLean/DigitBudget.lean` | Constantes e expoentes das construções digitais |
| `TNumbersLean/HeightOverlap.lean` | Núcleo lógico do argumento do último estágio admissível |
| `scripts/Audit.lean` | Lista dos teoremas auditados por axiomas |
| `scripts/check.sh` | Build completo, warnings-as-errors e checagem de `sorryAx` |

## 2. Ambiente

O projeto fixa:

- Lean 4.24.0;
- mathlib v4.24.0.

No macOS, abra o Terminal e entre na pasta do projeto:

```bash
cd "$HOME/Projects/TNumbersLean"
```

Depois rode:

```bash
lake exe cache get
lake build
bash scripts/check.sh
```

## 3. O que significa um build verde

Se

```bash
lake build
```

termina com

```text
Build completed successfully
```

os módulos do projeto compilaram no kernel do Lean.

O comando

```bash
bash scripts/check.sh
```

faz uma checagem adicional:

1. recompila o projeto;
2. trata warnings como erros nos arquivos do projeto;
3. imprime os axiomas dos teoremas principais listados;
4. falha caso apareça `sorryAx`.

## 4. O que está formalizado

Entre os cálculos formalizados estão:

[
2(K_n+3)le(n+2)^3,
]

a comparação que garante o overlap dos intervalos de alturas, a identidade

[
K_n+1=(n+1)^2,
]

o cálculo explícito do expoente de (B_n), e

[
rac{(d+1)^3}{d^2}-rac1d
=d+3+rac2d+rac1{d^2}.
]

No lado de Fourier:

[
rac5{100}=rac1{20},
qquad
rac1{20}-rac14=-rac15.
]

Na construção digital:

[
2cdot4^4=512,qquad
16cdot512=8192,qquad
100A-6A=94A.
]

## 5. O que não está formalizado

O projeto não pretende formalizar neste momento:

- o teorema de Schmidt;
- toda a recursão de graus e escalas;
- o teorema dos números primos;
- a construção completa das medidas;
- Borel--Cantelli e o critério de Weyl;
- os conjuntos perfeitos completos das duas construções.

Essas partes continuam provadas no manuscrito, mas não são objeto desta formalização seletiva.

## 6. GitHub Actions

Cada push para o GitHub executa automaticamente o workflow

```text
.github/workflows/lean.yml
```

O badge no README mostra o estado da branch `main`.

## 7. Regra importante

Não escreva no artigo que existe uma “full Lean formalization” dos teoremas principais.

A formulação correta é:

> A selective Lean 4 verification of the principal exponent calculations in the common Diophantine criterion, the Fourier perturbation budget, and the digit-block construction is available in the TNumbersLean repository.

Isso descreve exatamente o escopo certificado pelo repositório.
