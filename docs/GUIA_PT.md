# TNumbersLean — guia rápido

`TNumbersLean` acompanha o artigo *Normality in Mahler's Class of T-Numbers*.

O projeto formaliza em Lean 4 o núcleo diofantino da construção e verifica
passos quantitativos selecionados das partes de Fourier e de blocos digitais.

## O resultado principal

A declaração

`TNumbersLean.proposition_three_two`

prova todo o conteúdo lógico da Proposição 3.2 a partir das interfaces
`CriterionSchedule` e `CriterionInputs`: transcendência, separação uniforme
para grandes alturas, limites superiores e inferiores para os expoentes de
Koksma, divergência normalizada e a conclusão de T-número.

A cobertura global dos intervalos de alturas também é formalizada: para todo
`H` suficientemente grande existe estágio admissível `k` com

$$
Q_k^{\delta_n}\le H\le Q_k^{u_{k,n}}.
$$

## O que ainda falta

Para identificar esse teorema abstrato literalmente com a Proposição 3.2 do
artigo, ainda precisamos instanciar as interfaces com:

- o schedule concreto (3.1)--(3.3);
- grau algébrico e altura ingênua reais;
- Northcott;
- os centros provenientes de `E(J;Q_1)` e os bounds da Seção 2.

Schmidt e Icen continuarão como inputs matemáticos externos.

## Verificação

```bash
cd "$HOME/Projects/TNumbersLean"
lake exe cache get
bash scripts/check.sh
```

O script compila o projeto, trata warnings como erros, imprime os axiomas das
declarações auditadas e falha se alguma delas depender de `sorryAx`.

Commit da prova completa da proposição abstrata:

`05cb79aa572d156674c562ae0dd0120a5ae15a36`

Para os detalhes técnicos, veja [`VALIDATION.md`](../VALIDATION.md) e
[`PROPOSITION_3_2.md`](PROPOSITION_3_2.md).
