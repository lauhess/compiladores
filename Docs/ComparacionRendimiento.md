### Función de Ackermann con `m=3` y `n=8`
## Resultados sin optimización. Parámetros gcc: `-Os`

| Tipo de ejecución                         | Tiempo promedio (ms) | Desviación estándar (ms) |
|------------------------------------------|----------------------|--------------------------|
| Eval simple                              | *(dato)* | *(dato)*|
| CC                                       | 130.4               | 3.1                      |
| Bytecode 32 bit                          | 229.7               | 5.4                      |
| Bytecode 8 bit                           | 272.5               | 5.7                      |
| Ackermann recursivo C                    | 4.3                 | 0.1                      |
| Ackermann recursivo Haskell              | 69.7                | 2.3                      |
