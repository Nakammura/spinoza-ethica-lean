# Hallazgos destacados de la formalización

> Registro unificado de los resultados filosóficamente interesantes
> producidos al extender la mecanización de la *Ethica* de Spinoza
> en Lean 4 (rama `pars1-extensions`, extensiones post-v1.0.0).
> Cada hallazgo es un **hecho verificado por el kernel de Lean**, no
> una interpretación: cualquier afirmación de derivabilidad o de
> no-derivabilidad citada aquí está respaldada por un teorema o un
> contramodelo que compila en este repositorio sin `sorry`.
>
> Documento en español para uso del mantenedor; la documentación
> técnica canónica (en inglés) vive en `coverage.md`,
> `auxiliary_axioms.md` y `gaps.md`.

---

## 1. El argumento ontológico tiene un hueco irreducible (Prop. XI)

**Archivo**: `Ethica/Pars1/Models/NoGod.lean` · **Teoremas**: `noGodWorld_hasNoGod`, `A27_falsified`

La Proposición XI ("Dios existe necesariamente") **no puede derivarse
ni siquiera del registro completo de axiomas** `Pars1Axioms` (A1–A15,
incluyendo los compromisos metafísicos fuertes A12–A15). Lo prueba un
contramodelo de un solo elemento que satisface los quince axiomas y en
el que nada es Dios.

Por qué importa:

- La *demonstratio* de Spinoza (reductio vía Axioma 7 + Prop. VII)
  deriva una verdad **condicional** — "si algo es sustancia, su esencia
  implica existencia" — pero salta de ahí a la **instanciación**: que
  algo en el dominio satisfaga la definición de Dios. Ese salto es
  exactamente la objeción de Gassendi y Kant al argumento ontológico
  (la existencia no se sigue del concepto).
- Bennett (1984, §18) catalogó cuatro rutas de lectura de la
  demostración y conjeturó que todas requieren un compromiso extra.
  Nuestro contramodelo convierte esa conjetura en **hecho verificado
  por máquina** — y contra una línea de base *más fuerte* que la del
  paper original (que corría contra `StatedAxioms`, sin A12–A15).
- El compromiso mínimo que cierra el hueco quedó explícito como axioma
  **A27 "Deus datur"** (Sección III), con testigo de consistencia en
  `Models/GodWorld.lean`.

## 2. El dilema de la indivisibilidad es una elección, no una necesidad (Props. XII–XIII)

**Archivo**: `Ethica/Pars1/Models/CounterexamplesII.lean` · **Modelo**: `ModeParts` · **Teorema**: `A32_falsified`

Para probar que la sustancia es indivisible, Spinoza argumenta que las
partes de una sustancia serían *sustancias rivales de la misma
naturaleza* (absurdo por Prop. V). Formalizamos esa premisa como el
axioma **A32** — y construimos un contramodelo (`ModeParts`) que
satisface **todo el resto del registro extendido** (A1–A31, A33–A36)
mientras la falsifica: un mundo donde la sustancia tiene una parte
propia que es un **modo**, no una sustancia.

Por qué importa: la lectura "partes-como-modos" no es un artificio —
es esencialmente cómo Curley lee la Carta 12 a Meyer (la cantidad
concebida abstractamente tiene partes; como sustancia, no). El kernel
certifica que esa lectura alternativa es **consistente**: el dilema de
la Prop. XII descansa en una elección interpretativa genuina que nada
más en el sistema fuerza.

## 3. Nada distingue "necesario por causa" de "necesario por esencia" — salvo la Prop. XXIV

**Archivo**: `Ethica/Pars1/Models/CounterexamplesII.lean` · **Modelo**: `NecessaryMode` · **Teorema**: `A35_falsified`

La Prop. XXIV ("la esencia de las cosas producidas por Dios no implica
existencia") parece un corolario trivial de la Def. I — Spinoza la
despacha con "*patet ex definitione 1*". No lo es: el contramodelo
`NecessaryMode` contiene un **modo cuya propia esencia implica
existencia** y satisface todo el registro salvo A35.

Por qué importa: el perfil de ese modo es exactamente el de los *modos
infinitos* de las Props. XXI–XXIII (existen necesariamente y siempre),
con una única diferencia — la necesidad alojada en su esencia en lugar
de en su causa. La distinción entre esas dos necesidades es **todo el
contenido** de la Prop. XXIV, y ningún otro axioma la impone. El
"patet" de Spinoza esconde un compromiso sustantivo (A35, Sección III).

## 4. Una redundancia descubierta por el kernel: A34 se deriva de A37+A38

**Archivo**: `Ethica/Pars1/Consecutio.lean` (docstring de A38) · registro en `auxiliary_axioms.md`

Al introducir la capa de consecución ("seguirse de la necesidad de la
naturaleza divina"), el puente inherencia→causación (A34) resultó
derivable componiendo inherencia→consecución (A37) con
consecución→causación (A38). El costo axiomático real de la lectura
Curley/Della Rocca ("estar en Dios = ser causado por Dios = seguirse
de Dios") es de **dos** compromisos, no tres. A34 se retiene por
compatibilidad, con la redundancia registrada.

## 5. Los diecisiete axiomas nuevos son conjuntamente consistentes

**Archivo**: `Ethica/Pars1/Models/ConsecutioWitness.lean`

Un único modelo satisface simultáneamente A1–A15 + A27–A43 — la mayor
prueba de consistencia conjunta del proyecto. Garantiza que la
extensión (Theologia, Mereology, Inherence, Consecutio) no introdujo
ninguna contradicción: los teoremas nuevos no son vacuamente ciertos
por explosión.

## 6. Paridad metodológica completa en los compromisos de Sección III

Los tres axiomas de Sección III nuevos tienen **ambos** testigos, igual
que los del paper original (A12/A15) — y con líneas de base más fuertes:

| Axioma | Contenido | Testigo de consistencia | Testigo de irreducibilidad |
|--------|-----------|-------------------------|----------------------------|
| A27 | Deus datur (Prop. XI) | `GodWorld` | `NoGod` (vs. Pars1Axioms completo) |
| A32 | partes = sustancias rivales (Prop. XII) | `MereologyWitness` | `ModeParts` (vs. registro extendido) |
| A35 | esencia de modo ∌ existencia (Prop. XXIV) | `InherenceWitness` | `NecessaryMode` (vs. registro extendido) |

La pregunta rectora del proyecto — *¿cuántos compromisos no declarados
necesita realmente la Ética?* — tiene ahora respuesta parcial medida:
para el arco teológico completo de Pars I (27/36 proposiciones con
contenido mecanizado), el costo es **A27–A43**, con exactamente tres
compromisos irreducibles nuevos (A27, A32, A35) y el resto puentes
definicionales (Sección I) o promociones de contenido declarado
(Sección II).

## 7. ⭐ El teorema de colapso de atributos: Dios no puede tener dos atributos

**Archivo**: `Ethica/Pars1/Realitas.lean` · **Teoremas**: `attribute_collapse`, `god_no_two_attributes`, `def6_infinitis_attributis_unsatisfiable` · contraparte: `Models/MultiAttribute.lean`

El hallazgo más fuerte del proyecto hasta ahora, y uno que ningún
comentarista podía establecer con esta certeza: **en cualquier mundo
que satisfaga `Pars1Axioms` y contenga un Dios, todo atributo de toda
sustancia es idéntico a Dios**. En consecuencia, Dios no puede tener
ni siquiera *dos* atributos distintos — la cláusula "*constantem
infinitis attributis*" de la Definición VI no es que esté sin
formalizar (GAP-8a): es **insatisfacible** en el registro actual.

La anatomía del colapso — cinco compromisos que individualmente
parecen inocentes:

1. Los atributos habitan el mismo universo `Thing` que las sustancias
   (lectura del escolio de Prop. X, horneada en la definición de
   `Attribute`).
2. **A10**: todo atributo es concebido por sí (la propia Prop. X).
3. **A8**: "en sí" y "concebido por sí" son coextensivos → todo
   atributo **es una sustancia**.
4. **A14**: toda sustancia tiene un atributo → el atributo-sustancia
   tiene su propio atributo.
5. **A15**: Dios tiene todo atributo de toda sustancia → comparte ese
   atributo con él → **A12** los identifica: el atributo *es* Dios. ∎

El modelo espejo `MultiAttribute` (portador: `Nat`, una sustancia con
infinitos atributos en árbol) prueba que la incompatibilidad es
*nítida*: el registro completo **tolera** la pluralidad infinita de
atributos — exactamente mientras **no exista Dios**
(`multiAttribute_hasNoGod`, `multiAttribute_infinitude`). Es decir:

> **La existencia de Dios (A27) y la pluralidad de atributos son
> conjuntamente inconsistentes en el registro de Pars I.**
> La Def. VI de Spinoza quiere ambas; el sistema concede exactamente
> una.

Localización erudita: Bennett (1984, §16) rehusó aplicar la
coextensión de A8 a los atributos, tratándolos como "maneras básicas
de ser" y no como cosas — el colapso **vindica su cautela a nivel
kernel**. El resultado también valida formalmente la lectura de la
Carta 9 (a de Vries): sustancia y atributo son "una y la misma cosa
bajo dos nombres" — y muestra que esa identidad y la pluralidad real
de atributos no caben juntas. La vieja disputa
subjetivista/objetivista sobre los atributos (Wolfson vs. Gueroult)
deja de ser opcional en este registro: es una bifurcación forzada.

Rutas de escape identificadas (cada una revisa un compromiso): (i)
restringir A12 a sustancias que no sean atributos; (ii) debilitar la
mordida de A8/A10 sobre atributos (la línea de Bennett); (iii) tipar
los atributos fuera del universo `Thing`. Registrado como gap propio
en `gaps.md`.

De regalo, la **Prop. IX quedó mecanizada** en el camino
(`prop_9_moreRealityMoreAttributes`: el orden de realidad como
dominancia de atributos transfiere cualquier conteo, derivación
genuina sin axiomas nuevos; `prop_9_cor_godMaximalReality`: Dios tiene
realidad máxima, directo de A15).

## 8. La cadena causal finita se descompone: demote exitoso de A42

**Archivo**: `Ethica/Pars1/Classificatio.lean` · **Teorema**: `A42_demote_via_trichotomy` · registro Σ: `TrichotomySigma`

La Prop. XXVIII (todo modo finito es causado por otro modo finito, *ad
infinitum* — la columna vertebral causal que las Partes II–V consumen)
había sido comprometida como axioma directo (A42, patrón 📜). El
experimento de demote muestra que **A42 se deriva** del registro
Σ = {A38, A40, A41, **A44**}, donde A44 es la *tricotomía de
consecución*: todo modo se sigue o absolutamente de un atributo de
Dios, o de un modo eterno-infinito, o de otro modo finito.

Resultado en la taxonomía de demotes del proyecto: **descomposición de
fuerza igual** (el patrón de A15) — el residuo sustantivo es
exactamente la premisa de exhaustividad que la *demonstratio* de
Spinoza consume en silencio (el paso "*at non ex absoluta natura
alicujus attributi Dei…*"; Bennett 1984 §25 la señala como premisa no
argumentada). De paso quedó mecanizada la **Prop. XXIII** en forma
parcial (`prop_23_partial_classification`).

El contraste final de la taxonomía para las extensiones: A27, A32 y
A35 **resisten** descomposición (contramodelos en `Models/`); A42
**se descompone** en la clasificación A44. La estructura es la misma
que el paper original encontró en el registro v1.0.0: las cláusulas de
*universalidad/exhaustividad* son los compromisos duros; las cadenas
causales se reducen a ellas.

---

## Resumen numérico del estado (rama `pars1-extensions`)

- **Pars I**: 29/36 proposiciones con contenido mecanizado
  (las 7 restantes: XXVII y XXX–XXXII esperan Pars II; XXXIII la capa
  modal; XXXIV–XXXV la maquinaria de *potentia*).
- **Axiomas auxiliares nuevos**: A27–A44 (18), de los cuales 5 de
  Sección III genuinos (A27, A32, A35, A40, A41, A44 — con A42
  descompuesto en A44) y el resto puentes/promociones.
- **Modelos nuevos**: 9 (4 testigos de consistencia, 3 contramodelos
  de irreducibilidad, 1 bench multiatributo, 1 testigo global).
- **Teoremas de imposibilidad**: 2 (no-derivabilidad de la existencia
  de Dios; incompatibilidad Dios ∧ pluralidad de atributos).
- `lake build` limpio, **0 `sorry`**, ninguna declaración de v1.0.0
  modificada.

*Documento actualizado junto con cada tramo de trabajo.*
