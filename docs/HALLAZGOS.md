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

## 9. ⭐ El colapso era un artefacto del tipado — y la Def. VI se recupera

**Archivos**: `Ethica/Attributum/` (capa nueva, rama paralela) ·
**Teoremas**: `dual_god_with_two_attributes`, `inf_def6_recovered`,
`legacy_god_no_two_attributes`, `legacy_collapse`

El hallazgo 7 dejaba una pregunta abierta: ¿el colapso de atributos
refleja un compromiso real de Spinoza, o un accidente de cómo lo
formalizamos? Ahora está respondido, y la respuesta es **lo segundo**.

La capa `Ethica/Attributum/` tipa los atributos fuera del universo
`Thing` (`AttrWorld Thing Attr`, con `Attributum a s` donde
`a : Attr`). Con eso, el paso 3 de la cadena de cinco
—`attribute_is_substance`— deja de ser falso y pasa a ser
**inexpresable**: `Substance a` no tipa. La Prop. X sobrevive vía
`perSeConceivedAttr`, campo de una clase `AttrStructure Attr` que ni
siquiera menciona `Thing`. Lo único que se retira es la *mordida de
A8 sobre los atributos* — exactamente la posición de Bennett (1984
§16), ahora impuesta por el sistema de tipos y no por restringir un
axioma. Los cuatro axiomas de atributos se re-tipan verbatim como
A10′/A12′/A14′/A15′, conservando su clasificación de Sección.

Dos testigos, ambos **sin depender de ningún axioma** (verificado con
`#print axioms`):

- `Models/DualAttribute.lean` — un Dios con **dos** atributos
  distintos, `cogitatio` y `extensio`, en un mundo que satisface
  `AttrAxioms` **y** `StatedAxioms` (los A1–A11 propios de Spinoza,
  el registro contra el que corre el paper publicado).
- `Models/InfiniteAttribute.lean` — un Dios con **infinitos**
  atributos. La cláusula *constantem infinitis attributis* de la
  Def. VI queda satisfecha: **GAP-8a cerrado**. Contraste con
  `Models/MultiAttribute.lean`, que lograba la infinitud sobre el
  registro completo de Pars I solo a costa de ser *sin Dios*; aquí
  Dios y pluralidad coexisten.

El diagnóstico lo da `Bridge.lean`: `legacyAttrWorld` instancia
`Attr := Thing`, y bajo esa instancia `Attributum`, `IsGodAttr`,
`hasAtLeastNAttrs` y `HasInfiniteAttrs` son *definicionalmente* sus
contrapartes de Pars I (cuatro lemas `Iff.rfl`). Los teoremas
`legacy_collapse` y `legacy_god_no_two_attributes` transportan la
imposibilidad de Pars I al vocabulario nuevo.

> **La misma frase, bajo los mismos axiomas, es satisfacible cuando
> `Attr` es un tipo aparte y refutable cuando `Attr := Thing`.**
> El colapso no era un compromiso de Spinoza: era el escolio de la
> Prop. X identificando atributos con cosas.

Nada de `Ethica/Pars1/` fue modificado: la decisión fue **congelar
v1.0.0** para que el paper publicado (arXiv:2605.02331) siga válido.
El colapso sigue siendo verdadero de Pars I, y ahora sabemos
exactamente por qué.

Consecuencia práctica: **Pars II queda desbloqueada**. Sus
Proposiciones I y II afirman que Pensamiento y Extensión son dos
atributos distintos de Dios — literalmente lo que
`dual_god_with_two_attributes` exhibe.

## 10. Pars II arranca — y el paralelismo resulta ser una derivación genuina

**Archivos**: `Ethica/Pars2/Idea.lean`, `Ethica/Pars2/Models/MensWitness.lean` ·
**Teoremas**: `prop_2_1_2_deusHabetDuoAttributa`, `prop_2_7_ordoEtConnexio`,
`pars2_opening_triple_inconsistent_in_pars1`, `mens_coexistence`

Primer módulo fuera de Pars I: Proposiciones II.I, II.II, II.III y
II.VII. Dos hallazgos.

**(a) La conjunción de las Props. I y II es un teorema que Pars I
refuta.** Ninguna de las dos por separado es notable; juntas afirman
que Dios tiene dos atributos distintos, y
`prop_2_1_2_deusHabetDuoAttributa` lo *deriva* de A46+A47+A48. Es el
primer teorema del proyecto que el registro de Pars I **refuta
activamente** (`god_no_two_attributes`). El contraste quedó
mecanizado en el vocabulario de Pars I:
`pars2_opening_triple_inconsistent_in_pars1` prueba que, con
atributos tipados como cosas, Pensamiento y Extensión tendrían que
ser *el mismo* atributo. Eso es exactamente en qué sentido la capa
Attributum era un prerrequisito y no un refinamiento.

**(b) El paralelismo es derivable, no un compromiso.** La Prop. VII
—*ordo et connexio idearum idem est ac ordo et connexio rerum*, la
tesis más famosa de la Ética— tiene una *demonstratio* de dos frases:
"*Patet ex axiomate 4 partis I. Nam cujuscunque causati idea a
cognitione causæ cujus est effectus, dependet.*" Resulta que eso es
literalmente suficiente: A4ₛ da la dependencia de inteligibilidad
entre cosas, y A50 —que es *la segunda frase de Spinoza*, promovida
como puente de Sección II, no una reconstrucción nuestra— la traslada
a dependencia causal entre ideas. `prop_2_7_ordoEtConnexio` es una
derivación de dos pasos.

Honestidad sobre el alcance: en el batch 1.1 solo se mecanizó la
dirección cosas→ideas. La conversa se cerró en el batch 1.2 (A55,
hallazgo 11); la lectura de *identidad* del escolio ("*modus
extensionis et idea illius modi una eademque est res sed duobus
modis expressa*") sigue abierta — GAP-27b.

**Bonus: se retiró el placeholder más viejo del proyecto.** El A6 de
Spinoza (*Idea vera debet cum suo ideato convenire*) llevaba como
`True` desde v1.0.0, anotado "idea/ideatum machinery is Pars II".
A45 lo promueve a contenido sustantivo, en la lectura de
*funcionalidad* (una idea determina su objeto), con la lectura fuerte
de adecuación diferida al batch 1.4 y marcada como tal.

**El testigo prueba la coexistencia.** `MensWitness` satisface el
registro completo (A1–A15 + A4ₛ/A5ₛ + A10′–A15′ + A45–A50) en un solo
portador, y en ese mismo mundo valen a la vez:

- `mens_duo_attributa` — Dios tiene dos atributos tipo `Attr`;
- `mens_pars1_collapse_holds` — ningún Dios tiene dos atributos tipo
  `Thing` (vía `god_no_two_attributes`, porque `Pars1Axioms` vale de
  verdad ahí).

No hay tensión: el canal de atribución tipo `Thing` queda degenerado
exactamente como fuerza el teorema de colapso, y la estructura que
Pars II consume vive en `Attr`. Los dos canales conviven.

---

## 11. ⭐ El *quatenus* no cuesta metafísica — y el infinito de las ideas es una necesidad estructural

**Archivos**: `Ethica/Pars2/Quatenus.lean`,
`Ethica/Pars2/Models/MensWitness.lean` ·
**Teoremas**: `prop_2_6_modiSubSuoAttributo`,
`prop_2_5_ideaeSubCogitatione`, `prop_2_7_ordoEtConnexio_iff`,
`prop_2_3_ideaInDeo`, `mens_prop_6`, `mens_cause_irreflexive_deus`

Tres hallazgos, y el tercero fue una sorpresa.

**(a) Cinco axiomas nuevos, cero compromisos de Sección III.** La
capa *quatenus* introduce las primeras relaciones **relativizadas a
atributo** del proyecto (`modeUnder`, `causeUnder`,
`involvesConceptOf`) y con ellas las Props. II.V y II.VI. Los cinco
axiomas que necesita —A51–A55— son **todos de Sección II**: cada uno
es una frase que Spinoza escribe en la *demonstratio* correspondiente.
No hay ni un solo axioma con patrón 📜 en este tramo.

Es un resultado con contenido, no un detalle contable. La pregunta
que guía el proyecto es cuántos compromisos no declarados necesita
realmente la *Ética*; la respuesta aquí es **ninguno**. Las dos
cláusulas de la Prop. VI se *derivan*: la positiva desde
`prop_16_cor1_godEfficientCause` (ya mecanizada en Pars I) refinada
por A53, y la de exclusión desde la contradicción entre el segundo
conyunto de A51 y A52. La Prop. V es la Prop. VI especializada a
`a := cogitatio` vía A54 — la propia segunda *demonstratio* de
Spinoza. La maquinaria del *quatenus* es cara en **primitivos** y
gratis en **metafísica**.

**(b) Un hueco que resultó ser un `import` faltante.** GAP-26 (la
localización *in Deo* de la Prop. II.III) estaba anotado como
pendiente de un axioma más fuerte. No hacía falta: bastó re-basar
`Pars2World`/`Pars2Axioms` de `CausalWorld`/`CausalAxioms` a
`ConsecutioWorld`/`ConsecutioAxioms` para que `prop_15_allInGod`
quedara disponible, y `prop_2_3_ideaInDeo` deriva la localización de
ahí — que es la ruta del propio Spinoza ("*per propositionem 15
partis I*"). **Coste: cero axiomas nuevos.** Vale la pena registrar
el patrón: un hueco documentado como deuda metafísica era deuda de
arquitectura.

**(c) Las ideas de Spinoza tienen que ser infinitas — y el kernel lo
demuestra.** Al reconstruir el testigo apareció algo que no se leyó
del texto sino de la imposibilidad de construir el modelo: **A45
(cada idea tiene un único ideatum), A49 (todo tiene idea) y A54 (las
ideas son modos del pensamiento) son conjuntamente insatisfacibles en
cualquier portador finito.** A49 obliga a que cada cosa —incluida
cada idea— tenga su idea; A45 impide reciclarlas; A54 las saca del
único lugar donde el modelo podría cerrarse (la sustancia). El
portador tuvo que pasar de un elemento a

```lean
inductive MensThing | deus | idea : MensThing → MensThing
```

es decir, Dios más la *idea ideae in infinitum* del escolio de la
Prop. II.XXI. El regreso infinito de ideas que Spinoza afirma en ese
escolio **no es un adorno doctrinal: es lo que mantiene consistente
su propio registro**. Es la primera vez en el proyecto que una tesis
sustantiva de la *Ética* se recupera como condición de satisfacibilidad
en vez de como teorema.

Beneficio colateral: en ese portador las Props. V y VI valen de un
modo *real* (todo `idea x` es un `Mode` genuino), y su cláusula de
exclusión rechaza `extensio` sobre una relación que de hecho vale
bajo `cogitatio` — no sobre una relación vacía.
`mens_cause_irreflexive_deus` certifica además que `Cause` no es la
relación constante, así que el bicondicional del paralelismo
(`prop_2_7_ordoEtConnexio_iff`, GAP-27a cerrado por A55) tampoco es
trivialmente verdadero ahí.

---

## Resumen numérico del estado (rama `pars1-extensions`)

- **Pars I**: 29/36 proposiciones con contenido mecanizado
  (las 7 restantes: XXVII y XXX–XXXII esperan Pars II; XXXIII la capa
  modal; XXXIV–XXXV la maquinaria de *potentia*).
- **Axiomas auxiliares nuevos**: A27–A44 (18), de los cuales 5 de
  Sección III genuinos (A27, A32, A35, A40, A41, A44 — con A42
  descompuesto en A44) y el resto puentes/promociones.
- **Modelos nuevos**: 12 (4 testigos de consistencia, 3 contramodelos
  de irreducibilidad, 1 bench multiatributo, 1 testigo global, 2 de
  la capa Attributum y 1 de Pars II — `MensWitness`, reconstruido en
  el batch 1.2 sobre portador infinito).
- **Teoremas de imposibilidad**: 2 (no-derivabilidad de la existencia
  de Dios; incompatibilidad Dios ∧ pluralidad de atributos **en el
  registro de Pars I** — el hallazgo 9 muestra que la segunda depende
  del tipado, no de los axiomas).
- **Capa nueva `Ethica/Attributum/`**: 5 módulos; GAP-25 y GAP-8a
  cerrados; Def. VI recuperada; Pars II desbloqueada.
- **Pars II en marcha**: 6/49 proposiciones (I, II, III, V, VI, VII)
  más el corolario de la VI y el resultado de dos atributos que la
  conjunción I+II entrega. Axiomas A45–A55; A6 de Spinoza promovido
  tras estar como `True` desde v1.0.0. **A51–A55 son todos de
  Sección II**: el batch 1.2 no añadió ningún compromiso metafísico
  sustantivo. GAP-26 y GAP-27a cerrados; GAP-27b y GAP-28 abiertos
  con ruta.
- **Total de la obra**: 35/259 proposiciones con contenido (29 de
  Pars I + 6 de Pars II).
- `lake build` limpio, **0 `sorry`**, **0 `axiom`**, ninguna
  declaración de v1.0.0 modificada. El gate de CI ahora verifica
  mecánicamente las dos últimas condiciones.

*Documento actualizado junto con cada tramo de trabajo.*
