#!/bin/bash
# check-doc-sync.bash — detecta documentación DESINCRONIZADA del código real.
#
# Versión GENÉRICA de la plantilla: detecta sola la librería del proyecto desde
# `lakefile.lean` y no presupone ninguna estructura de capas. Lo que sí es específico
# de cada proyecto va en el bloque «CONFIGURACIÓN» de abajo — ajústalo al adoptar.
#
# Nace de dos fallos reales, ambos caros (ver AI-GUIDE.md §27):
#
#   1. Los documentos de estado se actualizan por su BANNER y no por su CUERPO.
#      `CURRENT-STATUS-PROJECT.md` llegó a tener un banner correcto y, tres líneas
#      más abajo, una tabla que decía «113 jobs, 99 módulos». Un ADR llevó un mes
#      diciendo «no implementado» sobre algo hecho.
#   2. Se citan como vigentes símbolos que YA NO EXISTEN en el código.
#
# [A], [C] y [D] son OBJETIVOS y rompen el check. [B] es un AVISO que pide juicio:
# hay menciones legítimas de símbolos inexistentes (históricas, planificadas, descartadas).
#
# Uso:
#   bash check-doc-sync.bash            # comprobación completa
#   bash check-doc-sync.bash --quick    # sin `lake build`
#   bash check-doc-sync.bash --fix-hint # además, sugiere el sed de cada corrección
#
# Salida: 0 si todo cuadra, 1 si hay desincronización.

set -uo pipefail
cd "$(dirname "$0")"

QUICK=0
HINT=0
for a in "$@"; do
  case "$a" in
    --quick)     QUICK=1 ;;
    --fix-hint)  HINT=1 ;;
    -h|--help)   sed -n '2,24p' "$0"; exit 0 ;;
    *) echo "opción desconocida: $a" >&2; exit 2 ;;
  esac
done

# ═══ CONFIGURACIÓN (ajustar por proyecto) ═══════════════════════════════════
#
# Documentos AUTORITATIVOS: los que describen el ESTADO ACTUAL y por tanto deben
# cuadrar con el código. Quedan fuera, y con razón, los de diario, diseño e historia
# (CHANGELOG, THOUGHTS, PLAN-*, AUDIT-*): sus cifras y símbolos son obsoletos POR
# DISEÑO, y marcarlos convertiría el control en ruido.
AUTHORITATIVE_BASE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md NEXT-STEPS.md"

# [B] Prefijos de los símbolos del proyecto que se citan en la prosa entre `backticks`.
# Ajustar a las familias de nombres reales (p. ej. 'prf_|pcc_|ax_' en un proyecto de
# aritmetización). Vacío ⇒ se salta el control [B].
SYMBOL_PREFIXES=''

# Directorios extra de declaraciones VIVAS (fuera de la librería: dependencias locales,
# cuarentenas, sondeos). Separados por espacios; los inexistentes se ignoran.
EXTRA_DECL_DIRS=''
# ═══════════════════════════════════════════════════════════════════════════

# ─── 0. DETECCIÓN DEL PROYECTO (misma lógica que gen-root.bash) ─────────────
LIB=$(grep -E 'lean_lib\s+«([^»]+)»' lakefile.lean 2>/dev/null | sed 's/.*«\(.*\)».*/\1/' | head -1)
[ -z "$LIB" ] && LIB=$(grep -E '^lean_lib\s+"([^"]+)"' lakefile.lean 2>/dev/null | sed 's/.*"\(.*\)".*/\1/' | head -1)
[ -z "$LIB" ] && LIB=$(grep -E 'package\s+«([^»]+)»' lakefile.lean 2>/dev/null | sed 's/.*«\(.*\)».*/\1/' | head -1)
[ -z "$LIB" ] && LIB=$(grep -E '^package\s+"([^"]+)"' lakefile.lean 2>/dev/null | sed 's/.*"\(.*\)".*/\1/' | head -1)
if [ -z "$LIB" ] || [ ! -d "$LIB" ]; then
  echo "❌ No se pudo detectar el directorio de la librería desde lakefile.lean." >&2
  exit 2
fi

# ─── 1. VERDAD DEL CÓDIGO ────────────────────────────────────────────────────
MODULES=$(find "$LIB" -name '*.lean' ! -name '_template.lean' 2>/dev/null | wc -l)
# ⚠️ Se excluyen las menciones entre BACKTICKS (`sorry` en prosa y docstrings) además
# de las líneas de comentario: contarlas daba 1 donde había 0 y rompía el check [A].
SORRY=$(grep -rE '(^|[^a-zA-Z_`])sorry([^a-zA-Z_`]|$)' "$LIB" --include=*.lean 2>/dev/null \
        | grep -vE '^[^:]*:\s*(--|/-|-/|\*)' | wc -l)
AXIOMS=$(grep -rhE '^axiom ' "$LIB" --include=*.lean 2>/dev/null | wc -l)

if [ "$QUICK" = "1" ]; then
  JOBS=""
else
  JOBS=$(lake build 2>&1 | grep -oE "Build completed successfully \([0-9]+ jobs\)" | grep -oE "[0-9]+" || true)
fi

echo "════ VERDAD DEL CÓDIGO ($LIB) ════"
printf "  módulos         : %s\n" "$MODULES"
printf "  sorry           : %s\n" "$SORRY"
printf "  axiom de Lean   : %s\n" "$AXIOMS"
[ -n "$JOBS" ] && printf "  build jobs      : %s\n" "$JOBS"
echo

DOCS="$AUTHORITATIVE_BASE $(ls doc/REFERENCE-*.md 2>/dev/null)"
FAIL=0

# ─── 2. [A] CIFRAS OBSOLETAS ─────────────────────────────────────────────────
echo "════ [A] CIFRAS ════"
A_FAIL=0
# ALCANCE: sólo la REGIÓN DE CABECERA (primeras 100 líneas) de cada doc autoritativo.
# Ahí viven el banner y las tablas resumen — lo que AFIRMA el estado actual. Más abajo
# están los registros de logros, donde «93 jobs» es historia correcta, no un error.
# Esta acotación es la que hace utilizable el control: sin ella, los diarios disparan
# una docena de falsos positivos y nadie vuelve a mirarlo.
HEADREGION=$(mktemp)
: > "$HEADREGION"
for d in $DOCS; do
  [ -e "$d" ] || continue
  head -100 "$d" | sed "s|^|$d:|" >> "$HEADREGION"
done

# ⚠️ Los patrones se pasan SIEMPRE entre comillas SIMPLES: un backtick dentro de
#    comillas dobles lo ejecuta bash como sustitución de comando y el patrón queda roto.
check_num () {   # $1 = regex con grupo numérico   $2 = valor correcto   $3 = etiqueta
  local pat="$1" good="$2" label="$3" hits n
  # Se descartan: menciones históricas, aproximaciones (~40), rangos (40-50) y ejemplos.
  hits=$(grep -nE "$pat" "$HEADREGION" 2>/dev/null \
         | grep -viE "hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|20[0-9]{2}-[0-9]{2}-[0-9]{2}|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+" || true)
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    n=$(echo "$line" | grep -oE "$pat" | grep -oE "[0-9]+" | head -1)
    if [ -n "$n" ] && [ "$n" != "$good" ]; then
      echo "  ✗ $label: dice $n, real $good"
      echo "      ${line:0:150}"
      A_FAIL=1
    fi
  done <<< "$hits"
  # Un patrón sin ninguna aparición no está comprobando nada: se avisa, no se calla.
  [ -z "$hits" ] && echo "  ⚠️  $label: la frase no aparece en ningún doc autoritativo — control VACÍO"
  return 0
}
# ⚠️ Estas cifras se comprueban con la FRASE EXACTA que usan los documentos de estado.
# Un patrón que no encuentra su frase en ninguna parte **da verde sin haber comprobado
# nada** — el peor resultado posible para un control cuyo cometido es que no te fibres de
# lo que dicen los docs. Por eso la plantilla fija una convención:
#
#   CURRENT-STATUS-PROJECT.md lleva en su cabecera una línea de CIFRAS CANÓNICAS
#   con esta forma literal (AI-GUIDE §27):
#
#       N jobs · N módulos propios · N sorry vigentes · N axiom propios
#
# Si cambias el fraseo, cámbialo en los dos sitios.
[ -n "$JOBS" ] && check_num '[0-9]+ jobs' "$JOBS" "jobs"
check_num '[0-9]+ módulos propios' "$MODULES" "módulos propios"
check_num '[0-9]+ `?sorry`? (vigentes|propios|restantes|reales)' "$SORRY" "sorry"
check_num '[0-9]+ `?axiom`? propios' "$AXIOMS" "axiom propios"
rm -f "$HEADREGION"
[ "$A_FAIL" = "0" ] && echo "  ✓ sin cifras obsoletas" || FAIL=1

# ─── 3. [B] SÍMBOLOS MUERTOS ─────────────────────────────────────────────────
# Un símbolo está MUERTO si se cita en un doc AUTORITATIVO pero ninguna declaración
# del árbol activo empieza por él.
#
# Dos calibraciones aprendidas al estrenar este control:
#   * Sólo se miran los docs AUTORITATIVOS. Los de diseño e historia citan por diseño
#     cosas que ya no están, y marcarlos sería ruido.
#   * Se compara por PREFIJO, no por igualdad: la prosa abrevia (`ax_C3` por
#     `ax_C3_concat_assoc`), y eso es legítimo. Un símbolo de verdad muerto no
#     prefija nada.
echo
echo "════ [B] SÍMBOLOS MUERTOS — AVISO, requiere juicio ════"
if [ -z "$SYMBOL_PREFIXES" ]; then
  echo "  — desactivado (SYMBOL_PREFIXES vacío en la CONFIGURACIÓN de este script)"
else
  echo "   (no rompe el check: hay menciones legítimas en secciones de diseño e historia.)"
  B_FAIL=0
  # Marcadores que hacen LEGÍTIMA la mención de un símbolo inexistente:
  #   (a) se declara retirado;  (b) es hipotético/propuesto/descartado;  (c) va en una
  #   entrada fechada (histórico por diseño);  (d) es un OBJETIVO declarado.
  DEAD_MARKER='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|histórico|ANTERIORES|🗑️|muert|tampoco existe|inexistente|desapareci|ya no son|se borró'
  DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot[eé]tic|har[ií]a falta|si se |habr[ií]a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9]{2}-[0-9]{2}-[0-9]{2}'
  DEAD_MARKER="$DEAD_MARKER"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta'
  DECLS=$(mktemp)
  # shellcheck disable=SC2086
  grep -rhoE "(theorem|lemma|def|abbrev|axiom|noncomputable def|structure|inductive) +[A-Za-z_][A-Za-z0-9_']*" \
       "$LIB" $EXTRA_DECL_DIRS --include=*.lean 2>/dev/null \
       | awk '{print $NF}' | sort -u > "$DECLS"
  # shellcheck disable=SC2086
  CANDS=$(grep -rhoE '`('"$SYMBOL_PREFIXES"')[A-Za-z0-9_'"'"']+`' $DOCS 2>/dev/null | tr -d '`' | sort -u)
  for sym in $CANDS; do
    grep -qE "^${sym}" "$DECLS" && continue
    # shellcheck disable=SC2086
    bad=$(grep -rn "\`${sym}\`" $DOCS 2>/dev/null | grep -vE "$DEAD_MARKER" || true)
    if [ -n "$bad" ]; then
      echo "  ✗ \`$sym\` no existe en el árbol activo, y se cita sin marcar como retirado:"
      echo "$bad" | head -2 | sed 's/^/      /' | cut -c1-140
      B_FAIL=1
    fi
  done
  rm -f "$DECLS"
  # [B] NO marca FAIL: es un aviso. [A], [C] y [D] sí son objetivos y sí lo marcan.
  # Razón: un control que grita lobo se acaba ignorando, y ése era justo el fallo que
  # este script existe para evitar.
  [ "$B_FAIL" = "0" ] && echo "  ✓ ningún símbolo muerto citado como vigente" \
                      || echo "  ⚠️  revisar los de arriba: ¿es una afirmación de que YA ESTÁ, o una mención histórica/planificada?"
fi

# ─── 4. [C] PROYECCIÓN: ¿está cada módulo en el catálogo? ────────────────────
echo
echo "════ [C] PROYECCIÓN (AI-GUIDE §1/§14) ════"
C_FAIL=0
while IFS= read -r f; do
  [ -e "$f" ] || continue
  m=$(basename "$f" .lean)
  if ! grep -q "$m" REFERENCE.md doc/REFERENCE-*.md 2>/dev/null; then
    echo "  ✗ $m NO aparece en el catálogo REFERENCE.md §1"
    C_FAIL=1
  fi
done < <(find "$LIB" -name '*.lean' ! -name '_template.lean' 2>/dev/null | sort)
[ "$C_FAIL" = "0" ] && echo "  ✓ todo módulo aparece en su catálogo" || FAIL=1

# ─── 5. [D] MARCAS DE TIEMPO (AI-GUIDE §22) ─────────────────────────────────
echo
echo "════ [D] MARCAS DE TIEMPO ════"
D_FAIL=0
for f in REFERENCE.md doc/REFERENCE-*.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md; do
  [ -e "$f" ] || continue
  grep -qE '\*\*(Last updated|Última actualización):\*\*' "$f" \
    || { echo "  ✗ $f sin marca de tiempo"; D_FAIL=1; }
done
[ "$D_FAIL" = "0" ] && echo "  ✓ todos los docs técnicos llevan marca de tiempo" || FAIL=1

# ─── RESUMEN ────────────────────────────────────────────────────────────────
echo
if [ "$FAIL" = "0" ]; then
  echo "✅ DOCUMENTACIÓN SINCRONIZADA."
else
  echo "❌ HAY DESINCRONIZACIÓN — corregir ANTES de commitear."
  if [ "$HINT" = "1" ]; then
    echo
    echo "Sugerencias de sed (revisar antes de aplicar):"
    [ -n "$JOBS" ] && echo "  sed -i -E 's/[0-9]+ jobs/$JOBS jobs/g' *.md doc/*.md"
    echo "  sed -i -E 's/[0-9]+ módulos propios/$MODULES módulos propios/g' *.md doc/*.md"
  fi
  echo
  echo "⚠️  Recordatorio: NO basta con arreglar el banner. Comprobar también el CUERPO"
  echo "    (tablas resumen, §Próximos pasos, notas de auditoría antiguas)."
fi
exit "$FAIL"
