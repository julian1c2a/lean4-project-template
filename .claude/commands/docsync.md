---
description: Comprueba que la documentación cuadra con el código real (AI-GUIDE §27) y corrige lo que falle
---

Ejecuta el control de sincronía documentación ↔ código y **deja el repositorio en verde**.

## Qué hacer

1. Ejecuta `bash check-doc-sync.bash` (o `--quick` si no hace falta rebuild).
2. **[A] cifras, [C] proyección, [D] marcas de tiempo** — son objetivos y rompen el check.
   **Corrígelos.** ⚠️ Al corregir una cifra, **no basta con el banner**: recorre también las
   tablas resumen, las secciones de «Próximos pasos» y las notas de auditoría antiguas. Ése es
   exactamente el fallo que este control existe para atrapar.
3. **[B] símbolos muertos** — es un **aviso** que pide juicio. Por cada símbolo reportado, decide:
   * ¿el texto afirma que **ya está**? → corrígelo (apunta al símbolo vivo que lo sustituye).
   * ¿es una mención **histórica, planificada o descartada**? → añade un marcador que lo deje
     claro («retirado», «falta», «propuesto», una fecha ISO), y así deja de reportarse.
4. Vuelve a ejecutar hasta que [A]/[C]/[D] estén en verde y los avisos de [B] estén adjudicados.
5. Informa en el chat, distinguiendo **hallazgos reales** de ruido descartado.

## Contexto

Este control nace de dos fallos reales de 2026-08-22, documentados en `AI-GUIDE.md` §27:

* **Los documentos de estado se actualizan por su BANNER y no por su CUERPO.**
  `CURRENT-STATUS-PROJECT.md` tuvo banner correcto y, tres líneas más abajo, una tabla diciendo
  «113 jobs, 99 módulos» y citando un teorema borrado. Un ADR llevó **un mes** diciendo «no
  implementado» sobre algo hecho.
* **Al contar por familia de símbolos, hay que contar la familia entera.** Un recuento buscó solo
  un prefijo y perdió dos miembros de la familia; la cifra falsa circuló meses por cuatro
  documentos.

Si el proyecto es nuevo, revisa antes el bloque `CONFIGURACIÓN` de `check-doc-sync.bash`:
los documentos autoritativos y `SYMBOL_PREFIXES` son lo único específico del proyecto.

$ARGUMENTS
