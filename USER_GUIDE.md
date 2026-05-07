# Guía del Usuario (User Guide)

Bienvenido a tu nueva plantilla de proyecto para **Lean 4**. Esta plantilla está diseñada no solo para proveerte una estructura base sólida, sino también un ecosistema completo de herramientas para trabajar de forma profesional, segura, y con la ayuda de asistentes de Inteligencia Artificial.

A continuación te explicamos paso a paso cómo sacar el máximo provecho de esta plantilla.

---

## 1. Primeros Pasos

### Clonar e Inicializar
1. Clona este repositorio o úsalo como plantilla (Template) en GitHub para crear el tuyo propio.
2. Abre una terminal en la carpeta raíz del proyecto.
3. Ejecuta el comando de inicialización para activar el sistema de seguridad (Git Hooks):
   ```bash
   make init
   ```
   *(Esto asegura que las herramientas de "congelación" de archivos funcionen correctamente).*

### Renombrar el Proyecto
Por defecto, la plantilla se llama `MyProject`. Para adaptarla a tu proyecto:
1. Renombra la carpeta `MyProject/` a tu nuevo nombre, por ejemplo, `SetTheory/`.
2. Renombra el archivo raíz `MyProject.lean` a `SetTheory.lean`.
3. Abre `lakefile.lean` y cambia el nombre del paquete `«MyProject»` a `«SetTheory»`.

---

## 2. Desarrollo y Flujo de Trabajo

### Crear Nuevos Módulos
Nunca crees archivos `.lean` a mano. Utiliza el comando integrado para que se generen con las cabeceras e importaciones correctas:
```bash
make new NAME=MiCarpeta/MiModulo
```
*Esto creará `MiCarpeta/MiModulo.lean` y generará automáticamente un archivo "barrel" `MiCarpeta.lean` si es necesario.*

### Mantener el Índice Actualizado
El archivo raíz (ej. `MyProject.lean`) debe importar todos los submódulos. No lo edites a mano; cuando añadas o elimines módulos, simplemente ejecuta:
```bash
make root
```

### Compilar y Comprobar Errores
Para compilar todo el proyecto y verificar que no hay errores lógicos:
```bash
make build
```

Para buscar si has dejado demostraciones sin terminar (`sorry`):
```bash
make sorry
```

---

## 3. Mantener el Proyecto Actualizado

La plantilla incluye un sistema inteligente para actualizar Lean 4 sin romper tu código.

Para actualizar siempre a la **última versión disponible**:
```bash
make update-toolchain
```
*El sistema descargará la información, mostrará los cambios, intentará compilar tu proyecto con la nueva versión y, si tiene éxito, aplicará y guardará el cambio.*

Si necesitas una **versión específica**:
```bash
make update-toolchain VERSION=v4.29.0
```

---

## 4. El Sistema de Bloqueo (Freeze / Lock)

Cuando terminas un archivo fundamental (como axiomas o definiciones base) y no quieres que tú (o la IA) lo modifique accidentalmente y rompa el resto del proyecto, debes "bloquearlo".

- **Bloquear un archivo:**
  ```bash
  make lock FILE=MyProject/Prelim.lean
  ```
- **Desbloquear un archivo (si necesitas editarlo):**
  ```bash
  make unlock FILE=MyProject/Prelim.lean
  ```
- **Ver qué archivos están bloqueados:**
  ```bash
  make list
  ```

---

## 5. El Ecosistema de Documentación

Esta plantilla exige separar el código estricto de la documentación legible. Tienes a tu disposición varios archivos fundamentales:

*   **`REFERENCE.md`**: Es la "biblia" de tu proyecto. Aquí deben estar listadas todas tus definiciones, axiomas y teoremas importantes (pero sin sus pruebas). Es lo que la IA lee para entender tu proyecto sin tener que compilarlo todo.
*   **`AI-GUIDE.md`**: Reglas estrictas para que tú y la IA programen en armonía.
*   **`NAMING-CONVENTIONS.md`**: El diccionario sobre cómo nombrar las cosas. *Ejemplo: `CamelCase` para Tipos, `snake_case` para funciones.*
*   **`NEXT-STEPS.md`** y **`PLANNING.md`**: Para apuntar lo que vas a programar a corto y largo plazo.

> **Regla de Oro:** Cada vez que demuestres un teorema importante o crees una definición nueva en un archivo `.lean`, cópiala inmediatamente en `REFERENCE.md`.

---

## 6. Comprobación Rápida de Estado

Si has estado trabajando un rato y quieres ver cómo está la salud de tu proyecto (archivos bloqueados y teoremas sin demostrar), ejecuta:
```bash
make status
```

¡Feliz demostración!