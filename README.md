# Résolution de problèmes de graphes par réduction à SAT (Z3)

Projet du module **Calculabilité et complexité (COCA)** — Master 1 Informatique, Université de Bordeaux.

Ce projet résout deux problèmes de graphes en les **réduisant à SAT**, puis en appelant le solveur **Z3** pour décider de leur satisfiabilité :

- **3-coloration** : peut-on colorier les sommets d'un graphe avec 3 couleurs sans que deux sommets voisins aient la même couleur ?
- **Routage de tunnels** (*Tunnel Network*) : problème de routage sur un réseau, modélisé puis résolu par réduction.

Le principe est le même dans les deux cas : on traduit l'instance du problème en une **formule booléenne** dont la satisfiabilité équivaut à l'existence d'une solution, Z3 résout la formule, et on reconstruit la solution à partir du modèle.

## Structure du projet

```
.
├── src/
│   ├── main/               # Point d'entrée, structure de graphe, interface avec Z3
│   │   ├── main.c
│   │   ├── Graph.c         # Représentation des graphes
│   │   └── Z3Tools.c       # Fonctions utilitaires pour construire les formules Z3
│   ├── ColouringProblem/   # Problème de 3-coloration
│   │   ├── ColouredGraph.c
│   │   ├── ColouringReduction.c    # Réduction coloration → SAT
│   │   └── ColouringResolution.c   # Résolution et reconstruction de la solution
│   ├── TunnelRouting/      # Problème de routage de tunnels
│   │   ├── TunnelNetwork.c
│   │   ├── TunnelReduction.c        # Réduction routage → SAT
│   │   └── TunnelBF.c               # Résolution de référence (force brute)
│   └── parser/             # Lecture des graphes au format .dot (flex + bison)
│       ├── Lexer.l
│       └── Parser.y
├── include/                # En-têtes correspondants
├── graphs/                 # Graphes d'exemple
│   ├── Colouring/          # Instances 3-colorables et non 3-colorables
│   └── TunnelNetwork/      # Instances de réseaux de tunnels
├── examples/               # Petits exemples d'utilisation (Z3, graphes)
├── CMakeLists.txt / Makefile
└── doxygen.config          # Génération de la documentation
```

## Prérequis

- Le solveur **Z3** et ses en-têtes de développement.
- **flex** et **bison** (lecture des fichiers `.dot`).
- **CMake** ou **make**.

```bash
sudo apt install z3 libz3-dev flex bison cmake
```

## Compilation

```bash
make
```

Cela produit l'exécutable `graphProblemSolver`.

## Utilisation

> ⚠️ À compléter avec les options exactes (voir `main.c`).

Le programme prend en entrée un graphe au format `.dot` et résout le problème demandé, par exemple :

```bash
# Exemple sur une instance 3-colorable
./graphProblemSolver graphs/Colouring/3colorableSmall.dot
```

Les graphes de test fournis dans `graphs/Colouring/` sont nommés selon qu'ils sont colorables ou non (`3colorable*`, `not_3colorable*`), ce qui permet de vérifier facilement les résultats.

## Documentation

La documentation du code peut être générée avec Doxygen :

```bash
doxygen doxygen.config
```

## Auteurs

Projet de groupe (voir l'historique Git pour les contributions).
