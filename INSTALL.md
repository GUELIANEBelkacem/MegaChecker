# Projet TAS - Installation

Le projet est hébergé sur un [GitLab privé](https://stl.algo-prog.info) du Master STL.
C'est sur ce GitLab que vous trouverez les sources du squelette d'analyseur, que vous créerez le projet git contenant votre analyseur et que ferez votre rendu.

## GitLab STL


### Accès au GitLab STL

Un compte sur le [GitLab privé STL](https://stl.algo-prog.info) a été créé pour vous par l'enseignant.
Vous devriez avoir reçu un *email* vous indiquant vos informations de *login*.
Nous utilisons initialement :
* comme *username* : votre numéro d'étudiant ;
* comme *email* : votre adresse `prenom.nom@etu.upmc.fr` (peut être changé par la suite) ;
* comme nom : la partie `prenom.nom` de votre *email* (peut être changé par la suite).

Pour commencer:
* Connectez-vous sur le [GitLab privé STL](https://stl.algo-prog.info) en utilisant les informations de connexion reçues par *email*. Si vous n'avez pas reçu d'email, prévenez les enseignants.
* Lors de la première connexion, vous devez choisir un mot de passe.
* Une fois connectés, vous pouvez modifier votre nom et *email* dans le menu en haut tout à droit, avec l'option *settings*.

Vous êtes automatiquement membre du groupe `TAS-XXXX`, où XXXX indique le semestre en cours (par exemple 2021oct ou 2021oct-INSTA).
Ce groupe continent le projet `projet-TAS` en lecture seule contenant un squelette d'analyseur.


### Création d'une copie personnelle du projet sur GitLab (`fork`)

Chaque élève doit faire un fork de ce projet-squelette pour créer un projet personnel.

* Dans l'onglet *Projects* > *Your projects*, sélectionnez le projet `TAS-XXXX/projet-TAS` (normalement, un seul projet est visible pour vous). `TAS-XXXX` représente le groupe et `projet-TAS` est le nom du projet. Ce projet est visible et commun pour tous les membres du groupe, c'est à dire toute la classe. Il est en lecure seule.
* Faites une copie privée en cliquant sur le bouton *Fork*, et cliquez sur votre nom. Ceci crée un projet personnel ayant pour nom `prenom.nom/projet-TAS`. Vous travaillerez désormais dans ce projet, et pas dans le groupe `TAS-XXXX`.
* Dans l'onglet *Projects* > *Your projects*, sélectionnez maintenant votre projet personnel.
* Cliquez sur `Settings` dans le menu de gauche, puis dans l'option `Members`, invitez votre chargé de TME, avec pour rôle `Master`.

**Attention** : votre projet sous GitLab STL doit rester _privé_ ; seuls vous et les enseignants doivent pouvoir y accéder, pas les autres élèves.



### Création d'une copie sur votre ordinateur (`clone`)

Pour développer sur le projet, vous travaillerez comme d'habitude avec git sur une copie locale, et en propageant vos modifications périodiquement dans le dépôt sur le serveur GitLab STL.
git vous permet de vous synchroniser entre différents ordinateurs, de garder un historique du développement, et de partager votre code avec les enseignants.

C'est une bonne idée de déposer une clé SSH sur le serveur GitLab pour accéder plus facilement au dépôt.

Commencez par créer une copie locale (`clone`) du projet personnel sur votre ordinateur avec `git clone URL-du-projet`.
L'URL est donnée par le bouton `Clone` sur la page GitLab du projet.

Attention à bien faire `clone` du projet personnel et pas du projet du groupe `TAS-XXXX`, vous ne pourrez pas propager vos modifications (`git push`) sur ce dernier !


## Installation des dépendances

Les dépendances suivantes doivent être installées sur votre ordinateur pour pouvoir compiler le projet :
* le langage [OCaml :camel:](https://ocaml.org/index.fr.html) (testé avec la version 4.13.1) ;
* [Dune](https://dune.build/) : un système de _build_ pour OCaml ;
* [Menhir](http://gallium.inria.fr/~fpottier/menhir) : un générateur d'analyseurs syntaxiques pour OCaml ;
* [GMP](https://gmplib.org) : une bibliothèque C d'entiers multiprécision (nécessaire pour Zarith et Apron) ;
* [MPFR](http://www.mpfr.org) : une bibliothèque C de flottants multiprécision (nécessaire pour Apron) ;
* [Zarith](http://github.com/ocaml/Zarith/) : une bibliothèque OCaml d'entiers multiprécision ;
* [CamlIDL](http://github.com/xavierleroy/camlidl/) : une bibliothèque OCaml d'interfaçage avec le C ;
* [Apron](https://antoinemine.github.io/Apron/doc/) : une bibliothèque C/OCaml de domaines numériques.


### Installation sous Linux

Sous Ubuntu, Debian et distributions dérivées, l'installation des dépendances peut se faire avec `apt-get` et [opam](https://opam.ocaml.org/) :
```
sudo apt-get update
sudo apt-get install -y build-essential opam libgmp-dev libmpfr-dev git
opam init -y
eval $(opam env)
opam install -y dune menhir zarith mlgmpidl apron
```
Si une des commandes `opam` échoue, essayez de supprimer le répertoire `.opam` et de recommencer en utilisant `opam init -y --disable-sandboxing` au lieu de `opam init -y`.

Les dépendances `apron` et `mlgmpidl` ne sont nécessaires que pour certaines extensions, et vous pouvez les ignorer pour l'instant si elles posent problème.


### Installation sous Windows 10

Le projet peut également être développé sous Windows en utilisant Windows Subsystem for Linux 2, à condition de posséder une version de Windows 10 récente.

Les étapes à suivre sont :
- Activer Windows Subsystem for Linux 2 : <https://docs.microsoft.com/fr-fr/windows/wsl/install-win10>
- Installer depuis Microsoft Store la dernière version d'Ubuntu (20.04 TLS au moment où ce document est écrit).

Vous pouvez ensuite lancer un shell Ubuntu et entrer les commandes indiquées à la section précédente.


### Autres systèmes

Une solution alternative mais plus lourde que WSL est d'installer un système Linux dans une machine virtuelle, e.g., [VirtualBox](https://www.virtualbox.org/).

Il est également possible que le projet fonctionne nativement sous MacOS X.



## Compilation et premiers tests

Après installation des dépendances, tapes la commande suivante sur votre copie locale pour compiler le projet :
```
dune build
``` 

L'exécutable peut ensuite être lancé avec :
```
dune exec -- src/main.exe
```

En cas de succès de la compilation, vous pouvez tester le binaire :
1. `dune exec -- src/main.exe tests/01_concrete/0111_rand.c` doit afficher sur la console le texte du programme `tests/01_concrete/0111_rand.c` (en réalité, le programme a été transformé en AST par le *parseur* et reconverti en texte)
2. `dune exec -- src/main.exe  tests/01_concrete/0111_rand.c -concrete` doit afficher sur la console le résultat de toutes les exécutions possibles du programme de test, ici, le fait que `x` vaut une valeur entre 1 et 5


## La suite

Le fichier [DOC.md](DOC.md) documente les aspects importants du projet.

Le fichier [TRAVAIL.md](TRAVAIL.md) détaille le travail demandé.
