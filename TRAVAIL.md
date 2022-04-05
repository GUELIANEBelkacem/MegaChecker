# Projet TAS - Travail demandé


## Développement du projet


Pour développer sur le projet, vous travaillerez comme d'habitude avec git sur une copie locale, et en propageant vos modifications périodiquement dans le dépôt sur le serveur GitLab STL.

Commencez par suivre les instructions d'installation dans [INSTALL.md](INSTALL.md).

Nous rappelons les commandes `git` les plus importantes :

* `git clone URL` pour la création de la copie locale, où URL peut être trouvée sur la page du projet ;
* `git add fichier` pour indiquer les fichiers ajoutés ou modifiés localement ;
* `git commit` pour enregistrer localement les ajouts ou modifications des fichiers spécifiés par `git add` ;
* `git push` pour propager l'enregistrement local vers le serveur ;
* `git pull` pour rapatrier localement les modifications depuis le serveur.


### Intégration continue

Le serveur GitLab STL utilise un mécanisme d'intégration continue.
Ainsi, après chaque `git push` :
* le contenu de votre projet est compilé sur le serveur GitLab STL ;
* des tests d'analyse sont lancés ;
* un rapport d'analyse au format HTML est généré.

Le projet est compilé et testé par le serveur GitLab STL dans une image Docker (voir [scripts-ci/Dockefile](scripts-ci/Dockerfile)) par le script [scripts-ci/run.sh](scripts-ci/run.sh).

Vous pouvez accéder au résultat du test d'intégration dans l'onglet `CI/CD` de votre projet.
La ligne la plus en haut correspond au dernier test effectué.
Deux étapes (_Stages_) sont effectuées : une première compile simplement le projet, tandis que l'autre l'exécute sur les tests du répertoire [tests/](tests/) et génère un rapport.
Le rapport de test est disponible _via_ l'icône *Artifacts* dans la colonne de droite, sous forme d'archive ZIP contenant un seul fichier `resultat.html` que vous pouvez ouvrir dans un navigateur.
Par ailleurs, cliquer sur les icônes de la colonne *Stages* permet d'accéder à la trace en console de la machine virtuelle, ce qui facilite le débogage.

Notez que vous pouvez également lancer le script de test directement en local.
Pour cela, placez-vous à la racine du projet  ; tapez :
```
dune build
./scripts-ci/run.sh
```
et consultez le fichier `resultat.html` généré (une trace est également affichée dans la console).

Les tests sont regroupés dans des sous-répertoires de [tests/](tests/).
Chaque fichier de source `test.c` est accompagné d'un fichier `test.expected` qui contient la sortie attendue de l'analyseur.
Si le fichier `test.expected` est absent, ou si le résultat de l'analyse ne correspond pas, une erreur est indiquée dans `resultat.html`.
Un *timeout* interrompt une analyse au bout de deux secondes.
Attention : le script emploie, pour comparer le résultat de l'analyse au résultat attendu, une comparaison de chaîne simple, donc sensible aux espaces, majuscules, ponctuations, caractères de fin de ligne, etc.

La fonction `run_test` de [scripts-ci/run.sh](scripts-ci/run.sh) contient un appel à `run_test_dir` pour chacun des sous-répertoires de tests.
L'appel précise, en deuxième argument, les options à passer à l'analyseur en ligne de commande, par exemple :
```
   run_test_dir "tests/01_concrete"         "-concrete"
   run_test_dir "tests/02_concrete_loop"    "-concrete"
  #run_test_dir "tests/03_concrete_assert"  "-concrete"
  #run_test_dir "tests/04_constant"         "-constant"
  ...
```

Notez que :

* Seules les deux premières lignes `run_test_dir` sont initialement actives, les autres étant commentées avec #. En effet, elles testent des fonctionalités encore absentes de l'analyseur. Vous décommenterez les lignes suivantes au fur et à mesure que vous implanterez ces fonctionnalités, afin de les tester - ceci sera précisé dans l'énoncé.

* Vous serez amené par la suite à écrire vos propres banques de tests.
Pour cela, vous créerez un nouveau sous-répertoire de `tests` que vous peuplerez de fichiers `.c`, avec les fichiers `.expected` correspondants (vous pourrez utiliser l'analyseur en ligne de commande pour générer les fichiers `.expected`) ; puis vous ajouterez la ligne `run_test_dir` correspondante dans le script [scripts-ci/run.sh](scripts-ci/run.sh) pour automatiser le test à chaque enregistrement dans le dépôt.

Votre but est que, à chaque étape de développement, tous les tests appropriés passent sans erreur.



## Rendu

Le rendu du projet sera l'ensemble des fichiers contenus dans votre projet dans le GitLab STL.
Il sera ramassé par les enseignants sur le GitLab STL à la date limite de rendu.

Assurez-vous que vous avez bien propagé vos dernières modifications sur le serveur, et que l'intégration continue du serveur indique que votre projet compile bien et passe avec succès le maximum de tests.

Vous devez également fournir dans [RAPPORT.md](RAPPORT.md) un court rapport de projet (en format texte brut ou Markdown) précisant :
* les fonctionnalités que vous avez implantées ;
* les tests que vous avez ajoutés ;
* les difficutés éventuelles rencontrées ; en particulier, si certains tests échouent, ou si certaines fonctionnalités demandéees ne fonctionnent pas, vous en expliquerez les raisons ;
* pour l'extension au choix, vous prendrez un soin tout particulier à détailler les extensions de syntaxe et de sémantique, les options ajoutées en ligne de commande et les tests ajoutés.



## 1. Prise en main


### 1.1 Analyse concrète

Le squelette du projet contient un interprète concret.
Après la compilation par `dune build`, il peut être lancé sur un programme `tests/01_concrete/0101_decl.c` par la commande :
```
dune exec -- src/main.exe -concrete tests/01_concrete/0101_decl.c
```

Vous pouvez également utiliser l'option `-trace` pour observer le déroulement des calculs (affichage de l'environnement après chaque instruction).

Note : nous n'analysons pas des programmes C réels mais, la syntaxe étant suffisamment proche, nous utilisons l'extension .c pour nos programmes pour bénéficier de la coloration syntaxique des éditeurs.

Pour vous familiariser avec la langage analysé, sa sémantique et le fonctionnement de l'analyseur, un premier travail consiste à lancer l'analyse concrète sur des exemples du répertoire [tests/01_concrete/](tests/01_concrete/) fourni et vos propres exemples.
Pour cela, vous pouvez lancer la commande `./scripts-ci/run.sh` et observer le fichier `result.html` fourni.

Vous pourrez valider votre compréhension de la sémantique en répondant aux questions suivantes :
1. Quelles est la sémantique de l'instruction `rand(l,h)` dans un programme ? quel est le résultat attendu de l'interprète ?
2. Sous quelles conditions l'exécution d'un programme s'arrête-t-elle ? quel est alors le résultat de l'interprète ?
3. Si le programme comporte une boucle infinie, est-il possible que l'interprète termine tout de même ? dans quels cas ?
Vous validerez votre réponse en observant l'analyse des exemples dans [tests/02_concrete_loop/](tests/02_concrete_loop/).



### 1.2 Ajout du support des assertions

Dans le squelette d'analyseur proposé, l'instruction `assert` n'est pas implantée ; elle se comporte comme une instruction `skip`.
Dans cette question, vous modifierez `interpreter.ml` pour corriger son interprétation, c'est à dire :
1. afficher un message d'erreur `assertion failure` si l'assertion n'est pas prouvée correcte ;
2. et continuer l'analyse en la supposant correcte (ceci afin de ne pas indiquer à l'utilisateur plusieurs erreurs ayant la même cause).

Décommentez dans [scripts-ci/run.sh](scripts-ci/run.sh) la ligne activant les tests [tests/03_concrete_assert/](tests/03_concrete_assert/) pour tester votre implantation.

Pour l'affichage du message, vous pourrez utiliser la fonction `error` de `interpreter.ml` dans la fonction `eval_stat` de la façon suivante :
```
error ext "assertion failure"
```
ce qui facilitera les tests de régression en produisant un message au même format que dans les fichiers `.expected`.


### 1.3 Complétion du domaine des constantes

L'analyse des constantes est accessible avec l'option `-constant`.
Cependant, le domaine n'est pas complet.
Le but de l'exercice est de le compléter.

Décommentez dans [scripts-ci/run.sh](scripts-ci/run.sh) la ligne [tests/04_constant/](tests/04_constant/) pour tester l'implantation fournie.
En cas d'échec d'un test, déterminez dans `constant_domain.ml` la source de l'imprécision et corrigez-là, jusqu'à ce que votre implantation passe tous les tests.


## 2 Travail demandé : partie commune


### 2.1 Domaine des intervalles

Dans cet exercice vous implanterez le domaine des intervalles vu en cours.
Comme le domaine des constantes, il obéit à la signature `Value_domain.VALUE_DOMAIN` et sert de paramètre au foncteur `Non_relational_domain.NonRelational`.
Faites attention à ce que l'on gère des ensembles d'entiers mathématiques arbitraires.
Les bornes des intervalles ne sont donc pas forcément des entiers, mais peuvent être aussi +∞ ou −∞.

La signature `Value_domain.VALUE_DOMAIN` comporte de nombreuses fonctions.
Vous implanterez de la manière la plus précise possible au moins les fonctions suivantes : `top`, `bottom`, `const`, `rand`, `meet`, `join`, `subset`, `is_bottom`, `print`, `unary`, `binary`, `compare`.
Pour les fonctions `bwd_unary` et `bwd_binary`, une implantation approchée suffira.
Néanmoins, il est indispensable que toutes les fonctions renvoient un résultat sûr, même s'il est imprécis.

Le domaine des intervalles sera activé par l'option `-interval` passée en ligne de commande.

Décommentez dans [scripts-ci/run.sh](scripts-ci/run.sh) la ligne [tests/10_interval/](tests/10_interval/) pour tester votre implantation.

Si vous choisissez d'implanter plus précisément `bwd_unary` et `bwd_binary`, vous pourrez tester ces fonctions en décommentant également la ligne [tests/11_interval_cmp/](tests/11_interval_cmp/).

Les fichiers `.expected` considèrent qu'une information d'intervalle est affichée soit comme `⊥` (vide), soit comme `[a;b]`, où a est la borne inférieure (entier ou `-∞`) et b est la borne supérieure (entier ou `+∞`).
Il est important de respecter ces conventions dans la fonction `print` de votre domaine pour faciliter les tests de régression.


### 2.2 Analyse des boucles

Le traitement des boucles dans `interpreter.ml` suppose que le domaine abstrait n'a pas de chaîne infinie strictement croissante.
Que se passe-t-il lors d'une analyse d'intervalles ?

Le but de la question est de corriger ce problème en ajoutant l'utilisation des élargissements.
Nous procéderons par étapes :
1. Assurez-vous que l'opération d'élargissement `widen` est bien implantée dans le domaine des intervalles.
2. Modifiez `interpreter.ml` pour que l'opération d'élargissement soit utilisée à tous les tours de boucle.
Décommentez dans [scripts-ci/run.sh](scripts-ci/run.sh) la ligne [tests/12_interval_loop/](tests/12_interval_loop/) pour tester votre implantation avec l'option `-interval`.
3. Ajoutez une option `-delay n`, permettant de remplacer les n premières applications de l'élargissement par une union (élargissement retardé).
Décommentez dans [scripts-ci/run.sh](scripts-ci/run.sh) la ligne [tests/13_interval_loop_delay/](tests/13_interval_loop_delay/) pour tester votre implantation avec les options `-interval -delay 3`.
4. Ajoutez une option `-unroll n`, permettant de dérouler les n premiers tours de boucle avant le calcul avec élargissement.
Décommentez dans [scripts-ci/run.sh](scripts-ci/run.sh) la ligne [tests/14_interval_loop_delay_unroll/](tests/14_interval_loop_delay_unroll/) pour tester votre implantation avec les options `-interval -unroll 3 -delay 3`.
Quelle différence avec `-delay n` ?


### 2.3 Produit réduit

Implantez le domaine de parité mentionné en cours, puis le produit réduit des intervalles avec la parité.
Essayez, autant que possible, de définir un foncteur générique "produit réduit" prenant en argument deux domaines abstraits de valeurs arbitraires.

Le domaine des intervalle sera activé par l'option `-parity-interval` passée en ligne de commande.

Décommentez dans [scripts-ci/run.sh](scripts-ci/run.sh) la ligne [tests/20_reduced](tests/20_reduced/) pour tester votre implantation avec l'option `-parity-interval`.
Le fichier `.expected` s'attend à ce qu'un invariant du produit réduit soit affiché sous la forme `parité ∧ intervalle`, où la parité est soit `even` (pair), soit `odd` (impair), et l'intervalle est affiché comme aux questions précédentes.


## 3. Travail demandé : extension au choix

Cette section propose plusieurs améliorations que vous pourrez apporter à votre analyseur.
Il est demandé dans le projet de choisir et d'implanter une de ces extensions, en plus de l'intégralité de la partie précédente.

De plus, vous fournirez des exemples de test qui utilisent votre extension dans un répertoire [tests/30_extension/](tests/30_extension/).


### Analyse relationnelle avec Apron

Ajoutez le support pour les domaines numériques relationnels.

Vous pourrez vous appuyer sur la bibliothèque  [Apron](https://antoinemine.github.io/Apron/doc/), qui propose des implantations toutes faites des octogones et des polyèdres, et possède une interface OCaml.
Proposez des exemples illustrant l'amélioration de la précision.


### Analyse disjonctive

L'analyse des intervalles est imprécise car elle ne représente que des ensembles convexes de valeurs.
Nous verrons en cours plusieurs constructions permettant de corriger ce problème en raisonnant sur des disjonctions d'intervalles : complétion disjonctive, partitionnement d'états, partitionnement de traces.
Implantez une de ces techniques dans votre analyseur, et proposez des exemples illustrant l'amélioration de la précision qu'elle apporte.


### Analyse des entiers machine modulaires

Le type `int` du language correspond à des entiers mathématiques parfaits.
Modifiez cette interprétation dans `concrete_domain.ml` pour correspondre à des entiers 32-bit signés (conseil : on peut voir une opération sur 32 bits comme une opération sur les entiers mathématiques, suivie d'une opération de correction qui ramène le résultat dans [−2^31 , 2^31−1] ; il suffit donc d'ajouter cette étape après chaque calcul).
Illustrez votre analyse avec des exemples de programmes où le comportement diffère.

Modifiez ensuite tous les domaines implantés (constantes, intervalles, parité) pour que la sémantique corresponde à un calcul dans des entiers signés 32-bit, et non dans les entiers mathématiques.
Montrez sur des exemples la différence entre ces deux sémantiques, et en particulier l'impact en terme de précision de l'analyse.


### Analyse de pointeurs

Ajoutez le support dans votre langage et dans votre analyse pour les pointeurs.

Une variable pointeur sera déclarée par avec `ptr p`.
Si `x` est une variable entière, alors une référence sur `x` peut être stockée dans `p` par l'instruction `p = &x`.
La variable référencée par `p` peut être lue par `*p`, utilisable au sein de toute expression (on peut par exemple écrire `x = *p + 1`).
La variable référencée par `p` peut être modifiée par `*p = expression`.
Enfin, si `q` est également une référence, il est possible de la copier dans `p` par `p = q` (ainsi, `*p` et `*q` dénotent la même variable).

Lire ou modifier la valeur référencée par un pointeur non initialisé (entre `ptr p` et la première affectation `p = ...`) provoque une erreur.
Par ailleurs, si `p` référence une variable `x` déclarée dans un bloc, alors référencer ce pointeur après la sortie du bloc provoquera également une erreur.
L'analyseur devra détecter ces erreurs et les afficher.

Le support pour les pointeurs peut être ajouté à l'analyseur par un domaine de pointeurs (vu en cours) qui associe à chaque variable pointeur un ensemble de variables possibles référencées.
Vous implanterez cette techniques et proposerez des exemples pour l'illustrer.


### Analyse de tableaux

Ajoutez le support dans votre langage et dans votre analyse pour les tableaux.

Chaque tableau sera déclaré avec une taille fixe, par exemple : `int tab[10]`.
Lors d'un accès dans un tableau `tab[expr]`, nous nous intéressons à :
1. vérifier que l'expression `expr` représente bien un indice valide du tableau, c'est à dire s'évalue en une valeur entre zéro et sa taille moins 1 (sinon, une erreur est affichée, à la manière d'un échec d'assertion) ;
2. inférer des informations sur les valeurs contenues dans le tableau (par exemple, un intervalle de valeurs).

Pour le deuxième point, deux représentations abstraites d'un tableau sont possibles :
* traiter chaque case `tab[0]`, ..., `tab[9]` comme une variable indépendante, et lui associer un intervalle ;
* ou utiliser une seule variable `tab[*]` et un unique intervalle par tableau qui représente l'ensemble de toutes les valeurs possibles de toutes les cases du tableau.

Vous implanterez ces deux techniques et proposerez des exemples pour illustrer la différence de précision et de coût entre les deux.


### Extension libre

Vous pouvez également proposer et implanter une extension non décrite ici, à condition que votre choix soit d'abord validé par le chargé de TME.

