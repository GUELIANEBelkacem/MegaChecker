# Projet d'analyseur statique du cours TAS

Le but du projet est d'implanter un analyseur statique par interprétation abstraite pour un langage "jouet" impératif très simple.
La syntaxe est inspirée de C, mais extrêmement simplifiée : le langage ne comporte que des entiers (mathématiques, non bornés), le *if-then-else* et la boucle *while*.
La langage ne comporte ni pointeur, ni fonction, ni tableau, ni allocation dynamique, ni objet.

Vos trouverez ici un squelette de base pour faciliter le développement de l'analyseur :
* un analyseur syntaxique qui transforme le texte du programme en arbre syntaxique abstrait ;
* un interprète par induction sur la syntaxe, paramétré par le choix d'un domaine d'interprétation ;
* des signatures pour les domaines d'environnements et les domaines de valeurs ;
* le domaine concret, permettant de collecter l'ensemble précis des états de programme accessibles ;
* le domaine abstrait des constantes.


L'interprète et le domaine des constantes sont encore incomplets.
Une première tâche sera donc de les compléter.


Commencez par suivre les instructions d'installation décrites dans le fichier [INSTALL.md](INSTALL.md).

Le fichier [TRAVAIL.md](TRAVAIL.md) détaille le travail demandé pour le projet.

Les sources fournies sont documentées dans le fichier [DOC.md](DOC.md).
