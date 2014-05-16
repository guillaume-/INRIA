INRIA
=====
README de https://github.com/guillaume-/INRIA

---------------
-----Présentation
---------------

3 branches disponnibles :
	cvrt-param-separation-ter_ité
	convention-paramétrée
	master

Master est la première branche à avoir été faite
Cette branche n'utilise pas d'itérateur.

Convention-paramétrée est la deuxième branche :
Les itérateurs sont tous utilisés à partir d'un fichier ter_iterateurs.ml

Enfin, cvrt-param-separation-ter_ité est la branche sur laquelle nous travaillons actuellement.
Un fichier par itérateur :

---------------
-----Comment utiliser
---------------
Il est possible de télécharger une branche via "Download zip"
Une fois téléchargé et extrait, on compile via make
et on exécute via ./main < fichier_signal

---------------
-----Nouveaux fichiers
---------------

ter_arith_to_call.ml
	définit la fonction qui, à partir d'une specification, 
	retourne une specification où toute fonction + devient un call add


ter_chk_spec.ml
	définit la fonction qui vérifie une spécification


ter_exception.ml
	définit l'ensemble des exceptions utilisées dans le reste du programme

ter_identite.ml
	définit le cas neutre des fonctions de l'itérateur d'une spécification

ter_iterateurs.ml
	définit l'itérateur d'une spécification

ter_no_submod.ml
	définit la fonction qui applatit le code signal

ter_schemas_latex.ml
	--annulée--
	devait définir la fonction ocaml utilisant les itérateurs,
	qui retourne du code en tikZ permettant d'afficher
	sous forme de boîte un code signal

ter_toString.ml
	définit la fonction qui affiche le code signal correspondant à une spécification

ter_transfos.ml
	définit les fonctions d'itération

ter_util.ml
	définit des fonctions utilitaires
--
