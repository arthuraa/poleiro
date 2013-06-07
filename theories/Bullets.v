(** Ltac scripts are notoriously hard to maintain. One problem that
arises often is ensuring that

** Bullets to the rescue

Since version 8.4, Coq comes with a nice feature for better
structuring proof scripts. One can now mark subgoals of a proof with
bullets ([-], [+] and [*]) and curly braces ([{}]), which greatly
improves readability. A similar feature was already present in the #<a
href="http://www.msr-inria.com/projects/mathematical-components/">SSReflect</a>#
Coq plugin for some time, but the new Coq version brings a significant
improvement: it checks that bullets are used consistently, which
limits the scope of tactics and makes errors more local and
tracktable.


First of all, it checks that bullets are used consistently. If you
start a subgoal with a bullet, Coq will require you to use the same
bullet in all corresponding subgoals. Also, trying to proceed to a new
bullet will fail if that bullet is still _open_, i.e. if it has been
used to introduce a subgoal that hasn't been solved yet. This ensures
that tactics will only run in the goal they were intended for, making
errors more local and tracktable. Another advantage is that opening a
bullet focuses the proof on the current subgoal *)
