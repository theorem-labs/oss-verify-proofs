From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
Open Scope Z_scope.

Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land15_mod16 : forall x, Z.land x 15 = x mod 16.
Proof. intros. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac uck_norm K := rewrite ?land1_mod2, ?land3_mod4, ?land7_mod8, ?land15_mod16 in K.

Ltac uck :=
  let K := fresh "UK" in
  first [ if_cases K; zify_cond K; uck_norm K; [exfalso; lia | clear K]
        | if_cases K; zify_cond K; uck_norm K; [clear K | exfalso; lia] ].

Ltac zb_fix :=
  repeat match goal with
  | |- context [?a <? ?b] => first [ replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)
                                    | replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) ]
  | |- context [?a =? ?b] => first [ replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)
                                    | replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) ]
  end;
  repeat match goal with
  | |- context [Z.b2z true] => change (Z.b2z true) with 1
  | |- context [Z.b2z false] => change (Z.b2z false) with 0
  end;
  repeat match goal with
  | |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
  end.
