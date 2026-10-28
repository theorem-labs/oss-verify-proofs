From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
Open Scope Z_scope.

Lemma fk_land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma fk_land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma fk_land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma fk_land15_mod16 : forall x, Z.land x 15 = x mod 16.
Proof. intros. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac fck_norm K := rewrite ?fk_land1_mod2, ?fk_land3_mod4, ?fk_land7_mod8, ?fk_land15_mod16 in K.

Ltac fck :=
  let K := fresh "UK" in
  first [ if_cases K; zify_cond K; fck_norm K; [exfalso; lia | clear K]
        | if_cases K; zify_cond K; fck_norm K; [clear K | exfalso; lia] ].
