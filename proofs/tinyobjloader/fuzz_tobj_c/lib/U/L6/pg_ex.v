From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ECfgCuts.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6 Require Import S_pg S_pgB pg_cuts pg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import PGC.

Definition lcuts_pgU : list lnode :=
  [mkLN (Pre_pg_U []) 20 []; mkLN Kfin 19 [(Vup false, V 120)]; mkLN Kcm 18 [(Vup false, V 120)];
   mkLN Knw 17 [(Vdown false, V 123)]; mkLN Kext 16 [(Vdown false, V 123)];
   mkLN Kbbp 15 [(Vdown false, V 123)]; mkLN Kproj 15 [(Vdown false, V 123)]].
Definition lexits_pgU : list lnode := [mkLN P_inv_U 0 []; mkLN P_ok_U 0 []; mkLN B_U 14 []].
Definition lnodes_pgU : list lnode := lcuts_pgU ++ lexits_pgU.

Lemma elc_0 : elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU 0 (mkLN (Pre_pg_U []) 20 []) = true.
Proof. apply CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_1 : elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU 1 (mkLN Kfin 19 [(Vup false, V 120)]) = true.
Proof. apply CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_2 : elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU 2 (mkLN Kcm 18 [(Vup false, V 120)]) = true.
Proof. apply CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_3 : elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU 3 (mkLN Knw 17 [(Vdown false, V 123)]) = true.
Proof. apply CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_4 : elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU 4 (mkLN Kext 16 [(Vdown false, V 123)]) = true.
Proof. apply CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_5 : elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU 5 (mkLN Kbbp 15 [(Vdown false, V 123)]) = true.
Proof. apply CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_6 : elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU 6 (mkLN Kproj 15 [(Vdown false, V 123)]) = true.
Proof. apply CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma elc_all : forall i n, nth_error lcuts_pgU i = Some n -> elcut segsU FUEL_pg cutpcs_pg NF lnodes_pgU i n = true.
Proof.
  intros i n Hn.
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_0|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_1|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_2|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_3|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_4|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_5|].
  destruct i as [|i]; [cbn in Hn; injection Hn as <-; exact elc_6|].
  destruct i; cbn in Hn; discriminate.
Qed.

Section PGX.
Hypothesis PGBX : pgB_sum_ex_stmt_U.

Theorem tess_polygon_sum_ex_U : tess_polygon_sum_ex_stmt_U.
Proof.
  intros K rho. change (Pre_pg_U []) with (ln_state (mkLN (Pre_pg_U []) 20 [])).
  apply (cfg_complete_auto2_cuts segsU FUEL_pg cutpcs_pg NF lcuts_pgU lexits_pgU
           (fun r => agree_below NF rho r) K (LQ segsU K NF rho Posts_pg_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact elc_all.
  - intros E rho' HinE HG. destruct HinE as [<-|[<-|[<-|[]]]]; cbn [ln_state].
    + apply eexit_post_L; [left; reflexivity | exact HG].
    + apply eexit_post_L; [right; left; reflexivity | exact HG].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
      exact (PGBX K rho rho' HG).
  - cbn. tauto.
  - apply agree_below_refl.
Qed.
End PGX.
