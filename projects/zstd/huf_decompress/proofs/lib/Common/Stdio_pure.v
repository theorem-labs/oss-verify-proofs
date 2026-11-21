(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (24 recorded proofs replaced by written proofs (sx32_small, b2z_range, unsigned_lit8 and 21 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel SFW1_lemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Stdio_pure () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega:ZMicromega;ZArithProof04K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Common;SFW1_lemmas:swrap32_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib6MStateAunsigned_lit_wrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib3Mem4sx32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3b2zK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes4bool02C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init5Logic4True01C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffC47Corelib4Init9Datatypes3appC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib7Classes9Morphisms:respectfulc59OSSVerify5KrLib6Common:Stdio_pure9wr_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_sysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib6Common:Stdio_pure=implM_sys_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:Stdio_pure>impl_post_evt'C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_updC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib3MemAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:Stdio_pure8C4_low32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:Stdio_pure?rw_cells_recastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqb".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac show_goal := match goal with |- ?g => idtac g end.
Ltac show_hyp H := let T := type of H in idtac H ":" T.

(* [comment removed for export] *)
Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB0 : forall segs m A cs, rw_cells segs m A cs -> rw_cells segs m A (CB 0 [] :: cs).
Proof. intros segs m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall segs m A cs, rw_cells segs m A (CB 0 [] :: cs) -> rw_cells segs m A cs.
Proof. intros segs m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.
(* [comment removed for export] *)
Lemma rw_cells_CB0_nil : forall segs m B, 0 <= B -> B <= 2^64 -> rw_cells segs m B [CB 0 []].
Proof.
  intros segs m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
  (9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64)%Z with 18446744073709551616%Z in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

(* [comment removed for export] *)
Ltac src_now SRC SEPS MU LSB :=
  unfold boxed in SRC;
  lazymatch goal with
  | |- bytes_at _ ?m' ?S (to_bytes ?s) =>
      destruct SEPS as [-> | [SEP1 SEP2]];
      [ apply bytes_at_nil; lia
      | apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
  end.

Section WithSegs.
  Variable segs : list Segment.
  Context {St : Type}.

  (* [comment removed for export] *)
  Lemma implM_sys_ret : forall {A} (n : node) (dec : resp -> option A) (s0 : St)
      (Q : unit -> St -> machine_state -> Prop) ms,
    evt segs (fun ms1 : machine_state => at_node segs n ms1 /\
                 (forall (rsp : resp) (a : A), dec rsp = Some a -> evt segs (Q tt s0) (nret ms1 rsp))) ms ->
    implM segs (Monad.mbind (msys n dec) (fun _ => Monad.mret tt)) s0 Q ms.
  Proof.
    intros A n dec s0 Q ms H.
    eapply implM_bind with (Q1 := fun _ s' ms' => s' = s0 /\ evt segs (Q tt s0) ms').
    - apply implM_sys. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp a E. apply evt_done. split; [reflexivity|]. exact (Hk rsp a E).
    - intros a s' ms' [-> H']. apply implM_ret. exact H'.
  Qed.

  (* [comment removed for export] *)
  Lemma implM_from_evt : forall {A} (c : M St A) s Q ms,
    evt segs (fun ms' => implM segs c s Q ms') ms -> implM segs c s Q ms.
  Proof. intros A c s Q ms H. unfold implM in *. apply impl_from_evt. exact H. Qed.

  (* [comment removed for export] *)
  Lemma impl_post_evt' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
    impl segs (at_node segs) t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') ->
    impl segs (at_node segs) t Q' ms.
  Proof.
    induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
    - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
    - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
  Qed.
  Lemma implM_post_evt' : forall {A} (c : M St A) s Q Q' ms,
    implM segs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt segs (Q' a s') ms') ->
    implM segs c s Q' ms.
  Proof.
    intros A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt'; [exact H|].
    intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
  Qed.

  (* [comment removed for export] *)
  Section So.
    Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
    Lemma implM_rdso : forall {A} (f : stdout_st -> @M St A) (s : St) Q ms,
      implM segs (f (get_so s)) s Q ms -> implM segs (Monad.mbind (rd_so get_so) f) s Q ms.
    Proof. intros A f s Q ms H. exact H. Qed.
    Lemma implM_updso : forall {A} (g : stdout_st -> stdout_st) (f : unit -> @M St A) (s : St) Q ms,
      implM segs (f tt) (set_so (g (get_so s)) s) Q ms -> implM segs (Monad.mbind (upd_so get_so set_so g) f) s Q ms.
    Proof. intros A g f s Q ms H. exact H. Qed.
    Lemma implM_updso_last : forall (g : stdout_st -> stdout_st) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
      Q tt (set_so (g (get_so s)) s) ms -> implM segs (upd_so get_so set_so g) s Q ms.
    Proof. intros g s Q ms H. apply implM_upd. apply evt_done. exact H. Qed.
  End So.
End WithSegs.

(* [comment removed for export] *)
Lemma rw_cells_recast : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof. intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall segs m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells segs m A (pre ++ C4 a :: post) -> rw_cells segs m A (pre ++ C4 b :: post).
Proof.
  intros segs m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_C4_CB4 : forall segs m A (v : word) cs,
  rw_cells segs m A (C4 v :: cs) -> rw_cells segs m A (CB 4 (le4 v) :: cs).
Proof.
  intros segs m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma rw_cells_CB4_C4 : forall segs m A (v : word) cs,
  rw_cells segs m A (CB 4 (le4 v) :: cs) -> rw_cells segs m A (C4 v :: cs).
Proof.
  intros segs m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.
Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Ltac if_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  end.
(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac exact_frm := lazymatch goal with |- frm0 ?f => first [is_evar f; fail 1 "exact_frm: evar" | assumption] end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
