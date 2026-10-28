(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Dmp_hdefsA Dmp_pj_ifaceA Dmp_insbA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_strA Dmp_pj_arrA Dmp_pj_objA Dmp_pj_oheadB Dmp_pj_obodyB Dmp_pj_otestB Dmp_pj_aevtA Dmp_pj_entryA Dmp_pj_casesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac ulx := unfold DMP_PJ_LEAF_A, DMP_PJ_FRAME_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Local Ltac acc_in := unfold ACC_LITS; cbn [In]; repeat (try (left; reflexivity); right).

Definition pj_frAH (j0 j8 j16 j24 j72 : list byte) (osp : Z) (jB : list byte) (f : Z) (jC : list byte) (doc i : Z) (sv : list cell) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 48 j24; CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC;
   C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv.

Definition pj_frAL (j24 : list byte) (osp : Z) (jB : list byte) (f : Z) (jC : list byte) (doc i : Z) (sv : list cell) : list cell :=
  [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 48 j24; C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB);
   C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv.

Lemma pj_frAH_size : forall j0 j8 j16 j24 j72 osp jB f jC doc i sv, cells_size sv = 104%nat ->
  cells_size (pj_frAH j0 j8 j16 j24 j72 osp jB f jC doc i sv) = 256%nat.
Proof. intros. unfold pj_frAH. rewrite cells_size_app, H. reflexivity. Qed.
Lemma pj_frAL_size : forall j24 osp jB f jC doc i sv, cells_size sv = 104%nat -> cells_size (pj_frAL j24 osp jB f jC doc i sv) = 256%nat.
Proof. intros. unfold pj_frAL. rewrite cells_size_app, H. reflexivity. Qed.

Lemma pj_frAH_0 : forall m S1 j0 j8 j16 j24 j72 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAH j0 j8 j16 j24 j72 osp jB f jC doc i sv) ->
  rw_cells bsegs m S1 [CB 8 j0; CB 8 j8; CB 8 j16].
Proof.
  intros. unfold pj_frAH in H.
  pose proof (rw_cells_mid m S1 [] [CB 8 j0; CB 8 j8; CB 8 j16]
                ([CB 48 j24; CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H) as X.
  replace (S1 + Z.of_nat (cells_size [])) with S1 in X by (cbn; lia). exact X.
Qed.
Lemma pj_frAH_72 : forall m S1 j0 j8 j16 j24 j72 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAH j0 j8 j16 j24 j72 osp jB f jC doc i sv) ->
  rw_cells bsegs m (S1 + 72) [CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frAH in H.
  exact (rw_cells_mid m S1 [CB 8 j0; CB 8 j8; CB 8 j16; CB 48 j24] [CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)]
           ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H).
Qed.
Lemma pj_frAH_88 : forall m S1 j0 j8 j16 j24 j72 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAH j0 j8 j16 j24 j72 osp jB f jC doc i sv) ->
  rw_cells bsegs m (S1 + 88) [C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frAH in H.
  exact (rw_cells_mid m S1 [CB 8 j0; CB 8 j8; CB 8 j16; CB 48 j24; CB 8 j72; C8 (Z_to_bv 64 SHB)] [C8 (Z_to_bv 64 osp)]
           ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H).
Qed.
Lemma pj_frAH_136 : forall m S1 j0 j8 j16 j24 j72 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAH j0 j8 j16 j24 j72 osp jB f jC doc i sv) ->
  rw_cells bsegs m (S1 + 136) [C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)].
Proof.
  intros. unfold pj_frAH in H.
  exact (rw_cells_mid m S1 [CB 8 j0; CB 8 j8; CB 8 j16; CB 48 j24; CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC]
           [C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] sv H).
Qed.
Lemma pj_frAL_0 : forall m S1 j24 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAL j24 osp jB f jC doc i sv) ->
  rw_cells bsegs m S1 [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)].
Proof.
  intros. unfold pj_frAL in H.
  pose proof (rw_cells_mid m S1 [] [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)]
                ([CB 48 j24; C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC;
                  C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H) as X.
  replace (S1 + Z.of_nat (cells_size [])) with S1 in X by (cbn; lia). exact X.
Qed.
Lemma pj_frAL_72 : forall m S1 j24 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAL j24 osp jB f jC doc i sv) ->
  rw_cells bsegs m (S1 + 72) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frAL in H.
  exact (rw_cells_mid m S1 [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 48 j24]
           [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)]
           ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H).
Qed.
Lemma pj_frAL_88 : forall m S1 j24 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAL j24 osp jB f jC doc i sv) ->
  rw_cells bsegs m (S1 + 88) [C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frAL in H.
  exact (rw_cells_mid m S1 [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 48 j24; C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB)]
           [C8 (Z_to_bv 64 osp)] ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H).
Qed.
Lemma pj_frAL_136 : forall m S1 j24 osp jB f jC doc i sv, rw_cells bsegs m S1 (pj_frAL j24 osp jB f jC doc i sv) ->
  rw_cells bsegs m (S1 + 136) [C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)].
Proof.
  intros. unfold pj_frAL in H.
  exact (rw_cells_mid m S1 [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 48 j24; C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB);
                             C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC] [C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] sv H).
Qed.

Lemma frD_AH : forall m m' S1 jA osp jB f jC doc i sv, cells_size sv = 104%nat ->
  rw_cells bsegs m S1 (pj_frD jA osp jB f jC doc i sv) -> munch [(S1 + 80, S1 + 88)] m m' ->
  rw_cells bsegs m' (S1 + 80) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ->
  exists j0 j8 j16 j24 j72, rw_cells bsegs m' S1 (pj_frAH j0 j8 j16 j24 j72 osp jB f jC doc i sv).
Proof.
  intros m m' S1 jA osp jB f jC doc i sv SVZ H MU H80. unfold pj_frD in H.
  change ([CB 88 jA; C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv)
    with ([] ++ CB 88 jA :: ([C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv)) in H.
  apply (rw_cells_split_CB bsegs m S1 [] 88 jA _ [8; 8; 8; 48; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  repeat match type of H with context [CB ?kk ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end.
  lazymatch type of H with rw_cells _ _ _ (CB 8 ?x0 :: CB 8 ?x8 :: CB 8 ?x16 :: CB 48 ?x24 :: CB 8 ?x72 :: CB 8 ?x80 :: C8 _ :: ?rest) =>
    exists x0, x8, x16, x24, x72; unfold pj_frAH;
    change (rw_cells bsegs m' S1 ([CB 8 x0; CB 8 x8; CB 8 x16; CB 48 x24; CB 8 x72] ++ ([C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ++ rest)));
    pose proof (rw_cells_mid m S1 [] [CB 8 x0; CB 8 x8; CB 8 x16; CB 48 x24; CB 8 x72] (CB 8 x80 :: C8 (Z_to_bv 64 osp) :: rest) H) as P1;
    pose proof (rw_cells_mid m S1 [CB 8 x0; CB 8 x8; CB 8 x16; CB 48 x24; CB 8 x72; CB 8 x80; C8 (Z_to_bv 64 osp)] rest [] ltac:(rewrite app_nil_r; exact H)) as P3
  end.
  cbn [cells_size csize Nat.add Z.of_nat] in P1, P3. rewrite Z.add_0_r in P1.
  apply rw_cells_app. split.
  - eapply rw_cells_agree_nw; [exact P1|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [lia| exact I].
  - cbn [cells_size csize Nat.add]. apply rw_cells_app. split; [replace (S1 + Z.of_nat 80) with (S1 + 80) by lia; exact H80|].
    cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat 80 + Z.of_nat 16) with (S1 + 96) by lia.
    eapply rw_cells_agree_nw; [exact P3|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. split; [lia| exact I].
Qed.

Lemma frAH_AL : forall m m' S1 (W : list (Z * Z)) j0 j8 j16 j24 j72 osp jB f jC doc i sv,
  rw_cells bsegs m S1 (pj_frAH j0 j8 j16 j24 j72 osp jB f jC doc i sv) -> munch W m m' ->
  (forall x, S1 + 24 <= x < S1 + 72 \/ S1 + 96 <= x -> outside W x) ->
  rw_cells bsegs m' S1 [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)] ->
  rw_cells bsegs m' (S1 + 72) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ->
  rw_cells bsegs m' S1 (pj_frAL j24 osp jB f jC doc i sv).
Proof.
  intros m m' S1 W j0 j8 j16 j24 j72 osp jB f jC doc i sv H MU HW H0 H72. unfold pj_frAH in H. unfold pj_frAL.
  pose proof (rw_cells_mid m S1 [CB 8 j0; CB 8 j8; CB 8 j16] [CB 48 j24]
                ([CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H) as P2.
  pose proof (rw_cells_mid m S1 [CB 8 j0; CB 8 j8; CB 8 j16; CB 48 j24; CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)]
                ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) [] ltac:(rewrite app_nil_r; exact H)) as P4.
  cbn [cells_size csize Nat.add Z.of_nat] in P2, P4.
  change (rw_cells bsegs m' S1 ([C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)] ++ ([CB 48 j24] ++
            ([C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ++
             ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv))))).
  apply rw_cells_app. split; [exact H0|]. cbn [cells_size csize Nat.add].
  apply rw_cells_app. split.
  - eapply rw_cells_agree_nw; [exact P2|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HW. left. lia.
  - cbn [cells_size csize Nat.add]. apply rw_cells_app. split; [replace (S1 + Z.of_nat 24 + Z.of_nat 48) with (S1 + 72) by lia; exact H72|].
    cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat 24 + Z.of_nat 48 + Z.of_nat 24) with (S1 + 96) by lia.
    eapply rw_cells_agree_nw; [exact P4|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW. right. lia.
Qed.

Lemma elem_kindA : forall T S sn d i j, elem T S sn ck_any d i j -> pj_kindA T S sn i j.
Proof.
  intros T S sn d i j EL. unfold pj_kindA. destruct d as [|d']; cbn [elem] in EL.
  - destruct EL as [SC|[]]. destruct SC as [X|[X|X]]; [left; exact X| right; left; exact X| right; right; left; exact X].
  - destruct EL as [SC|CO].
    + destruct SC as [X|[X|X]]; [left; exact X| right; left; exact X| right; right; left; exact X].
    + destruct CO as (e2 & c2 & cv2 & -> & CK & [(X & _ & _)|(X & _ & _)]); do 3 right; exists cv2; unfold ck_any in CK; (split; [exact CK|]); [left| right]; exact X.
Qed.

Definition pj_frOH (j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 : list byte) (osp : Z) (jB : list byte) (f : Z) (jC : list byte) (doc i : Z) (sv : list cell) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp);
   CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv.

Definition pj_frOE (j0 j8 j16 j24 j32 j40 j48 j56 : list byte) (e osp : Z) (jB : list byte) (f : Z) (jC : list byte) (doc i : Z) (sv : list cell) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 SHB);
   C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv.

Definition pj_frOL (E : aenvA) (f e osp : Z) (jB jC : list byte) (doc i : Z) (sv : list cell) : list cell :=
  (pj_oframe E f e osp ++ [CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)]) ++ sv.

Lemma pj_frOH_size : forall j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 osp jB f jC doc i sv, cells_size sv = 104%nat ->
  cells_size (pj_frOH j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 osp jB f jC doc i sv) = 256%nat.
Proof. intros. unfold pj_frOH. rewrite cells_size_app, H. reflexivity. Qed.
Lemma pj_frOE_size : forall j0 j8 j16 j24 j32 j40 j48 j56 e osp jB f jC doc i sv, cells_size sv = 104%nat ->
  cells_size (pj_frOE j0 j8 j16 j24 j32 j40 j48 j56 e osp jB f jC doc i sv) = 256%nat.
Proof. intros. unfold pj_frOE. rewrite cells_size_app, H. reflexivity. Qed.
Lemma pj_frOL_pre_size : forall E f e osp jB jC doc i,
  cells_size (pj_oframe E f e osp ++ [CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)]) = 152%nat.
Proof. intros. reflexivity. Qed.
Lemma pj_frOL_size : forall E f e osp jB jC doc i sv, cells_size sv = 104%nat -> cells_size (pj_frOL E f e osp jB jC doc i sv) = 256%nat.
Proof. intros. unfold pj_frOL. rewrite cells_size_app, pj_frOL_pre_size, H. reflexivity. Qed.

Lemma pj_frOE_88 : forall m S1 j0 j8 j16 j24 j32 j40 j48 j56 e osp jB f jC doc i sv,
  rw_cells bsegs m S1 (pj_frOE j0 j8 j16 j24 j32 j40 j48 j56 e osp jB f jC doc i sv) -> rw_cells bsegs m (S1 + 88) [C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frOE in H.
  exact (rw_cells_mid m S1 [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 SHB)]
           [C8 (Z_to_bv 64 osp)] ([CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv) H).
Qed.
Lemma pj_frOL_0 : forall m S1 E f e osp jB jC doc i sv, rw_cells bsegs m S1 (pj_frOL E f e osp jB jC doc i sv) ->
  rw_cells bsegs m S1 [C8 (Z_to_bv 64 DMP_LIT_RBRC_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)].
Proof.
  intros. unfold pj_frOL, pj_oframe in H. cbn [app] in H.
  pose proof (rw_cells_mid m S1 [] [_; _; _] _ H) as X.
  replace (S1 + Z.of_nat (cells_size [])) with S1 in X by (cbn; lia). exact X.
Qed.
Lemma pj_frOL_88 : forall m S1 E f e osp jB jC doc i sv, rw_cells bsegs m S1 (pj_frOL E f e osp jB jC doc i sv) ->
  rw_cells bsegs m (S1 + 88) [C8 (Z_to_bv 64 osp)].
Proof.
  intros. unfold pj_frOL, pj_oframe in H. cbn [app] in H.
  pose proof (rw_cells_mid m S1 [_; _; _; _; _; _; _; _; _; _; _] [_] _ H) as X. exact X.
Qed.

Lemma frD_OH : forall m m' S1 jA osp jB f jC doc i sv,
  rw_cells bsegs m S1 (pj_frD jA osp jB f jC doc i sv) -> munch [(S1 + 80, S1 + 88)] m m' ->
  rw_cells bsegs m' (S1 + 80) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ->
  exists j0 j8 j16 j24 j32 j40 j48 j56 j64 j72, rw_cells bsegs m' S1 (pj_frOH j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 osp jB f jC doc i sv).
Proof.
  intros m m' S1 jA osp jB f jC doc i sv H MU H80. unfold pj_frD in H.
  change ([CB 88 jA; C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv)
    with ([] ++ CB 88 jA :: ([C8 (Z_to_bv 64 osp); CB 8 jB; C8 (Z_to_bv 64 f); CB 24 jC; C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)] ++ sv)) in H.
  apply (rw_cells_split_CB bsegs m S1 [] 88 jA _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  repeat match type of H with context [CB ?kk ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end.
  lazymatch type of H with rw_cells _ _ _ (CB 8 ?x0 :: CB 8 ?x8 :: CB 8 ?x16 :: CB 8 ?x24 :: CB 8 ?x32 :: CB 8 ?x40 :: CB 8 ?x48 :: CB 8 ?x56 :: CB 8 ?x64 :: CB 8 ?x72 :: CB 8 ?x80 :: C8 _ :: ?rest) =>
    exists x0, x8, x16, x24, x32, x40, x48, x56, x64, x72; unfold pj_frOH;
    change (rw_cells bsegs m' S1 ([CB 8 x0; CB 8 x8; CB 8 x16; CB 8 x24; CB 8 x32; CB 8 x40; CB 8 x48; CB 8 x56; CB 8 x64; CB 8 x72] ++ ([C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ++ rest)));
    pose proof (rw_cells_mid m S1 [] [CB 8 x0; CB 8 x8; CB 8 x16; CB 8 x24; CB 8 x32; CB 8 x40; CB 8 x48; CB 8 x56; CB 8 x64; CB 8 x72] (CB 8 x80 :: C8 (Z_to_bv 64 osp) :: rest) H) as P1;
    pose proof (rw_cells_mid m S1 [CB 8 x0; CB 8 x8; CB 8 x16; CB 8 x24; CB 8 x32; CB 8 x40; CB 8 x48; CB 8 x56; CB 8 x64; CB 8 x72; CB 8 x80; C8 (Z_to_bv 64 osp)] rest []
                  ltac:(rewrite app_nil_r; exact H)) as P3
  end.
  cbn [cells_size csize Nat.add Z.of_nat] in P1, P3. rewrite Z.add_0_r in P1.
  apply rw_cells_app. split.
  - eapply rw_cells_agree_nw; [exact P1|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [lia| exact I].
  - cbn [cells_size csize Nat.add]. apply rw_cells_app. split; [replace (S1 + Z.of_nat 80) with (S1 + 80) by lia; exact H80|].
    cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat 80 + Z.of_nat 16) with (S1 + 96) by lia.
    eapply rw_cells_agree_nw; [exact P3|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. split; [lia| exact I].
Qed.

Lemma pj_frOL_of : forall m S1 E f e osp jB jC doc i sv, rw_cells bsegs m S1 (pj_frOL E f e osp jB jC doc i sv) ->
  rw_cells bsegs m S1 (pj_oframe E f e osp).
Proof.
  intros. unfold pj_frOL in H. rewrite <- app_assoc in H.
  pose proof (rw_cells_mid m S1 [] (pj_oframe E f e osp) _ H) as X.
  replace (S1 + Z.of_nat (cells_size [])) with S1 in X by (cbn; lia). exact X.
Qed.

Lemma fr_join152 : forall m m' S1 (P0 P sv : list cell) (W : list (Z * Z)),
  cells_size P0 = 152%nat -> cells_size P = 152%nat ->
  rw_cells bsegs m S1 (P0 ++ sv) -> munch W m m' ->
  (forall x, S1 + 152 <= x < S1 + 152 + Z.of_nat (cells_size sv) -> outside W x) ->
  rw_cells bsegs m' S1 P -> rw_cells bsegs m' S1 (P ++ sv).
Proof.
  intros m m' S1 P0 P sv W S0 SP H MU HW H'.
  apply rw_cells_app in H. destruct H as [_ H]. rewrite S0 in H. change (Z.of_nat 152) with 152 in H.
  apply rw_cells_app. split; [exact H'|]. rewrite SP. change (Z.of_nat 152) with 152.
  eapply rw_cells_agree_nw; [exact H|]. apply (agree_of_munch _ _ _ _ MU). exact HW.
Qed.

Section Loops.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc2_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis PUT : os_put_cpsA RT PMc.
Notation aevt := (aevt RT PMc).
Notation PINVA := (PINVA RT).
Notation KEXITA := (KEXITA RT PMc).

Variable G : pctx.
Hypothesis GOK : pctx_ok G.
Hypothesis AI0 : AINV_A (g_E G) (g_m0 G).
Hypothesis IOS0 : io_ssp (g_m0 G).

Variable d' : nat.
Hypothesis GD : g_d G = S d'.
Hypothesis PJ : Dmp_pj_ifaceA.pj_cpsA RT PMc d'.
Notation E := (g_E G).
Notation n := (ae_n (g_E G)).
Notation T := (ae_T (g_E G)).
Notation S := (ae_S (g_E G)).
Notation sn := (ae_sn (g_E G)).
Notation osp := (g_OS G + 128).

Let facts : aenvA_ok E /\ 0x6d5000 <= g_q G - 256 /\ g_q G < 2^63 /\ 0 <= g_OS G + 128 < 2^64 /\ 0 < g_ff G /\ ae_n E < 2^32 /\ 0 <= ae_sn E < 2^56
            /\ g_ff G + 256 < 2^63 /\ shad (g_ff G) + 32 < 2^63 /\ ae_lo E <= g_q G - 256.
Proof.
  destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (OK & _) (EIN & ELO & EHI & _) (F0 & F64 & FSEG & FLO & FHI & SHLO & _) _ _ RFR _ _ _].
  pose proof (RFR _ _ EIN) as (_ & ESEG & EL & _). pose proof (pj_needA_0 (g_d G)) as ND. pose proof (Atp_defsA.ok_wf E OK) as (NR & SNR & _).
  assert (0 <= fs_size (g_kO G)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  split; [exact OK|]. repeat split; try assumption; ulx.
Qed.

Let facts2 : ae_lo E <= g_q G - 272 /\ 0 < osp < 2^63 /\ osp mod 8 = 0.
Proof.
  destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ (EIN & ELO & EHI & EM & _) _ _ _ RFR _ _ _].
  pose proof (RFR _ _ EIN) as (FP & _ & FL & _). pose proof (pj_needA_0 (g_d G)) as ND.
  assert (0 <= fs_size (g_kO G)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK, USTACK_TOP in *.
  split; [lia|]. split; [lia|]. clear - EM. Z.div_mod_to_equations. lia.
Qed.

Definition KCLOSEA (fcs : list cell) (kc : Z) (K : config -> Prop) (gp : word) (lit : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + 2 <= kc ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 (wz (g_q G)) (wz (g_S1 G)) a0 (wz lit) a2 a3 a4 a5 a6 a7
                      s2 (wz (g_ff G)) s4 s5 s6 (wz (g_ff G)) s8 s9 s10 (wz (shad (g_ff G))) t3 t4 t5 t6) F (wz DMP_PJ_CLOSE_A) fc None m (seg_rom bsegs)).

Definition KLOOPXA (fcs : list cell) (kc : Z) (K : config -> Prop) (gp : word) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + 2 <= kc ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 (wz (g_q G)) (wz (g_S1 G)) a0 a1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz (shad (g_ff G))) t3 t4 t5 t6) F (wz DMP_PJ_LOOPX_A) fc None m (seg_rom bsegs)).

Lemma pa_close : forall (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (lit : Z),
  (lit = DMP_LIT_RBRK_A \/ lit = DMP_LIT_RBRC_A) ->
  (forall mx, rw_cells bsegs mx (g_S1 G) fcs -> rw_cells bsegs mx (g_S1 G + 88) [C8 (wz osp)]) ->
  kx <= g_cr G -> KEXITA G fcs kx K gp -> KCLOSEA fcs kx K gp lit.
Proof using AF FDO MST PUT GOK facts.
  intros fcs kx K gp lit LIT X88 KX HK. unfold KCLOSEA. intros until fc. intros GI FRM KB. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (X88 _ FR) as FO.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_close0 (g_q G) osp ra gp (wz TPV_A) t0 t1 t2 (wz (g_q G)) a0 (wz lit) a2 a3 a4 a5 a6 a7
                             s2 (wz (g_ff G)) s4 s5 s6 (wz (g_ff G)) s8 s9 s10 (wz (shad (g_ff G))) t3 t4 t5 t6 F fc m QLO QH OR FO MI)|].
  cbv beta. intros ms1 ->. apply evt_done.
  destruct LIT as [-> | ->]; unfold DMP_LIT_RBRK_A, DMP_LIT_RBRC_A.
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K _ 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K _ 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
Qed.

Lemma pa_xclose : forall (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (lit : Z),
  (lit = DMP_LIT_RBRK_A \/ lit = DMP_LIT_RBRC_A) ->
  (forall mx, rw_cells bsegs mx (g_S1 G) fcs -> rw_cells bsegs mx (g_S1 G) [C8 (wz lit); C8 (wz (g_ff G)); C8 (wz (g_ff G))]) ->
  (forall mx, rw_cells bsegs mx (g_S1 G) fcs -> rw_cells bsegs mx (g_S1 G + 88) [C8 (wz osp)]) ->
  kx <= g_cr G -> KEXITA G fcs kx K gp -> KLOOPXA fcs kx K gp.
Proof using AF FDO MST PUT GOK facts.
  intros fcs kx K gp lit LIT X0 X88 KX HK. unfold KLOOPXA. intros until fc. intros GI FRM KB. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _).
  pose proof (X88 _ FR) as FO. pose proof (X0 _ FR) as F0C.
  assert (LR : 0 <= lit < 2^64) by (destruct LIT as [-> | ->]; unfold DMP_LIT_RBRK_A, DMP_LIT_RBRC_A; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_close1 (g_q G) (g_ff G) osp lit ra gp (wz TPV_A) t0 t1 t2 (wz (g_q G)) a0 a1 a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz (shad (g_ff G))) t3 t4 t5 t6 F fc m QLO QH OR LR F0 FH F0C FO MI)|].
  cbv beta. intros ms1 ->. apply evt_done.
  destruct LIT as [-> | ->]; unfold DMP_LIT_RBRK_A, DMP_LIT_RBRC_A.
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K _ 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
  - eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K _ 1 2 1%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
      | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even DMP_PJ_EXIT_A) by (unfold DMP_PJ_EXIT_A; lia).
    eapply HK; [exact GI2| clear - KB; lia| exact FRM].
Qed.

Definition ALSA (e it pc : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (pjRL E (g_q G) (g_ff G) osp e gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz it) t0 t1 t2 t3 t4 t5 t6) F (wz pc) fc None m (seg_rom bsegs).

Definition KALOOPA (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (e it : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + DMP_PJ_CW * (e - it) + 2 <= kx ->
    aevt Σ K (ALSA e it DMP_PJ_ALOOP_A gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m).

Lemma pa_head : forall (jA jB jC : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i e cv : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) jC (ae_DOC E) i sv) k Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX ->
  T i = cword t_arr (e + 1) cv -> k + 2 <= kx -> kx <= g_cr G ->
  (forall j0 j8 j16 j24 j72, KCLOSEA (pj_frAH j0 j8 j16 j24 j72 osp jB (g_ff G) jC (ae_DOC E) i sv) kx K gp DMP_LIT_RBRK_A) ->
  (i + 1 <> e -> forall j24, KALOOPA (pj_frAL j24 osp jB (g_ff G) jC (ae_DOC E) i sv) kx K gp e (i + 1)) ->
  k + 2 + DMP_PJ_CW * (e - (i + 1)) + 2 <= kx ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
               F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT GOK AI0 facts.
  intros until m. intros GI FRM I0 IE EN CV TI KB KX HC HL KBL. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof (Atp_defsA.ok_tape E OK) as (T16 & NT8 & TN & TP0 & TL).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & FSZ) & _).
  assert (SVZ : cells_size sv = 104%nat) by (unfold pj_frD in FSZ; rewrite cells_size_app in FSZ; cbn [cells_size csize Nat.add] in FSZ; lia).
  destruct (pj_frD_80 _ _ _ _ _ _ _ _ _ _ FR) as (j80 & F80).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  unfold CNT_MAX in CV.
  assert (TIR : 0 <= T i < 2^64) by (rewrite TI; apply cword_range; unfold t_arr, CNT_MAX; lia).
  assert (TY : ttype (T i) = 91) by (rewrite TI, ttype_cword by (unfold CNT_MAX; lia); reflexivity).
  assert (TB : ae_TAPE E + 8 * i < 2^63) by (clear - TN TL LOS QH IE EN; lia).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_open1 E 91 (g_q G) (g_ff G) osp i gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 j80 F fc m
                             OK ltac:(clear - I0 IE EN; lia) TIR TY ltac:(left; reflexivity) QLO QH OR AI SHZT F80 MI)|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & F801). apply evt_done.
  destruct (frD_AH m m1 (g_S1 G) jA osp jB (g_ff G) jC (ae_DOC E) i sv SVZ FR MU1 F801) as (j0 & j8 & j16 & j24 & j72 & FR1).
  assert (GI1 : PINVA G (pj_frAH j0 j8 j16 j24 j72 osp jB (g_ff G) jC (ae_DOC E) i sv) k Σ m1).
  { apply (PINVA_cw RT AF G GOK _ _ k Σ m m1 _ GI MU1 WM1 MI1); [| exact FR1| apply pj_frAH_size; exact SVZ].
    intros a. destruct (outside_dec [(g_S1 G + 80, g_S1 G + 88)] a) as [O|IN]; [left; exact O| right]. unfold own. cbn [inW] in IN. clear - IN. lia. }
  unfold pjR, pj_open_ret, pj_open_lit. cbn [Z.eqb Pos.eqb].
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K _ 1 2 1%nat); [exact PUT| exact GI1| unfold DMP_LIT_LBRK_A; acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| unfold DMP_LIT_LBRK_A; lia| unfold DMP_LIT_LBRK_A, SEGTOP_A; lia| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even 0xaf13c) by lia.

  pose proof GI2 as (_ & MI2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2 & _) & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI2) as (SHZT2 & _ & SHZD2). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI2) as AI2.
  pose proof (pj_frAH_136 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR2) as FD2.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ahead1 E (g_q G) (g_ff G) osp i e cv gp (wz 0xaf13c) (wz osp) e1 e2 e3 e4 e5 e6 e7 s6 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 F2 fc m2
                             OK I0 IE EN NR CV TI QLO QH OR F0 FH SFH AI2 SHZT2 SHZD2 FD2 MI2)|].
  cbv beta. intros ms3 ->. apply evt_done. unfold pjR.
  eapply (p_tix RT AF PMc MST G GOK _ (k + 2) Σ2 K i); [exact GI2| exact AI0| exact I0| exact TB|].
  intros a4x m3 GI3. rewrite (ret_pc_even DMP_PJ_AH1RET_A) by (unfold DMP_PJ_AH1RET_A; lia).

  pose proof GI3 as (_ & MI3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR3 & _) & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI3) as (SHZT3 & _ & SHZD3). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI3) as AI3.
  pose proof (pj_frAH_136 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR3) as FD3.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ahead2 E (g_q G) (g_ff G) osp i e cv gp (wz DMP_PJ_AH1RET_A)
                             a4x e5 e6 e7 s6 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 F2 fc m3
                             OK I0 IE EN NR CV TI QLO QH OR F0 FH SFH AI3 SHZT3 SHZD3 FD3 MI3)|].
  cbv beta. intros ms4 ->. apply evt_done. unfold pjR.
  eapply (p_tix RT AF PMc MST G GOK _ (k + 2) Σ2 K i); [exact GI3| exact AI0| exact I0| exact TB|].
  intros a4y m4 GI4. rewrite (ret_pc_even DMP_PJ_AH2RET_A) by (unfold DMP_PJ_AH2RET_A; lia).

  pose proof GI4 as (_ & MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR4 & _) & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI4) as (SHZT4 & _ & SHZD4). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI4) as AI4.
  pose proof (pj_frAH_136 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR4) as FD4.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ahead3 E (g_q G) (g_ff G) osp i e cv gp (wz DMP_PJ_AH2RET_A)
                             a4y e5 e6 e7 s6 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 F2 fc m4
                             OK I0 IE EN NR CV TI QLO QH OR F0 FH SFH AI4 SHZT4 SHZD4 FD4 MI4)|].
  cbv beta. intros ms5 ->. apply evt_done. unfold pjR.
  eapply (p_tix RT AF PMc MST G GOK _ (k + 2) Σ2 K i); [exact GI4| exact AI0| exact I0| exact TB|].
  intros a4z m5 GI5. rewrite (ret_pc_even DMP_PJ_AH3RET_A) by (unfold DMP_PJ_AH3RET_A; lia).

  pose proof GI5 as (_ & MI5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR5 & _) & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI5) as (SHZT5 & _ & SHZD5). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI5) as AI5.
  pose proof (pj_frAH_136 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR5) as FD5.
  pose proof (pj_frAH_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR5) as F05.
  pose proof (pj_frAH_72 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR5) as F725.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ahead4 E (g_q G) (g_ff G) osp i e cv gp (wz DMP_PJ_AH3RET_A)
                             a4z e5 e6 e7 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 j0 j8 j16 j72 F2 fc m5
                             OK I0 IE EN NR CV TI QLO QH OR F0 FH SFH AI5 SHZT5 SHZD5 FD5 F05 F725 MI5)|].
  cbv beta. intros ms6 POST. apply evt_done.
  destruct POST as [(EQ & a0x & a2x & a3x & ->)|(NE & m6 & a0x & a1x & a2x & a3x & -> & MU6 & WM6 & MI6 & F06 & F726)].
  - unfold pjR. eapply (HC j0 j8 j16 j24 j72); [exact GI5| exact FRM| clear - KBL EQ; unfold DMP_PJ_CW in KBL; lia].
  - assert (FR6 : rw_cells bsegs m6 (g_S1 G) (pj_frAL j24 osp jB (g_ff G) jC (ae_DOC E) i sv))
      by exact (frAH_AL m5 m6 (g_S1 G) _ j0 j8 j16 j24 j72 osp jB (g_ff G) jC (ae_DOC E) i sv FR5 MU6
                 ltac:(intros x Hx; cbn [outside]; repeat split; try exact I; lia) F06 F726).
    assert (GI6 : PINVA G (pj_frAL j24 osp jB (g_ff G) jC (ae_DOC E) i sv) (k + 2) Σ2 m6).
    { apply (PINVA_cw RT AF G GOK _ _ (k + 2) Σ2 m5 m6 _ GI5 MU6 WM6 MI6); [| exact FR6| apply pj_frAL_size; exact SVZ].
      intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end.
      unfold own. cbn [inW] in IN. clear - IN. lia. }
    unfold KALOOPA, ALSA in HL. eapply (HL NE j24); [exact GI6| exact FRM| clear - KBL; lia].
Qed.

Lemma pa_step : forall (j24 jB jC : list byte) (sv : list cell) (i k kx : Z) (Σ : rts RT) (K : config -> Prop) (e it j : Z)
    (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let fcs := pj_frAL j24 osp jB (g_ff G) jC (ae_DOC E) i sv in
  PINVA G fcs k Σ m -> frm0 fc -> elem T S sn ck_any d' it j -> 0 <= it -> j <= e -> e + 1 <= n ->
  k + pj_costE it j + 2 <= kx -> kx <= g_cr G ->
  (forall (Σ' : rts RT) (m' : mem) (k' : Z) (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     PINVA G fcs k' Σ' m' -> frm0 fc' -> k' <= k + pj_costE it j + 2 ->
     aevt Σ' K (ALSA e j DMP_PJ_ATEST_A gp ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' F' fc' m')) ->
  aevt Σ K (ALSA e it DMP_PJ_ALOOP_A gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros until m. cbv zeta. intros GI FRM EL I0 JE EN KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof (Atp_defsA.ok_tape E OK) as (T16 & NT8 & TN & TP0 & TL).
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  assert (CE : 0 <= pj_costE it j) by (unfold pj_costE, DMP_PJ_CW; clear - IJ; lia).
  assert (ER : 0 <= e < 2^63) by (clear - I0 IJ JE EN NR; lia).
  pose proof GI as (_ & MI & _). unfold ALSA.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_aloop1 E (g_q G) (g_ff G) osp e it gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m MI)|].
  cbv beta. intros ms1 ->. apply evt_done. unfold pjRL.
  eapply (p_child RT AF PMc FDO MST G GOK d' _ k Σ K it j); [exact PJ| exact GI| exact AI0| exact IOS0| exact FRM| exact EL| exact I0| clear - JE EN; lia| exact GD| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even 0xaf4b0) by lia.
  pose proof GI2 as (_ & MI2 & _).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_aloop2 E (g_q G) (g_ff G) osp e it gp (wz 0xaf4b0) b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 F2 fc2 m2 MI2)|].
  cbv beta. intros ms3 ->. apply evt_done. unfold pjRL.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ (k + pj_costE it j) Σ2 K _ 1 2 1%nat); [exact PUT| exact GI2| unfold DMP_LIT_COMMA_A; acc_in| vm_compute; reflexivity
    | vm_compute; reflexivity| cbn; lia| cbn; lia| unfold DMP_LIT_COMMA_A; lia| unfold DMP_LIT_COMMA_A, SEGTOP_A; lia| clear - KB KX CE; lia|].
  intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 m4 GI4. rewrite (ret_pc_even DMP_PJ_ASTEP_A) by (unfold DMP_PJ_ASTEP_A; lia).

  pose proof GI4 as (_ & MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR4 & _) & _).
  pose proof (pj_frAL_136 _ _ _ _ _ _ _ _ _ _ FR4) as FD4.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_astep3 E (g_q G) (g_ff G) osp e it i gp (wz DMP_PJ_ASTEP_A) (wz osp) c1 c2 c3 c4 c5 c6 c7 v0 v1 v2 v3 v4 v5 v6 F4 fc2 m4
                             OK I0 ltac:(clear - IJ JE EN; lia) NR QLO QH FD4 MI4)|].
  cbv beta. intros ms5 ->. apply evt_done. unfold pjRL.
  eapply (p_tix RT AF PMc MST G GOK _ (k + pj_costE it j + 2) Σ4 K it); [exact GI4| exact AI0| exact I0| clear - TN TL LOS QH IJ JE EN; lia|].
  intros a4x m5 GI5. rewrite (ret_pc_even 0xaf4cc) by lia.

  pose proof GI5 as (_ & MI5 & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI5) as (SHZT5 & _ & SHZD5). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI5) as AI5.
  pose proof (elem_kindA _ _ _ _ _ _ EL) as KIND.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_astep4 E (g_q G) (g_ff G) osp e it j gp (wz 0xaf4cc) a4x c5 c6 c7 v0 v1 v2 v3 v4 v5 v6 F4 fc2 m5
                             OK I0 IJ ltac:(clear - JE EN; lia) NR KIND QLO QH OR ltac:(clear - ER; lia) F0 SFH AI5 SHZT5 SHZD5 MI5)|].
  cbv beta. intros ms6 POST. apply evt_done.
  destruct POST as [(a0x & a1x & a2x & a3x & ->)|((cv & CV & TC) & ->)].
  - eapply HK; [exact GI5| exact FRM2| clear; lia].
  - unfold pjRL.
    eapply (p_tix RT AF PMc MST G GOK _ (k + pj_costE it j + 2) Σ4 K it); [exact GI5| exact AI0| exact I0| clear - TN TL LOS QH IJ JE EN; lia|].
    intros a4y m6 GI6. rewrite (ret_pc_even 0xaf514) by lia.
    pose proof GI6 as (_ & MI6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR6 & _) & _).
    pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI6) as (SHZT6 & _ & SHZD6). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI6) as AI6.
    pose proof (pj_frAL_72 _ _ _ _ _ _ _ _ _ _ FR6) as F726.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_astep5 E (g_q G) (g_ff G) osp e it j cv gp (wz 0xaf514) a4y c5 c6 c7 v0 v1 v2 v3 v4 v5 v6 F4 fc2 m6
                               OK I0 IJ ltac:(clear - JE EN; lia) NR CV TC QLO QH OR ltac:(clear - ER; lia) F0 SFH AI6 SHZT6 SHZD6 F726 MI6)|].
    cbv beta. intros ms7 (a0x & a1x & a2x & a3x & ->). apply evt_done.
    eapply HK; [exact GI6| exact FRM2| clear; lia].
Qed.

Lemma pa_loop : forall (j24 jB jC : list byte) (sv : list cell) (kx : Z) (K : config -> Prop) (gp : word) (i e c it : Z),
  let fcs := pj_frAL j24 osp jB (g_ff G) jC (ae_DOC E) i sv in
  tiles (elem T S sn ck_any d') it e c -> it <> e -> 0 <= it -> e + 1 <= n -> kx <= g_cr G ->
  KLOOPXA fcs kx K gp -> KALOOPA fcs kx K gp e it.
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros j24 jB jC sv kx K gp i e c it. cbv zeta. intros HT. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  induction HT as [it0|it0 j1 e0 c0 EL HT' IH]; intros NE I0 EN KX HC; [congruence|].
  unfold KALOOPA. intros until fc. intros GI FRM KB.
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ. pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ HT') as [JE _].
  eapply (pa_step j24 jB jC sv i _ kx); [exact GI| exact FRM| exact EL| exact I0| exact JE| exact EN| unfold pj_costE, DMP_PJ_CW in *; clear - KB IJ JE; lia| exact KX|].
  intros Σ2 m2 k2 ra' b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 F2 fc2 GI2 FRM2 K2. unfold ALSA.
  pose proof GI2 as (_ & MI2 & _).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_atest E (g_q G) (g_ff G) osp e0 j1 gp ra' b0 b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 F2 fc2 m2 ltac:(clear - I0 IJ JE EN NR; lia) ltac:(clear - I0 IJ JE EN NR; lia) MI2)|].
  cbv beta. intros ms3 ->. apply evt_done.
  destruct (Z.eqb_spec j1 e0) as [JE0|JNE].
  -
    unfold pjRL. eapply HC; [exact GI2| exact FRM2| unfold pj_costE, DMP_PJ_CW in *; clear - KB K2 IJ JE0; lia].
  -
    unfold KALOOPA, ALSA in IH. eapply IH; [exact JNE| clear - I0 IJ; lia| exact EN| exact KX| exact HC| exact GI2| exact FRM2| unfold pj_costE, DMP_PJ_CW in *; clear - KB K2 IJ; lia].
Qed.

Lemma pj_arr_caseA : forall (jA jB jC : list byte) (sv : list cell) (kx : Z) (Σ : rts RT) (K : config -> Prop) (i e c cv : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) jC (ae_DOC E) i sv) 1 Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX ->
  T i = cword t_arr (e + 1) cv -> tiles (elem T S sn ck_any d') (i + 1) e c ->
  pj_costE i (e + 1) <= kx -> kx <= g_cr G ->
  (forall LC, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
               F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts.
  intros until m. intros GI FRM I0 IE EN CV TI HT KB KX HKX.
  eapply (pa_head jA jB jC sv 1 kx Σ K i e cv); [exact GI| exact FRM| exact I0| exact IE| exact EN| exact CV| exact TI| unfold pj_costE, DMP_PJ_CW in KB; clear - KB IE; lia| exact KX
    | | | unfold pj_costE, DMP_PJ_CW in *; clear - KB IE; lia].
  - intros j0 j8 j16 j24 j72. apply pa_close; [left; reflexivity| intros mx H; exact (pj_frAH_88 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)| exact KX|].
    unfold pj_frAH. apply HKX. reflexivity.
  - intros NE j24. eapply (pa_loop j24 jB jC sv kx K gp i e c (i + 1)); [exact HT| exact NE| clear - I0; lia| exact EN| exact KX|].
    apply (pa_xclose _ kx K gp DMP_LIT_RBRK_A); [left; reflexivity| intros mx H; exact (pj_frAL_0 _ _ _ _ _ _ _ _ _ _ H)
      | intros mx H; exact (pj_frAL_88 _ _ _ _ _ _ _ _ _ _ H)| exact KX|].
    unfold pj_frAL. apply HKX. reflexivity.
Qed.

Definition OLSA (kk : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (pjRO E (g_q G) (g_ff G) kk gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_OLOOP_A) fc None m (seg_rom bsegs).

Definition KOLOOPA (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) (e kk : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    PINVA G fcs k Σ m -> frm0 fc -> k + DMP_PJ_CW * (e - kk) + 2 <= kx ->
    aevt Σ K (OLSA kk gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 F fc m).

Lemma po_head : forall (jA jB jC : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i e cv : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) jC (ae_DOC E) i sv) k Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX ->
  T i = cword t_obj (e + 1) cv -> k + 2 <= kx -> kx <= g_cr G ->
  (forall j0 j8 j16 j24 j32 j40 j48 j56, KCLOSEA (pj_frOE j0 j8 j16 j24 j32 j40 j48 j56 e osp jB (g_ff G) jC (ae_DOC E) i sv) kx K gp DMP_LIT_RBRC_A) ->
  (i + 1 <> e -> KOLOOPA (pj_frOL E (g_ff G) e osp jB jC (ae_DOC E) i sv) kx K gp e (i + 1)) ->
  k + 2 + DMP_PJ_CW * (e - (i + 1)) + 2 <= kx ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
               F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT GOK AI0 facts facts2.
  intros until m. intros GI FRM I0 IE EN CV TI KB KX HC HL KBL. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof facts2 as (LO2 & OSP & OSM).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & FSZ) & _).
  assert (SVZ : cells_size sv = 104%nat) by (unfold pj_frD in FSZ; rewrite cells_size_app in FSZ; cbn [cells_size csize Nat.add] in FSZ; lia).
  destruct (pj_frD_80 _ _ _ _ _ _ _ _ _ _ FR) as (j80 & F80).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  unfold CNT_MAX in CV.
  assert (TIR : 0 <= T i < 2^64) by (rewrite TI; apply cword_range; unfold t_obj, CNT_MAX; lia).
  assert (TY : ttype (T i) = 123) by (rewrite TI, ttype_cword by (unfold CNT_MAX; lia); reflexivity).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_open1 E 123 (g_q G) (g_ff G) osp i gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 j80 F fc m
                             OK ltac:(clear - I0 IE EN; lia) TIR TY ltac:(right; reflexivity) QLO QH OR AI SHZT F80 MI)|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & F801). apply evt_done.
  destruct (frD_OH m m1 (g_S1 G) jA osp jB (g_ff G) jC (ae_DOC E) i sv FR MU1 F801) as (j0 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & FR1).
  assert (GI1 : PINVA G (pj_frOH j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 osp jB (g_ff G) jC (ae_DOC E) i sv) k Σ m1).
  { apply (PINVA_cw RT AF G GOK _ _ k Σ m m1 _ GI MU1 WM1 MI1); [| exact FR1| apply pj_frOH_size; exact SVZ].
    intros a. destruct (outside_dec [(g_S1 G + 80, g_S1 G + 88)] a) as [O|IN]; [left; exact O| right]. unfold own. cbn [inW] in IN. clear - IN. lia. }
  unfold pjR, pj_open_ret, pj_open_lit. cbn [Z.eqb Pos.eqb].
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K _ 1 2 1%nat); [exact PUT| exact GI1| unfold DMP_LIT_LBRC_A; acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| unfold DMP_LIT_LBRC_A; lia| unfold DMP_LIT_LBRC_A, SEGTOP_A; lia| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even 0xaefb4) by lia.

  pose proof GI2 as (HA2 & MI2 & _ & _ & _ & _ & ST2 & _ & _ & _ & _ & (FR2 & _) & _).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI2) as (SHZT2 & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI2) as AI2.
  unfold pj_frOH in FR2. pose proof FR2 as FH2. apply rw_cells_app in FH2. destruct FH2 as [FH2 _].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ohead2 E (g_q G) (g_ff G) osp i e cv j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 jB jC
                             gp (wz 0xaefb4) e1 e2 e3 e4 e5 e6 e7 s6 s8 s9 s11 u0 u1 u2 u3 u4 u5 u6 F2 fc m2
                             OK I0 IE EN NR CV TI QLO LO2 QH OSP OSM F0 FH SFH AI2 (af_client_consts RT AF Σ2 m2 HA2) ST2 SHZT2 FH2 MI2)|].
  cbv beta. intros ms3 (m3 & rax & a0x & a1x & a2x & a3x & a4x & s2x & s10x & MU3 & WM3 & MI3 & ST3 & POST). apply evt_done.
  destruct POST as [(EQ & -> & FH3)|(NE & -> & FH3)].
  - assert (FR3 : rw_cells bsegs m3 (g_S1 G) (pj_frOE j0 j8 j16 j24 j32 j40 j48 j56 e osp jB (g_ff G) jC (ae_DOC E) i sv)).
    { unfold pj_frOE. refine (fr_join152 m2 m3 (g_S1 G) _ _ sv _ _ _ FR2 MU3 _ FH3); [reflexivity| reflexivity|].
      intros x Hx. rewrite SVZ in Hx. cbn [outside]. repeat split; try exact I; lia. }
    assert (GI3 : PINVA G (pj_frOE j0 j8 j16 j24 j32 j40 j48 j56 e osp jB (g_ff G) jC (ae_DOC E) i sv) (k + 2) Σ2 m3).
    { apply (PINVA_cwB RT AF G GOK _ _ (k + 2) Σ2 m2 m3 _ GI2 MU3 WM3 MI3); [| exact ST3| exact FR3| apply pj_frOE_size; exact SVZ].
      intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end.
      unfold ownB. cbn [inW] in IN. clear - IN LO2. lia. }
    unfold KCLOSEA in HC. eapply (HC j0 j8 j16 j24 j32 j40 j48 j56); [exact GI3| exact FRM| clear - KBL EQ; unfold DMP_PJ_CW in KBL; lia].
  - assert (FR3 : rw_cells bsegs m3 (g_S1 G) (pj_frOL E (g_ff G) e osp jB jC (ae_DOC E) i sv)).
    { unfold pj_frOL. refine (fr_join152 m2 m3 (g_S1 G) _ _ sv _ _ _ FR2 MU3 _ FH3); [reflexivity| apply pj_frOL_pre_size|].
      intros x Hx. rewrite SVZ in Hx. cbn [outside]. repeat split; try exact I; lia. }
    assert (GI3 : PINVA G (pj_frOL E (g_ff G) e osp jB jC (ae_DOC E) i sv) (k + 2) Σ2 m3).
    { apply (PINVA_cwB RT AF G GOK _ _ (k + 2) Σ2 m2 m3 _ GI2 MU3 WM3 MI3); [| exact ST3| exact FR3| apply pj_frOL_size; exact SVZ].
      intros a. match goal with |- outside ?W _ \/ _ => destruct (outside_dec W a) as [O|IN]; [left; exact O| right] end.
      unfold ownB. cbn [inW] in IN. clear - IN LO2. lia. }
    unfold KOLOOPA, OLSA in HL. eapply (HL NE); [exact GI3| exact FRM| clear - KBL; lia].
Qed.

Lemma po_step : forall (jB jC : list byte) (sv : list cell) (i k kx : Z) (Σ : rts RT) (K : config -> Prop) (e kk b : Z)
    (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let fcs := pj_frOL E (g_ff G) e osp jB jC (ae_DOC E) i sv in
  PINVA G fcs k Σ m -> frm0 fc -> is_str T S sn kk -> elem T S sn ck_any d' (kk + 1) b -> 0 <= kk -> b <= e -> e + 1 <= n ->
  k + 6 + pj_costE (kk + 1) b <= kx -> kx <= g_cr G ->
  (b <> e -> KOLOOPA fcs kx K gp e b) -> KLOOPXA fcs kx K gp ->
  k + 6 + pj_costE (kk + 1) b + DMP_PJ_CW * (e - b) + 2 <= kx ->
  aevt Σ K (OLSA kk gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 F fc m).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts facts2.
  intros until m. cbv zeta. intros GI FRM STR EL K0 BE EN KB KX HL HC KBL. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  pose proof facts2 as (LO2 & OSP & OSM).
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  assert (CE : 0 <= pj_costE (kk + 1) b) by (unfold pj_costE, DMP_PJ_CW; clear - IJ; lia).
  assert (ER : 0 <= e < 2^63) by (clear - K0 IJ BE EN NR; lia).
  destruct (is_str_read _ _ _ (proj2 SNR) _ STR) as [KT (l & SA)].
  assert (TIR : 0 <= T kk < 2^64).
  { destruct STR as (o0 & l0 & X & SA0). rewrite X. apply tword_range; [unfold t_str; lia| pose proof (str_at_bounds _ _ (proj2 SNR) _ _ SA0); lia]. }
  assert (HWL : forall a, outside [(g_q G - 272, g_q G - 256)] a \/ g_lo G <= a < g_S1 G).
  { intros a. destruct (outside_dec [(g_q G - 272, g_q G - 256)] a) as [O|IN]; [left; exact O| right; cbn [inW] in IN; clear - IN LO2; lia]. }
  pose proof GI as (HA & MI & _ & _ & _ & _ & ST & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frOL_of _ _ _ _ _ _ _ _ _ _ _ FR) as FO.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & SHZS & SHZD). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI. unfold OLSA.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_okey1 E (g_q G) (g_ff G) osp e kk (tval (T kk)) l gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 F fc m
                             OK ltac:(clear - K0 IJ BE EN; lia) NR TIR eq_refl SA QLO LO2 QH AI (af_client_consts RT AF Σ m HA) ST SHZT SHZS SHZD FO MI)|].
  cbv beta. intros ms1 (m1 & a3x & a4x & MU1 & WM1 & MI1 & ST1 & ->). apply evt_done.
  pose proof (PINVA_lowB RT AF G GOK _ k Σ m m1 _ GI MU1 WM1 MI1 ST1 HWL) as GI1.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K _ 1 2 1%nat); [exact PUT| exact GI1| unfold DMP_LIT_QUOT_A; acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| unfold DMP_LIT_QUOT_A; lia| unfold DMP_LIT_QUOT_A, SEGTOP_A; lia| clear - KB KX CE; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even 0xaf810) by lia. pose proof GI2 as (_ & MI2 & _).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_okey2 E (g_q G) (g_ff G) kk (tval (T kk)) l gp (wz 0xaf810) (wz osp) e1 e2 e3 e4 e5 e6 e7 (wz (ae_DOC E + 8))
                             u0 u1 u2 u3 u4 u5 u6 F2 fc m2 OK SA MI2)|].
  cbv beta. intros ms3 (s3x & s4x & s7x & ->). apply evt_done.
  eapply (p_put_live RT AF PMc FDO MST G GOK _ (k + 2) Σ2 K (tval (T kk)) l); [exact PUT| exact GI2| exact AI0| exact SA| clear - KB KX CE; lia|].
  intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 m4 GI4. rewrite (ret_pc_even 0xaf830) by lia.
  pose proof GI4 as (_ & MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR4 & _) & _). pose proof (pj_frOL_of _ _ _ _ _ _ _ _ _ _ _ FR4) as FO4.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_okey3 E (g_q G) (g_ff G) osp e kk gp (wz 0xaf830) (wz osp) c1 c2 c3 c4 c5 c6 c7 s3x s4x s7x (wz (ae_DOC E + 8))
                             (wz (ae_S E (tval (T kk)))) (wz (ae_SBUF E + tval (T kk) + 4)) v0 v1 v2 v3 v4 v5 v6 F4 fc m4 QLO QH FO4 MI4)|].
  cbv beta. intros ms5 ->. apply evt_done.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ (k + 2 + 2) Σ4 K _ 3 4 3%nat); [exact PUT| exact GI4| unfold DMP_LIT_QCOL_A; acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| unfold DMP_LIT_QCOL_A; lia| unfold DMP_LIT_QCOL_A, SEGTOP_A; lia| clear - KB KX CE; lia|].
  intros Σ6 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F6 m6 GI6. rewrite (ret_pc_even 0xaf83c) by lia.
  pose proof GI6 as (_ & MI6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR6 & _) & _). pose proof (pj_frOL_of _ _ _ _ _ _ _ _ _ _ _ FR6) as FO6.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ochild E (g_q G) (g_ff G) osp e kk gp (wz 0xaf83c) (wz osp) g1 g2 g3 g4 g5 g6 g7 s3x s4x s7x (wz (ae_DOC E + 8))
                             (wz (ae_S E (tval (T kk)))) (wz (ae_SBUF E + tval (T kk) + 4)) w0 w1 w2 w3 w4 w5 w6 F6 fc m6
                             QLO QH K0 ltac:(clear - K0 IJ BE EN NR; lia) FO6 MI6)|].
  cbv beta. intros ms7 ->. apply evt_done.
  eapply (p_child RT AF PMc FDO MST G GOK d' _ (k + 2 + 2 + 2) Σ6 K (kk + 1) b); [exact PJ| exact GI6| exact AI0| exact IOS0| exact FRM| exact EL| clear - K0; lia| clear - BE EN; lia| exact GD| clear - KB KX; lia|].
  intros Σ8 x0 x1 x2 h0 h1 h2 h3 h4 h5 h6 h7 x3 x4 x5 x6 F8 fc8 m8 GI8 FRM8. rewrite (ret_pc_even 0xaf854) by lia.
  pose proof GI8 as (HA8 & MI8 & _ & _ & _ & _ & ST8 & _ & _ & _ & _ & (FR8 & _) & _). pose proof (pj_frOL_of _ _ _ _ _ _ _ _ _ _ _ FR8) as FO8.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI8) as (SHZT8 & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI8) as AI8.
  pose proof (elem_kindA _ _ _ _ _ _ EL) as KIND.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_ostep E (g_q G) (g_ff G) osp e kk b gp (wz 0xaf854) h0 h1 h2 h3 h4 h5 h6 h7 s3x s4x (wz (ae_S E (tval (T kk))))
                             x0 x1 x2 x3 x4 x5 x6 F8 fc8 m8
                             OK K0 IJ ltac:(clear - BE EN; lia) NR KIND QLO LO2 QH AI8 (af_client_consts RT AF Σ8 m8 HA8) ST8 SHZT8 FO8 MI8)|].
  cbv beta. intros ms9 (m9 & rbx & b0x & b1x & b2x & b3x & b4x & MU9 & WM9 & MI9 & ST9 & ->). apply evt_done.
  pose proof (PINVA_lowB RT AF G GOK _ _ Σ8 m8 m9 _ GI8 MU9 WM9 MI9 ST9 HWL) as GI9.
  pose proof GI9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR9 & _) & _). pose proof (pj_frOL_of _ _ _ _ _ _ _ _ _ _ _ FR9) as FO9.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_otest E (g_q G) (g_ff G) osp e b gp rbx b0x b1x b2x b3x b4x h5 h6 h7 s4x (wz (ae_DOC E + 8)) (wz (kk + 1))
                             x0 x1 x2 x3 x4 x5 x6 F8 fc8 m9 QLO QH ltac:(clear - K0 IJ BE EN NR; lia) ER FO9 MI9)|].
  cbv beta. intros ms10 POST. apply evt_done.
  destruct POST as [(BNE & ->)|(BE0 & ->)].
  - unfold KOLOOPA, OLSA in HL. eapply (HL BNE); [exact GI9| exact FRM8| clear - KBL; lia].
  - unfold pjRO. eapply HC; [exact GI9| exact FRM8| clear - KBL BE0 CE; lia].
Qed.

Lemma po_loop : forall (jB jC : list byte) (sv : list cell) (kx : Z) (K : config -> Prop) (gp : word) (i e c kk : Z),
  let fcs := pj_frOL E (g_ff G) e osp jB jC (ae_DOC E) i sv in
  tiles (field T S sn (elem T S sn ck_any d')) kk e c -> kk <> e -> 0 <= kk -> e + 1 <= n -> kx <= g_cr G ->
  KLOOPXA fcs kx K gp -> KOLOOPA fcs kx K gp e kk.
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts facts2.
  intros jB jC sv kx K gp i e c kk. cbv zeta. intros HT. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR & FH & SFH & LOS).
  induction HT as [k0|k0 b0 e0 c0 FL HT' IH]; intros NE K0 EN KX HC; [congruence|].
  unfold KOLOOPA. intros until fc. intros GI FRM KB.
  destruct FL as [STR EL]. pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
  pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ HT') as [BE _].
  eapply (po_step jB jC sv i _ kx); [exact GI| exact FRM| exact STR| exact EL| exact K0| exact BE| exact EN| unfold pj_costE, DMP_PJ_CW in *; clear - KB IJ BE; lia| exact KX| | exact HC
    | unfold pj_costE, DMP_PJ_CW in *; clear - KB IJ BE; lia].
  intros BNE. unfold KOLOOPA, OLSA in IH |- *. intros. eapply IH; [exact BNE| clear - K0 IJ; lia| exact EN| exact KX| exact HC| eassumption| eassumption| eassumption].
Qed.

Lemma pj_obj_caseA : forall (jA jB jC : list byte) (sv : list cell) (kx : Z) (Σ : rts RT) (K : config -> Prop) (i e c cv : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA osp jB (g_ff G) jC (ae_DOC E) i sv) 1 Σ m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX ->
  T i = cword t_obj (e + 1) cv -> tiles (field T S sn (elem T S sn ck_any d')) (i + 1) e c ->
  pj_costE i (e + 1) <= kx -> kx <= g_cr G ->
  (forall LC, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
               F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT GOK AI0 IOS0 GD PJ facts facts2.
  intros until m. intros GI FRM I0 IE EN CV TI HT KB KX HKX.
  eapply (po_head jA jB jC sv 1 kx Σ K i e cv); [exact GI| exact FRM| exact I0| exact IE| exact EN| exact CV| exact TI| unfold pj_costE, DMP_PJ_CW in KB; clear - KB IE; lia| exact KX
    | | | unfold pj_costE, DMP_PJ_CW in *; clear - KB IE; lia].
  - intros j0 j8 j16 j24 j32 j40 j48 j56. apply pa_close; [right; reflexivity| intros mx H; eapply pj_frOE_88; exact H| exact KX|].
    unfold pj_frOE. apply HKX. reflexivity.
  - intros NE. eapply (po_loop jB jC sv kx K gp i e c (i + 1)); [exact HT| exact NE| clear - I0; lia| exact EN| exact KX|].
    apply (pa_xclose _ kx K gp DMP_LIT_RBRC_A); [right; reflexivity| intros mx H; eapply pj_frOL_0; exact H
      | intros mx H; eapply pj_frOL_88; exact H| exact KX|].
    unfold pj_frOL. apply HKX. apply pj_frOL_pre_size.
Qed.

End Loops.
