(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/CJ/RL/GX/G_sn_write.v, with its module paths and numbers changed; 237 of its 432 lines of code are new or changed and 255 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import G_memcpy G_fwritex.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.StoreCache.StoreFast.
Import ListNotations.
Open Scope bv_scope.

Definition sn_write_prog (B B_memcpy : Z) : RStep.ptree :=
PNode 120%Z
    (PNode 40%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 0 2 2 4032 4
          (PJ_Store_SZ8_nnn 4 2 1 56 4
          (PJ_Store_SZ8_nnn 8 2 8 48 4
          (PJ_Store_SZ8_nnn 12 2 9 40 4
          (PJ_Store_SZ8_nnn 16 2 18 32 4
          (PJ_Store_SZ8_nnn 20 2 19 24 4
          (PJ_Store_SZ8_nnn 24 2 20 16 4
          (PJ_Store_SZ8_nnn 28 2 21 8 4
          (PJ_OpImm_ALU_ADD_nnn 32 8 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 36 18 11 0 4 nil)))))))))))
      (PNode 80%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 40 9 10 0 4
            (PJ_Load_SZ8_true_nnn 44 21 10 152 4
            (PJ_Load_SZ8_true_nnn 48 10 10 40 4
            (PJ_Load_SZ8_true_nnn 52 11 9 56 4
            (PJ_Load_SZ8_true_nnn 56 19 21 8 4
            (PJ_Op_ALU_SUB_nnn 60 10 10 11 4
            (PJ_OpImm_ALU_ADD_nnn 64 20 19 0 4
            (PJ_Branch_BC_LTU_nnn 68 19 10 8 4
            (PJ_OpImm_ALU_ADD_nnn 72 20 10 0 4
            (PJ_Load_SZ8_true_nnn 76 10 21 0 4 nil)))))))))))
        (PLeaf
            (PJ_Branch_BC_EQ_nnn 80 20 0 36 4
            (PJ_OpImm_ALU_ADD_nnn 84 12 20 0 4
            (PJ_Jal_nt 88 1 (jimm21 (B_memcpy - (B + 88))) 4
            (PJ_Load_SZ8_true_nnn 92 10 21 0 4
            (PJ_Load_SZ8_true_nnn 96 11 21 8 4
            (PJ_Op_ALU_ADD_nnn 100 10 10 20 4
            (PJ_Op_ALU_SUB_nnn 104 19 11 20 4
            (PJ_Store_SZ8_nnn 108 21 10 0 4
            (PJ_Store_SZ8_nnn 112 21 19 8 4
            (PJ_Branch_BC_LTU_nnn 116 19 8 8 4 nil)))))))))))))
    (PNode 160%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 120 19 8 0 4
          (PJ_Branch_BC_EQ_nnn 124 19 0 40 4
          (PJ_OpImm_ALU_ADD_nnn 128 11 18 0 4
          (PJ_OpImm_ALU_ADD_nnn 132 12 19 0 4
          (PJ_Jal_nt 136 1 (jimm21 (B_memcpy - (B + 136))) 4
          (PJ_Load_SZ8_true_nnn 140 10 21 0 4
          (PJ_Load_SZ8_true_nnn 144 11 21 8 4
          (PJ_Op_ALU_ADD_nnn 148 10 10 19 4
          (PJ_Op_ALU_SUB_nnn 152 11 11 19 4
          (PJ_Store_SZ8_nnn 156 21 10 0 4 nil)))))))))))
      (PNode 200%Z
        (PLeaf
            (PJ_Store_SZ8_nnn 160 21 11 8 4
            (PJ_Store_SZ1_nnn 164 10 0 0 4
            (PJ_Load_SZ8_true_nnn 168 10 9 88 4
            (PJ_Store_SZ8_nnn 172 9 10 40 4
            (PJ_Store_SZ8_nnn 176 9 10 56 4
            (PJ_OpImm_ALU_ADD_nnn 180 10 8 0 4
            (PJ_Load_SZ8_true_nnn 184 1 2 56 4
            (PJ_Load_SZ8_true_nnn 188 8 2 48 4
            (PJ_Load_SZ8_true_nnn 192 9 2 40 4
            (PJ_Load_SZ8_true_nnn 196 18 2 32 4 nil)))))))))))
        (PLeaf
            (PJ_Load_SZ8_true_nnn 200 19 2 24 4
            (PJ_Load_SZ8_true_nnn 204 20 2 16 4
            (PJ_Load_SZ8_true_nnn 208 21 2 8 4
            (PJ_OpImm_ALU_ADD_nnn 212 2 2 64 4
            (PJ_Jalr_nnn 216 0 1 0 4 nil)))))))).

Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_sn_write (IMG : RImg) := sn_write_prog (sym 0x7f000300) (sym 0x21334).
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Open Scope Z_scope.

Definition sn_k (cn : Z) (pend src : list byte) : Z := Z.min cn (Z.of_nat (length pend + length src)).

Lemma rw_CB_len : forall segs m a n (l : list byte), rw_cells segs m a [CB n l] -> length l = n.
Proof. intros segs m a n l [[[H _] _] _]. exact H. Qed.

Lemma rw_CB_split : forall segs m a (n1 n2 : nat) (l : list byte),
  rw_cells segs m a [CB (n1 + n2) l] ->
  rw_cells segs m a [CB n1 (firstn n1 l)] /\ rw_cells segs m (a + Z.of_nat n1)%Z [CB n2 (skipn n1 l)].
Proof.
  intros segs m a n1 n2 l H. pose proof (rw_CB_len _ _ _ _ _ H) as HL.
  apply (rw_cells_split_CB segs m a [] (n1 + n2) l [] [n1; n2]) in H; [ | cbn; lia ].
  cbn [mk_CB_cells app] in H.
  apply (proj1 (rw_cells_app segs m a [_] _)) in H. destruct H as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2.
  rewrite firstn_all2 in H2 by (rewrite length_skipn; lia). split; assumption.
Qed.

Lemma rw_CB_join : forall segs m a (n1 n2 : nat) (l1 l2 : list byte),
  rw_cells segs m a [CB n1 l1] -> rw_cells segs m (a + Z.of_nat n1)%Z [CB n2 l2] ->
  rw_cells segs m a [CB (n1 + n2) (l1 ++ l2)].
Proof.
  intros segs m a n1 n2 l1 l2 H1 H2.
  assert (J : rw_cells segs m a ([] ++ [CB n1 l1; CB n2 l2] ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app segs m a [_] _)). split; [exact H1|].
    cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J.
  rewrite Nat.add_0_r, app_nil_r in J. exact J.
Qed.

Lemma rw_CB_nil : forall segs m a, (0 <= a <= 2^64)%Z -> rw_cells segs m a [CB 0 []].
Proof.
  intros segs m a Ha. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact Ha.
  - cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Local Ltac wtac := first [ reflexivity | f_equal; rewrite ?land_W64_small by lia; lia ].

Local Ltac cont20 v pc' H :=
  lazymatch goal with |- evt ?sg ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F' _ ?fc' ?rv ?mm ?ro) =>
    assert (H : evt sg Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 v x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F' pc' fc' rv mm ro))
  end.
Local Ltac cont19 v pc' H :=
  lazymatch goal with |- evt ?sg ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F' _ ?fc' ?rv ?mm ?ro) =>
    assert (H : evt sg Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 v x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F' pc' fc' rv mm ro))
  end.
Local Ltac setreg10 v :=
  lazymatch goal with |- evt ?sg ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F' ?pc ?fc' ?rv ?mm ?ro) =>
    replace (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      by (f_equal; wtac)
  end.
Local Ltac setreg19 v :=
  lazymatch goal with |- evt ?sg ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F' ?pc ?fc' ?rv ?mm ?ro) =>
    replace (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 v x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      by (f_equal; wtac)
  end.
Local Ltac zcond K := zify_cond K; try (rewrite ?unsigned_lit in K by lia); try (rewrite ?land_W64_small in K by lia).
Lemma sn_bytes : forall (pend src dst : list byte) (c k1n k2n : nat) (z : byte),
  k1n = Nat.min c (length pend) -> k2n = Nat.min (c - k1n) (length src) -> (k1n + k2n < length dst)%nat ->
  firstn k1n pend ++ firstn k2n src ++ upd (skipn k2n (skipn k1n dst)) 0 z
  = firstn c (pend ++ src) ++ z :: skipn (S (k1n + k2n)) dst.
Proof.
  intros pend src dst c k1n k2n z E1 E2 HL.
  rewrite firstn_app.
  assert (A1 : firstn k1n pend = firstn c pend).
  { subst k1n. destruct (Nat.le_ge_cases c (length pend)).
    - rewrite Nat.min_l by lia. reflexivity.
    - rewrite Nat.min_r by lia. rewrite !firstn_all2 by lia. reflexivity. }
  assert (A2 : firstn k2n src = firstn (c - length pend) src).
  { subst k2n k1n. destruct (Nat.le_ge_cases c (length pend)).
    - replace (c - Nat.min c (length pend))%nat with 0%nat by lia. replace (c - length pend)%nat with 0%nat by lia.
      reflexivity.
    - replace (c - Nat.min c (length pend))%nat with (c - length pend)%nat by lia.
      destruct (Nat.le_ge_cases (c - length pend) (length src)).
      + rewrite Nat.min_l by lia. reflexivity.
      + rewrite Nat.min_r by lia. rewrite !firstn_all2 by lia. reflexivity. }
  rewrite A1, A2, <- app_assoc. f_equal. f_equal.
  rewrite upd_firstn_skipn by (rewrite !length_skipn; lia).
  rewrite firstn_O, app_nil_l, !skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma le1_z0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Definition hid (P : Prop) : Prop := P.
Local Ltac hide_h H := let T := type of H in change T with (hid T) in H.
Local Ltac unhide_h H := unfold hid in H.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_sn_write : CodeAtT img_segs (sym 0x7f000300) (PROGAT_CODE_sn_write IMG)}.
  Context {RB_sn_write : RelCode (sym 0x7f000300) 220}.
  Context {RN_B_memcpy_7f000300 : RelNear (sym 0x7f000300) (sym 0x21334)}.
  Context {SPEC_memcpy : memcpy_contract}.
  Collection ImgHyps := IMG CODE_sn_write RB_sn_write RN_B_memcpy_7f000300 SPEC_memcpy.

Definition memcpy_postk (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (Dst : Z) (n : nat) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(Dst, Dst + Z.of_nat n)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' Dst [CB n src].

Lemma memcpy_callk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src : Z) (n : nat) (src junk : list byte),
  bv_unsigned a0 = Dst -> bv_unsigned a1 = Src -> bv_unsigned a2 = Z.of_nat n ->
  bytes_at img_segs m Src src -> length src = n ->
  rw_cells img_segs m Dst [CB n junk] ->
  (Src + Z.of_nat n <= Dst \/ Dst + Z.of_nat n <= Src)%Z ->
  mem_inv img_segs m ->
  evt img_segs (memcpy_postk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 Dst n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros HD HS HN SRC LEN DST SEP MI. subst Dst Src.
  eapply evt_mono.
  { eapply (SPEC_memcpy ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
      rewrite ?HN, ?Nat2Z.id; [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. unfold memcpy_postk. rewrite HN, Nat2Z.id in P.
  destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & DC & _).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'. tauto.
Qed.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f bufp CK cs cn : Z) (pend src dst : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length src))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (f + 40, f + 48); (f + 56, f + 64); (CK, CK + 16);
              (cs, cs + Z.of_nat (length dst))]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 64) (bv_unsigned sp)
    /\ rw_cells img_segs m' (f + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells img_segs m' (f + 56) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells img_segs m' CK [C8 (Z_to_bv 64 (cs + sn_k cn pend src)); C8 (Z_to_bv 64 (cn - sn_k cn pend src))]
    /\ rw_cells img_segs m' cs [CB (length dst) (firstn (Z.to_nat cn) (pend ++ src) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (sn_k cn pend src))) dst)].

Definition sn_write_contract : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (f WB bufp CK cs cn : Z) (pend src dst : list byte),
  a0 = Z_to_bv 64 f ->
  bytes_at img_segs m (bv_unsigned a1) src ->
  bv_unsigned a2 = Z.of_nat (length src) ->
  rw_cells img_segs m (f + 40) [C8 (Z_to_bv 64 (WB + Z.of_nat (length pend)))] ->
  rw_cells img_segs m (f + 56) [C8 (Z_to_bv 64 WB)] ->
  rw_cells img_segs m (f + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells img_segs m (f + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells img_segs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)] ->
  bytes_at img_segs m WB pend -> (WB + Z.of_nat (length pend) < 2^64)%Z ->
  rw_cells img_segs m cs [CB (length dst) dst] ->
  (0 <= cn < 2^64)%Z -> (sn_k cn pend src < Z.of_nat (length dst))%Z ->
  stk img_segs m (bv_unsigned sp - 64) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z ->
  mem_inv img_segs m ->
  (f + 160 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= f + 40)%Z ->
  (CK + 16 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= CK)%Z ->
  (cs + Z.of_nat (length dst) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= cs)%Z ->
  (WB + Z.of_nat (length pend) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= WB)%Z ->
  (bv_unsigned a1 + Z.of_nat (length src) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (CK + 16 <= f + 40 \/ f + 160 <= CK)%Z ->
  (cs + Z.of_nat (length dst) <= f + 40 \/ f + 160 <= cs)%Z ->
  (cs + Z.of_nat (length dst) <= CK \/ CK + 16 <= cs)%Z ->
  (WB + Z.of_nat (length pend) <= cs \/ cs + Z.of_nat (length dst) <= WB)%Z ->
  (bv_unsigned a1 + Z.of_nat (length src) <= cs \/ cs + Z.of_nat (length dst) <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + Z.of_nat (length src) <= CK \/ CK + 16 <= bv_unsigned a1)%Z ->
  evt img_segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f bufp CK cs cn pend src dst m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000300)) fc None m (seg_rom img_segs)).


Lemma sn_write_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (f WB bufp CK cs cn : Z) (pend src dst : list byte),
  a0 = Z_to_bv 64 f ->
  bytes_at img_segs m (bv_unsigned a1) src ->
  bv_unsigned a2 = Z.of_nat (length src) ->
  rw_cells img_segs m (f + 40) [C8 (Z_to_bv 64 (WB + Z.of_nat (length pend)))] ->
  rw_cells img_segs m (f + 56) [C8 (Z_to_bv 64 WB)] ->
  rw_cells img_segs m (f + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells img_segs m (f + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells img_segs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)] ->
  bytes_at img_segs m WB pend -> (WB + Z.of_nat (length pend) < 2^64)%Z ->
  rw_cells img_segs m cs [CB (length dst) dst] ->
  (0 <= cn < 2^64)%Z -> (sn_k cn pend src < Z.of_nat (length dst))%Z ->
  stk img_segs m (bv_unsigned sp - 64) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z ->
  mem_inv img_segs m ->
  (f + 160 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= f + 40)%Z ->
  (CK + 16 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= CK)%Z ->
  (cs + Z.of_nat (length dst) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= cs)%Z ->
  (WB + Z.of_nat (length pend) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= WB)%Z ->
  (bv_unsigned a1 + Z.of_nat (length src) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (CK + 16 <= f + 40 \/ f + 160 <= CK)%Z ->
  (cs + Z.of_nat (length dst) <= f + 40 \/ f + 160 <= cs)%Z ->
  (cs + Z.of_nat (length dst) <= CK \/ CK + 16 <= cs)%Z ->
  (WB + Z.of_nat (length pend) <= cs \/ cs + Z.of_nat (length dst) <= WB)%Z ->
  (bv_unsigned a1 + Z.of_nat (length src) <= cs \/ cs + Z.of_nat (length dst) <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + Z.of_nat (length src) <= CK \/ CK + 16 <= bv_unsigned a1)%Z ->
  evt img_segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f bufp CK cs cn pend src dst m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000300)) fc None m (seg_rom img_segs)).
Proof.
  intros until dst. intros -> SRC LEN WPOS WBASE BUF COOKIE CKC PEND PHI DST HCN HK ST SPLO MI
    S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11.
  assert (EA2 : a2 = Z_to_bv 64 (Z.of_nat (length src))) by (rewrite <- LEN; symmetry; apply Z_to_bv_bv_unsigned).
  subst a2. clear LEN.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB. rewrite Nat.add_0_r in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (rw_cells_bound _ _ _ _ WPOS) as FB2. cbn [cells_size csize Nat.add] in FB2.
  pose proof (bytes_at_bound _ _ _ _ PEND) as PB. pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (f + 40, f + 48); (f + 56, f + 64); (CK, CK + 16);
                          (cs, cs + Z.of_nat (length dst))]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat ST.
  do 8 zstep.
  do 3 zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  setreg10 (Z_to_bv 64 (Z.of_nat (length pend))).
  pose (k1 := Z.min cn (Z.of_nat (length pend))). assert (Ek1 : k1 = Z.min cn (Z.of_nat (length pend))) by reflexivity. clearbody k1.
  pose (k2 := Z.min (cn - k1) (Z.of_nat (length src))). assert (Ek2 : k2 = Z.min (cn - k1) (Z.of_nat (length src))) by reflexivity. clearbody k2.
  assert (Hk1 : 0 <= k1 <= cn /\ k1 <= Z.of_nat (length pend)) by lia.
  assert (Hk2 : 0 <= k2 <= cn - k1 /\ k2 <= Z.of_nat (length src)) by lia.
  assert (Hk : sn_k cn pend src = k1 + k2) by (unfold sn_k; rewrite Nat2Z.inj_add; lia).
  rewrite Hk in HK.
  hide_h Ek1. hide_h Ek2. hide_h Hk.
  cont20 (Z_to_bv 64 k1) (Z_to_bv 64 (sym 0x7f000300 + 76)) C76.
  2:{ zstep. if_cases K0; zcond K0; unhide_h Ek1.
      - replace (Z_to_bv 64 k1) with (Z_to_bv 64 cn) in C76 by (f_equal; lia). exact C76.
      - zstep. replace (Z_to_bv 64 k1) with (Z_to_bv 64 (Z.of_nat (length pend))) in C76 by (f_equal; lia). exact C76. }
  zstep. zstep. if_cases K1; zcond K1.
  all: remember (Z.to_nat k1) as k1n eqn:Ek1n; assert (Hk1n : Z.of_nat k1n = k1) by lia; hide_h Ek1n;
       remember (length dst - k1n)%nat as r1 eqn:Er1; assert (Hr1 : (k1n + r1 = length dst)%nat) by lia; hide_h Er1.
  1: (assert (E0 : k1n = 0%nat) by lia;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (DA : rw_cells img_segs mm cs [CB k1n (firstn k1n pend)]) by (rewrite E0; cbn [firstn]; apply rw_CB_nil; lia);
        assert (DB0 : rw_cells img_segs mm (cs + Z.of_nat k1n) [CB r1 (skipn k1n dst)])
          by (rewrite E0; cbn [skipn Z.of_nat]; rewrite Z.add_0_r; replace r1 with (length dst) by lia; exact DST)
      end;
      clear DST;
      setreg10 (Z_to_bv 64 (cs + k1)); setreg19 (Z_to_bv 64 (cn - k1));
      replace (Z_to_bv 64 cs) with (Z_to_bv 64 (cs + k1)) in CKC by (f_equal; lia);
      replace (Z_to_bv 64 cn) with (Z_to_bv 64 (cn - k1)) in CKC by (f_equal; lia)).
  2: (pose proof PEND as PA; rewrite <- (firstn_skipn k1n pend) in PA;
      apply (proj1 (bytes_at_app _ _ _ _ _)) in PA; destruct PA as [PA _];
      assert (LPA : length (firstn k1n pend) = k1n) by (rewrite length_firstn; lia);
      replace (length dst) with (k1n + r1)%nat in DST at 1 by lia;
      apply rw_CB_split in DST; destruct DST as [DA0 DB0];
      zstep; zstep;
      lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply (memcpy_callk) with (Dst := cs) (Src := WB) (n := k1n) (src := firstn k1n pend);
          [ rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit by lia; lia
          | exact PA | exact LPA | exact DA0 | lia | assumption ]
        | post_call sg mm ]
      end;
      match goal with H : rw_cells _ _ cs [CB k1n (firstn k1n pend)] |- _ => rename H into DA end;
      zstep; zstep; zstep; zstep; zstep; zstep;
      setreg10 (Z_to_bv 64 (cs + k1)); setreg19 (Z_to_bv 64 (cn - k1));
      lazymatch type of CKC with rw_cells _ _ _ [C8 ?v1; C8 ?v2] =>
        replace v1 with (Z_to_bv 64 (cs + k1)) in CKC by wtac; replace v2 with (Z_to_bv 64 (cn - k1)) in CKC by wtac end).
  all: cont19 (Z_to_bv 64 k2) (Z_to_bv 64 (sym 0x7f000300 + 124)) C124;
    [ | zstep; if_cases K2; zcond K2; unhide_h Ek2;
        [ replace (Z_to_bv 64 k2) with (Z_to_bv 64 (cn - k1)) in C124 by (f_equal; lia); exact C124
        | zstep; replace (Z_to_bv 64 k2) with (Z_to_bv 64 (Z.of_nat (length src))) in C124 by (f_equal; lia); exact C124 ] ].
  all: zstep; if_cases K3; zcond K3.
  all: remember (Z.to_nat k2) as k2n eqn:Ek2n; assert (Hk2n : Z.of_nat k2n = k2) by lia; hide_h Ek2n;
       remember (r1 - k2n)%nat as r2 eqn:Er2; assert (Hr2 : (k2n + r2 = r1)%nat) by lia; hide_h Er2.
  all: lazymatch type of K3 with
    | _ = 0 => (assert (E0' : k2n = 0%nat) by lia;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (DB1 : rw_cells img_segs mm (cs + Z.of_nat k1n) [CB k2n (firstn k2n src)])
            by (rewrite E0'; cbn [firstn]; apply rw_CB_nil; lia);
          assert (DC : rw_cells img_segs mm (cs + Z.of_nat k1n + Z.of_nat k2n) [CB r2 (skipn k2n (skipn k1n dst))])
            by (rewrite E0'; cbn [skipn Z.of_nat]; rewrite Z.add_0_r; replace r2 with r1 by lia; exact DB0)
        end;
        clear DB0;
        setreg10 (Z_to_bv 64 (cs + k1 + k2));
        replace (Z_to_bv 64 (cs + k1)) with (Z_to_bv 64 (cs + k1 + k2)) in CKC by (f_equal; lia);
        replace (Z_to_bv 64 (cn - k1)) with (Z_to_bv 64 (cn - k1 - k2)) in CKC by (f_equal; lia))
    | _ => (pose proof SRC as SA; rewrite <- (firstn_skipn k2n src) in SA;
        apply (proj1 (bytes_at_app _ _ _ _ _)) in SA; destruct SA as [SA _];
        assert (LSA : length (firstn k2n src) = k2n) by (rewrite length_firstn; lia);
        replace r1 with (k2n + r2)%nat in DB0 by lia;
        apply rw_CB_split in DB0; destruct DB0 as [DB1' DC];
        zstep; zstep; zstep;
        lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_cut;
          [ eapply (memcpy_callk) with (Dst := cs + Z.of_nat k1n) (Src := bv_unsigned a1) (n := k2n) (src := firstn k2n src);
            [ rewrite unsigned_lit by lia; lia | reflexivity | rewrite unsigned_lit by lia; lia
            | exact SA | exact LSA | exact DB1' | lia | assumption ]
          | post_call sg mm ]
        end;
        rename POST into DB1;
        zstep; zstep; zstep; zstep; zstep; zstep;
        setreg10 (Z_to_bv 64 (cs + k1 + k2));
        lazymatch type of CKC with rw_cells _ _ _ [C8 ?v1; C8 ?v2] =>
          replace v1 with (Z_to_bv 64 (cs + k1 + k2)) in CKC by wtac; replace v2 with (Z_to_bv 64 (cn - k1 - k2)) in CKC by wtac end)
    end.
  all: pose proof (rw_CB_len _ _ _ _ _ DC) as LDC; pose proof (u8arr_of_rw_cells _ _ _ _ _ DC) as DCA; clear DC.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         pose proof (u8arr_store_ok img_segs mm (cs + Z.of_nat k1n + Z.of_nat k2n) _ 0 (Z_to_bv 64 (cs + k1 + k2)) DCA
                       ltac:(rewrite LDC; lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
  all: zstep.
  all: rewrite le1_z0.
  all: replace (Z_to_bv 64 (cs + k1 + k2)) with (wa (cs + Z.of_nat k1n + Z.of_nat k2n + 0)) by (unfold wa; f_equal; lia).
  all: pose proof (u8arr_write img_segs _ _ _ 0 (Z_to_bv 8 0) DCA ltac:(rewrite LDC; lia)) as DCA2; clear DCA.
  all: store_done.
  all: pose proof (rw_cells_of_u8arr _ _ _ _ DCA2) as DC; rewrite upd_length, LDC in DC; clear DCA2.
  all: zstep; zstep; zstep; zstep.
  all: do 7 zstep.
  all: zstep; zstep.
  all: release_frame FR ST (bv_unsigned sp).
  all: unhide_h Hk; unhide_h Ek1; unhide_h Ek2; unhide_h Ek1n; unhide_h Ek2n; unhide_h Er1; unhide_h Er2.
  all: apply evt_done; unfold sn_write_post.
  all: do 15 eexists.
  all: split; [ ms_eq | ].
  all: replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia.
  all: split; [ exact MU | ].
  all: split; [ exact WM | ].
  all: split; [ assumption | ].
  all: split; [ exact ST | ].
  all: split; [ exact WPOS | ].
  all: split; [ exact WBASE | ].
  all: split; [ rewrite Hk; replace (cs + (k1 + k2)) with (cs + k1 + k2) by lia;
                replace (cn - (k1 + k2)) with (cn - k1 - k2) by lia; exact CKC | ].
  all: pose proof (rw_CB_join _ _ _ _ _ _ _ DA DB1) as J1;
       replace (cs + Z.of_nat k1n + Z.of_nat k2n) with (cs + Z.of_nat (k1n + k2n)) in DC by lia;
       pose proof (rw_CB_join _ _ _ _ _ _ _ J1 DC) as J2;
       rewrite <- app_assoc in J2;
       change (Z.to_nat 0) with 0%nat in J2;
       rewrite (sn_bytes pend src dst (Z.to_nat cn) k1n k2n (Z_to_bv 8 0)) in J2 by lia;
       replace (length dst) with (k1n + k2n + r2)%nat by lia;
       replace (Z.to_nat (sn_k cn pend src)) with (k1n + k2n)%nat by lia;
       exact J2.
Qed.

Lemma sn_write_contract_ok : sn_write_contract.
Proof. exact sn_write_spec. Qed.


End Img.

Existing Class sn_write_contract.
