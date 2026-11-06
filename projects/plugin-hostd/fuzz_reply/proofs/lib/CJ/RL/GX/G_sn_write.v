(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Port of the released leptonica walk of musl's sn_write to this unit's plain and ubsan images.
   Donors (leptonica fhmtgen_fuzzer proofs):
     projects/leptonica/fhmtgen_fuzzer/proofs/lib/K5/A10/F_sn_write.v   sha256 49c4c8c7825e
     projects/leptonica/fhmtgen_fuzzer/proofs/lib/K5/A10/F_sn_write2.v  sha256 436660f6f07a
   The donors walk the same 55 instructions; they call the sanitizer's memcpy and assume that nothing is cut.
   This file calls the plain memcpy contract of this unit and also covers a cookie count below the pending and
   source lengths (the two min branches of the code). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require Import G_memcpy G_fwritex.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.StoreCache.StoreFast.
Import ListNotations.
Open Scope bv_scope.

(* Program tree of sn_write (220 bytes), as decoded from the image. *)
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

(* Stepping goes through the relocated program tree. *)
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_sn_write (IMG : RImg) := sn_write_prog (sym 0x7f000300) (sym 0x21334).
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.

(* Bytes sn_write copies: the cookie count, capped by what is pending plus what is new. *)
Definition sn_k (cn : Z) (pend src : list byte) : Z := Z.min cn (Z.of_nat (length pend + length src)).

Lemma rw_CB_len : forall (segs : list Segment) (m : word -> option byte) (a : Z) (n : nat) (l : list byte),
  rw_cells segs m a [CB n l] -> length l = n.
Proof. intros segs m a n l [[[Hn _] _] _]. exact Hn. Qed.

Lemma rw_CB_split : forall (segs : list Segment) (m : word -> option byte) (a : Z) (n1 n2 : nat) (l : list byte),
  rw_cells segs m a [CB (n1 + n2) l] ->
  rw_cells segs m a [CB n1 (firstn n1 l)] /\ rw_cells segs m (a + Z.of_nat n1) [CB n2 (skipn n1 l)].
Proof.
  intros segs m a n1 n2 l Hc.
  pose proof (rw_CB_len _ _ _ _ _ Hc) as Hlen.
  apply (rw_cells_split_CB segs m a [] (n1 + n2) l [] [n1; n2]) in Hc; [| cbn; lia].
  cbn [mk_CB_cells app] in Hc.
  apply (proj1 (rw_cells_app segs m a [_] _)) in Hc. destruct Hc as [Hlo Hhi].
  cbn [cells_size csize] in Hhi. rewrite Nat.add_0_r in Hhi.
  rewrite firstn_all2 in Hhi by (rewrite length_skipn; lia).
  split; assumption.
Qed.

Lemma rw_CB_join : forall (segs : list Segment) (m : word -> option byte) (a : Z) (n1 n2 : nat) (l1 l2 : list byte),
  rw_cells segs m a [CB n1 l1] -> rw_cells segs m (a + Z.of_nat n1) [CB n2 l2] ->
  rw_cells segs m a [CB (n1 + n2) (l1 ++ l2)].
Proof.
  intros segs m a n1 n2 l1 l2 Hlo Hhi.
  assert (Hboth : rw_cells segs m a ([] ++ [CB n1 l1; CB n2 l2] ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app segs m a [_] _)). split; [exact Hlo|].
    cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hhi. }
  apply rw_cells_merge in Hboth. cbn [cells_size cells_bytes csize cbytes app] in Hboth.
  rewrite Nat.add_0_r, app_nil_r in Hboth. exact Hboth.
Qed.

Lemma rw_CB_nil : forall (segs : list Segment) (m : word -> option byte) (a : Z),
  0 <= a <= 2 ^ 64 -> rw_cells segs m a [CB 0 []].
Proof.
  intros segs m a Ha. unfold rw_cells, cells_at, bytes_at, wr_at. cbn.
  repeat split; intros; cbn in *; lia.
Qed.

(* The bytes left in the buffer: the copied prefix, then the terminator over the old contents. *)
Lemma sn_bytes : forall (pend src dst : list byte) (c k1n k2n : nat) (z : byte),
  k1n = Nat.min c (length pend) -> k2n = Nat.min (c - k1n) (length src) -> (k1n + k2n < length dst)%nat ->
  firstn k1n pend ++ firstn k2n src ++ upd (skipn k2n (skipn k1n dst)) 0 z
  = firstn c (pend ++ src) ++ z :: skipn (S (k1n + k2n)) dst.
Proof.
  intros pend src dst c k1n k2n z E1 E2 Hroom.
  rewrite firstn_app, <- app_assoc.
  assert (P1 : firstn c pend = firstn k1n pend).
  { destruct (Nat.le_ge_cases c (length pend)) as [Hc|Hc].
    - replace k1n with c by lia. reflexivity.
    - rewrite (firstn_all2 (n := c)) by lia. rewrite (firstn_all2 (n := k1n)) by lia. reflexivity. }
  assert (P2 : firstn (c - length pend) src = firstn k2n src).
  { destruct (Nat.le_ge_cases c (length pend)) as [Hc|Hc].
    - replace (c - length pend)%nat with 0%nat by lia. replace k2n with 0%nat by lia. reflexivity.
    - destruct (Nat.le_ge_cases (c - length pend) (length src)) as [Hs|Hs].
      + replace k2n with (c - length pend)%nat by lia. reflexivity.
      + rewrite (firstn_all2 (n := (c - length pend)%nat)) by lia. rewrite (firstn_all2 (n := k2n)) by lia.
        reflexivity. }
  rewrite P1, P2. f_equal. f_equal.
  rewrite upd_firstn_skipn by (rewrite !length_skipn; lia).
  rewrite firstn_O, app_nil_l, !skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma le1_z0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

(* Identity wrapper: a hypothesis wrapped in it is skipped by the store transport. *)
Definition hid (P : Prop) : Prop := P.

Local Ltac park H := let T := type of H in change (hid T) in H.
Local Ltac park_off_stack H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => park H end.
(* Wrap every memory fact that is not about the stack, before the frame stores. *)
Local Ltac park_heap sp n MUf WMf :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)] m) as MUf;
    pose proof (wmono_refl segs m) as WMf;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => park_off_stack H A sp
    | H : bytes_at segs m ?A _ |- _ => park_off_stack H A sp
    end
  end.
(* Unwrap them and move them past the frame stores in one transport. *)
Local Ltac unpark_heap MUf WMf :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUf with munch _ ?m _ =>
      unfold hid in *; transport_after_call segs m mm MUf WMf; clear MUf WMf end end.

(* The two min computations of the code each end in a two-way branch that meets again one instruction later.
   Cut the walk at the meeting point: the state there is the current one with the min register set to [v]. *)
Local Ltac meet_s4 v :=
  lazymatch goal with
  | |- evt ?sg _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 _
                         ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (if _ then ?pT else _) ?fc ?rv ?mm ?ro) =>
      apply (evt_cut sg (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 v
                                            x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pT fc rv mm ro))
  end.
Local Ltac meet_s3 v :=
  lazymatch goal with
  | |- evt ?sg _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 _ ?x20
                         ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (if _ then ?pT else _) ?fc ?rv ?mm ?ro) =>
      apply (evt_cut sg (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 v x20
                                            x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pT fc rv mm ro))
  end.
(* Case on a branch condition and state it over Z. *)
Local Ltac case_if K := if_cases K; zify_cond K.
(* Call a function whose contract the tactic [t] applies; continue after its return. *)
Local Ltac call_with t :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ t | post_call segs m ] end.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_sn_write : CodeAtT img_segs (sym 0x7f000300) (PROGAT_CODE_sn_write IMG)}.
  Context {RB_sn_write : RelCode (sym 0x7f000300) 220}.
  Context {RN_B_memcpy_7f000300 : RelNear (sym 0x7f000300) (sym 0x21334)}.
  Context {SPEC_memcpy : memcpy_contract}.

(* What the memcpy contract gives, with the destination and length named. *)
Definition memcpy_postk (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (Dst : Z) (n : nat) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(Dst, Dst + Z.of_nat n)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' Dst [CB n src].

Lemma memcpy_callk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Dst Src : Z) (n : nat) (src junk : list byte),
  bv_unsigned a0 = Dst -> bv_unsigned a1 = Src -> bv_unsigned a2 = Z.of_nat n ->
  bytes_at img_segs m Src src -> length src = n -> rw_cells img_segs m Dst [CB n junk] ->
  Src + Z.of_nat n <= Dst \/ Dst + Z.of_nat n <= Src ->
  mem_inv img_segs m ->
  evt img_segs (memcpy_postk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 Dst n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).
Proof using IMG SPEC_memcpy.
  intros until junk. intros Hd Hs Hn Hsrc Hlen Hdst Hsep Hmi. subst Dst Src.
  rewrite <- (Nat2Z.id n), <- Hn in Hdst.
  eapply evt_mono.
  { eapply (SPEC_memcpy ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2); try eassumption.
    - rewrite Hlen, Hn, Nat2Z.id. reflexivity.
    - rewrite Hn. exact Hsep. }
  intros ms' Hpost. unfold memcpy_post in Hpost. unfold memcpy_postk.
  destruct Hpost as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & Hms & Hmu & Hwm & Hmi' & Hcells & _).
  exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, m'.
  rewrite Hn, Nat2Z.id in Hcells. rewrite Hn in Hmu.
  split; [exact Hms|]. split; [exact Hmu|]. split; [exact Hwm|]. split; [exact Hmi'|]. exact Hcells.
Qed.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f bufp CK cs cn : Z) (pend src dst : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length src))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (f + 40, f + 48); (f + 56, f + 64); (CK, CK + 16);
              (cs, cs + Z.of_nat (length dst))] m m'
    /\ wmono img_segs m m'
    /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 64) (bv_unsigned sp)
    /\ rw_cells img_segs m' (f + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells img_segs m' (f + 56) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells img_segs m' CK [C8 (Z_to_bv 64 (cs + sn_k cn pend src)); C8 (Z_to_bv 64 (cn - sn_k cn pend src))]
    /\ rw_cells img_segs m' cs
         [CB (length dst) (firstn (Z.to_nat cn) (pend ++ src) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (sn_k cn pend src))) dst)].

Definition sn_write_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f WB bufp CK cs cn : Z) (pend src dst : list byte),
  a0 = Z_to_bv 64 f ->
  bytes_at img_segs m (bv_unsigned a1) src ->
  bv_unsigned a2 = Z.of_nat (length src) ->
  rw_cells img_segs m (f + 40) [C8 (Z_to_bv 64 (WB + Z.of_nat (length pend)))] ->
  rw_cells img_segs m (f + 56) [C8 (Z_to_bv 64 WB)] ->
  rw_cells img_segs m (f + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells img_segs m (f + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells img_segs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)] ->
  bytes_at img_segs m WB pend ->
  WB + Z.of_nat (length pend) < 2 ^ 64 ->
  rw_cells img_segs m cs [CB (length dst) dst] ->
  0 <= cn < 2 ^ 64 ->
  sn_k cn pend src < Z.of_nat (length dst) ->
  stk img_segs m (bv_unsigned sp - 64) (bv_unsigned sp) ->
  64 <= bv_unsigned sp ->
  mem_inv img_segs m ->
  f + 160 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= f + 40 ->
  CK + 16 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= CK ->
  cs + Z.of_nat (length dst) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= cs ->
  WB + Z.of_nat (length pend) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a1 ->
  CK + 16 <= f + 40 \/ f + 160 <= CK ->
  cs + Z.of_nat (length dst) <= f + 40 \/ f + 160 <= cs ->
  cs + Z.of_nat (length dst) <= CK \/ CK + 16 <= cs ->
  WB + Z.of_nat (length pend) <= cs \/ cs + Z.of_nat (length dst) <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= cs \/ cs + Z.of_nat (length dst) <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat (length src) <= CK \/ CK + 16 <= bv_unsigned a1 ->
  evt img_segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f bufp CK cs cn pend src dst m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000300)) fc None m (seg_rom img_segs)).

(* The walk names its facts: Dlo, Dmid, Dtop are the three parts of the buffer (copied pending bytes, copied
   source bytes, the rest), Hck the cookie, Hsrc the source; X* and Y* are the separation facts. A visible
   separation fact costs every arithmetic call a case split, so each phase shows only those its memory steps
   need. *)
Local Ltac park_seps := repeat match goal with H : _ \/ _ |- _ => park H end.
Local Ltac unpark H := unfold hid in H.
(* Run [t] only in the branch where the count that the branch fact [K] tests is zero (resp. is not zero). *)
Local Ltac when_zero K t := lazymatch type of K with Z.of_nat _ = 0 => t | _ => idtac end.
Local Ltac when_nonzero K t := lazymatch type of K with Z.of_nat _ = 0 => idtac | _ => t end.

Lemma sn_write_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f WB bufp CK cs cn : Z) (pend src dst : list byte),
  a0 = Z_to_bv 64 f ->
  bytes_at img_segs m (bv_unsigned a1) src ->
  bv_unsigned a2 = Z.of_nat (length src) ->
  rw_cells img_segs m (f + 40) [C8 (Z_to_bv 64 (WB + Z.of_nat (length pend)))] ->
  rw_cells img_segs m (f + 56) [C8 (Z_to_bv 64 WB)] ->
  rw_cells img_segs m (f + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells img_segs m (f + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells img_segs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)] ->
  bytes_at img_segs m WB pend ->
  WB + Z.of_nat (length pend) < 2 ^ 64 ->
  rw_cells img_segs m cs [CB (length dst) dst] ->
  0 <= cn < 2 ^ 64 ->
  sn_k cn pend src < Z.of_nat (length dst) ->
  stk img_segs m (bv_unsigned sp - 64) (bv_unsigned sp) ->
  64 <= bv_unsigned sp ->
  mem_inv img_segs m ->
  f + 160 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= f + 40 ->
  CK + 16 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= CK ->
  cs + Z.of_nat (length dst) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= cs ->
  WB + Z.of_nat (length pend) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a1 ->
  CK + 16 <= f + 40 \/ f + 160 <= CK ->
  cs + Z.of_nat (length dst) <= f + 40 \/ f + 160 <= cs ->
  cs + Z.of_nat (length dst) <= CK \/ CK + 16 <= cs ->
  WB + Z.of_nat (length pend) <= cs \/ cs + Z.of_nat (length dst) <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= cs \/ cs + Z.of_nat (length dst) <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat (length src) <= CK \/ CK + 16 <= bv_unsigned a1 ->
  evt img_segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f bufp CK cs cn pend src dst m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000300)) fc None m (seg_rom img_segs)).
Proof using IMG CODE_sn_write RB_sn_write RN_B_memcpy_7f000300 SPEC_memcpy.
  intros until dst.
  intros Hf Hsrc Hl Hwpos Hwbase Hbuf Hcp Hck Hpend Hwbhi Hdst Hcn Hk Hstk Hsp Hmi
    Xf Xck Xcs Xwb Xsrc Yckf Ycsf Ycsck Ywbcs Ysrccs Ysrcck.
  subst a0.
  (* The length register: name its value, and keep its range. *)
  assert (Lsrc : Z.of_nat (length src) < 2 ^ 64).
  { rewrite <- Hl. pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2. exact (proj2 Ra2). }
  assert (Ea2 : a2 = Z_to_bv 64 (Z.of_nat (length src))) by (rewrite <- Hl; symmetry; apply Z_to_bv_bv_unsigned).
  subst a2. clear Hl.
  pose proof (rw_cells_bound _ _ _ _ Hwpos) as Bf. cbn [cells_size csize Nat.add] in Bf.
  pose proof (rw_cells_bound _ _ _ _ Hcp) as Bf2. cbn [cells_size csize Nat.add] in Bf2.
  pose proof (rw_cells_bound _ _ _ _ Hck) as Bck. cbn [cells_size csize Nat.add] in Bck.
  pose proof (rw_cells_bound _ _ _ _ Hdst) as Bcs. cbn [cells_size csize Nat.add] in Bcs.
  pose proof (bytes_at_bound _ _ _ _ Hsrc) as Bsrc.
  pose proof (bytes_at_bound _ _ _ _ Hpend) as Bpend.
  unfold sn_k in Hk.
  remember (Nat.min (Z.to_nat cn) (length pend)) as n1 eqn:En1.
  remember (Nat.min (Z.to_nat cn - n1) (length src)) as n2 eqn:En2.
  assert (Hroom : (n1 + n2 < length dst)%nat) by lia.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (f + 40, f + 48); (f + 56, f + 64); (CK, CK + 16);
                          (cs, cs + Z.of_nat (length dst))] m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat Hstk.
  park_heap sp 64 MUf WMf.
  do 8 zstep.
  unpark_heap MUf WMf.
  do 7 zstep.
  zstep. replace (WB + Z.of_nat (length pend) - WB) with (Z.of_nat (length pend)) by lia.
  zstep. zstep.
  meet_s4 (Z_to_bv 64 (Z.of_nat n1)).
  { case_if K1.
    - apply evt_done. ms_eq.
    - zstep. apply evt_done. ms_eq. }
  intros ms' ->.
  zstep.
  (* Cut the buffer at the end of the pending part. *)
  replace (length dst) with (n1 + (length dst - n1))%nat in Hdst at 1 by lia.
  apply rw_CB_split in Hdst. destruct Hdst as [Dlo Dhi].
  zstep. case_if K2.
  (* Goal 1: nothing to copy from the pending bytes (at offset 116). Goal 2: copy them (at offset 84). *)
  1: clear Hpend Ywbcs Xwb Hwbhi.
  1: replace (firstn n1 dst) with (firstn n1 pend) in Dlo by (replace n1 with 0%nat by lia; reflexivity).
  2: zstep. 2: zstep.
  2: rewrite <- (firstn_skipn n1 pend) in Hpend.
  2: apply (proj1 (bytes_at_app _ _ _ _ _)) in Hpend.
  2: destruct Hpend as [Hpend1 _].
  2: (park Xf; park Xck; park Xwb; park Xsrc; park Yckf; park Ysrcck).
  2: call_with ltac:(eapply memcpy_callk with (Dst := cs) (Src := WB) (n := n1) (src := firstn n1 pend) (junk := firstn n1 dst);
                     [ apply unsigned_lit; lia | apply unsigned_lit; lia | apply unsigned_lit; lia | exact Hpend1
                     | rewrite length_firstn; lia | exact Dlo | lia | assumption ]).
  2: rename POST into Dlo.
  (* Advance the cookie past the copied bytes. *)
  2: (clear Ywbcs Xwb Hwbhi; park_seps; unpark Yckf; unpark Ysrcck; unpark Xck; unpark Ycsck).
  2: do 6 zstep.
  (* Both goals are at offset 116: cap the source count. *)
  all: park_seps.
  all: zstep.
  all: meet_s3 (Z_to_bv 64 (Z.of_nat n2));
       [ case_if K3; [ apply evt_done; ms_eq | zstep; apply evt_done; ms_eq ] | intros ms' -> ].
  (* Cut the rest of the buffer at the end of the copied source part. *)
  all: replace (length dst - n1)%nat with (n2 + (length dst - n1 - n2))%nat in Dhi by lia.
  all: apply rw_CB_split in Dhi.
  all: destruct Dhi as [Dmid Dtop].
  all: zstep.
  all: case_if K4.
  (* Where no source byte is copied (count zero) the goal is at offset 164; elsewhere at offset 128. *)
  all: when_zero K4 ltac:(clear Hsrc Ysrccs Ysrcck Xsrc).
  all: when_zero K4 ltac:(replace (firstn n2 (skipn n1 dst)) with (firstn n2 src) in Dmid
                            by (replace n2 with 0%nat by lia; reflexivity)).
  all: when_nonzero K4 ltac:(do 3 zstep).
  all: when_nonzero K4 ltac:(rewrite <- (firstn_skipn n2 src) in Hsrc).
  all: when_nonzero K4 ltac:(apply (proj1 (bytes_at_app _ _ _ _ _)) in Hsrc).
  all: when_nonzero K4 ltac:(destruct Hsrc as [Hsrc1 _]).
  all: when_nonzero K4 ltac:(unpark Ycsf; unpark Ycsck; unpark Xcs; unpark Ysrccs).
  all: when_nonzero K4 ltac:(idtac;
         call_with ltac:(eapply memcpy_callk with (Dst := cs + Z.of_nat n1) (Src := bv_unsigned a1) (n := n2)
                           (src := firstn n2 src) (junk := firstn n2 (skipn n1 dst));
                         [ first [ reflexivity | rewrite unsigned_lit; lia ] | reflexivity
                         | first [ reflexivity | rewrite unsigned_lit; lia ] | exact Hsrc1
                         | rewrite length_firstn; lia | exact Dmid | lia | assumption ])).
  all: when_nonzero K4 ltac:(rename POST into Dmid).
  (* Advance the cookie past the copied bytes. *)
  all: when_nonzero K4 ltac:(clear Ysrccs Ysrcck Xsrc; park_seps; unpark Yckf; unpark Xck; unpark Ycsck).
  all: when_nonzero K4 ltac:(do 6 zstep).
  (* All four goals are at offset 164: store the terminator after the copied bytes. *)
  all: (park_seps; unpark Xcs; unpark Ycsf; unpark Ycsck).
  all: pose proof (rw_CB_len _ _ _ _ _ Dtop) as Ltop.
  all: pose proof (u8arr_of_rw_cells _ _ _ _ _ Dtop) as Utop.
  all: clear Dtop.
  all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         pose proof (u8arr_store_ok img_segs _ _ _ 0 av Utop ltac:(rewrite Ltop; lia) ltac:(unfold wa; f_equal; lia)) as Sok
       end.
  all: zstep.
  all: rewrite le1_z0.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?av _) _) =>
         replace av with (wa (cs + Z.of_nat n1 + Z.of_nat n2 + 0)) by (unfold wa; f_equal; lia)
       end.
  all: pose proof (u8arr_write img_segs _ _ _ 0 (Z_to_bv 8 0) Utop ltac:(rewrite Ltop; lia)) as Utop2.
  all: clear Utop.
  all: store_done.
  all: pose proof (rw_cells_of_u8arr _ _ _ _ Utop2) as Dtop.
  all: rewrite upd_length, Ltop in Dtop.
  all: clear Utop2.
  (* Reset the write pointers to the buffer, return the source length, restore the frame. *)
  all: (unpark Xf; unpark Yckf; park Xcs; park Ycsck).
  all: do 13 zstep.
  all: release_frame FR Hstk (bv_unsigned sp).
  all: replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in MU by lia.
  all: replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in Hstk by lia.
  all: apply evt_done.
  all: unfold sn_write_post.
  all: repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [ ms_eq | ].
  all: split; [ exact MU | ].
  all: split; [ exact WM | ].
  all: split; [ assumption | ].
  all: split; [ exact Hstk | ].
  all: split; [ exact Hwpos | ].
  all: split; [ exact Hwbase | ].
  (* The cookie moved by the number of copied bytes. *)
  all: split;
       [ lazymatch goal with
         | H : rw_cells _ ?mm ?A [C8 ?x'; C8 ?y'] |- rw_cells _ ?mm ?A [C8 ?x; C8 ?y] =>
             replace x with x' by (f_equal; unfold sn_k; lia); replace y with y' by (f_equal; unfold sn_k; lia); exact H
         end | ].
  (* Join the three parts of the buffer. *)
  all: pose proof (rw_CB_join _ _ _ _ _ _ _ Dlo Dmid) as D12.
  all: replace (cs + Z.of_nat n1 + Z.of_nat n2) with (cs + Z.of_nat (n1 + n2)) in Dtop by lia.
  all: pose proof (rw_CB_join _ _ _ _ _ _ _ D12 Dtop) as Dall.
  all: rewrite <- app_assoc in Dall.
  all: change (Z.to_nat 0) with 0%nat in Dall.
  all: rewrite (sn_bytes pend src dst (Z.to_nat cn) n1 n2 (Z_to_bv 8 0) En1 En2 Hroom) in Dall.
  all: replace (n1 + n2 + (length dst - n1 - n2))%nat with (length dst) in Dall by lia.
  all: replace (Z.to_nat (sn_k cn pend src)) with (n1 + n2)%nat by (unfold sn_k; lia).
  all: exact Dall.
Qed.

Lemma sn_write_contract_ok : sn_write_contract.
Proof using IMG CODE_sn_write RB_sn_write RN_B_memcpy_7f000300 SPEC_memcpy.
  exact sn_write_spec.
Qed.

End Img.

Existing Class sn_write_contract.
