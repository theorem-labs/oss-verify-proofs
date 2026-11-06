(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names and addresses changed; 288 of its 364 lines of code are new or changed and 670 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memset_c same_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LedgerCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c fuzz_alloc_ran_out.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* The straight-line runs of check_no_overread in the #102 ubsan image (pin 45b0357d, unstripped twin 27566683952ebd54;
   entry 0x13868, size 464, frame 0xf0 = 240), walked on its listing; every pc, offset and callee entry below is that
   image's:  padded 0x1448c, memset 0x22924, fuzz_alloc_ran_out 0x15f90, parse_noting 0x13a38, same 0x14520,
   pj_free 0x16340, free 0x18250.
   The prologue saves ra, s0 .. s7 at sp + 0xe8 .. sp + 0xa8; s2 = data and s4 = n until the copies are made; the three
   padded copies go to s0 (fill 0x31), s1 (fill 0x32) and s2 (fill 0); the three trees at sp + 0x70, sp + 0x38 and sp
   are zeroed by memset; s7 = CNO_S7 (auipc) addresses g_own_ran_out at s7 - 0x6ac; s3 = 1 (ran_out); before each
   reading and once after the third, out_of_memory() = lbu g_own_ran_out, then fuzz_alloc_ran_out; the readings' results
   go to s5, s6, s4; s3 = 0 when no test ran out, and a0 = s3 at the return.
   These runs are the same text in lib/U/Prog and lib/U/Prog/CF: they are stated with evt alone, no SR. *)

Ltac br_lits := unfold_cond; rewrite ?unsigned_lit by lia.

Ltac fin_post :=
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf;
  hot_eexists_all;
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.AndN.and_splits;
  try assumption.

(* A branch whose condition is closed (it reads only loaded constants and x0): decide it by computation. *)
Ltac cno_br_closed b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

(* auipc s7, 0x22 at 0x138fc: s7 = 0x138fc + 0x22000, and s7 - 0x6ac is g_own_ran_out. *)
Definition CNO_S7 : Z := 0x358fc.

Lemma cno_s7_own : CNO_S7 + -1708 = GL_OWN_RAN_OUT.
Proof. reflexivity. Qed.

(* The read of g_own_ran_out (one byte) that each out_of_memory() test makes. *)
Lemma cno_own_read : forall m, bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  ov_read_bytes rsegs m (wa (CNO_S7 + -1708)) 1 = Some (le1 (Z_to_bv 64 0)).
Proof.
  intros m H. rewrite cno_s7_own. replace (wa GL_OWN_RAN_OUT) with (wa (GL_OWN_RAN_OUT + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) 0 1 H ltac:(lia)) by (rewrite length_le1; lia).
  reflexivity.
Qed.

(* lbu a0, -0x6ac(s7) with s7 = CNO_S7, on the read fact of cno_own_read. *)
Ltac cno_lbu_own :=
  lazymatch goal with
  | H : bytes_at rsegs ?mm GL_OWN_RAN_OUT _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RD := fresh "RD" in pose proof (cno_own_read mm H) as RD; unfold CNO_S7 in RD; step; clear RD
  end.

(* jal fuzz_alloc_ran_out with g_ran_out = 0: it returns a0 = 0 and writes nothing (fuzz_alloc_ran_out_holds). *)
Ltac cno_ran_out :=
  eapply evt_cut;
  [ eapply (fuzz_alloc_ran_out_holds) with (ran_out := Z_to_bv 64 0); [vm_compute; reflexivity | eassumption]
  | let ms' := fresh "ms'" in let E := fresh "E" in
    intros ms' E; cbv beta in E; subst ms';
    lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end ].

Ltac cno_call_memset MS0 j :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MS0 with (junk := j); rewrite ?unsigned_lit by lia; eassumption
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memset_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.

Definition jump_post (R : bvmap 5 word) (F : bvmap 5 word) (pc' : word) (fc : bv 32) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => ms' = MS R F pc' fc None m (seg_rom rsegs).

(* 0x13868 .. 0x1389c: the prologue (sp -= 0xf0; ra, s0 .. s7 saved at sp + 0xe8 .. sp + 0xa8), s4 = n, s2 = data,
   a2 = 0x31, then jal padded (0x1448c) with ra 0x138a0 and a0 = data, a1 = n. *)
Definition seg0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (d n : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x138a0) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d)
                  (Z_to_bv 64 n) (Z_to_bv 64 0x31) a3 a4 a5 a6 a7 (Z_to_bv 64 d) s3 (Z_to_bv 64 n) s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x1448c) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -72, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cno_seg0 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d n : Z) (j : list byte),
  0 <= d < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 240 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp + -72) [CB 72 j] ->
  evt rsegs (seg0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13868) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n j
    Hd Hn Hsp FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -72, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 72%nat j [] [8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 14 step.
  finish.
Qed.

(* 0x138a0 .. 0x138b0: s0 = the first copy; a2 = 0x32, a0 = s2 = data, a1 = s4 = n; jal padded, ra 0x138b4. *)
Lemma cno_segP1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x138b4) sp gp tp t0 t1 t2 a0 s1 s2 s4 (Z_to_bv 64 0x32) a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1448c) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138a0) fc None m (seg_rom rsegs)).
Proof.
  intros. do 5 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x138b4 .. 0x138c4: s1 = the second copy; a0 = s2 = data, a1 = s4 = n, a2 = 0; jal padded, ra 0x138c8. *)
Lemma cno_segP2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x138c8) sp gp tp t0 t1 t2 s0 a0 s2 s4 (Z_to_bv 64 0) a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1448c) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138b4) fc None m (seg_rom rsegs)).
Proof.
  intros. do 5 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

Definition segM_post (sp gp tp s0 s1 s2 s4 s5 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x1392c) sp gp tp t0 t1 t2 s0 s1 s0 s4 (Z_to_bv 64 (bv_unsigned sp + 112)) a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 1) s4 s5 s6 (Z_to_bv 64 CNO_S7) s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13a38) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp, bv_unsigned sp + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Section Memset.
Hypothesis MS0 : memset_contract.

(* 0x138c8 .. 0x13928: s2 = the third copy; memset of 0x38 zero bytes on the trees at sp + 0x70, sp + 0x38 and sp
   (ra 0x138dc, 0x138ec, 0x138fc); s7 = CNO_S7; the first out_of_memory() test: lbu g_own_ran_out reads 0, so bnez
   (0x13908, to 0x139d0) is not taken, and fuzz_alloc_ran_out (ra 0x13910) returns the 0 of g_ran_out, so beqz
   (0x13910) goes to 0x1391c; s3 = 1 on the way; a2 = sp + 0x70, a0 = s0, a1 = s4 = n; jal parse_noting, ra 0x1392c. *)
Lemma cno_segM : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j0 j1 j2 : list byte),
  bv_unsigned sp + 240 <= 2 ^ 64 -> GL_OWN_RAN_OUT + 1 <= bv_unsigned sp -> G_RAN_OUT + 1 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp) [CB (Z.to_nat 56) j0] ->
  rw_cells rsegs m (bv_unsigned sp + 56) [CB (Z.to_nat 56) j1] ->
  rw_cells rsegs m (bv_unsigned sp + 112) [CB (Z.to_nat 56) j2] ->
  bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) -> bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  mem_inv rsegs m ->
  evt rsegs (segM_post sp gp tp s0 s1 a0 s4 s5 s6 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138c8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j0 j1 j2
    Hsp Hown Hgro T0 T1 T2 OWN GRO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 step.
  cno_call_memset MS0 j2.
  do 4 step.
  cno_call_memset MS0 j1.
  do 4 step.
  cno_call_memset MS0 j0.
  step.
  cno_lbu_own.
  step.
  step. cno_br_closed false.
  step.
  cno_ran_out.
  step. cno_br_closed true.
  do 4 step.
  finish.
Qed.

End Memset.

(* 0x1392c .. 0x13954: s5 = the first reading's result; out_of_memory() (lbu g_own_ran_out = 0: bnez 0x13934 not
   taken; fuzz_alloc_ran_out, ra 0x1393c, returns 0: beqz goes to 0x13948); a2 = sp + 0x38, a0 = s1, a1 = s4 = n;
   jal parse_noting, ra 0x13958.  Memory is not written. *)
Lemma cno_segR1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 56 < 2 ^ 64 ->
  bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) -> bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x13958) sp gp tp t0 t1 t2 s0 s1 s1 s4 (Z_to_bv 64 (bv_unsigned sp + 56))
                           a3 a4 a5 a6 a7 s2 s3 s4 a0 s6 (Z_to_bv 64 CNO_S7) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13a38) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 CNO_S7) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1392c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hsp OWN GRO.
  step.
  cno_lbu_own.
  step. cno_br_closed false.
  step.
  cno_ran_out.
  step. cno_br_closed true.
  do 4 step.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x13958 .. 0x13980: s6 = the second reading's result; out_of_memory() as above (bnez 0x13960 not taken;
   fuzz_alloc_ran_out, ra 0x13968; beqz goes to 0x13974); a2 = sp, a0 = s2, a1 = s4 = n; jal parse_noting,
   ra 0x13984. *)
Lemma cno_segR2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) -> bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x13984) sp gp tp t0 t1 t2 s0 s1 s2 s4 sp
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 a0 (Z_to_bv 64 CNO_S7) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13a38) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 CNO_S7) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13958) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OWN GRO.
  step.
  cno_lbu_own.
  step. cno_br_closed false.
  step.
  cno_ran_out.
  step. cno_br_closed true.
  do 4 step.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x13984 .. 0x13994: s4 = the third reading's result; ran_out = out_of_memory() (lbu g_own_ran_out = 0: bnez
   0x1398c not taken; fuzz_alloc_ran_out, ra 0x13994, returns 0: bnez 0x13994 not taken), to the compare block at
   0x13998 with a0 = 0. *)
Lemma cno_segR3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bytes_at rsegs m GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) -> bytes_at rsegs m G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x13994) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2
                           a3 a4 a5 a6 a7 s2 s3 a0 s5 s6 (Z_to_bv 64 CNO_S7) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13998) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 CNO_S7) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13984) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OWN GRO.
  step.
  cno_lbu_own.
  step. cno_br_closed false.
  step.
  cno_ran_out.
  step. cno_br_closed false.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x13998 .. 0x139d4 when the three readings failed (s5 = s6 = s4 <> 0): bnez s5 is taken to 0x139c4, bne s5, s4 and
   bne s6, s4 are not; s3 = 0 (0x139cc); a0 = sp + 0x70; jal pj_free (0x16340), ra 0x139d8. *)
Lemma cno_cmp_none : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  s5 = s4 -> s6 = s4 -> bv_unsigned s4 <> 0 -> bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139d8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 112)) a1 a2
                           a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16340) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13998) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    E5 E6 HA Hsp.
  subst s5 s6.
  step. if_true.
  step. if_false.
  step. if_false.
  step. step. step.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

Definition cmp_some_post (sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (L : Z -> Z -> Prop) (lo : Z) (t : jv) (D1 D2 D0 : list (Z * Z)) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x139d8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 112)) a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x16340) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - same_k t, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    pj_node rsegs m' L (bv_unsigned sp + 112) t D1 /\ pj_node rsegs m' L (bv_unsigned sp + 56) t D2 /\
    pj_node rsegs m' L (bv_unsigned sp) t D0.

Section Same.
Hypothesis SAME : same_contract.

(* 0x13998 .. 0x139d4 when the three readings succeeded (s5 = s6 = s4 = 0): bnez s5 / bnez s6 not taken;
   same(sp + 0x70, sp + 0x38) (0x14520, ra 0x139ac) returns 1 on the equal trees, so beqz a0 (abort) is not taken;
   bnez s4 not taken; same(sp + 0x70, sp) (ra 0x139c0), beqz a0 not taken; bne s5, s4 and bne s6, s4 not taken;
   s3 = 0; a0 = sp + 0x70; jal pj_free, ra 0x139d8. *)
Lemma cno_cmp_some : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L : Z -> Z -> Prop) (lo : Z) (t : jv)
    (D1 D2 D0 : list (Z * Z)),
  bv_unsigned sp + 168 <= 2 ^ 64 -> same_ledger L ->
  pj_node rsegs m L (bv_unsigned sp + 112) t D1 -> pj_node rsegs m L (bv_unsigned sp + 56) t D2 ->
  pj_node rsegs m L (bv_unsigned sp) t D0 ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + same_k t <= bv_unsigned sp ->
  (forall z, pj_foot (bv_unsigned sp + 112) D1 z -> outside [(bv_unsigned sp - same_k t, bv_unsigned sp)] z) ->
  (forall z, pj_foot (bv_unsigned sp + 56) D2 z -> outside [(bv_unsigned sp - same_k t, bv_unsigned sp)] z) ->
  (forall z, pj_foot (bv_unsigned sp) D0 z -> outside [(bv_unsigned sp - same_k t, bv_unsigned sp)] z) ->
  evt rsegs (cmp_some_post sp gp tp s0 s1 s2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s7 s8 s9 s10 s11 F fc m L lo
               t D1 D2 D0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13998) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L lo t D1 D2 D0
    Hsp LG P1 P2 P0 MI ST LO O1 O2 O0.
  assert (SP0 : 0 < bv_unsigned sp).
  { destruct ST as [Hlo _]. unfold same_k, SAME_FS in LO. clear - Hlo LO. lia. }
  step. if_false.
  step. if_false.
  step. step. step.
  eapply evt_cut.
  { eapply SAME with (pa := bv_unsigned sp + 112) (pb := bv_unsigned sp + 56) (ta := t) (tb := t)
      (Da := D1) (Db := D2) (L := L) (lo := lo); first [reflexivity | eassumption | lia]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & ST2 & RES & Q1 & Q2).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x139ac)) with (Z_to_bv 64 0x139ac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RES as [(_ & Er)|(NE & _)]; [subst r | congruence].
  pose proof (pj_node_munch rsegs _ m L m2 L _ t D0 P0 (pj_node_blocks rsegs t m L _ D0 P0) MU2 O0) as Q0.
  clear P1 P2 P0 MI ST.
  step. if_false.
  step. if_false.
  step. step. step.
  eapply evt_cut.
  { eapply SAME with (pa := bv_unsigned sp + 112) (pb := bv_unsigned sp) (ta := t) (tb := t)
      (Da := D1) (Db := D0) (L := L) (lo := lo);
      first [reflexivity | eassumption | symmetry; apply Z_to_bv_bv_unsigned | lia]. }
  intros ms' (t0'' & t1'' & t2'' & r & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3'' & t4'' & t5'' & t6'' & m3 &
              E & MU3 & WM3 & MI3 & ST3 & RES & R1 & R0).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x139c0)) with (Z_to_bv 64 0x139c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RES as [(_ & Er)|(NE & _)]; [subst r | congruence].
  pose proof (pj_node_munch rsegs _ m2 L m3 L _ t D2 Q2 (pj_node_blocks rsegs t m2 L _ D2 Q2) MU3 O2) as R2.
  pose proof (munch_trans _ _ _ _ MU2 MU3) as MU.
  pose proof (wmono_trans rsegs _ _ _ WM2 WM3) as WM.
  clear Q1 Q2 Q0 MI2 ST2 MU2 MU3 WM2 WM3.
  step. if_false.
  step. if_false.
  step. if_false.
  step. step. step.
  finish.
Qed.

End Same.

(* 0x139d8 .. 0x139dc: a0 = sp + 0x38; jal pj_free, ra 0x139e0. *)
Lemma cno_mv_free2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 56 < 2 ^ 64 ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139e0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 56)) a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16340) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139d8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139e0 .. 0x139e4: a0 = sp; jal pj_free, ra 0x139e8. *)
Lemma cno_mv_free3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139e8) sp gp tp t0 t1 t2 s0 s1 sp a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16340) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139e0) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139e8 .. 0x139ec: a0 = s0; jal free (0x18250), ra 0x139f0. *)
Lemma cno_mv_rel1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139f0) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18250) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139e8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139f0 .. 0x139f4: a0 = s1; jal free, ra 0x139f8. *)
Lemma cno_mv_rel2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139f8) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18250) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139f0) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139f8 .. 0x139fc: a0 = s2; jal free, ra 0x13a00. *)
Lemma cno_mv_rel3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x13a00) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18250) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139f8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x13a00 .. 0x13a2c: a0 = s3 (ran_out); reload ra, s0 .. s7 from sp + 0xe8 .. sp + 0xa8, sp += 240, ret. *)
Lemma cno_epilogue : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v s7v : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 240 < 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned sp + 168)
    (le8 s7v ++ le8 s6v ++ le8 s5v ++ le8 s4v ++ le8 s3v ++ le8 s2v ++ le8 s1v ++ le8 s0v ++ le8 rav) ->
  evt rsegs (jump_post (mkR rav (Z_to_bv 64 (bv_unsigned sp + 240)) gp tp t0 t1 t2 s0v s1v s3 a1 a2
                           a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a00) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    rav s0v s1v s2v s3v s4v s5v s6v s7v F fc m Hsp BY.
  assert (RO : ro_cells rsegs m (bv_unsigned sp + 168)
                 [C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]).
  { split; [cbn [cells_wf cell_wf]; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY. }
  clear BY.
  do 12 step. apply evt_done. unfold jump_post. reflexivity.
Qed.
