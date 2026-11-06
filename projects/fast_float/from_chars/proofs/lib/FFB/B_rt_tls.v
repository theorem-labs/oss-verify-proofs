(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt B_rt_lemmas.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac lia4 ::= first [ lia_t1 | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Notation B_TLS_THUNK := 0x5040c%Z.
Notation B_TLS_DESC := 0xdf230%Z.
Notation TLS_NEED := 176%Z.

Definition tls_chain_W (sp : word) : list ivl := [(bv_unsigned sp - TLS_NEED, bv_unsigned sp)]%Z.

Definition tls_chain_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (v : rt_vals) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TPV) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (tls_chain_W sp) m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - TLS_NEED) (bv_unsigned sp)
    /\ RT m' v.

Definition tls_chain_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : rt_vals),
    a0 = Z_to_bv 64 B_TLS_DESC ->
    tp = Z_to_bv 64 TPV ->
    RT m v ->
    stk BSEGS m (bv_unsigned sp - TLS_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - TLS_NEED)%Z -> (KHI <= bv_unsigned sp - TLS_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    rt_disj v (bv_unsigned sp - TLS_NEED) (bv_unsigned sp) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt BSEGS (tls_chain_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 B_TLS_THUNK) fc None m (seg_rom BSEGS)).

Lemma tls_chain_spec : tls_chain_stmt.
Proof.
  unfold tls_chain_stmt. intros until v. intros Ha0 Htp RTH ST SP1 SP2 SP3 AL16 PRG PRT RDJ RA.
  subst a0 tp.
  pose proof (munch_refl (tls_chain_W sp) m) as MU. cbv delta [tls_chain_W] in MU.
  pose proof (wmono_refl BSEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  open_RT RTH.
  destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
  pose proof (bv_unsigned_in_range 8 fb) as Rfb. unfold bv_modulus in Rfb.
  unfold rt_disj in RDJ. destruct RDJ as (Dc & Dt & Db).
  step. (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 6 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  do 3 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -32)%Z.
  do 2 step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -32)%Z.
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  carve_frame 144%nat ST.
  do 14 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  do 2 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  if_taken.
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_not_taken.
  step. (* [comment removed for export] *)
  do 14 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -32)%Z.
  step. (* [comment removed for export] *)
  do 5 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold tls_chain_post. finish.
  close_RT.
Qed.
