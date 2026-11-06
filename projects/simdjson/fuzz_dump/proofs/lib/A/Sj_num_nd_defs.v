(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_iface Sj_num_adefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section NDDefs.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Lemma aevt_frame_release : forall (Σ Σ' : rts RT) (K : config -> Prop) ms,
  rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> aevt RT PMc Σ' K ms -> aevt RT PMc Σ K ms.
Proof.
  intros Σ Σ' K ms HA HM H T c Hc Hk. exact (H T c (ASTA_switch RT Σ Σ' PMc (eq ms) c Hc HA HM) Hk).
Qed.

Definition ndca_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X e cr lo : Z),
  tp = Z_to_bv 64 0x69ec68 -> frm0 fc ->
  (length (rt_frames RT Σ) + 2 <= FRAMES_MAX)%nat -> 0 <= e < 135 * (cr + 1) -> 0 <= cr -> e < 2147483648 -> cr + 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + NDCA_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  abig RT Σ m X ->
  (forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, X + 504)] m m' ->
     abig RT Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - (cr + 1) <= rt_credit RT Σ' ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 (Z_to_bv 64 (- e)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0xe021c) fc None m (seg_rom asegs)).
End NDDefs.

Definition nd_W (X spq f : Z) : list (Z * Z) :=
  [(spq, spq + 56); (f + 32, f + 536); (f / 8 + 2147450884, f / 8 + 2147450947); (X, X + 504)].

Definition nd_inv (X spq f : Z) (m0 : mem) (tsh : list byte) (c16 : word) (mm : mem) (xlen tlen : Z) : Prop :=
  (exists c0 c8 c24 c32 c40 c48, rw_cells asegs mm spq [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48]) /\
  (exists xbs, u8arr asegs mm X xbs /\ length xbs = 496%nat) /\
  rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] /\ 0 <= xlen <= 62 /\
  bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  (exists tbs, u8arr asegs mm (f + 32) tbs /\ length tbs = 496%nat) /\
  rw_cells asegs mm (f + 528) [C2 (Z_to_bv 64 tlen)] /\ 0 <= tlen <= 62 /\
  rw_cells asegs mm (f / 8 + 2147450884) [CB 63 tsh] /\
  mem_inv asegs mm /\ munch (nd_W X spq f) m0 mm /\ wmono asegs m0 mm.

Definition nd_xinv (X spq f : Z) (m0 : mem) (mm : mem) : Prop :=
  (exists jsp, rw_cells asegs mm spq [CB 56 jsp]) /\
  (exists xbs, u8arr asegs mm X xbs /\ length xbs = 496%nat) /\
  (exists xlen, rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] /\ 0 <= xlen <= 62) /\
  bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  (exists jt, rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jt]) /\
  mem_inv asegs mm /\ munch (nd_W X spq f) m0 mm /\ wmono asegs m0 mm.

Ltac nd_xclose :=
  lazymatch goal with
  | |- nd_xinv _ _ _ _ _ =>
      unfold nd_xinv, nd_W;
      split; [lazymatch goal with SP : rw_cells asegs ?m ?A [_; _; _; _; _; _; _] |- _ =>
                let j := fresh "j" in let Hj := fresh "Hj" in destruct (rw_cells_forget asegs m A _ SP) as [j Hj]; cbn [cells_size csize Nat.add] in Hj; exists j; exact Hj end|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac nd_open H :=
  let xbs := fresh "xbs" in let tbs := fresh "tbs" in
  destruct H as ((?c0 & ?c8 & ?c24 & ?c32 & ?c40 & ?c48 & SPILL) & (xbs & XA & XL) & XN & ?LEN & ZR & (tbs & TA & TL) & TN & ?TLN & TSH & MI & MU & WM);
  unfold nd_W in MU.
Ltac nd_forget := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
  | H : length _ = 496%nat |- _ => clear H | H : length _ = length _ |- _ => clear H end.
Ltac nd_close :=
  lazymatch goal with
  | |- nd_inv _ _ _ _ _ _ _ _ _ =>
      unfold nd_inv, nd_W;
      split; [do 6 eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
