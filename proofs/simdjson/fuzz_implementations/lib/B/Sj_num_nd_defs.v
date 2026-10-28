(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_iface Sj_num_bdefs.
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
End NDDefs.

Definition nd_W (X spq f : Z) : list (Z * Z) :=
  [(spq, spq + 56); (f + 32, f + 536); (f / 8 + 2147450884, f / 8 + 2147450947); (X, X + 504)].

Definition nd_spill (f : Z) (c0 c8 c16 c32 c40 : word) : list cell :=
  [C8 c0; C8 c8; C8 c16; C8 (Z_to_bv 64 f); C8 c32; C8 c40; C8 (Z_to_bv 64 f)].

Definition nd_inv (X spq f : Z) (m0 : mem) (tsh : list byte) (mm : mem) (xlen tlen : Z) : Prop :=
  (exists c0 c8 c16 c32 c40, rw_cells bsegs mm spq (nd_spill f c0 c8 c16 c32 c40)) /\
  (exists xbs, u8arr bsegs mm X xbs /\ length xbs = 496%nat) /\
  rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] /\ 0 <= xlen <= 62 /\
  bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  (exists tbs, u8arr bsegs mm (f + 32) tbs /\ length tbs = 496%nat) /\
  rw_cells bsegs mm (f + 528) [C2 (Z_to_bv 64 tlen)] /\ 0 <= tlen <= 62 /\
  rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 tsh] /\
  mem_inv bsegs mm /\ munch (nd_W X spq f) m0 mm /\ wmono bsegs m0 mm.

Ltac nd_open H :=
  let xbs := fresh "xbs" in let tbs := fresh "tbs" in
  destruct H as ((?c0 & ?c8 & ?c16 & ?c32 & ?c40 & SPILL) & (xbs & XA & XL) & XN & ?LEN & ZR & (tbs & TA & TL) & TN & ?TLN & TSH & MI & MU & WM);
  unfold nd_spill in SPILL; unfold nd_W in MU.
Ltac nd_close :=
  lazymatch goal with
  | |- nd_inv _ _ _ _ _ _ _ _ =>
      unfold nd_inv, nd_spill, nd_W;
      split; [do 5 eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Definition nd_xinv (X spq f : Z) (m0 : mem) (mm : mem) : Prop :=
  (exists jsp, rw_cells bsegs mm spq [CB 56 jsp]) /\
  (exists xbs, u8arr bsegs mm X xbs /\ length xbs = 496%nat) /\
  (exists xlen, rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] /\ 0 <= xlen <= 62) /\
  bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
  (exists jt, rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jt]) /\
  mem_inv bsegs mm /\ munch (nd_W X spq f) m0 mm /\ wmono bsegs m0 mm.

Ltac nd_xclose :=
  lazymatch goal with
  | |- nd_xinv _ _ _ _ _ =>
      unfold nd_xinv, nd_W;
      split; [lazymatch goal with SP : rw_cells bsegs ?m ?A [_; _; _; _; _; _; _] |- _ =>
                let j := fresh "j" in let Hj := fresh "Hj" in destruct (rw_cells_forget bsegs m A _ SP) as [j Hj]; cbn [cells_size csize Nat.add] in Hj; exists j; exact Hj end|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eexists; split; [eassumption| lia]|];
      split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; eassumption
  end.

Section NDK.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X p2 e spq f : Z) (m0 : mem).
  Variable Q : machine_state -> Prop.
  Notation S := (f / 8 + 2147450880)%Z.
  Notation NDINV := (nd_inv X spq f m0).
  Notation NDS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 (Z_to_bv 64 S) (Z_to_bv 64 (p2 mod 4294967296)) xs5 (Z_to_bv 64 X) (Z_to_bv 64 (- e)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (0 - p2)) xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition nd_p5_k : Prop :=
    forall (q2 : Z) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 (mm : mem) xlen,
      NDINV (repeat (Z_to_bv 8 0) 63) mm xlen 1 -> e <> 0 -> -2424192 <= q2 <= 2424192 ->
      evt bsegs Q (NDS 0xfbb10 (Z_to_bv 64 0xfb420) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 e) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 q2) xs5 xt3 xt4 xt5 xt6 mm).

  Definition nd_shlt_k : Prop :=
    forall (n : Z) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 (mm : mem) xlen tlen,
      NDINV (repeat (Z_to_bv 8 0) 63) mm xlen tlen -> 0 < n <= 2424192 ->
      evt bsegs Q (NDS 0xfcfe0 (Z_to_bv 64 0xfb434) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 n) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 n) xs5 xt3 xt4 xt5 xt6 mm).
  Definition nd_shlx_k : Prop :=
    forall (n : Z) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 (mm : mem) xlen tlen,
      NDINV (repeat (Z_to_bv 8 0) 63) mm xlen tlen -> 0 < n <= 2424192 ->
      evt bsegs Q (NDS 0xfcfe0 (Z_to_bv 64 0xfb434) xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 n) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 n) xs5 xt3 xt4 xt5 xt6 mm).

  Definition nd_55c_k : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 (r0 r1 : word) xt3 xt4 xt5 xt6 (mm : mem),
      nd_xinv X spq f m0 mm ->
      evt bsegs Q (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 (Z_to_bv 64 1172321806) xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 f) (Z_to_bv 64 S) r1 r0 (Z_to_bv 64 X) (Z_to_bv 64 (- e)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
                           (Z_to_bv 64 (0 - p2)) xt3 xt4 xt5 xt6)
                      F (Z_to_bv 64 0xfb6c4) fc None mm (seg_rom bsegs)).
End NDK.
