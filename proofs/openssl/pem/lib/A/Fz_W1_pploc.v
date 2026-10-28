(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_W1_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section PPLoc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Definition pp_loc (frames : list (Z * nat)) (m : mem) (usp PP : Z) : Prop :=
  (usp <= PP /\ PP + 8 <= USTACK_TOP - 16)
  \/ (exists f k, In (f, k) frames /\ f <= PP /\ PP + 8 <= f + fs_size k - 8 /\ bytes_at asegs m (shad PP) [z8]).

Lemma pp_facts : forall (Σ : rts RT) (m : mem) usp lo PP, ART RT Σ m -> pp_loc (rt_frames RT Σ) m usp PP -> PP mod 8 = 0 ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= usp -> usp + 16 <= USTACK_TOP ->
  0 < PP /\ PP + 8 <= 2 ^ 47 /\ (PP + 8 <= IMG_UT_LO \/ IMG_UT_HI <= PP) /\ (PP + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= PP) /\ (PP + 8 <= lo \/ usp <= PP)
  /\ (forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (PP + i))
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> PP + 8 <= p \/ p + n <= PP)
  /\ (forall m' : mem, ART RT Σ m' -> (forall a : word, in_fframe_shadow (rt_frames RT Σ) (bv_unsigned a) -> m' a = m a) -> acc asegs m' PP 8).
Proof.
  intros Σ m usp lo PP ART0 LOC PPAL LOW LOR SPT.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  destruct LOC as [(H1 & H2) | (f & k & Hin & H1 & H2 & SHZ)].
  - split; [unfold RT_STACK, STACK_WIN in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. split; [right; unfold IMG_UT_HI, RT_STACK, STACK_WIN in *; lia|].
    split; [right; unfold RT_STACK, STACK_WIN in *; lia|]. split; [right; exact H1|].
    split; [intros i Hi; left; lia|]. split.
    + intros p n Hp. pose proof (af_live_range RT AF Σ m p n ART0 Hp) as (_ & HP & _). right. unfold RT_STACK in *. lia.
    + intros m' ART' _. apply (af_acc_stack RT AF Σ m' PP 8 ART'); unfold RT_STACK in *; lia.
  - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (F0 & FHI & _ & FAP). pose proof (af_frames_hi RT AF Σ m f k ART0 Hin) as FSH.
    pose proof (proj2 (af_frames_align RT AF Σ m f k ART0 Hin)) as FLOI.
    split; [lia|]. split; [unfold USTACK_TOP, STACK_WIN in *; lia|]. split; [right; unfold IMG_UT_HI, SEGTOP_A in *; lia|].
    split; [clear - FSH H1 H2; lia|]. split; [left; lia|].
    split; [intros i Hi; do 3 right; left; exists f, k; split; [exact Hin | lia]|]. split.
    + intros p n Hp. destruct (FAP p n Hp); [left | right]; lia.
    + intros m' ART' AG. apply (acc_zero_run asegs m' PP 1%nat PPAL ltac:(lia)). cbn [repeat].
      apply (bytes_at_agree asegs m m' _ _ SHZ). intros a Ha. cbv beta in Ha. cbn [length Z.of_nat Pos.of_succ_nat] in Ha. apply AG.
      exists f, k. split; [exact Hin|]. unfold shad in *. split; [apply Z.le_trans with (PP / 8 + SHB); [apply Z.add_le_mono_r; apply Z.div_le_mono; lia | lia]|].
      apply Z.lt_le_trans with (PP / 8 + SHB + 1); [lia|]. apply Z.add_le_mono_r with (p := SHB) in H2.
      assert (PP / 8 + 1 <= (f + fs_size k) / 8) by (Z.div_mod_to_equations; lia). lia.
Qed.

End PPLoc.
