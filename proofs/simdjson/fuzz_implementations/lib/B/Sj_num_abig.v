(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bdefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section ABig.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Definition abig_raw (Σ : rts RT) (m : mem) (X : Z) (bs : list byte) (len : Z) : Prop :=
  u8arr bsegs m X bs /\ length bs = 496%nat /\ rw_cells bsegs m (X + 496) [C2 (Z_to_bv 64 len)] /\ 0 <= len <= 62
  /\ bytes_at bsegs m (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63)
  /\ X mod 8 = 0 /\ (exists f c, In (f, c) (rt_frames RT Σ) /\ f <= X /\ X + 504 <= f + fs_size c - 8).

Lemma abig_elim : forall Σ m X, abig RT Σ m X -> exists bs len, abig_raw Σ m X bs len.
Proof.
  intros Σ m X ((A8 & _ & (f & c & Hin & F1 & F2) & HB) & (bs & BL & XA) & (len & XN & LEN)).
  exists bs, len. split; [exact XA|]. split; [exact BL|]. split; [exact XN|]. split; [exact LEN|].
  split; [exact HB|]. split; [exact A8|]. exists f, c. split; [exact Hin|]. split; [exact F1|].
  change (8 * ((504 + 7) / 8)) with 504 in F2. exact F2.
Qed.

Lemma abig_intro : forall Σ m X bs len, abig_raw Σ m X bs len -> abig RT Σ m X.
Proof.
  intros Σ m X bs len (XA & BL & XN & LEN & HB & A8 & (f & c & Hin & F1 & F2)).
  split; [| split; [exists bs; split; [exact BL| exact XA]| exists len; split; [exact XN| exact LEN]]].
  split; [exact A8|]. split; [lia|]. split; [| exact HB].
  exists f, c. split; [exact Hin|]. split; [exact F1|]. change (8 * ((504 + 7) / 8)) with 504. exact F2.
Qed.

Lemma fframe_obj_facts : forall Σ m X n lo, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> X mod 8 = 0 -> 0 <= n -> n mod 8 = 0 ->
  (exists f c, In (f, c) (rt_frames RT Σ) /\ f <= X /\ X + n <= f + fs_size c - 8) ->
  0x6e0000 <= X /\ X + n <= lo
  /\ (X + n <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + n / 8 <= X)
  /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + n / 8 <= lo.
Proof using AF.
  intros Σ m X n lo HA LO X8 N0 N8 (f & c & Hin & F1 & F2).
  pose proof (fframe_ranges RT AF Σ m f c HA Hin) as (F0 & FHI & FSZ & S0 & S3).
  pose proof (af_frames_align RT AF Σ m f c HA Hin) as (F64 & FSEG).
  pose proof (af_fshadow_apart RT AF Σ m f c HA Hin) as (_ & AFR). specialize (AFR f c Hin).
  assert (M1 : shad f <= shad X) by (unfold shad; pose proof (Z.div_le_mono f X 8 ltac:(lia) F1); lia).
  assert (M2 : shad X + n / 8 <= shad (f + fs_size c)).
  { unfold shad. assert (X / 8 + n / 8 <= (f + fs_size c) / 8); [| lia].
    apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod X 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)). lia. }
  unfold shad, SHB in *. unfold SEGTOP_A in FSEG.
  split; [lia|]. split; [lia|]. split; [| split; [| lia]].
  - destruct AFR as [H|H]; [left; lia| right; lia].
  - assert (0 <= X / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma abig_facts : forall Σ m X bs len lo, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> abig_raw Σ m X bs len ->
  0x6e0000 <= X /\ X + 504 <= lo
  /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
  /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo.
Proof using AF.
  intros Σ m X bs len lo HA LO (_ & _ & _ & _ & _ & A8 & FR).
  exact (fframe_obj_facts Σ m X 504 lo HA LO A8 ltac:(lia) eq_refl FR).
Qed.

End ABig.
