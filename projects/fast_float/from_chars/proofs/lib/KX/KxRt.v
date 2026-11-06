(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn M4A_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sb_uar_t : region := track (RGz (lconst 0xe4db8) 12 FxCore.RT TEmpty) 0 (bk8 SHB ++ bkn 4 1).
Lemma sb_uar_c_eq : sb_uar_c = sb_uar_t. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rt_rgs_t : list region :=
  [ RG (lconst 0xe4620) (lconst 8) FxCore.RT (put_bytes (put_bytes TEmpty 0 [BK 1]) 4 (bkn 4 0));
    track (RGz (lconst 0xe5a98) 2 FxCore.RT TEmpty) 0 [BK 1; BK 1];
    track (RGz (lconst 0xe5aa0) 24 FxCore.RT TEmpty) 0 (bk8 (KTOP - 1) ++ bk8 0 ++ bk8 0);
    track (RGz (lconst 0x174858) 4 FxCore.RT TEmpty) 0 (bkn 4 0);
    track (RGz (lconst 0x176971) 1 FxCore.RT TEmpty) 0 [BV FB 0];
    track (RGz (lconst 0x617f28) 8 FxCore.RT TEmpty) 0 (bk8 0x639328);
    track (track (track (track (RGz (lconst 0x617f78) 56 FxCore.RT TEmpty) 0 (bk8 0x617fa0)) 8 (bv8 FS)) 16 (bv8 BLK)) 48 (bk8 0x618780);
    track (RGz (lconst 0x639328) 8 FxCore.RT TEmpty) 0 (bv8 CTX);
    track (RGz (laddc CTX 152) 8 FxCore.RT TEmpty) 0 (bv8 THR);
    track (RGz (laddc THR 48) 16 FxCore.RT TEmpty) 0 (bv8 TLSB ++ bv8 TLSE);
    track (RGz (laddc BLK 24) 8 FxCore.RT TEmpty) 0 (bv8 BEG) ].
Lemma rt_rgs_c_eq : rt_rgs_c = rt_rgs_t. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ws_nort (rgs : list region) (ws : list nat) : bool :=
  forallb (fun j => match nth_error rgs j with Some R => negb (is_rt (rg_kind R)) | None => true end) ws.

(* [comment removed for export] *)
Lemma rt_frame : forall E rgs (ws : list nat) (x : word),
  rgs_disj E rgs -> ws_nort rgs ws = true ->
  Exists (fun R => is_rt (rg_kind R) = true /\ in_rg E R x) rgs ->
  forall j Rj, In j ws -> nth_error rgs j = Some Rj ->
    ~ (bv_unsigned (lden E (rg_base Rj)) <= bv_unsigned x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj).
Proof.
  intros E rgs ws x HD Hw Hx j Rj Hj HRj Hin.
  apply Exists_exists in Hx as (R & HR & Hrt & Hxin). apply In_nth_error in HR as (i & Hi).
  unfold ws_nort in Hw. rewrite forallb_forall in Hw. pose proof (Hw j Hj) as Hb. rewrite HRj in Hb.
  destruct (Nat.eq_dec i j) as [->|Hij].
  - rewrite Hi in HRj. injection HRj as <-. rewrite Hrt in Hb. discriminate.
  - pose proof (rgs_disj_nth E rgs i j R Rj HD Hij Hi HRj) as D. unfold rg_disj, in_rg in *. lia.
Qed.


(* [comment removed for export] *)
Lemma rt_out_ok : forall E need, 0 <= need -> Forall (fact_ok E) (rt_out need) ->
  (bv_unsigned (E 15%positive) + 160 <= bv_unsigned (E 4%positive) - need \/ bv_unsigned (E 4%positive) <= bv_unsigned (E 15%positive)) /\
  (bv_unsigned (E 16%positive) + 80 <= bv_unsigned (E 4%positive) - need \/ bv_unsigned (E 4%positive) <= bv_unsigned (E 16%positive)) /\
  (bv_unsigned (E 17%positive) + 32 <= bv_unsigned (E 4%positive) - need \/ bv_unsigned (E 4%positive) <= bv_unsigned (E 17%positive)).
Proof.
  intros E need Hn HO. unfold rt_out in HO. cbn [List.flat_map app] in HO.
  apply Forall_cons_iff in HO as [O1 HO]. apply Forall_cons_iff in HO as [O2 HO]. apply Forall_cons_iff in HO as [O3 _].
  cbn [fact_ok] in O1, O2, O3. lnorm_in O1. lnorm_in O2. lnorm_in O3. rewrite !u_Z_to_bv in O1, O2, O3. unfold vz in *.
  pose proof (bv_unsigned_in_range _ (E 4%positive)) as B4. pose proof (bv_unsigned_in_range _ (E 15%positive)) as B15.
  pose proof (bv_unsigned_in_range _ (E 16%positive)) as B16. pose proof (bv_unsigned_in_range _ (E 17%positive)) as B17.
  unfold bv_modulus in B4, B15, B16, B17. change (2 ^ Z.of_N 64) with two64 in B4, B15, B16, B17.
  set (sp := bv_unsigned (E 4%positive)) in *. set (c := bv_unsigned (E 15%positive)) in *.
  set (t := bv_unsigned (E 16%positive)) in *. set (b := bv_unsigned (E 17%positive)) in *.
  assert (K : forall X n, 0 <= X < two64 -> 0 <= sp < two64 -> 0 <= n ->
            0 <= (0 + (18446744073709551615 * sp + (1 * X + 0))) mod two64 <= 2 ^ 64 - need - n -> X + n <= sp - need \/ sp <= X).
  { intros X n HX Hs Hn' H. destruct (Z.le_gt_cases sp X) as [Hle|Hlt]; [right; exact Hle|left].
    assert (Hm : (0 + (18446744073709551615 * sp + (1 * X + 0))) mod two64 = X - sp + two64).
    { symmetry. apply Z.mod_unique with (q := sp - 1). - unfold two64 in *; lia. - unfold two64. ring. }
    rewrite Hm in H. unfold two64 in *. lia. }
  split; [|split].
  - exact (K c 160 B15 B4 ltac:(lia) O1).
  - exact (K t 80 B16 B4 ltac:(lia) O2).
  - exact (K b 32 B17 B4 ltac:(lia) O3).
Qed.

(* [comment removed for export] *)
Lemma zeros_bytes_of_rt : forall (segs : list Segment) E m R A n, rg_ok segs E m R ->
  tracked_b (rg_cont R) 0 (List.repeat (BK 0) n) = true -> (0 < n)%nat ->
  bv_unsigned (lden E (rg_base R)) = A -> bytes_at segs m A (repeat (Z_to_bv 8 0) n).
Proof.
  intros segs E m R A n HR Hb Hn HA. pose proof (cont_bytes_at segs E m R 0 _ HR ltac:(lia) ltac:(rewrite repeat_length; exact Hn) Hb) as X.
  rewrite HA, Z.add_0_r, map_repeat in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma u_laddc_var : forall E (x : positive) k, 0 <= k -> bv_unsigned (E x) + k < two64 ->
  bv_unsigned (lden E (laddc (lvar x) k)) = bv_unsigned (E x) + k.
Proof.
  intros E x k Hk Hr. pose proof (bv_unsigned_in_range _ (E x)) as B. unfold bv_modulus in B. change (2 ^ Z.of_N 64) with two64 in B.
  rewrite lden_laddc, lden_lvar, u_Z_to_bv. apply Z.mod_small. lia.
Qed.
Lemma u_ctx152 : forall E, bv_unsigned (E 15%positive) <= 2 ^ 47 - 160 -> bv_unsigned (lden E (laddc CTX 152)) = bv_unsigned (E 15%positive) + 152.
Proof. intros E H. apply u_laddc_var; unfold two64; lia. Qed.
Lemma u_thr48 : forall E, bv_unsigned (E 16%positive) <= 2 ^ 47 - 80 -> bv_unsigned (lden E (laddc THR 48)) = bv_unsigned (E 16%positive) + 48.
Proof. intros E H. apply u_laddc_var; unfold two64; lia. Qed.
Lemma u_blk24 : forall E, bv_unsigned (E 17%positive) <= 2 ^ 47 - 32 -> bv_unsigned (lden E (laddc BLK 24)) = bv_unsigned (E 17%positive) + 24.
Proof. intros E H. apply u_laddc_var; unfold two64; lia. Qed.
