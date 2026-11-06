(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxRgs FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem MState Exec Frame Cells Step Image Bridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Fn.
Variable segs : list Segment.

#[using="Type"] Lemma isteps_msteps : forall ms ms', isteps segs ms ms' -> Exec.msteps segs ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 Hs Hst Hi IH]; [apply msteps_refl|].
  eapply msteps_cons; [split; eassumption | exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem fn_evt : forall (Q : machine_state -> Prop) t img ins depth p P0 finals E ms0,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p P0 = Some finals ->
  sden segs E P0 ms0 -> bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins ins (s_rgs P0) = true ->
  (forall L E' ms', In L finals -> isteps segs ms0 ms' -> sden segs E' L ms' -> (forall x, In x ins -> E' x = E x) ->
     (forall x, FxStep.outside E (s_rgs P0) x -> ms_mem ms' x = ms_mem ms0 x) -> shape (s_rgs L) = shape (s_rgs P0) ->
     evt segs Q ms') ->
  evt segs Q ms0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Q t img ins depth p P0 finals E ms0 Ht Himg Hck Hd Hwf Hbi K.
  destruct (check_frame segs t img ins depth p P0 finals Ht Himg Hck E ms0 Hd Hwf Hbi)
    as (L & ms' & E' & HL & Hst & Hd' & Hins & Hfr & Hsh & _).
  apply (evt_msteps segs Q ms0 ms' (isteps_msteps _ _ Hst)).
  exact (K L E' ms' HL Hst Hd' Hins Hfr Hsh).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fn_ret_step : forall E L ms w,
  sden segs E L ms -> s_resv L = RNone -> fetch_word segs (Z_to_bv 64 (s_pc L)) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr (0%bv) (1%bv) (0%bv), 4%Z) ->
  Exec.mstep segs ms (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ret_pc (getr (ms_regs ms) 1)) (ms_mem ms) (ms_rom ms)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms w Hd Hr Hf He Hdec. pose proof (sden_svc _ _ _ _ Hd) as Hs.
  split; [exact Hs|]. rewrite (sden_mkst segs E L ms Hd Hr) at 1.
  rewrite (step_jalr_gen segs (ms_regs ms) (Z_to_bv 64 (s_pc L)) (ms_mem ms) (ms_rom ms) w 0%bv 1%bv 0%bv Hf He Hdec).
  rewrite bv_eqb_refl. f_equal. f_equal. rewrite ret_pc_landZ. unfold jalr_tgt, jalr_tgtZ. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_rw_of_stk : forall E m b n lo, bv_unsigned (lden E b) = lo -> 0 <= n < 2 ^ 64 -> lo + n <= 2 ^ 64 ->
  stk segs m lo (lo + n) -> rg_ok segs E m (RGz b n RW TEmpty).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m b n lo Hb Hn Hhi (S1 & S2 & S). unfold rg_ok.
  assert (Hs : rsz E (RGz b n RW TEmpty) = n) by (apply rsz_RGz; unfold two64; lia). rewrite Hs. cbn [RGz rg_base rg_kind rg_cont]. rewrite Hb.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. destruct (S (lo + i) ltac:(lia)) as (W & (bb & R)). split; [|exact W].
    unfold rd1. unfold mrd in R. unfold wa in R. rewrite R. discriminate.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Type"] Lemma stk_of_rg_rw : forall E m R lo n, rg_ok segs E m R -> rg_kind R = RW -> bv_unsigned (lden E (rg_base R)) = lo ->
  rsz E R = n -> stk segs m lo (lo + n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R lo n HR Hk Hb Hn. unfold rg_ok in HR. cbv zeta in HR. destruct HR as (H1 & H2 & H3 & _). rewrite Hk in H3.
  rewrite Hb, Hn in *. pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as B. unfold bv_modulus in B.
  split; [lia|]. split; [unfold two64 in H2; lia|]. intros a Ha. destruct (H3 (a - lo) ltac:(lia)) as (R1 & W1).
  replace (lo + (a - lo)) with a in R1, W1 by lia. split; [exact W1|].
  unfold rd1 in R1. unfold mrd, wa. destruct (m (Z_to_bv 64 a)) as [bb|]; [exists bb; reflexivity|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [bb|]; [exists bb; reflexivity | exfalso; exact (R1 eq_refl)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ro_none : forall E m R, rg_ok segs E m R -> rg_kind R = RO ->
  forall i, 0 <= i < rsz E R -> m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros E m R HR Hk i Hi. unfold rg_ok in HR. cbv zeta in HR. destruct HR as (_ & _ & H3 & _). specialize (H3 i Hi). rewrite Hk in H3. exact (proj1 H3). Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma rg_rw_of_cells : forall E m b A cs, bv_unsigned (lden E b) = A -> A + Z.of_nat (cells_size cs) < 2 ^ 64 ->
  rw_cells segs m A cs -> rg_ok segs E m (RGz b (Z.of_nat (cells_size cs)) RW TEmpty).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m b A cs Hb Hn ((Hwf & (B1 & B2 & B)) & (W1 & W2 & W)). unfold rg_ok.
  assert (Hs : rsz E (RGz b (Z.of_nat (cells_size cs)) RW TEmpty) = Z.of_nat (cells_size cs)) by (apply rsz_RGz; unfold two64; lia).
  rewrite Hs. cbn [RGz rg_base rg_kind rg_cont]. rewrite Hb.
  rewrite cells_bytes_length in B2, B by exact Hwf.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. split; [|exact (W i Hi)].
    pose proof (B (Z.to_nat i) ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. unfold rd1. unfold mrd, wa in R.
    destruct (nth_error (cells_bytes cs) (Z.to_nat i)) eqn:Hn'; [|apply nth_error_None in Hn'; rewrite cells_bytes_length in Hn' by exact Hwf; lia].
    rewrite R. discriminate.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Type"] Lemma cells4_of_rg_rw : forall E m R A, rg_ok segs E m R -> rg_kind R = RW -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = 4 ->
  exists r', rw_cells segs m A [C4 r'].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A HR Hk Hb Hn. unfold rg_ok in HR. cbv zeta in HR. destruct HR as (H1 & H2 & H3 & _). rewrite Hk in H3. rewrite Hb, Hn in *.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as BR. unfold bv_modulus in BR.
  assert (Hrd : forall i, 0 <= i < 4 -> exists bb, mrd segs m (wa (A + i)) = Some bb).
  { intros i Hi. destruct (H3 i Hi) as (R1 & _). unfold rd1 in R1. unfold mrd, wa.
    destruct (m (Z_to_bv 64 (A + i))) as [bb|]; [exists bb; reflexivity|].
    destruct (seg_rom segs (Z_to_bv 64 (A + i))) as [bb|]; [exists bb; reflexivity | exfalso; exact (R1 eq_refl)]. }
  destruct (Hrd 0 ltac:(lia)) as (b0 & E0). destruct (Hrd 1 ltac:(lia)) as (b1 & E1). destruct (Hrd 2 ltac:(lia)) as (b2 & E2). destruct (Hrd 3 ltac:(lia)) as (b3 & E3).
  exists (Z_to_bv 64 (lez [b0; b1; b2; b3])). split.
  - split; [cbn; split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    assert (HL : le4 (Z_to_bv 64 (lez [b0; b1; b2; b3])) = [b0; b1; b2; b3]).
    { unfold le4. rewrite u_small64 by (pose proof (lez_bound_len [b0; b1; b2; b3] 4 eq_refl) as X; unfold two64; lia).
      exact (Z_to_le_bytes_lez [b0; b1; b2; b3]). }
    rewrite HL. split; [lia|]. split; [cbn [length]; unfold two64 in H2; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|[|[|[|i]]]]; [exact E0 | exact E1 | exact E2 | exact E3 | lia].
  - split; [lia|]. split; [cbn [cells_size csize]; unfold two64 in H2; lia|]. intros i Hi. cbn [cells_size csize] in Hi.
    exact (proj2 (H3 i ltac:(lia))).
Qed.

End Fn.
