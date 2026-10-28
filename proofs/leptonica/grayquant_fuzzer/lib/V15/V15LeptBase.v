(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib LeptDefs LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptStderr V15_code_15000_16000 V15_code_28000_29000.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

#[export] Instance LLU16 : LeptLayout := {|
  ll_hcell := 0x35270; ll_devnull := 0x154e8;
  ll_clr := [(0x341a8, 0x34240); (0x35268, 0x35270); (0x35278, 0x35288)];
  ll_ro := (0x10000, 0x34000); ll_img := (0x10000, 0x67000);
  ll_lg := (0x454f0, 0x658b8); ll_ag := (0x658b8, 0x65c68); ll_errno := (0x4551c, 0x45520) |}.

(* [comment removed for export] *)
Definition LSF : Z := 3376.

(* [comment removed for export] *)
Class V15Pins {AL : AllocLayout} {CL : CallocLayout} : Prop := {
  p16_segs : al_segs = SEGS;
  p16_malloc : al_malloc_pc = Z_to_bv 64 0x28b94;
  p16_free : al_free_pc = Z_to_bv 64 0x28a54;
  p16_calloc : al_calloc_pc = Z_to_bv 64 0x2891c;
  p16_tp : al_gp = Z_to_bv 64 0x455c0 }.

Section Base.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
Let AL_segs : al_segs = SEGS := p16_segs.

#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma W_img16 : forall C A m md i, W C A m md -> 0x10000 <= i < 0x34000 -> m (Z_to_bv 64 i) = None.
Proof. intros C A m md i HW Hi. apply (W_ro C A m md); [exact HW|]. unfold inZ. cbn [fst snd ll_ro LLU16]. rewrite u_Z2bv by lia. exact Hi. Qed.

Local Ltac clr_read HW lo n :=
  rewrite <- AL_segs; rewrite (W_rdn_clr _ _ _ _ lo n HW); [rewrite AL_segs; vm_refl_bv | intros z Hz; cbv [inZs inZ fst snd ll_clr LLU16]; lia | lia | cbn; lia].

Lemma W_sev_got : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x341f8) 8 = Some (Z_to_le_bytes 8 0x35268).
Proof. intros C A m md HW. clr_read HW 0x341f8 8%nat. Qed.

Lemma W_sev : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x35268) 4 = Some (Z_to_le_bytes 4 3).
Proof. intros C A m md HW. clr_read HW 0x35268 4%nat. Qed.

Lemma W_can_got : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x34228) 8 = Some (Z_to_le_bytes 8 0x65828).
Proof. intros C A m md HW. clr_read HW 0x34228 8%nat. Qed.

Lemma W_pmm_malloc : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x35278) 8 = Some (Z_to_le_bytes 8 0x28b94).
Proof. intros C A m md HW. clr_read HW 0x35278 8%nat. Qed.

Lemma W_pmm_free : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x35280) 8 = Some (Z_to_le_bytes 8 0x28a54).
Proof. intros C A m md HW. clr_read HW 0x35280 8%nat. Qed.

Lemma W_hdl16 : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x35270) 8 = Some (Z_to_le_bytes 8 0x154e8).
Proof. intros C A m md HW. rewrite <- AL_segs. pose proof (w_hdl _ _ _ _ HW) as H. cbn [ll_hcell ll_devnull LLU16] in H. rewrite w2b_Z in H by lia. exact H. Qed.

(* [comment removed for export] *)
Lemma canary_any : forall m, exists cv, 0 <= cv < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 0x65828) 8 = Some (Z_to_le_bytes 8 cv).
Proof.
  intros m.
  assert (HT : exists T, rdn SEGS (fun _ => None) (Z_to_bv 64 0x65828) 8 = Some T) by img_exists.
  destruct HT as [T HT]. destruct (rdn_rom_any SEGS m 8 _ _ HT) as (bs & Hbs & L).
  exists (lez bs). split; [| rewrite Hbs, <- L, Z_to_le_bytes_lez; reflexivity].
  pose proof (lez_bound_len bs 8%nat L) as B. cbn in B. lia.
Qed.

(* [comment removed for export] *)
Definition str16 (a k : Z) : Prop := rostr_chk SEGS a k = true /\ 0 <= k <= 200 /\ 0x10000 <= a /\ a + SSP.rostr_win a k <= 0x34000.
Ltac str16_tac :=
  split; [vm_compute; reflexivity
         | match goal with |- context [SSP.rostr_win ?a ?k] =>
             let c := eval vm_compute in (SSP.rostr_win a k) in change (SSP.rostr_win a k) with c end; lia].

Lemma str16_fmt2 : str16 0x11483 16.
Proof. str16_tac. Qed.

Lemma W_rostr : forall C A m md a k, W C A m md -> str16 a k -> SSP.rostr SEGS m a k.
Proof.
  intros C A m md a k HW (Hc & Hk & Ha & Hw).
  assert (Hwin : k + 1 <= SSP.rostr_win a k).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (a + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + k) 8 ltac:(lia)). lia. }
  apply rostr_intro; [lia | unfold SSP.flatZ; lia | exact Hc |].
  intros i Hi. apply (W_img16 C A m md). 1: exact HW. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cs_kept_of_list : forall R R',
  SSP.regs_kept_l [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat R R' -> cs_kept R R'.
Proof.
  intros R R' K. cbn [SSP.regs_kept_l SSP.reg_of] in K.
  destruct K as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & _).
  apply cs_kept_intro; assumption.
Qed.

(* [comment removed for export] *)
Lemma W_sok_win : forall C A m md (a : Z) (n : nat), Cok C -> W C A m md ->
  c_top C - LSTK <= a -> a + Z.of_nat n <= c_top C -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md a n CK HW Hlo Hhi. pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  rewrite <- AL_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) as [b|] eqn:E; [discriminate|].
  exfalso. apply (w_win _ _ _ _ HW x); [unfold win; lia | exact E].
Qed.

(* [comment removed for export] *)
Lemma lept_stderr2_W : forall C A m md regs (s a1 a2 : Z) k1 k2 (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + LSF <= s -> s <= c_top C ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0x11483 -> getr regs 11 = Z_to_bv 64 a1 -> getr regs 12 = Z_to_bv 64 a2 ->
  str16 a1 k1 -> str16 a2 k2 ->
  (forall m' regs', W C A m' md ->
      (forall a : word, ~ (s - LSF <= u a < s) -> m' a = m a) -> mem_grows m m' ->
      cs_kept regs regs' ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15520 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s a1 a2 k1 k2 ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 S1 S2 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro ll_lg ll_ag ll_errno ll_hcell LLU16] in *. unfold LSF in *.
  destruct (canary_any m) as (cv & Hcv & Ccan).
  pose proof S1 as (_ & K1 & A1 & B1). pose proof S2 as (_ & K2 & A2 & B2).
  assert (W1 : k1 + 1 <= SSP.rostr_win a1 k1).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (a1 + k1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a1 + k1) 8 ltac:(lia)). lia. }
  assert (W2 : k2 + 1 <= SSP.rostr_win a2 k2).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (a2 + k2) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a2 + k2) 8 ltac:(lia)). lia. }
  assert (PRE : SSP.spec_pre SEGS (SSP.spec_lept_stderr_s2 LU16) [0x11483; a1; a2; 0x154e8; 0x65828; cv] regs m).
  { unfold SSP.spec_lept_stderr_s2. SSP.spec_unfold. cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
    cbn [SSP.ls_fmts2 SSP.ls_handler_cell SSP.ls_devnull SSP.ls_canary_got SSP.ls_canary SSP.ls_img_lo SSP.ls_img_hi
         SSP.ls_sp_lo SSP.ls_sp_hi SSP.ls_frame LU16].
    rewrite H1, H2, H10, H11, H12. rewrite !u_Z2bv by lia.
    split; [|split; [|split; [|exact Hret]]].
    - split; [split; [reflexivity | lia]|].
      split; [cbn; tauto|].
      split; [exists 16; split; [lia | exact (W_rostr C A m md _ _ HW str16_fmt2)]|].
      split; [split; [reflexivity | lia]|].
      split; [exists k1; split; [lia | exact (W_rostr C A m md a1 k1 HW S1)]|].
      split; [split; [reflexivity | lia]|].
      split; [exists k2; split; [lia | exact (W_rostr C A m md a2 k2 HW S2)]|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (W_hdl16 C A m md HW)]]]|].
      split; [reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (W_can_got C A m md HW)]]]|].
      split; [reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Ccan]]]|].
      split; [intros i Hi; exact (W_img16 C A m md i HW Hi)|].
      split; [split; [lia | exact Hs16]|].
      split; [lia | exact I].
    - split; [lia|]. split; [unfold SSP.flatZ; lia|]. split; [|exact I].
      apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia].
    - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; try lia. all: exact I.
  }
  pose proof (lept_stderr_s2 (fx:=fx)) as CT. unfold SSP.sum_contract in CT.
  destruct (CT [0x11483; a1; a2; 0x154e8; 0x65828; cv] regs m al_rom eq_refl PRE) as (outs & R' & M' & _ & RUN & POST).
  unfold SSP.spec_lept_stderr_s2 in POST. SSP.spec_unfold_in POST. destruct POST as (KEPT & _ & FRMx & GR & _).
  cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_lept_stderr_s2 SSP.ls_entry SSP.ls_frame LU16] in RUN, FRMx.
  rewrite H1 in RUN. rewrite H2, u_Z2bv in FRMx by lia.
  assert (OUT : forall a : word, ~ (s - 3376 <= u a < s) -> M' a = m a).
  { intros a Ha. apply FRMx. split; [lia | exact I]. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | |].
  { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 0x15520) by (apply bv_eq; reflexivity) end.
    exact RUN. }
  apply HK.
  - apply (W_mod_local C A m M' md CK HW).
    + intros a Ha. left. unfold win. destruct (Z_lt_ge_dec (u a) (s - 3376)); [exfalso; apply Ha; apply OUT; lia|].
      destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply Ha; apply OUT; lia.
    + exact GR.
    + intros a Ha. destruct (Z_lt_ge_dec (u a) (s - 3376)); [rewrite OUT in Ha by lia; exact Ha|].
      destruct (Z_lt_ge_dec (u a) s); [|rewrite OUT in Ha by lia; exact Ha].
      apply (w_win _ _ _ _ HW). unfold win. lia.
  - exact OUT.
  - exact GR.
  - exact (cs_kept_of_list regs R' KEPT).
Qed.

(* [comment removed for export] *)
Lemma lept_stderr1_W : forall C A m md regs (s fmt a1 : Z) kf k1 (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + LSF <= s -> s <= c_top C ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 fmt -> getr regs 11 = Z_to_bv 64 a1 ->
  In fmt (SSP.ls_fmts1 LU16) -> str16 fmt kf -> str16 a1 k1 ->
  (forall m' regs', W C A m' md ->
      (forall a : word, ~ (s - LSF <= u a < s) -> m' a = m a) -> mem_grows m m' ->
      cs_kept regs regs' ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15520 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s fmt a1 kf k1 ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 Hin Sf S1 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro ll_lg ll_ag ll_errno ll_hcell LLU16] in *. unfold LSF in *.
  destruct (canary_any m) as (cv & Hcv & Ccan).
  pose proof Sf as (_ & Kf & Af & Bf). pose proof S1 as (_ & K1 & A1 & B1).
  assert (Wf : kf + 1 <= SSP.rostr_win fmt kf).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (fmt + kf) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fmt + kf) 8 ltac:(lia)). lia. }
  assert (W1 : k1 + 1 <= SSP.rostr_win a1 k1).
  { unfold SSP.rostr_win. pose proof (Z.div_mod (a1 + k1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a1 + k1) 8 ltac:(lia)). lia. }
  assert (PRE : SSP.spec_pre SEGS (SSP.spec_lept_stderr_s1 LU16) [fmt; a1; 0x154e8; 0x65828; cv] regs m).
  { unfold SSP.spec_lept_stderr_s1. SSP.spec_unfold. cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
    cbn [SSP.ls_handler_cell SSP.ls_devnull SSP.ls_canary_got SSP.ls_canary SSP.ls_img_lo SSP.ls_img_hi
         SSP.ls_sp_lo SSP.ls_sp_hi SSP.ls_frame LU16].
    rewrite H1, H2, H10, H11. rewrite !u_Z2bv by lia.
    split; [|split; [|split; [|exact Hret]]].
    - split; [split; [reflexivity | lia]|].
      split; [exact Hin|].
      split; [exists kf; split; [lia | exact (W_rostr C A m md fmt kf HW Sf)]|].
      split; [split; [reflexivity | lia]|].
      split; [exists k1; split; [lia | exact (W_rostr C A m md a1 k1 HW S1)]|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (W_hdl16 C A m md HW)]]]|].
      split; [reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (W_can_got C A m md HW)]]]|].
      split; [reflexivity|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Ccan]]]|].
      split; [intros i Hi; exact (W_img16 C A m md i HW Hi)|].
      split; [split; [lia | exact Hs16]|].
      split; [lia | exact I].
    - split; [lia|]. split; [unfold SSP.flatZ; lia|]. split; [|exact I].
      apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia].
    - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; try lia. all: exact I.
  }
  pose proof (lept_stderr_s1 (fx:=fx)) as CT. unfold SSP.sum_contract in CT.
  destruct (CT [fmt; a1; 0x154e8; 0x65828; cv] regs m al_rom eq_refl PRE) as (outs & R' & M' & _ & RUN & POST).
  unfold SSP.spec_lept_stderr_s1 in POST. SSP.spec_unfold_in POST. destruct POST as (KEPT & _ & FRMx & GR & _).
  cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_lept_stderr_s1 SSP.ls_entry SSP.ls_frame LU16] in RUN, FRMx.
  rewrite H1 in RUN. rewrite H2, u_Z2bv in FRMx by lia.
  assert (OUT : forall a : word, ~ (s - 3376 <= u a < s) -> M' a = m a).
  { intros a Ha. apply FRMx. split; [lia | exact I]. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | |].
  { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 0x15520) by (apply bv_eq; reflexivity) end.
    exact RUN. }
  apply HK.
  - apply (W_mod_local C A m M' md CK HW).
    + intros a Ha. left. unfold win. destruct (Z_lt_ge_dec (u a) (s - 3376)); [exfalso; apply Ha; apply OUT; lia|].
      destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply Ha; apply OUT; lia.
    + exact GR.
    + intros a Ha. destruct (Z_lt_ge_dec (u a) (s - 3376)); [rewrite OUT in Ha by lia; exact Ha|].
      destruct (Z_lt_ge_dec (u a) s); [|rewrite OUT in Ha by lia; exact Ha].
      apply (w_win _ _ _ _ HW). unfold win. lia.
  - exact OUT.
  - exact GR.
  - exact (cs_kept_of_list regs R' KEPT).
Qed.

(* [comment removed for export] *)
Lemma fmts1_16 : forall f, In f [0x10389; 0x10454; 0x10493; 0x108c1; 0x1094b; 0x109e6; 0x10a94; 0x10ac2; 0x10bfa; 0x10cf9; 0x10d7a; 0x10e47; 0x10fe4; 0x11199; 0x1124f; 0x11310; 0x11372] -> In f (SSP.ls_fmts1 LU16).
Proof. intros f H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FRM_rdn16 : forall C s m m' (a : Z) (n : nat), Cok C -> FRM C s m m' ->
  s <= a -> a + Z.of_nat n <= 2 ^ 64 -> c_top C - LSTK <= s ->
  rdn SEGS m' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof. rewrite <- AL_segs. exact (FRM_rdn_above). Qed.

Local Ltac pcfix E :=
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ -> _ =>
    replace pc with (Z_to_bv 64 E) by (apply bv_eq; reflexivity) end.

Lemma W_calloc16 : forall C A m md regs (cnt sz : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + CALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> cs_kept regs regs' ->
      ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
        \/ (u res <> 0 /\ live A res = None /\ live A' res = Some (cnt * sz) /\ live (c_A0 C) res = None /\
            (forall q, q <> res -> live A' q = live A q) /\
            (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) /\
            u res mod 16 = 0 /\ u res + round16 (cnt * sz) <= alloc_top (c_vm C)) ) ->
      POSTM C A s m m' ->
      roomtr A (m_vmmaps md) A' vm' 1 (alloc_margin (cnt * sz)) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x2891c) m al_rom) md) S.
Proof.
  intros until S. rewrite <- AL_segs, <- p16_calloc, <- p16_tp. exact (W_calloc_l C A m md regs cnt sz ret s S).
Qed.

Lemma W_malloc16 : forall C A m md regs (n : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 61 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> cs_kept regs regs' ->
      ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
        \/ (u res <> 0 /\ live A res = None /\ live A' res = Some n /\ live (c_A0 C) res = None /\
            (forall q, q <> res -> live A' q = live A q) /\
            u res mod 16 = 0 /\ u res + round16 n <= alloc_top (c_vm C)) ) ->
      POSTM C A s m m' ->
      roomtr A (m_vmmaps md) A' vm' 1 (alloc_margin n) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x28b94) m al_rom) md) S.
Proof.
  intros until S. rewrite <- AL_segs, <- p16_malloc, <- p16_tp. exact (W_malloc_l C A m md regs n ret s S).
Qed.

Lemma W_free16 : forall C A m md regs (p ret : word) (n s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = p -> live A p = Some n -> live (c_A0 C) p = None ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs',
      W C A' m' (with_vmmaps vm' md) ->
      cs_kept regs regs' ->
      live A' p = None -> (forall q, q <> p -> live A' q = live A q) ->
      POSTM C A' s m m' ->
      roomtr A (m_vmmaps md) A' vm' 0 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x28a54) m al_rom) md) S.
Proof.
  intros until S. rewrite <- AL_segs, <- p16_free, <- p16_tp. exact (W_free_l C A m md regs p ret n s S).
Qed.

(* [comment removed for export] *)
Lemma W_calloc16_sure : forall C A m md regs (cnt sz kR bR : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  aroom A (m_vmmaps md) kR bR -> 1 <= kR -> alloc_margin (cnt * sz) <= bR -> cnt * sz <= ROOM_NMAX ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + CALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> cs_kept regs regs' ->
      u res <> 0 -> live A res = None -> live A' res = Some (cnt * sz) -> live (c_A0 C) res = None ->
      (forall q, q <> res -> live A' q = live A q) ->
      (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) ->
      u res mod 16 = 0 -> u res + round16 (cnt * sz) <= alloc_top (c_vm C) ->
      POSTM C A s m m' ->
      aroom A' vm' (kR - 1) (bR - alloc_margin (cnt * sz)) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x2891c) m al_rom) md) S.
Proof.
  intros until S. rewrite <- AL_segs, <- p16_calloc, <- p16_tp. exact (W_calloc_sure C A m md regs cnt sz kR bR ret s S).
Qed.

Lemma W_malloc16_sure : forall C A m md regs (n kR bR : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 61 ->
  aroom A (m_vmmaps md) kR bR -> 1 <= kR -> alloc_margin n <= bR -> n <= ROOM_NMAX ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> cs_kept regs regs' ->
      u res <> 0 -> live A res = None -> live A' res = Some n -> live (c_A0 C) res = None ->
      (forall q, q <> res -> live A' q = live A q) ->
      u res mod 16 = 0 -> u res + round16 n <= alloc_top (c_vm C) ->
      POSTM C A s m m' ->
      aroom A' vm' (kR - 1) (bR - alloc_margin n) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x28b94) m al_rom) md) S.
Proof.
  intros until S. rewrite <- AL_segs, <- p16_malloc, <- p16_tp. exact (W_malloc_sure C A m md regs n kR bR ret s S).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cellsZ (m : word -> option byte) (l : list (Z * word)) : Prop :=
  match l with
  | [] => True
  | (a, v) :: t => rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) /\ cellsZ m t
  end.

Lemma cellsZ_frm : forall C s' m m' l, Cok C -> FRM C s' m m' -> c_top C - LSTK <= s' ->
  Forall (fun av => s' <= fst av /\ fst av + 8 <= 2 ^ 64) l -> cellsZ m l -> cellsZ m' l.
Proof.
  intros C s' m m' l CK F Hlo HL. induction l as [|[a v] t IH]; intros CE; [exact I|].
  destruct CE as [R CE]. inversion HL as [|x t' [Ha Hn] HL']; subst. cbn in Ha, Hn.
  split; [| exact (IH HL' CE)]. rewrite (FRM_rdn16 C s' m m' a 8 CK F); [exact R | lia | cbn; lia | lia].
Qed.

Lemma cellsZ_keep : forall m m' l,
  Forall (fun av => 0 <= fst av /\ fst av + 8 <= 2 ^ 64 /\ forall x : word, fst av <= u x < fst av + 8 -> m' x = m x) l ->
  cellsZ m l -> cellsZ m' l.
Proof.
  intros m m' l HL. induction l as [|[a v] t IH]; intros CE; [exact I|].
  destruct CE as [R CE]. inversion HL as [|x t' (Ha & Hn & Hd) HL']; subst. cbn in Ha, Hn, Hd.
  split; [| exact (IH HL' CE)]. rewrite <- R. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply Hd. cbn in Hx. lia.
Qed.

Lemma cellsZ_out : forall m m' (lo hi : Z) l, (forall x : word, ~ (lo <= u x < hi) -> m' x = m x) ->
  Forall (fun av => 0 <= fst av /\ fst av + 8 <= 2 ^ 64 /\ (hi <= fst av \/ fst av + 8 <= lo)) l -> cellsZ m l -> cellsZ m' l.
Proof.
  intros m m' lo hi l OUT HL. induction l as [|[a v] t IH]; intros CE; [exact I|].
  destruct CE as [R CE]. inversion HL as [|x t' (Ha & Hn & Hd) HL']; subst. cbn in Ha, Hn, Hd.
  split; [| exact (IH HL' CE)]. rewrite <- R. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT. cbn in Hx. lia.
Qed.

End Base.

(* [comment removed for export] *)
Ltac str16_tac :=
  split; [vm_compute; reflexivity
         | match goal with |- context [SSP.rostr_win ?a ?k] =>
             let c := eval vm_compute in (SSP.rostr_win a k) in change (SSP.rostr_win a k) with c end; lia].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
