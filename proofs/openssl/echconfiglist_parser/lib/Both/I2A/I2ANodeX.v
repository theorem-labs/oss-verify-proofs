(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX ECH_Xpres AsStack0 SecLazy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit I2ANodeM I2ANodeSig I2ANodeS I2AFill.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia0 := Zify.zify; xlia zchecker.
Ltac slia :=
  repeat match goal with
         | HB : @eq bool _ _ |- _ => clear HB
         | HB : _ = Z.min _ _ |- _ => clear HB
         | HB : context [to_Z (Uint63.add _ _)] |- _ => clear HB
         | HB : context [to_Z (Uint63.sub _ _)] |- _ => clear HB
         end;
  Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ptr_arg_inv : forall M v n t off, ptr_arg M v n = Some (t, off) ->
  v = FV t (W64 0 off) /\ t <> 0%uint63 /\ exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= to_Z off
    /\ to_Z off + to_Z n <= to_Z (rg_len rg) /\ to_Z n <= to_Z (rg_len rg).
Proof.
  intros M [tv [top o]] n t off H. unfold ptr_arg in H.
  destruct ((top =? 0) && negb (tv =? 0))%uint63 eqn:E; [|discriminate]. apply andb_true_iff in E as [E1 E2]. apply Uint63.eqb_spec in E1. subst top.
  apply negb_true_iff in E2. apply Uint63.eqb_false_spec in E2.
  destruct (iget tv M) as [rg|] eqn:Hrg; [|discriminate].
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:E; [|discriminate] end. injection H as <- <-.
  rewrite !andb_true_iff in E. destruct E as [[E3 E4] E5]. apply Uint63.leb_spec in E3. apply Z.leb_le in E4. apply Uint63.leb_spec in E5.
  split; [reflexivity|]. split; [exact E2|]. exists rg. repeat split; assumption.
Qed.

Lemma src_arg_inv : forall M v n t off, src_arg M v n = Some (t, off) ->
  (t = 0%uint63 /\ v = FV 0%uint63 (W64 0 off)) \/ (t <> 0%uint63 /\ ptr_arg M v n = Some (t, off)).
Proof.
  intros M [tv [top o]] n t off H. unfold src_arg in H.
  destruct ((tv =? 0) && (top =? 0))%uint63 eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Uint63.eqb_spec in E1. apply Uint63.eqb_spec in E2. subst. injection H as <- <-. left. split; reflexivity.
  - right. pose proof (ptr_arg_inv _ _ _ _ _ H) as (_ & Ht0 & _). split; [exact Ht0| exact H].
Qed.

Lemma rview_mrd : forall m a, rview asegs m a = mrd asegs m a.
Proof. intros m a. unfold rview, mrd, seg_rom. destruct (m a); reflexivity. Qed.

Lemma loc_okb_inv : forall A st (src : bool) t off n, loc_okb A st src t off n = true -> t <> 0%uint63 ->
  let K := ka_K A in
  (t = 1%uint63 /\ exists spo rg1 tp', FxState.rget (a_F st) 2 = FV 1 (W64 tp' spo) /\ iget 1%uint63 (f_mem (a_F st)) = Some rg1
                  /\ to_Z spo <= to_Z off /\ to_Z (rg_lo rg1 + 64)%uint63 <= to_Z off /\ to_Z (off + n + 64)%uint63 <= to_Z (c_stack K))
  \/ (t <> 0%uint63 /\ t <> 1%uint63 /\ (In t (map fst (a_blk st)) \/ In t (map fst (a_ff st)))).
Proof.
  intros A st src t off n H E0 K. unfold loc_okb in H.
  rewrite (proj2 (Uint63.eqb_false_spec _ _) E0) in H.
  destruct (t =? 1)%uint63 eqn:E1.
  - apply Uint63.eqb_spec in E1. left. split; [exact E1|].
    destruct (FxState.rget (a_F st) 2) as [ts [tp' spo]]. destruct (iget 1%uint63 (f_mem (a_F st))) as [rg1|] eqn:Hrg1; [|discriminate].
    rewrite !andb_true_iff in H. destruct H as [[[Hts H1] H2] H3]. apply Uint63.eqb_spec in Hts. subst ts.
    apply Uint63.leb_spec in H1. apply Uint63.leb_spec in H2. apply Uint63.leb_spec in H3.
    exists spo, rg1, tp'. repeat split; assumption.
  - apply Uint63.eqb_false_spec in E1. right. split; [exact E0|]. split; [exact E1|]. unfold is_objb in H. apply orb_true_iff in H.
    destruct H as [H|H]; [left|right]; apply existsb_exists in H as ([t' k'] & Hin & E); cbn [fst] in E; apply Uint63.eqb_spec in E; subst t';
      (apply in_map_iff; eexists; split; [| exact Hin]; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma to_Z_land255 : forall b : int, to_Z (b land 255)%uint63 = to_Z b mod 256.
Proof. intros b. apply (i63_land_ones b 255%uint63 8); [reflexivity| slia0]. Qed.

Lemma acc_bytes_sound {HCEIL : HeapCeil} : forall IM (k : nat) M t (x : int) (D : Z) m (ts : int),
  acc_bytes IM k M t x = true -> t <> 0%uint63 ->
  ts = (if (t =? 1)%uint63 then 2%uint63 else (t + 1)%uint63) ->
  D mod 8 = 0 -> 0 <= D -> to_Z x + Z.of_nat k <= 2 ^ 62 ->
  (forall os b, to_Z x / 8 <= to_Z os -> to_Z os * 8 < to_Z x + Z.of_nat k -> byte_at IM M ts os = SK b ->
     mrd asegs m (wa (sh D + to_Z os)) = Some (Z_to_bv 8 (to_Z b))) ->
  forall z, D + to_Z x <= z < D + to_Z x + Z.of_nat k -> exists v, 0 <= v < 8 /\ mrd asegs m (wa (sh z)) = Some (b8 v) /\ byte_ok v z.
Proof.
  intros IM k. induction k as [|k IH]; intros M t x D m ts Hacc Ht0 Hts HD8 HD0 Hxk Hbyte z Hz; [exfalso; clear - Hz; slia0|].
  pose proof (i63_range x) as Hx.
  cbn [acc_bytes] in Hacc. unfold sh_loc in Hacc. destruct (t =? 0)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; congruence|].
  assert (Esl : (if (t =? 1)%uint63 then (2%uint63, x >> 3) else ((t + 1)%uint63, x >> 3)) = (ts, x >> 3)) by (rewrite Hts; destruct (t =? 1)%uint63; reflexivity).
  rewrite Esl in Hacc. destruct (byte_at IM M ts (x >> 3)) as [b0| |] eqn:Hb; cbn [slot_byte] in Hacc; try discriminate Hacc.
  apply andb_true_iff in Hacc as [Hcond Hrest].
  assert (Ex1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; [reflexivity| slia0]).
  destruct (Z.eq_dec z (D + to_Z x)) as [->|Hne].
  - pose proof (to_Z_land255 b0) as Eb. pose proof (to_Z_land7 x) as E7. pose proof (i63_range b0) as Hb0.
    specialize (Hbyte (x >> 3)%uint63 b0 ltac:(rewrite to_Z_lsr3; slia0) ltac:(rewrite to_Z_lsr3; clear - Hx; Z.div_mod_to_equations; slia0) Hb).
    exists (to_Z b0 mod 256). split; [| split].
    + rewrite orb_true_iff, andb_true_iff in Hcond. destruct Hcond as [E|[E1 E2]].
      * apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Eb in E. change (to_Z 0%uint63) with 0 in E. rewrite E. clear; slia0.
      * apply Uint63.leb_spec in E2. rewrite Eb in E2. change (to_Z 7%uint63) with 7 in E2. clear - E2. Z.div_mod_to_equations. slia0.
    + rewrite to_Z_lsr3 in Hbyte. unfold b8. rewrite Z_to_bv8_mod.
      replace (sh (D + to_Z x)) with (sh D + to_Z x / 8); [exact Hbyte|]. unfold sh. clear - HD8 HD0 Hx. Z.div_mod_to_equations. slia0.
    + unfold byte_ok. rewrite orb_true_iff, andb_true_iff in Hcond. destruct Hcond as [E|[E1 E2]].
      * left. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Eb in E. exact E.
      * right. apply Uint63.leb_spec in E1. rewrite Eb in E1. rewrite Uint63.add_spec, E7 in E1. change (to_Z 1%uint63) with 1 in E1. change wB with (2 ^ 63) in E1.
        rewrite Z.mod_small in E1 by (clear - Hx; Z.div_mod_to_equations; slia0).
        replace ((D + to_Z x) mod 8) with (to_Z x mod 8) by (clear - HD8 HD0 Hx; Z.div_mod_to_equations; slia0). exact E1.
  - apply (IH M t (x + 1)%uint63 D m ts Hrest Ht0 Hts HD8 HD0 ltac:(rewrite Ex1; slia0)).
    + intros os b Hos1 Hos2 Hb'. apply Hbyte; [rewrite Ex1 in Hos1; clear - Hos1 Hx; Z.div_mod_to_equations; slia0| rewrite Ex1 in Hos2; clear - Hos2; slia0| exact Hb'].
    + rewrite Ex1. clear - Hz Hne. slia0.
Qed.

(* [comment removed for export] *)
Lemma acc_bytes_sound0 {HCEIL : HeapCeil} : forall IM (k : nat) M (x : int) m,
  acc_bytes IM k M 0%uint63 x = true -> to_Z x + Z.of_nat k <= 2 ^ 62 ->
  (forall os b, to_Z x / 8 + to_Z shadow_K <= to_Z os -> (to_Z os - to_Z shadow_K) * 8 < to_Z x + Z.of_nat k -> byte_at IM M 3%uint63 os = SK b ->
     mrd asegs m (wa (to_Z os)) = Some (Z_to_bv 8 (to_Z b))) ->
  forall z, to_Z x <= z < to_Z x + Z.of_nat k -> exists v, 0 <= v < 8 /\ mrd asegs m (wa (sh z)) = Some (b8 v) /\ byte_ok v z.
Proof.
  intros IM k. induction k as [|k IH]; intros M x m Hacc Hxk Hbyte z Hz; [exfalso; clear - Hz; slia0|].
  pose proof (i63_range x) as Hx.
  cbn [acc_bytes] in Hacc. unfold sh_loc in Hacc. rewrite Uint63.eqb_refl in Hacc.
  assert (Eos : to_Z ((x >> 3) + shadow_K)%uint63 = to_Z x / 8 + to_Z shadow_K).
  { rewrite to_Z_add_small; rewrite to_Z_lsr3; [reflexivity|]. change (to_Z shadow_K) with 2147450880. clear - Hx Hxk. Z.div_mod_to_equations. slia0. }
  destruct (byte_at IM M 3%uint63 ((x >> 3) + shadow_K)%uint63) as [b0| |] eqn:Hb; cbn [slot_byte] in Hacc; try discriminate Hacc.
  apply andb_true_iff in Hacc as [Hcond Hrest].
  assert (Ex1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; [reflexivity| slia0]).
  destruct (Z.eq_dec z (to_Z x)) as [->|Hne].
  - pose proof (to_Z_land255 b0) as Eb. pose proof (to_Z_land7 x) as E7. pose proof (i63_range b0) as Hb0.
    specialize (Hbyte ((x >> 3) + shadow_K)%uint63 b0 ltac:(rewrite Eos; slia0) ltac:(rewrite Eos; clear - Hx; Z.div_mod_to_equations; slia0) Hb).
    exists (to_Z b0 mod 256). split; [| split].
    + rewrite orb_true_iff, andb_true_iff in Hcond. destruct Hcond as [E|[E1 E2]].
      * apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Eb in E. change (to_Z 0%uint63) with 0 in E. rewrite E. clear; slia0.
      * apply Uint63.leb_spec in E2. rewrite Eb in E2. change (to_Z 7%uint63) with 7 in E2. clear - E2. Z.div_mod_to_equations. slia0.
    + rewrite Eos in Hbyte. unfold b8. rewrite Z_to_bv8_mod.
      replace (sh (to_Z x)) with (to_Z x / 8 + to_Z shadow_K); [exact Hbyte|]. unfold sh. rewrite ASHADOW_BASE_val. change (to_Z shadow_K) with 2147450880. clear. slia0.
    + unfold byte_ok. rewrite orb_true_iff, andb_true_iff in Hcond. destruct Hcond as [E|[E1 E2]].
      * left. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Eb in E. exact E.
      * right. apply Uint63.leb_spec in E1. rewrite Eb in E1. rewrite Uint63.add_spec, E7 in E1. change (to_Z 1%uint63) with 1 in E1. change wB with (2 ^ 63) in E1.
        rewrite Z.mod_small in E1 by (clear - Hx; Z.div_mod_to_equations; slia0). exact E1.
  - apply (IH M (x + 1)%uint63 m Hrest ltac:(rewrite Ex1; slia0)).
    + intros os b Hos1 Hos2 Hb'. apply Hbyte; [rewrite Ex1 in Hos1; clear - Hos1 Hx; Z.div_mod_to_equations; slia0| rewrite Ex1 in Hos2; clear - Hos2; slia0| exact Hb'].
    + rewrite Ex1. clear - Hz Hne. slia0.
Qed.

(* [comment removed for export] *)
Section NodeX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Local Abbreviation IM := (im_ro IMX).
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HIMX : image_ok asegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Let HH : asan_rt_hyps H := proj1 HHx.

  Ltac hk_err :=
    let E1 := fresh "Eerr" in let E2 := fresh "Eerr8" in let E3 := fresh "Ebi" in let E4 := fresh "Ewin" in let E5 := fresh "Eac" in
    let E6 := fresh "Etp" in let E7 := fresh "Em1" in let E8 := fresh "Em2" in let E9 := fresh "Em3" in let E10 := fresh "Em4" in
    let E11 := fresh "Ef1" in let E12 := fresh "Ef2" in let E13 := fresh "Ef3" in let E14 := fresh "Ef4" in
    let E15 := fresh "Est16" in let E16 := fresh "Est40" in
    destruct (HK_err A HK) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16);
    pose proof (i63_range (c_errbi K)); pose proof (i63_range (c_errcell K)); pose proof (i63_range (c_stack K));
    pose proof (i63_range (c_mstack K)).

  (* [comment removed for export] *)
  Lemma stk_of_wview_high : forall m lo hi, AIMG_TOP <= lo -> hi <= 2 ^ 64 ->
    (forall a, lo <= a < hi -> wview asegs m (wa a) <> None) -> stk asegs m lo hi.
  Proof.
    intros m lo hi Hlo Hhi W. split; [unfold AIMG_TOP in Hlo; slia0|]. split; [exact Hhi|]. intros a Ha. split; [exact (W a Ha)|].
    specialize (W a Ha). unfold wview in W. unfold mrd. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply W. rewrite wa_unsigned by (unfold AIMG_TOP in Hlo; clear - Hlo Hhi Ha; slia0). rewrite asegs_find_segment_none_high by (unfold AIMG_TOP in Hlo; clear - Hlo Ha; slia0). reflexivity.
  Qed.

  Lemma mrd_overlay_high : forall m a, AIMG_TOP <= a < 2 ^ 64 -> mrd asegs m (wa a) = m (wa a).
  Proof.
    intros m a Ha. unfold mrd. destruct (m (wa a)); [reflexivity|]. unfold seg_rom, memory_read.
    rewrite wa_unsigned by (unfold AIMG_TOP in Ha; slia0). rewrite asegs_find_segment_none_high by (unfold AIMG_TOP in Ha; slia0). reflexivity.
  Qed.

  Lemma stk_keep : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' ->
    (forall a, lo <= a < hi -> m' (wa a) = m (wa a) \/ exists b, mrd asegs m' (wa a) = Some b) -> stk asegs m' lo hi.
  Proof.
    intros m m' lo hi (S0 & S1 & S) WM K. split; [exact S0|]. split; [exact S1|]. intros a Ha. destruct (S a Ha) as [W [b Hb]].
    split; [apply WM; exact W|]. destruct (K a Ha) as [E|[b' Hb']]; [| exists b'; exact Hb']. exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma u8arr_stk : forall m a bs, u8arr asegs m a bs -> stk asegs m a (a + Z.of_nat (length bs)).
  Proof.
    intros m a bs [(B0 & B1 & BY) (_ & _ & W)]. split; [exact B0|]. split; [exact B1|]. intros x Hx. split; [replace x with (a + (x - a)) by slia0; apply W; slia0|].
    set (i := Z.to_nat (x - a)). replace x with (a + Z.of_nat i) by (subst i; clear - Hx; slia0). exists (nth i bs (b8 0)). rewrite BY by (subst i; clear - Hx; slia0). apply nth_error_nth'. subst i; clear - Hx; slia0.
  Qed.

  Lemma wa_id : forall w : word, wa (bv_unsigned w) = w.
  Proof. intros w. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

  Lemma pw_keep : forall (m m' : AsShadow.mem) (x : word), m' x = m x ->
    rview asegs m' x = rview asegs m x /\ (wview asegs m x <> None -> wview asegs m' x <> None).
  Proof. intros m m' x E. split; [unfold rview; rewrite E; reflexivity| unfold wview; rewrite E; intros W'; exact W']. Qed.

  Lemma pw_keep' : forall (m m' : AsShadow.mem) (x : word), m' x = m x ->
    m' x = m x /\ (wview asegs m x <> None -> wview asegs m' x <> None).
  Proof. intros m m' x E. split; [exact E| unfold wview; rewrite E; intros W'; exact W']. Qed.

  Lemma app_vs_shX : forall A0 n B k, aapp A0 n -> 0 <= n -> aapp B k -> 0 <= k -> A0 + n <= sh B \/ sh B + nsh k <= A0.
  Proof.
    intros A0 n B k APA Hn APB Hk. acb. pose proof (sh_aapp_range B k APB Hk) as (X1 & X2 & X3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in X1.
    clear APB. destruct APA as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO, AIMG_TOP in *; slia0.
  Qed.

  (* [comment removed for export] *)
  Lemma acc_head : forall IMz M t x k, acc_bytes IMz (S k) M t x = true -> t <> 0%uint63 -> to_Z t + 1 < 2 ^ 63 ->
    exists b rgs p c, byte_at IMz M (if (t =? 1)%uint63 then 2%uint63 else (t + 1)%uint63) (x >> 3) = SK b
      /\ iget (if (t =? 1)%uint63 then 2%uint63 else (t + 1)%uint63) M = Some rgs
      /\ iget ((x >> 3) >> 12) (rg_pages rgs) = Some p /\ iget (((x >> 3) land 4095) >> 3) (pg_cells p) = Some c.
  Proof.
    intros IMz M t x k Hacc Ht0 Ht62. cbn [acc_bytes] in Hacc. unfold sh_loc in Hacc. destruct (t =? 0)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; congruence|].
    assert (Esl : (if (t =? 1)%uint63 then (2%uint63, x >> 3) else ((t + 1)%uint63, x >> 3)) = ((if (t =? 1)%uint63 then 2%uint63 else (t + 1)%uint63), x >> 3)) by (destruct (t =? 1)%uint63; reflexivity).
    rewrite Esl in Hacc. set (ts := if (t =? 1)%uint63 then 2%uint63 else (t + 1)%uint63) in *.
    destruct (byte_at IMz M ts (x >> 3)) as [b| |] eqn:Hb; cbn [slot_byte] in Hacc; try discriminate Hacc.
    exists b. pose proof Hb as Hb0. unfold byte_at in Hb.
    assert (Ets0 : (ts =? 0)%uint63 = false).
    { subst ts. destruct (t =? 1)%uint63; [reflexivity|]. destruct (t + 1 =? 0)%uint63 eqn:E; [|reflexivity]. exfalso.
      apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Uint63.add_spec in E. change (to_Z 1%uint63) with 1 in E. change (to_Z 0%uint63) with 0 in E.
      change wB with (2 ^ 63) in E. pose proof (i63_range t). rewrite Z.mod_small in E by slia0. slia0. }
    rewrite Ets0 in Hb. destruct (iget ts M) as [rgs|] eqn:Hrgs; [|discriminate Hb]. destruct (iget ((x >> 3) >> 12) (rg_pages rgs)) as [p|] eqn:Hp; [|discriminate Hb].
    destruct (iget (((x >> 3) land 4095) >> 3) (pg_cells p)) as [c|] eqn:Hc; [|discriminate Hb].
    exists rgs, p, c. split; [first [exact Hb0| reflexivity]| split; [reflexivity| split; [exact Hp| exact Hc]]].
  Qed.

  (* [comment removed for export] *)
  Lemma range_obj : forall Q st rho msF mo s LB G FF XS ms (src : bool) (td o n off : int) rgd,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    FxState.rget (a_F st) 2 = FV 1 (W64 0 off) -> to_Z (ka_istack A) <= to_Z off -> to_Z off <= to_Z (c_stack K) ->
    to_Z (a_n st) < 2 ^ 59 ->
    td <> 0%uint63 -> iget td (f_mem (a_F st)) = Some rgd -> to_Z (rg_lo rgd) <= to_Z o ->
    to_Z o + to_Z n <= to_Z (rg_len rgd) -> to_Z n <= to_Z (rg_len rgd) -> to_Z n <= 65536 ->
    loc_okb A st src td o n = true -> acc_bytes IM (Z.to_nat (to_Z n)) (f_mem (a_F st)) td o = true ->
    let SP := q_sp0 Q - to_Z (c_stack K) + to_Z off in
    let ts := if (td =? 1)%uint63 then 2%uint63 else (td + 1)%uint63 in
    exists D : Z,
     (      rho td = wa D /\ 0 <= D /\ D mod 8 = 0 /\ AIMG_TOP <= D
      /\ rg_lo rgd = 0%uint63 /\ rg_dflt rgd = Some PKUnk /\ (forall pn p, iget pn (rg_pages rgd) = Some p -> pg_kind p = PKUnk)
      /\ to_Z o + to_Z n <= to_Z (rg_len rgd) /\ D + to_Z (rg_len rgd) <= AAPP_HI
      /\ (td = 1%uint63 -> D = q_sp0 Q - to_Z (c_stack K) /\ SP <= D + to_Z o /\ 64 <= to_Z o /\ to_Z o + to_Z n + 64 <= to_Z (c_stack K))
      /\ (td <> 1%uint63 -> D + to_Z (rg_len rgd) <= aceil /\ aapp D (to_Z (rg_len rgd)) /\ 1 <= to_Z (rg_len rgd)
            /\ ((exists g, In g G /\ g_tag g = td /\ g_addr g = D /\ g_size g = rg_len rgd) \/ (exists f, In f FF /\ f_tag f = td /\ f_ff f = D /\ I2RunA.fsz (f_k f) = rg_len rgd)))
      /\ (shvis (ms_mem ms) (D + to_Z o) (D + to_Z o + to_Z n) /\ in_app_mem (D + to_Z o) (D + to_Z o + to_Z n) /\ aconst_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ aclient_write_ok H LB (D + to_Z o, D + to_Z o + to_Z n) /\ stack0_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ afs_write_ok H (LF_of Q FF) (D + to_Z o, D + to_Z o + to_Z n)
          /\ (D + to_Z o + to_Z n <= q_lo Q \/ SP <= D + to_Z o) /\ D + to_Z o + to_Z n <= q_sp0 Q
          /\ (forall a, client0 H Q a -> ~ named_addr Q a -> ~ rin_ivs XS a -> ~ (D + to_Z o <= a < D + to_Z o + to_Z n)))
      /\ (Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem (a_F st)) = Some rgs /\ rho ts = wa (sh D) /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7
            /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs)))
     /\ accessible (ms_mem ms) (D + to_Z o) (to_Z n)
     /\ (forall hi, D + to_Z o <= hi <= D + to_Z (rg_len rgd) -> stk asegs (ms_mem ms) (D + to_Z o) hi).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms src td o n off rgd X Esp2 Hoff1 Hoff2 Hn59 Htd0 Hrgd Hloo Hon Hnlen Hn64k Hloc Hacc SP ts.
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (tn := a_n st) in *.
    pose proof (i63_range tn) as Htn. destruct Xn0 as [Xn0a Xn0b].
    pose proof (i63_range n) as Hn. pose proof (i63_range o) as Ho. pose proof (i63_range td) as Htd.
    assert (Hag : agree tn rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR. pose proof (R_mem _ _ _ _ _ HR) as Hmem. cbn [f_mem] in Hmem. fold F in Hmem.
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Espu : SP = q_sp0 Q - to_Z (c_stack K) + to_Z off) by reflexivity.
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0.
    destruct Xreg1 as (rg1 & Hrg1 & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
    assert (OLDLT : forall x rg, iget x (f_mem F) = Some rg -> to_Z x < to_Z tn).
    { intros x rg Hx. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]];
        [change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia| change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia
        | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia| change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia| ..].
      - apply in_map_iff in Hb as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). pose proof (i63_range (g_tag g)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hf as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 2%uint63) with 2; clear - Htg2 H0 Hn59; slia0). change (to_Z 2%uint63) with 2. clear - Htg2. slia. }
    assert (Htd_lt : to_Z td < to_Z tn) by exact (OLDLT td rgd Hrgd).
    fold F in Esp2, Hloc, Hacc |- *.
    assert (OBJ : exists D : Z,
      rho td = wa D /\ 0 <= D /\ D mod 8 = 0 /\ AIMG_TOP <= D
      /\ rg_lo rgd = 0%uint63 /\ rg_dflt rgd = Some PKUnk /\ (forall pn p, iget pn (rg_pages rgd) = Some p -> pg_kind p = PKUnk)
      /\ to_Z o + to_Z n <= to_Z (rg_len rgd) /\ D + to_Z (rg_len rgd) <= AAPP_HI
      /\ (td = 1%uint63 -> D = q_sp0 Q - to_Z (c_stack K) /\ SP <= D + to_Z o /\ 64 <= to_Z o /\ to_Z o + to_Z n + 64 <= to_Z (c_stack K))
      /\ (td <> 1%uint63 -> D + to_Z (rg_len rgd) <= aceil /\ aapp D (to_Z (rg_len rgd)) /\ 1 <= to_Z (rg_len rgd)
            /\ ((exists g, In g G /\ g_tag g = td /\ g_addr g = D /\ g_size g = rg_len rgd) \/ (exists f, In f FF /\ f_tag f = td /\ f_ff f = D /\ I2RunA.fsz (f_k f) = rg_len rgd)))
      /\ (shvis (ms_mem ms) (D + to_Z o) (D + to_Z o + to_Z n) /\ in_app_mem (D + to_Z o) (D + to_Z o + to_Z n) /\ aconst_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ aclient_write_ok H LB (D + to_Z o, D + to_Z o + to_Z n) /\ stack0_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ afs_write_ok H (LF_of Q FF) (D + to_Z o, D + to_Z o + to_Z n)
          /\ (D + to_Z o + to_Z n <= q_lo Q \/ SP <= D + to_Z o) /\ D + to_Z o + to_Z n <= q_sp0 Q
          /\ (forall a, client0 H Q a -> ~ named_addr Q a -> ~ rin_ivs XS a -> ~ (D + to_Z o <= a < D + to_Z o + to_Z n)))
      /\ (Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ rho ts = wa (sh D) /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7
            /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs))).
    { pose proof (proj1 (proj1 Hmem td rgd Hrgd)) as (_ & Hlen62 & _). destruct Xnamed as [XG0in XLB0nd].
      (* [comment removed for export] *)
      assert (SHD : (Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7) ->
                    to_Z o + to_Z n <= to_Z (rg_len rgd)).
      { intros _. exact Hon. }
      destruct (loc_okb_inv A st src td o n Hloc Htd0) as [(Etd1 & spo & rg1' & tp' & Esp2' & Hrg1' & Hspo & H64 & Hcs64)| (_ & Ntd1 & Hobj)].
      - (* [comment removed for export] *)
        fold F in Esp2', Hrg1'. rewrite Hrg1 in Hrg1'. injection Hrg1' as <-. rewrite Esp2 in Esp2'. injection Esp2' as E0 Espo. subst spo.
        assert (Ergd : rgd = rg1) by (rewrite Etd1 in Hrgd; clear - Hrgd Hrg1; congruence).
        rewrite Hlo1 in H64. change (to_Z (0 + 64)%uint63) with 64 in H64.
        destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
        assert (SHF : Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ rho ts = wa (sh (q_sp0 Q - to_Z (c_stack K))) /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7
                       /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs)).
        { intros _. exists (sh_region false 1%uint63 (c_stack K)). subst ts. rewrite Etd1, Uint63.eqb_refl. split; [exact Xreg2|]. split; [exact Xr2|].
          rewrite Ergd, Hlen1. unfold sh_region. cbn [rg_len]. rewrite (nsh_eq (c_stack K)) by (clear - Hcs Est40; slia). clear - Hcs. split; Z.div_mod_to_equations; slia0. }
        assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by (apply SHD; intros Hk; destruct (SHF Hk) as (rgs & A1 & _ & A3 & _); exists rgs; split; assumption).
        rewrite Ergd, Hlen1 in RNG.
        rewrite !Uint63.add_spec in Hcs64. change (to_Z 64%uint63) with 64 in Hcs64. change wB with (2 ^ 63) in Hcs64. rewrite !Z.mod_small in Hcs64 by (clear - RNG Ho Hn Est40 Hcs; slia0).
        exists (q_sp0 Q - to_Z (c_stack K)). rewrite Etd1. split; [exact Xr1|]. split; [clear - Hhl Hlsp ACEILB; slia|]. split; [clear - Hsp32; Z.div_mod_to_equations; slia|].
        split; [clear - Hhl Hlsp ACEILB; unfold AIMG_TOP; slia|]. rewrite Ergd. split; [exact Hlo1|]. split; [exact Hd1|]. split; [exact Hkd1|].
        split; [rewrite Hlen1; exact RNG|]. split; [rewrite Hlen1; clear - SB2 Hshi; slia|].
        split; [intros _; split; [reflexivity|]; split; [clear - Hspo Espu; slia| split; [exact H64| exact Hcs64]]|].
        split; [intros NE; exfalso; apply NE; reflexivity|].
        assert (DLO : AHI_LO <= q_sp0 Q - to_Z (c_stack K) + to_Z o) by (clear - Hhl Hlsp Ho ACEILB; unfold AHI_LO; slia).
        split; [| intros Hk; destruct (SHF Hk) as (rgs & A1 & A2 & A3); exists rgs; split; [exact A1|]; split; [exact A2|]; rewrite Ergd in A3; exact A3].
        split.
        { (* [comment removed for export] *)
          destruct Xst0 as (g0 & G01 & G02 & G03 & [_ SH0]). pose proof (SHAD_aligned _ _ _ SH0) as [_ G8]. destruct SH0 as (_ & _ & U8).
          pose proof (u8arr_stk _ _ _ U8) as SST. rewrite (shadow_of_length (q_shi Q - g0)) in SST by (clear - G01 G02; slia).
          pose proof (hull_lo_le (q_sp0 Q - to_Z (c_stack K) + to_Z o) ltac:(clear - DLO; unfold AHI_LO in DLO; slia)) as (HL1 & HL2 & HL3).
          pose proof (hull_hi_ge (q_sp0 Q - to_Z (c_stack K) + to_Z o + to_Z n) ltac:(clear - DLO Hn; unfold AHI_LO in DLO; slia)) as (HH1 & HH2 & HH3).
          replace (sh g0 + nsh (q_shi Q - g0)) with (sh (q_shi Q)) in SST by (clear - G8 G03 G01 G02; unfold sh, nsh; Z.div_mod_to_equations; slia).
          assert (M1' : sh g0 <= sh (hull_lo (q_sp0 Q - to_Z (c_stack K) + to_Z o))) by (apply sh_mono; clear - G01 HL2 H64 Hhl Hlsp; slia).
          assert (M2' : sh (hull_hi (q_sp0 Q - to_Z (c_stack K) + to_Z o + to_Z n)) <= sh (q_shi Q)) by (apply sh_mono; clear - HH2 Hcs64 RNG Hshi Hn; slia).
          unfold shvis. destruct SST as (S0' & S1' & SS). split; [clear - S0' M1'; slia|]. split; [clear - S1' M2'; slia|]. intros a Ha. apply SS. clear - Ha M1' M2'. slia. }
        split; [right; split; [exact DLO| clear - Hcs64 Hshi SB2; slia]|].
        split; [apply aconst_ok_hi; exact DLO|].
        split; [left; cbn [fst]; clear - Hhl Hlsp H64; slia|].
        split; [apply stack0_ok_app; exact DLO|].
        split; [left; cbn [fst snd]; clear - F2 Hhl Hlsp H64 ACEILB; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; slia|].
        split; [right; clear - Hspo Espu; slia|].
        split; [clear - Hcs64 Hn; slia|].
        intros a Hcl Hna Hnx Ha. unfold client0, aclient_addr in Hcl.
        destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        * clear - Hs Ha Hcs64 Hn. slia.
        * clear - Hst Ha Hhl Hlsp H64 ACEILB. unfold aimg_client, AIMG_LO, AIMG_TOP in *. slia.
        * destruct (XLB0h b Hb) as [_ Bh]. clear - Hr Bh Ha Hhl Hlsp H64. slia.
        * destruct (XLB0h b Hb) as [B0 Bh]. pose proof (sh_nsh_high (blk_addr b) (blk_size b) B0 ltac:(clear - Hr; unfold nsh in Hr; Z.div_mod_to_equations; slia) ltac:(clear - Bh ACEILB; unfold AAPP_HI; slia)) as SB.
          clear - Hr SB Ha DLO. slia.
        * clear - Hfs F2 Ha Hhl Hlsp H64. slia.
        * pose proof (sh_below_app (as_FSB H + AFS_SIZE) ltac:(clear - F1 F2 ACEILB; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; slia)) as SB. clear - Hfss SB Ha DLO. slia.
        * clear - Hss Ha DLO. slia.
      - (* [comment removed for export] *)
        destruct Hobj as [Hb|Hf].
        + rewrite XG, map_map in Hb. cbn [fst] in Hb. apply in_map_iff in Hb as (g & Etg & Hg).
          pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
          rewrite Etg in *. assert (Ergd : rgg = rgd) by (clear - Hgg Hrgd; congruence). subst rgg.
          pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
          destruct (Xkinds td rgd Hrgd Htd0) as [_ Hkdd]. pose proof (i63_range (g_size g)) as Hgs0.
          assert (SHF : Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ rho ts = wa (sh (g_addr g)) /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7
                         /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs)).
          { intros Hk. destruct (Z.to_nat (to_Z n)) as [|k] eqn:En; [exfalso; exact (Hk eq_refl)|].
            destruct (acc_head IM (f_mem F) td o k Hacc Htd0 ltac:(clear - Htd_lt Hn59 Htd; slia0)) as (b & rgs & p & cc & Hb' & Hrgs & _). subst ts.
            rewrite (proj2 (Uint63.eqb_false_spec _ _) Ntd1) in Hrgs |- *. destruct (Hshg rgs Hrgs) as (Ers & Hrs & _). exists rgs. split; [exact Hrgs|]. split; [exact Hrs|].
            rewrite Ers, Hleng. unfold sh_region. cbn [rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 Hleng ACEILB Hgs0; slia). clear - Hgs0. split; Z.div_mod_to_equations; slia0. }
          assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by (apply SHD; intros Hk; destruct (SHF Hk) as (rgs & A1 & _ & A3 & _); exists rgs; split; assumption).
          exists (g_addr g). split; [exact Hrg|]. split; [clear - G1; slia|]. split; [clear - G2; Z.div_mod_to_equations; slia|]. split; [exact G4|].
          split; [exact Hlog|]. split; [exact Hdfg|]. split; [exact Hkdd|]. split; [exact RNG|]. rewrite <- Hleng in *. split; [clear - G5 ACEILB; unfold AAPP_HI; slia|].
          split; [intros E; exfalso; exact (Ntd1 E)|].
          split; [intros _; split; [exact G5|]; split; [exact G7|]; split; [exact Hsz|]; left; exists g; repeat split; assumption || reflexivity || (symmetry; assumption)|].
          split; [| exact SHF].
          split; [eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ Xheap Hin)| clear - G1; slia| clear - Ho; slia| clear - RNG; slia| clear - Hn; slia| clear - G1 G3; slia]|].
          split; [destruct G7 as [[Q1 Q2]|[Q1 Q2]]; [left; clear - Q1 Q2 G1 Ho Hn RNG; unfold ALOWSH_LO in *; rewrite ASHADOW_BASE_val; unfold AIMG_TOP in *; slia| right; clear - Q1 Q2 Ho Hn RNG ACEILB; unfold AAPP_HI; slia]|].
          split; [eapply aconst_ok_aapp; [exact G7| clear - Ho; slia| clear - RNG; slia]|].
          split; [do 2 right; left; eexists; split; [exact Hin| cbn [blk_addr blk_size fst snd]; clear - Ho RNG; slia]|].
          split; [eapply stack0_ok_aapp; [exact G7| cbn [fst]; clear - Ho; slia| cbn [snd]; clear - RNG; slia]|].
          split; [left; cbn [fst snd]; clear - G4 G6 Ho RNG Hn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; slia|].
          split; [left; clear - G5 Hhl RNG; slia|].
          split; [clear - G5 Hhl Hlsp RNG Hcs; slia|].
          intros a Hcl Hna Hnx Ha. pose proof (proj1 (Forall_forall _ _) XGnew g Hg) as [Hn0 | [Hfr _]].
          * apply Hna. exists g. split; [exact Hn0|]. left. rewrite <- Hleng. clear - Ha Ho RNG. slia.
          * apply (proj1 (Hfr a Hcl Hna)). rewrite <- Hleng. clear - Ha Ho RNG. slia.
        + rewrite XFF, map_map in Hf. cbn [fst] in Hf. apply in_map_iff in Hf as (f & Etg & Hf).
          pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
          rewrite Etg in *. assert (Ergd : rgf = rgd) by (clear - Hgf Hrgd; congruence). subst rgf.
          destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
          pose proof (fsz_eq _ Hkf) as EFZ. pose proof (fsz_fshn (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as [E1 E2].
          destruct (Xkinds td rgd Hrgd Htd0) as [_ Hkdd].
          assert (SHF : Z.to_nat (to_Z n) <> 0%nat -> exists rgs', iget ts (f_mem F) = Some rgs' /\ rho ts = wa (sh (f_ff f)) /\ 8 * to_Z (rg_len rgs') <= to_Z (rg_len rgd) + 7
                         /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs')).
          { intros _. exists rgs. subst ts. rewrite (proj2 (Uint63.eqb_false_spec _ _) Ntd1). split; [exact Hgs|]. split; [exact Hf1|]. rewrite Hlens, Hlenf, EFZ, E2. clear. split; slia0. }
          assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by (apply SHD; intros Hk; destruct (SHF Hk) as (rgs' & A1 & _ & A3 & _); exists rgs'; split; assumption).
          exists (f_ff f). split; [exact Hf0|]. split; [clear - K2' F1; unfold AFS_HDR, AIMG_TOP in *; slia|]. split; [exact (frame_al8 H _ _ _ (conj K1 (conj K2' (conj K3 (conj K4 K5)))))|].
          split; [clear - K2' F1; unfold AFS_HDR in *; slia|]. split; [exact Hlof|]. split; [exact Hdff|]. split; [exact Hkdd|]. split; [exact RNG|].
          rewrite Hlenf, EFZ in *. split; [clear - K3 F2 ACEILB; unfold AAPP_HI; slia|].
          split; [intros E; exfalso; exact (Ntd1 E)|].
          pose proof (aapp_sub (as_FSB H) AFS_SIZE (f_ff f) (AsIface.fsz (to_Z (f_k f))) F4 ltac:(clear - K2'; unfold AFS_HDR in *; slia) K3) as APf.
          split; [intros _; split; [clear - K3 F2; slia|]; split; [exact APf|];
                 split; [clear - FPf; slia|]; right; exists f; split; [exact Hf|]; split; [exact Etg|]; split; [reflexivity|]; first [reflexivity| symmetry; exact Hlenf]|].
          split; [| exact SHF].
          split; [eapply shvis_sub; [exact (ah_frm_shvis H HH _ _ (ff_of f) Xrfs ltac:(unfold LF_of; apply in_or_app; left; apply in_map; exact Hf))| cbn [ff_addr ff_of fst snd]; clear - K2' F1; unfold AFS_HDR, AIMG_TOP in *; slia| cbn [ff_addr ff_of fst snd]; clear - Ho; slia| cbn [ff_addr ff_class ff_of fst snd]; clear - RNG; slia| clear - Hn; slia| cbn [ff_addr ff_class ff_of fst snd]; clear - K2' F1 FPf; unfold AFS_HDR, AIMG_TOP in *; slia]|].
          split; [destruct F4 as [[Q1 Q2]|[Q1 Q2]]; [left; clear - Q1 Q2 K2' K3 F1 Ho Hn RNG; unfold ALOWSH_LO, AFS_HDR, AIMG_TOP in *; rewrite ASHADOW_BASE_val; slia| right; clear - Q1 Q2 K2' K3 F2 Ho Hn RNG ACEILB; unfold AAPP_HI, AFS_HDR in *; slia]|].
          split; [eapply aconst_ok_aapp; [exact APf| clear - Ho; slia| clear - RNG; slia]|].
          split; [do 4 right; left; cbn [fst snd]; clear - K2' K3 Ho RNG; unfold AFS_HDR in *; slia|].
          split; [eapply stack0_ok_aapp; [exact APf| cbn [fst]; clear - Ho; slia| cbn [snd]; clear - RNG; slia]|].
          split; [right; exists (ff_of f); split; [unfold LF_of; apply in_or_app; left; apply in_map; exact Hf| cbn [ff_addr ff_class ff_of fst snd]; clear - Ho RNG; slia]|].
          split; [left; clear - K3 F2 Hhl RNG; slia|].
          split; [clear - K3 F2 Hhl Hlsp RNG Hcs; slia|].
          intros a Hcl Hna Hnx Ha. apply Hnx. apply X2. clear - Ha Ho RNG. slia. }
    destruct OBJ as (D & OBJB). pose proof OBJB as (ErD & HD0 & HD8 & HDtop & Hlod & Hdfd & Hkdd & RNG & HDhi & STK & OBJF & (SHV & IAM & ACO & CWD & S0D & AFD & LOD & SP0D & EXD) & SHF).

    pose proof (proj1 (proj1 Hmem td rgd Hrgd)) as (_ & Hlen62' & _). pose proof (i63_range (rg_len rgd)) as Hld.
    set (d := D + to_Z o) in *.
    assert (ACC : accessible (ms_mem ms) d (to_Z n)).
    { split; [clear - HD0 Ho; subst d; slia|]. split; [clear - HDhi RNG Ho; subst d; slia|].
      destruct (Z.to_nat (to_Z n)) as [|k] eqn:En; [intros z Hz; exfalso; clear - Hz En Hn; slia0|].
      destruct (SHF ltac:(discriminate)) as (rgs & Hrgs & Ers & Hls1 & Hls2). pose proof (i63_range (rg_len rgs)) as Hlsr.
      intros z Hz. apply (acc_bytes_sound IM (S k) (f_mem F) td o D (ms_mem ms) ts); [first [exact Hacc| rewrite <- En; exact Hacc]| exact Htd0| reflexivity| exact HD8| exact HD0
        | rewrite <- En, Z2Nat.id by (clear - Hn; slia0); clear - RNG Hld Hlen62' Ho; slia0| | subst d; rewrite <- En, Z2Nat.id by (clear - Hn; slia0); exact Hz].
      intros os b Hos1 Hos2 Hb. pose proof (i63_range os) as Hos.
      rewrite <- (adr_eq_wa rho ts (sh D) (to_Z os) Ers) by (first [clear - HD0 HDhi Hos Hos2 Hls2 RNG En Hn Hlsr; pose proof (sh_above_image D HD0); unfold sh, AIMG_TOP, AAPP_HI in *; rewrite ?ASHADOW_BASE_val in *; Z.div_mod_to_equations; slia0]).
      assert (Hts0 : ts <> 0%uint63).
      { subst ts. destruct (td =? 1)%uint63; [intros E; discriminate E|]. intros E. apply (f_equal to_Z) in E. rewrite Uint63.add_spec in E.
        change (to_Z 1%uint63) with 1 in E. change (to_Z 0%uint63) with 0 in E. change wB with (2 ^ 63) in E. rewrite Z.mod_small in E by (clear - Htd Htd_lt Hn59; slia0). clear - E Htd. slia0. }
      exact (byte_at_SK_sound asegs IM rho Xr0 (f_mem F) (ms_mem ms) ts os rgs b Hmem Hts0 Hrgs (fun pn p ci cc Hp Hc => Xinb ts rgs pn p ci cc Hrgs Hp Hc)
               ltac:(rewrite <- En, Z2Nat.id in Hos2 by (clear - Hn; slia0); clear - Hos2 Hls2 RNG; Z.div_mod_to_equations; slia0) Hb). }

    assert (SRD : forall hi, d <= hi <= D + to_Z (rg_len rgd) -> stk asegs (ms_mem ms) d hi).
    { intros hi Hhi. destruct (Uint63.eqb td 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. destruct (STK E1) as (ED & SPd & _ & Hcs64). assert (Ergd : rgd = rg1) by (rewrite E1 in Hrgd; clear - Hrgd Hrg1; congruence).
        pose proof (stk_split asegs _ _ d _ Xstk ltac:(clear - SPd Espu Hhl Hlsp Hoff1 Ef2 SP0D Hn; slia)) as [_ S2].
        exact (proj1 (stk_split asegs _ _ hi _ S2 ltac:(rewrite Ergd, Hlen1, ED in Hhi; clear - Hhi; slia))).
      - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & _ & EgD & EgS)|(f0 & Hf0 & _ & EfD & EfS)]).
        + pose proof (proj1 (Forall_forall _ _) XGstk g0 Hg0) as S0. cbn beta in S0. rewrite EgD, EgS in S0.
          pose proof (stk_split asegs _ _ d _ S0 ltac:(clear - Ho Hhi; subst d; slia)) as [_ S2].
          exact (proj1 (stk_split asegs _ _ hi _ S2 ltac:(clear - Hhi; slia))).
        + pose proof (proj1 (Forall_forall _ _) XFFstk f0 Hf0) as S0. cbn beta in S0. rewrite EfD in S0.
          pose proof (proj1 (Forall_forall _ _) XFFin f0 Hf0) as (_ & _ & _ & Hkf0 & _). rewrite <- (fsz_eq _ Hkf0), EfS in S0.
          pose proof (stk_split asegs _ _ d _ S0 ltac:(clear - Ho Hhi; subst d; slia)) as [_ S2].
          exact (proj1 (stk_split asegs _ _ hi _ S2 ltac:(clear - Hhi; slia))). }
    exists D. split; [exact OBJB| split; [exact ACC| exact SRD]].
  Qed.

  (* [comment removed for export] *)
  Lemma range_objW : forall Q st rho msF mo s LB G FF XS ms (src : bool) (td o n off : int) rgd,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    FxState.rget (a_F st) 2 = FV 1 (W64 0 off) -> to_Z (ka_istack A) <= to_Z off -> to_Z off <= to_Z (c_stack K) ->
    to_Z (a_n st) < 2 ^ 59 ->
    td <> 0%uint63 -> iget td (f_mem (a_F st)) = Some rgd -> to_Z (rg_lo rgd) <= to_Z o ->
    to_Z o + to_Z n <= to_Z (rg_len rgd) -> to_Z n <= to_Z (rg_len rgd) -> to_Z n <= 65536 ->
    loc_okb A st src td o n = true ->
    let SP := q_sp0 Q - to_Z (c_stack K) + to_Z off in
    exists D : Z,
     (      rho td = wa D /\ 0 <= D /\ D mod 8 = 0 /\ AIMG_TOP <= D
      /\ rg_lo rgd = 0%uint63 /\ rg_dflt rgd = Some PKUnk /\ (forall pn p, iget pn (rg_pages rgd) = Some p -> pg_kind p = PKUnk)
      /\ to_Z o + to_Z n <= to_Z (rg_len rgd) /\ D + to_Z (rg_len rgd) <= AAPP_HI
      /\ (td = 1%uint63 -> D = q_sp0 Q - to_Z (c_stack K) /\ SP <= D + to_Z o /\ 64 <= to_Z o /\ to_Z o + to_Z n + 64 <= to_Z (c_stack K))
      /\ (td <> 1%uint63 -> D + to_Z (rg_len rgd) <= aceil /\ aapp D (to_Z (rg_len rgd)) /\ 1 <= to_Z (rg_len rgd)
            /\ ((exists g, In g G /\ g_tag g = td /\ g_addr g = D /\ g_size g = rg_len rgd) \/ (exists f, In f FF /\ f_tag f = td /\ f_ff f = D /\ I2RunA.fsz (f_k f) = rg_len rgd)))
      /\ (shvis (ms_mem ms) (D + to_Z o) (D + to_Z o + to_Z n) /\ in_app_mem (D + to_Z o) (D + to_Z o + to_Z n) /\ aconst_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ aclient_write_ok H LB (D + to_Z o, D + to_Z o + to_Z n) /\ stack0_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ afs_write_ok H (LF_of Q FF) (D + to_Z o, D + to_Z o + to_Z n)
          /\ (D + to_Z o + to_Z n <= q_lo Q \/ SP <= D + to_Z o) /\ D + to_Z o + to_Z n <= q_sp0 Q
          /\ (forall a, client0 H Q a -> ~ named_addr Q a -> ~ rin_ivs XS a -> ~ (D + to_Z o <= a < D + to_Z o + to_Z n))))
     /\ (forall hi, D + to_Z o <= hi <= D + to_Z (rg_len rgd) -> stk asegs (ms_mem ms) (D + to_Z o) hi).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms src td o n off rgd X Esp2 Hoff1 Hoff2 Hn59 Htd0 Hrgd Hloo Hon Hnlen Hn64k Hloc SP.
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (tn := a_n st) in *.
    pose proof (i63_range tn) as Htn. destruct Xn0 as [Xn0a Xn0b].
    pose proof (i63_range n) as Hn. pose proof (i63_range o) as Ho. pose proof (i63_range td) as Htd.
    assert (Hag : agree tn rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR. pose proof (R_mem _ _ _ _ _ HR) as Hmem. cbn [f_mem] in Hmem. fold F in Hmem.
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Espu : SP = q_sp0 Q - to_Z (c_stack K) + to_Z off) by reflexivity.
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0.
    destruct Xreg1 as (rg1 & Hrg1 & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
    assert (OLDLT : forall x rg, iget x (f_mem F) = Some rg -> to_Z x < to_Z tn).
    { intros x rg Hx. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]];
        [change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia| change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia
        | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia| change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia| ..].
      - apply in_map_iff in Hb as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). pose proof (i63_range (g_tag g)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hf as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 2%uint63) with 2; clear - Htg2 H0 Hn59; slia0). change (to_Z 2%uint63) with 2. clear - Htg2. slia. }
    assert (Htd_lt : to_Z td < to_Z tn) by exact (OLDLT td rgd Hrgd).
    fold F in Esp2, Hloc |- *.
    assert (OBJ : exists D : Z,
      rho td = wa D /\ 0 <= D /\ D mod 8 = 0 /\ AIMG_TOP <= D
      /\ rg_lo rgd = 0%uint63 /\ rg_dflt rgd = Some PKUnk /\ (forall pn p, iget pn (rg_pages rgd) = Some p -> pg_kind p = PKUnk)
      /\ to_Z o + to_Z n <= to_Z (rg_len rgd) /\ D + to_Z (rg_len rgd) <= AAPP_HI
      /\ (td = 1%uint63 -> D = q_sp0 Q - to_Z (c_stack K) /\ SP <= D + to_Z o /\ 64 <= to_Z o /\ to_Z o + to_Z n + 64 <= to_Z (c_stack K))
      /\ (td <> 1%uint63 -> D + to_Z (rg_len rgd) <= aceil /\ aapp D (to_Z (rg_len rgd)) /\ 1 <= to_Z (rg_len rgd)
            /\ ((exists g, In g G /\ g_tag g = td /\ g_addr g = D /\ g_size g = rg_len rgd) \/ (exists f, In f FF /\ f_tag f = td /\ f_ff f = D /\ I2RunA.fsz (f_k f) = rg_len rgd)))
      /\ (shvis (ms_mem ms) (D + to_Z o) (D + to_Z o + to_Z n) /\ in_app_mem (D + to_Z o) (D + to_Z o + to_Z n) /\ aconst_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ aclient_write_ok H LB (D + to_Z o, D + to_Z o + to_Z n) /\ stack0_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ afs_write_ok H (LF_of Q FF) (D + to_Z o, D + to_Z o + to_Z n)
          /\ (D + to_Z o + to_Z n <= q_lo Q \/ SP <= D + to_Z o) /\ D + to_Z o + to_Z n <= q_sp0 Q
          /\ (forall a, client0 H Q a -> ~ named_addr Q a -> ~ rin_ivs XS a -> ~ (D + to_Z o <= a < D + to_Z o + to_Z n)))).
    { pose proof (proj1 (proj1 Hmem td rgd Hrgd)) as (_ & Hlen62 & _). destruct Xnamed as [XG0in XLB0nd].
      (* [comment removed for export] *)
      destruct (loc_okb_inv A st src td o n Hloc Htd0) as [(Etd1 & spo & rg1' & tp' & Esp2' & Hrg1' & Hspo & H64 & Hcs64)| (_ & Ntd1 & Hobj)].
      - (* [comment removed for export] *)
        fold F in Esp2', Hrg1'. rewrite Hrg1 in Hrg1'. injection Hrg1' as <-. rewrite Esp2 in Esp2'. injection Esp2' as E0 Espo. subst spo.
        assert (Ergd : rgd = rg1) by (rewrite Etd1 in Hrgd; clear - Hrgd Hrg1; congruence).
        rewrite Hlo1 in H64. change (to_Z (0 + 64)%uint63) with 64 in H64.
        destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
        assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by exact Hon.
        rewrite Ergd, Hlen1 in RNG.
        rewrite !Uint63.add_spec in Hcs64. change (to_Z 64%uint63) with 64 in Hcs64. change wB with (2 ^ 63) in Hcs64. rewrite !Z.mod_small in Hcs64 by (clear - RNG Ho Hn Est40 Hcs; slia0).
        exists (q_sp0 Q - to_Z (c_stack K)). rewrite Etd1. split; [exact Xr1|]. split; [clear - Hhl Hlsp ACEILB; slia|]. split; [clear - Hsp32; Z.div_mod_to_equations; slia|].
        split; [clear - Hhl Hlsp ACEILB; unfold AIMG_TOP; slia|]. rewrite Ergd. split; [exact Hlo1|]. split; [exact Hd1|]. split; [exact Hkd1|].
        split; [rewrite Hlen1; exact RNG|]. split; [rewrite Hlen1; clear - SB2 Hshi; slia|].
        split; [intros _; split; [reflexivity|]; split; [clear - Hspo Espu; slia| split; [exact H64| exact Hcs64]]|].
        split; [intros NE; exfalso; apply NE; reflexivity|].
        assert (DLO : AHI_LO <= q_sp0 Q - to_Z (c_stack K) + to_Z o) by (clear - Hhl Hlsp Ho ACEILB; unfold AHI_LO; slia).
        split.
        { (* [comment removed for export] *)
          destruct Xst0 as (g0 & G01 & G02 & G03 & [_ SH0]). pose proof (SHAD_aligned _ _ _ SH0) as [_ G8]. destruct SH0 as (_ & _ & U8).
          pose proof (u8arr_stk _ _ _ U8) as SST. rewrite (shadow_of_length (q_shi Q - g0)) in SST by (clear - G01 G02; slia).
          pose proof (hull_lo_le (q_sp0 Q - to_Z (c_stack K) + to_Z o) ltac:(clear - DLO; unfold AHI_LO in DLO; slia)) as (HL1 & HL2 & HL3).
          pose proof (hull_hi_ge (q_sp0 Q - to_Z (c_stack K) + to_Z o + to_Z n) ltac:(clear - DLO Hn; unfold AHI_LO in DLO; slia)) as (HH1 & HH2 & HH3).
          replace (sh g0 + nsh (q_shi Q - g0)) with (sh (q_shi Q)) in SST by (clear - G8 G03 G01 G02; unfold sh, nsh; Z.div_mod_to_equations; slia).
          assert (M1' : sh g0 <= sh (hull_lo (q_sp0 Q - to_Z (c_stack K) + to_Z o))) by (apply sh_mono; clear - G01 HL2 H64 Hhl Hlsp; slia).
          assert (M2' : sh (hull_hi (q_sp0 Q - to_Z (c_stack K) + to_Z o + to_Z n)) <= sh (q_shi Q)) by (apply sh_mono; clear - HH2 Hcs64 RNG Hshi Hn; slia).
          unfold shvis. destruct SST as (S0' & S1' & SS). split; [clear - S0' M1'; slia|]. split; [clear - S1' M2'; slia|]. intros a Ha. apply SS. clear - Ha M1' M2'. slia. }
        split; [right; split; [exact DLO| clear - Hcs64 Hshi SB2; slia]|].
        split; [apply aconst_ok_hi; exact DLO|].
        split; [left; cbn [fst]; clear - Hhl Hlsp H64; slia|].
        split; [apply stack0_ok_app; exact DLO|].
        split; [left; cbn [fst snd]; clear - F2 Hhl Hlsp H64 ACEILB; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; slia|].
        split; [right; clear - Hspo Espu; slia|].
        split; [clear - Hcs64 Hn; slia|].
        intros a Hcl Hna Hnx Ha. unfold client0, aclient_addr in Hcl.
        destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        * clear - Hs Ha Hcs64 Hn. slia.
        * clear - Hst Ha Hhl Hlsp H64 ACEILB. unfold aimg_client, AIMG_LO, AIMG_TOP in *. slia.
        * destruct (XLB0h b Hb) as [_ Bh]. clear - Hr Bh Ha Hhl Hlsp H64. slia.
        * destruct (XLB0h b Hb) as [B0 Bh]. pose proof (sh_nsh_high (blk_addr b) (blk_size b) B0 ltac:(clear - Hr; unfold nsh in Hr; Z.div_mod_to_equations; slia) ltac:(clear - Bh ACEILB; unfold AAPP_HI; slia)) as SB.
          clear - Hr SB Ha DLO. slia.
        * clear - Hfs F2 Ha Hhl Hlsp H64. slia.
        * pose proof (sh_below_app (as_FSB H + AFS_SIZE) ltac:(clear - F1 F2 ACEILB; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; slia)) as SB. clear - Hfss SB Ha DLO. slia.
        * clear - Hss Ha DLO. slia.
      - (* [comment removed for export] *)
        destruct Hobj as [Hb|Hf].
        + rewrite XG, map_map in Hb. cbn [fst] in Hb. apply in_map_iff in Hb as (g & Etg & Hg).
          pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
          rewrite Etg in *. assert (Ergd : rgg = rgd) by (clear - Hgg Hrgd; congruence). subst rgg.
          pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
          destruct (Xkinds td rgd Hrgd Htd0) as [_ Hkdd]. pose proof (i63_range (g_size g)) as Hgs0.
          assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by exact Hon.
          exists (g_addr g). split; [exact Hrg|]. split; [clear - G1; slia|]. split; [clear - G2; Z.div_mod_to_equations; slia|]. split; [exact G4|].
          split; [exact Hlog|]. split; [exact Hdfg|]. split; [exact Hkdd|]. split; [exact RNG|]. rewrite <- Hleng in *. split; [clear - G5 ACEILB; unfold AAPP_HI; slia|].
          split; [intros E; exfalso; exact (Ntd1 E)|].
          split; [intros _; split; [exact G5|]; split; [exact G7|]; split; [exact Hsz|]; left; exists g; repeat split; assumption || reflexivity || (symmetry; assumption)|].
          split; [eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ Xheap Hin)| clear - G1; slia| clear - Ho; slia| clear - RNG; slia| clear - Hn; slia| clear - G1 G3; slia]|].
          split; [destruct G7 as [[Q1 Q2]|[Q1 Q2]]; [left; clear - Q1 Q2 G1 Ho Hn RNG; unfold ALOWSH_LO in *; rewrite ASHADOW_BASE_val; unfold AIMG_TOP in *; slia| right; clear - Q1 Q2 Ho Hn RNG ACEILB; unfold AAPP_HI; slia]|].
          split; [eapply aconst_ok_aapp; [exact G7| clear - Ho; slia| clear - RNG; slia]|].
          split; [do 2 right; left; eexists; split; [exact Hin| cbn [blk_addr blk_size fst snd]; clear - Ho RNG; slia]|].
          split; [eapply stack0_ok_aapp; [exact G7| cbn [fst]; clear - Ho; slia| cbn [snd]; clear - RNG; slia]|].
          split; [left; cbn [fst snd]; clear - G4 G6 Ho RNG Hn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; slia|].
          split; [left; clear - G5 Hhl RNG; slia|].
          split; [clear - G5 Hhl Hlsp RNG Hcs; slia|].
          intros a Hcl Hna Hnx Ha. pose proof (proj1 (Forall_forall _ _) XGnew g Hg) as [Hn0 | [Hfr _]].
          * apply Hna. exists g. split; [exact Hn0|]. left. rewrite <- Hleng. clear - Ha Ho RNG. slia.
          * apply (proj1 (Hfr a Hcl Hna)). rewrite <- Hleng. clear - Ha Ho RNG. slia.
        + rewrite XFF, map_map in Hf. cbn [fst] in Hf. apply in_map_iff in Hf as (f & Etg & Hf).
          pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
          rewrite Etg in *. assert (Ergd : rgf = rgd) by (clear - Hgf Hrgd; congruence). subst rgf.
          destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
          pose proof (fsz_eq _ Hkf) as EFZ. pose proof (fsz_fshn (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as [E1 E2].
          destruct (Xkinds td rgd Hrgd Htd0) as [_ Hkdd].
          assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by exact Hon.
          exists (f_ff f). split; [exact Hf0|]. split; [clear - K2' F1; unfold AFS_HDR, AIMG_TOP in *; slia|]. split; [exact (frame_al8 H _ _ _ (conj K1 (conj K2' (conj K3 (conj K4 K5)))))|].
          split; [clear - K2' F1; unfold AFS_HDR in *; slia|]. split; [exact Hlof|]. split; [exact Hdff|]. split; [exact Hkdd|]. split; [exact RNG|].
          rewrite Hlenf, EFZ in *. split; [clear - K3 F2 ACEILB; unfold AAPP_HI; slia|].
          split; [intros E; exfalso; exact (Ntd1 E)|].
          pose proof (aapp_sub (as_FSB H) AFS_SIZE (f_ff f) (AsIface.fsz (to_Z (f_k f))) F4 ltac:(clear - K2'; unfold AFS_HDR in *; slia) K3) as APf.
          split; [intros _; split; [clear - K3 F2; slia|]; split; [exact APf|];
                 split; [clear - FPf; slia|]; right; exists f; split; [exact Hf|]; split; [exact Etg|]; split; [reflexivity|]; first [reflexivity| symmetry; exact Hlenf]|].
          split; [eapply shvis_sub; [exact (ah_frm_shvis H HH _ _ (ff_of f) Xrfs ltac:(unfold LF_of; apply in_or_app; left; apply in_map; exact Hf))| cbn [ff_addr ff_of fst snd]; clear - K2' F1; unfold AFS_HDR, AIMG_TOP in *; slia| cbn [ff_addr ff_of fst snd]; clear - Ho; slia| cbn [ff_addr ff_class ff_of fst snd]; clear - RNG; slia| clear - Hn; slia| cbn [ff_addr ff_class ff_of fst snd]; clear - K2' F1 FPf; unfold AFS_HDR, AIMG_TOP in *; slia]|].
          split; [destruct F4 as [[Q1 Q2]|[Q1 Q2]]; [left; clear - Q1 Q2 K2' K3 F1 Ho Hn RNG; unfold ALOWSH_LO, AFS_HDR, AIMG_TOP in *; rewrite ASHADOW_BASE_val; slia| right; clear - Q1 Q2 K2' K3 F2 Ho Hn RNG ACEILB; unfold AAPP_HI, AFS_HDR in *; slia]|].
          split; [eapply aconst_ok_aapp; [exact APf| clear - Ho; slia| clear - RNG; slia]|].
          split; [do 4 right; left; cbn [fst snd]; clear - K2' K3 Ho RNG; unfold AFS_HDR in *; slia|].
          split; [eapply stack0_ok_aapp; [exact APf| cbn [fst]; clear - Ho; slia| cbn [snd]; clear - RNG; slia]|].
          split; [right; exists (ff_of f); split; [unfold LF_of; apply in_or_app; left; apply in_map; exact Hf| cbn [ff_addr ff_class ff_of fst snd]; clear - Ho RNG; slia]|].
          split; [left; clear - K3 F2 Hhl RNG; slia|].
          split; [clear - K3 F2 Hhl Hlsp RNG Hcs; slia|].
          intros a Hcl Hna Hnx Ha. apply Hnx. apply X2. clear - Ha Ho RNG. slia. }
    destruct OBJ as (D & OBJB). pose proof OBJB as (ErD & HD0 & HD8 & HDtop & Hlod & Hdfd & Hkdd & RNG & HDhi & STK & OBJF & (SHV & IAM & ACO & CWD & S0D & AFD & LOD & SP0D & EXD)).

    pose proof (proj1 (proj1 Hmem td rgd Hrgd)) as (_ & Hlen62' & _). pose proof (i63_range (rg_len rgd)) as Hld.
    set (d := D + to_Z o) in *.
    assert (SRD : forall hi, d <= hi <= D + to_Z (rg_len rgd) -> stk asegs (ms_mem ms) d hi).
    { intros hi Hhi. destruct (Uint63.eqb td 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. destruct (STK E1) as (ED & SPd & _ & Hcs64). assert (Ergd : rgd = rg1) by (rewrite E1 in Hrgd; clear - Hrgd Hrg1; congruence).
        pose proof (stk_split asegs _ _ d _ Xstk ltac:(clear - SPd Espu Hhl Hlsp Hoff1 Ef2 SP0D Hn; slia)) as [_ S2].
        exact (proj1 (stk_split asegs _ _ hi _ S2 ltac:(rewrite Ergd, Hlen1, ED in Hhi; clear - Hhi; slia))).
      - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & _ & EgD & EgS)|(f0 & Hf0 & _ & EfD & EfS)]).
        + pose proof (proj1 (Forall_forall _ _) XGstk g0 Hg0) as S0. cbn beta in S0. rewrite EgD, EgS in S0.
          pose proof (stk_split asegs _ _ d _ S0 ltac:(clear - Ho Hhi; subst d; slia)) as [_ S2].
          exact (proj1 (stk_split asegs _ _ hi _ S2 ltac:(clear - Hhi; slia))).
        + pose proof (proj1 (Forall_forall _ _) XFFstk f0 Hf0) as S0. cbn beta in S0. rewrite EfD in S0.
          pose proof (proj1 (Forall_forall _ _) XFFin f0 Hf0) as (_ & _ & _ & Hkf0 & _). rewrite <- (fsz_eq _ Hkf0), EfS in S0.
          pose proof (stk_split asegs _ _ d _ S0 ltac:(clear - Ho Hhi; subst d; slia)) as [_ S2].
          exact (proj1 (stk_split asegs _ _ hi _ S2 ltac:(clear - Hhi; slia))). }
    exists D. split; [exact OBJB| exact SRD].
  Qed.

  Theorem anode_memset_sound : anode_memset_sig H IMX A.
  Proof.
    unfold anode_memset_sig, anode_concl.
    intros Q st st' rho msF mo Hnode Hpc Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_memset in Hnode.
    destruct (call_okn K (ka_istack A) st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) 11)) as [c|] eqn:Hcc; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) 12)) as [n|] eqn:Hnn; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hg1; [|discriminate] end.
    destruct (ptr_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) n) as [[td o]|] eqn:Hpa; [|discriminate].
    destruct (range_okb IM A st false td o n) eqn:Hro; [|discriminate].
    destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
    destruct (fill_bytes (Z.to_nat (to_Z n)) M1 td o (c land 255)) as [M2|] eqn:HM2; [|discriminate].
    injection Hnode as <-.
    destruct (call_okn_inv A _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv A _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv.
    apply andb_true_iff in Hg1 as [Hn64k Hc255]. apply Uint63.leb_spec in Hn64k. apply Uint63.leb_spec in Hc255.
    change (to_Z 65536%uint63) with 65536 in Hn64k. change (to_Z 255%uint63) with 255 in Hc255.
    pose proof (conc63_inv _ _ Hcc) as Ea1. pose proof (conc63_inv _ _ Hnn) as Ea2.
    destruct (ptr_arg_inv _ _ _ _ _ Hpa) as (Ea0 & Htd0 & rgd & Hrgd & Hloo & Hon & Hnlen).
    unfold range_okb in Hro. apply andb_true_iff in Hro as [Hloc Hacc].
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (tn := a_n st) in *.
    pose proof (i63_range tn) as Htn. change (to_Z two59) with (2 ^ 59) in Hn59. destruct Xn0 as [Xn0a Xn0b].
    pose proof (i63_range n) as Hn. pose proof (i63_range o) as Ho. pose proof (i63_range c) as Hc. pose proof (i63_range td) as Htd.
    assert (Etn14 : to_Z (tn + 14)%uint63 = to_Z tn + 14) by (rewrite to_Z_add_small; change (to_Z 14%uint63) with 14; clear - Htn Hn59; slia0).
    assert (Hag : agree tn rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR. pose proof (R_mem _ _ _ _ _ HR) as Hmem. cbn [f_mem] in Hmem. fold F in Hmem.
    pose proof (canonR_R asegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    assert (Epc : to_Z (f_pc F) = AASAN_MEMSET).
    { destruct (HK_parts A HK) as (_ & _ & Hpcs & _). unfold K_pcs_ok in Hpcs. rewrite !andb_true_iff in Hpcs. destruct Hpcs as [[[[[[[[[[_ _] _] Hm] _] _] _] _] _] _] _].
      apply Z.eqb_eq in Hm. rewrite <- Hm. fold F in Hpc. rewrite Hpc. reflexivity. }
    rewrite Epc in Ems.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); clear - Hhl Hlsp HspB HB64 Hcs Hoff Hoff2 ACEILB; slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 ATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    assert (Ea1v : rv rho F 11 = Z_to_bv 64 (to_Z c)).
    { rewrite Erv. change (of_Z 11) with 11%uint63. fold F in Ea1. rewrite Ea1. apply dv_conc63. exact Xr0. }
    assert (Ea2v : rv rho F 12 = Z_to_bv 64 (to_Z n)).
    { rewrite Erv. change (of_Z 12) with 12%uint63. fold F in Ea2. rewrite Ea2. apply dv_conc63. exact Xr0. }
    set (SP := bv_unsigned (rv rho F 2)) in *.
    destruct (stk_split asegs _ (q_lo Q) SP (q_sp0 Q) Xstk ltac:(clear - Espu Hhl Hlsp Hoff Hoff2; slia)) as [Hstk_lo Hstk_hi].
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0.
    destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. assert (Erg1 : rg1_ = rg1) by (clear - Hrg1 Hrg1_; congruence). subst rg1_.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
    (* [comment removed for export] *)
    assert (OLDLT : forall x rg, iget x (f_mem F) = Some rg -> to_Z x < to_Z tn).
    { intros x rg Hx. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]];
        [change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia| change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia
        | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia| change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia| ..].
      - apply in_map_iff in Hb as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). pose proof (i63_range (g_tag g)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hf as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 2%uint63) with 2; clear - Htg2 H0 Hn59; slia0). change (to_Z 2%uint63) with 2. clear - Htg2. slia. }
    assert (SR : sh aceil <= sh (q_sp0 Q - to_Z (c_stack K)) /\ sh (q_sp0 Q - to_Z (c_stack K)) + nsh (to_Z (c_stack K)) <= sh (q_sp0 Q)
                 /\ sh (q_sp0 Q) <= AHI_LO /\ AIMG_TOP <= sh (q_sp0 Q - to_Z (c_stack K))).
    { split; [apply sh_mono; clear - Hlsp Hhl; slia|]. split; [| split].
      - clear - Hsp32 Hcs Est16. unfold nsh, sh. Z.div_mod_to_equations. slia.
      - clear - SB2 Hshi. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
      - apply sh_above_image. clear - Hlsp Hhl ACEILB. slia. }
    assert (REGLO : forall x rg, iget x (f_mem F) = Some rg -> x <> 1%uint63 ->
              0 <= bv_unsigned (rho x) + to_Z (rg_lo rg) /\ bv_unsigned (rho x) + to_Z (rg_len rg) <= aceil).
    { intros x rg Hx Hne1. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]].
      - rewrite Hrg0 in Hx. injection Hx as <-. rewrite Xr0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0. clear - ACEILB. unfold AIMG_LO, AIMG_TOP. slia.
      - exfalso. exact (Hne1 eq_refl).
      - rewrite Xreg2 in Hx. injection Hx as <-. rewrite Xr2. unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (c_stack K)) by (clear - Hcs Est40; slia).
        change (to_Z 0%uint63) with 0. fold (nsh (to_Z (c_stack K))).
        rewrite wa_unsigned by (clear - SR Hcs; unfold AIMG_TOP, AHI_LO, nsh in SR; Z.div_mod_to_equations; slia). clear - SR ACEILB. unfold AHI_LO, AIMG_TOP in *. slia.
      - rewrite Xreg3 in Hx. injection Hx as <-. rewrite Xr3, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold abs_region. cbn [rg_lo rg_len].
        destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
        apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. rewrite Hslo, Hslen. clear - ACEILB. unfold sh, AIMG_LO, AIMG_TOP. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
      - apply in_map_iff in Hb as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
        rewrite Hgg in Hx. injection Hx as <-. rewrite Hlog, Hleng, Hrg. change (to_Z 0%uint63) with 0.
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
        rewrite wa_unsigned by (clear - G1 G3 G5 ACEILB; slia). clear - G1 G5. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hshg). destruct (Hshg rg Hx) as (-> & Hrs & _).
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 ACEILB; slia). change (to_Z 0%uint63) with 0. fold (nsh (to_Z (g_size g))).
        rewrite Hrs. pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 G3) as (U1 & U2 & U3). pose proof (sh_above_image (g_addr g) ltac:(clear - G1; slia)) as SAg.
        rewrite wa_unsigned by (clear - U2 U3 SAg G1 Hsz; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        clear - U2 U3 SAg Hsz ACEILB. unfold AIMG_TOP, AHI_LO, nsh in *. Z.div_mod_to_equations. slia.
      - apply in_map_iff in Hf as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
        rewrite Hgf in Hx. injection Hx as <-. rewrite Hlof, Hlenf, Hf0, (fsz_eq _ Hkf). change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
        rewrite wa_unsigned by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE in *; slia). clear - K2' K3 F1 F2 FPf. unfold AIMG_TOP, AFS_HDR in *. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
        rewrite Hgs in Hx. injection Hx as <-. rewrite Hlos, Hlens, Hf1. change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as [E1 E2].
        assert (B : AIMG_TOP <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) <= AAPP_HI) by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE, AAPP_HI in *; slia).
        pose proof (sh_above_image (f_ff f) ltac:(unfold AIMG_TOP in B; clear - B; slia)) as SA1.
        pose proof (sh_nsh_high (f_ff f) (AsIface.fsz (to_Z (f_k f))) ltac:(unfold AIMG_TOP in B; clear - B; slia) ltac:(clear - FPf; slia) (proj2 B)) as SA2.
        rewrite wa_unsigned by (clear - B SA1 SA2 FPf E1; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        rewrite E1. clear - SA1 SA2 ACEILB. unfold AIMG_TOP, AHI_LO in *. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & _ & Hflg & _).
        rewrite Hflg in Hx. injection Hx as <-. unfold flag_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. rewrite Hf2.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _].
        rewrite wa_unsigned by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia). clear - K5 F1 F2. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *. slia. }

    (* [comment removed for export] *)
    assert (Htd_lt : to_Z td < to_Z tn) by exact (OLDLT td rgd Hrgd).
    assert (Ea0v : rv rho F 10 = adr rho td (to_Z o)).
    { rewrite Erv. change (of_Z 10) with 10%uint63. fold F in Ea0. rewrite Ea0. apply dv_adr; [clear - Htd_lt Hn59; slia0| reflexivity]. }
    set (ts := if (td =? 1)%uint63 then 2%uint63 else (td + 1)%uint63) in *.
    assert (OBJ : exists D : Z,
      rho td = wa D /\ 0 <= D /\ D mod 8 = 0 /\ AIMG_TOP <= D
      /\ rg_lo rgd = 0%uint63 /\ rg_dflt rgd = Some PKUnk /\ (forall pn p, iget pn (rg_pages rgd) = Some p -> pg_kind p = PKUnk)
      /\ to_Z o + to_Z n <= to_Z (rg_len rgd) /\ D + to_Z (rg_len rgd) <= AAPP_HI
      /\ (td = 1%uint63 -> D = q_sp0 Q - to_Z (c_stack K) /\ rgd = rg1 /\ SP <= D + to_Z o /\ 64 <= to_Z o /\ to_Z o + to_Z n + 64 <= to_Z (c_stack K))
      /\ (td <> 1%uint63 -> D + to_Z (rg_len rgd) <= aceil /\ aapp D (to_Z (rg_len rgd)) /\ 1 <= to_Z (rg_len rgd)
            /\ ((exists g, In g G /\ g_tag g = td /\ g_addr g = D /\ g_size g = rg_len rgd) \/ (exists f, In f FF /\ f_tag f = td /\ f_ff f = D /\ I2RunA.fsz (f_k f) = rg_len rgd)))
      /\ (shvis (ms_mem ms) (D + to_Z o) (D + to_Z o + to_Z n) /\ in_app_mem (D + to_Z o) (D + to_Z o + to_Z n) /\ aconst_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ aclient_write_ok H LB (D + to_Z o, D + to_Z o + to_Z n) /\ stack0_ok (D + to_Z o, D + to_Z o + to_Z n)
          /\ afs_write_ok H (LF_of Q FF) (D + to_Z o, D + to_Z o + to_Z n)
          /\ (D + to_Z o + to_Z n <= q_lo Q \/ SP <= D + to_Z o) /\ D + to_Z o + to_Z n <= q_sp0 Q
          /\ (forall a, client0 H Q a -> ~ named_addr Q a -> ~ rin_ivs XS a -> ~ (D + to_Z o <= a < D + to_Z o + to_Z n)))
      /\ (Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ rho ts = wa (sh D) /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7
            /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs))).
    { pose proof (proj1 (proj1 Hmem td rgd Hrgd)) as (_ & Hlen62 & _). destruct Xnamed as [XG0in XLB0nd].
      (* [comment removed for export] *)
      assert (SHD : (Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7) ->
                    to_Z o + to_Z n <= to_Z (rg_len rgd)).
      { intros _. exact Hon. }
      destruct (loc_okb_inv A st false td o n Hloc Htd0) as [(Etd1 & spo & rg1' & tp' & Esp2' & Hrg1' & Hspo & H64 & Hcs64)| (_ & Ntd1 & Hobj)].
      - (* [comment removed for export] *)
        fold F in Esp2', Hrg1'. rewrite Hrg1 in Hrg1'. injection Hrg1' as <-. rewrite Esp2 in Esp2'. injection Esp2' as E0 Espo. subst spo.
        assert (Ergd : rgd = rg1) by (rewrite Etd1 in Hrgd; clear - Hrgd Hrg1; congruence).
        rewrite Hlo1 in H64. change (to_Z (0 + 64)%uint63) with 64 in H64.
        destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
        assert (SHF : Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ rho ts = wa (sh (q_sp0 Q - to_Z (c_stack K))) /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7
                       /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs)).
        { intros _. exists (sh_region false 1%uint63 (c_stack K)). subst ts. rewrite Etd1, Uint63.eqb_refl. split; [exact Xreg2|]. split; [exact Xr2|].
          rewrite Ergd, Hlen1. unfold sh_region. cbn [rg_len]. rewrite (nsh_eq (c_stack K)) by (clear - Hcs Est40; slia). clear - Hcs. split; Z.div_mod_to_equations; slia0. }
        assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by (apply SHD; intros Hk; destruct (SHF Hk) as (rgs & A1 & _ & A3 & _); exists rgs; split; assumption).
        rewrite Ergd, Hlen1 in RNG.
        rewrite !Uint63.add_spec in Hcs64. change (to_Z 64%uint63) with 64 in Hcs64. change wB with (2 ^ 63) in Hcs64. rewrite !Z.mod_small in Hcs64 by (clear - RNG Ho Hn Est40 Hcs; slia0).
        exists (q_sp0 Q - to_Z (c_stack K)). rewrite Etd1. split; [exact Xr1|]. split; [clear - Hhl Hlsp ACEILB; slia|]. split; [clear - Hsp32; Z.div_mod_to_equations; slia|].
        split; [clear - Hhl Hlsp ACEILB; unfold AIMG_TOP; slia|]. rewrite Ergd. split; [exact Hlo1|]. split; [exact Hd1|]. split; [exact Hkd1|].
        split; [rewrite Hlen1; exact RNG|]. split; [rewrite Hlen1; clear - SB2 Hshi; slia|].
        split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [clear - Hspo Espu; slia| split; [exact H64| exact Hcs64]]|].
        split; [intros NE; exfalso; apply NE; reflexivity|].
        assert (DLO : AHI_LO <= q_sp0 Q - to_Z (c_stack K) + to_Z o) by (clear - Hhl Hlsp Ho ACEILB; unfold AHI_LO; slia).
        split; [| intros Hk; destruct (SHF Hk) as (rgs & A1 & A2 & A3); exists rgs; split; [exact A1|]; split; [exact A2|]; rewrite Ergd in A3; exact A3].
        split.
        { (* [comment removed for export] *)
          destruct Xst0 as (g0 & G01 & G02 & G03 & [_ SH0]). pose proof (SHAD_aligned _ _ _ SH0) as [_ G8]. destruct SH0 as (_ & _ & U8).
          pose proof (u8arr_stk _ _ _ U8) as SST. rewrite (shadow_of_length (q_shi Q - g0)) in SST by (clear - G01 G02; slia).
          pose proof (hull_lo_le (q_sp0 Q - to_Z (c_stack K) + to_Z o) ltac:(clear - DLO; unfold AHI_LO in DLO; slia)) as (HL1 & HL2 & HL3).
          pose proof (hull_hi_ge (q_sp0 Q - to_Z (c_stack K) + to_Z o + to_Z n) ltac:(clear - DLO Hn; unfold AHI_LO in DLO; slia)) as (HH1 & HH2 & HH3).
          replace (sh g0 + nsh (q_shi Q - g0)) with (sh (q_shi Q)) in SST by (clear - G8 G03 G01 G02; unfold sh, nsh; Z.div_mod_to_equations; slia).
          assert (M1' : sh g0 <= sh (hull_lo (q_sp0 Q - to_Z (c_stack K) + to_Z o))) by (apply sh_mono; clear - G01 HL2 H64 Hhl Hlsp; slia).
          assert (M2' : sh (hull_hi (q_sp0 Q - to_Z (c_stack K) + to_Z o + to_Z n)) <= sh (q_shi Q)) by (apply sh_mono; clear - HH2 Hcs64 RNG Hshi Hn; slia).
          unfold shvis. destruct SST as (S0' & S1' & SS). split; [clear - S0' M1'; slia|]. split; [clear - S1' M2'; slia|]. intros a Ha. apply SS. clear - Ha M1' M2'. slia. }
        split; [right; split; [exact DLO| clear - Hcs64 Hshi SB2; slia]|].
        split; [apply aconst_ok_hi; exact DLO|].
        split; [left; cbn [fst]; clear - Hhl Hlsp H64; slia|].
        split; [apply stack0_ok_app; exact DLO|].
        split; [left; cbn [fst snd]; clear - F2 Hhl Hlsp H64 ACEILB; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; slia|].
        split; [right; clear - Hspo Espu; slia|].
        split; [clear - Hcs64 Hn; slia|].
        intros a Hcl Hna Hnx Ha. unfold client0, aclient_addr in Hcl.
        destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        * clear - Hs Ha Hcs64 Hn. slia.
        * clear - Hst Ha Hhl Hlsp H64 ACEILB. unfold aimg_client, AIMG_LO, AIMG_TOP in *. slia.
        * destruct (XLB0h b Hb) as [_ Bh]. clear - Hr Bh Ha Hhl Hlsp H64. slia.
        * destruct (XLB0h b Hb) as [B0 Bh]. pose proof (sh_nsh_high (blk_addr b) (blk_size b) B0 ltac:(clear - Hr; unfold nsh in Hr; Z.div_mod_to_equations; slia) ltac:(clear - Bh ACEILB; unfold AAPP_HI; slia)) as SB.
          clear - Hr SB Ha DLO. slia.
        * clear - Hfs F2 Ha Hhl Hlsp H64. slia.
        * pose proof (sh_below_app (as_FSB H + AFS_SIZE) ltac:(clear - F1 F2 ACEILB; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; slia)) as SB. clear - Hfss SB Ha DLO. slia.
        * clear - Hss Ha DLO. slia.
      - (* [comment removed for export] *)
        destruct Hobj as [Hb|Hf].
        + rewrite XG, map_map in Hb. cbn [fst] in Hb. apply in_map_iff in Hb as (g & Etg & Hg).
          pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
          rewrite Etg in *. assert (Ergd : rgg = rgd) by (clear - Hgg Hrgd; congruence). subst rgg.
          pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
          destruct (Xkinds td rgd Hrgd Htd0) as [_ Hkdd]. pose proof (i63_range (g_size g)) as Hgs0.
          assert (SHF : Z.to_nat (to_Z n) <> 0%nat -> exists rgs, iget ts (f_mem F) = Some rgs /\ rho ts = wa (sh (g_addr g)) /\ 8 * to_Z (rg_len rgs) <= to_Z (rg_len rgd) + 7
                         /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs)).
          { intros Hk. destruct (Z.to_nat (to_Z n)) as [|k] eqn:En; [exfalso; exact (Hk eq_refl)|].
            destruct (acc_head IM (f_mem F) td o k Hacc Htd0 ltac:(clear - Htd_lt Hn59 Htd; slia0)) as (b & rgs & p & cc & Hb' & Hrgs & _). subst ts.
            rewrite (proj2 (Uint63.eqb_false_spec _ _) Ntd1) in Hrgs |- *. destruct (Hshg rgs Hrgs) as (Ers & Hrs & _). exists rgs. split; [exact Hrgs|]. split; [exact Hrs|].
            rewrite Ers, Hleng. unfold sh_region. cbn [rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 Hleng ACEILB Hgs0; slia). clear - Hgs0. split; Z.div_mod_to_equations; slia0. }
          assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by (apply SHD; intros Hk; destruct (SHF Hk) as (rgs & A1 & _ & A3 & _); exists rgs; split; assumption).
          exists (g_addr g). split; [exact Hrg|]. split; [clear - G1; slia|]. split; [clear - G2; Z.div_mod_to_equations; slia|]. split; [exact G4|].
          split; [exact Hlog|]. split; [exact Hdfg|]. split; [exact Hkdd|]. split; [exact RNG|]. rewrite <- Hleng in *. split; [clear - G5 ACEILB; unfold AAPP_HI; slia|].
          split; [intros E; exfalso; exact (Ntd1 E)|].
          split; [intros _; split; [exact G5|]; split; [exact G7|]; split; [exact Hsz|]; left; exists g; repeat split; assumption || reflexivity || (symmetry; assumption)|].
          split; [| exact SHF].
          split; [eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ Xheap Hin)| clear - G1; slia| clear - Ho; slia| clear - RNG; slia| clear - Hn; slia| clear - G1 G3; slia]|].
          split; [destruct G7 as [[Q1 Q2]|[Q1 Q2]]; [left; clear - Q1 Q2 G1 Ho Hn RNG; unfold ALOWSH_LO in *; rewrite ASHADOW_BASE_val; unfold AIMG_TOP in *; slia| right; clear - Q1 Q2 Ho Hn RNG ACEILB; unfold AAPP_HI; slia]|].
          split; [eapply aconst_ok_aapp; [exact G7| clear - Ho; slia| clear - RNG; slia]|].
          split; [do 2 right; left; eexists; split; [exact Hin| cbn [blk_addr blk_size fst snd]; clear - Ho RNG; slia]|].
          split; [eapply stack0_ok_aapp; [exact G7| cbn [fst]; clear - Ho; slia| cbn [snd]; clear - RNG; slia]|].
          split; [left; cbn [fst snd]; clear - G4 G6 Ho RNG Hn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; slia|].
          split; [left; clear - G5 Hhl RNG; slia|].
          split; [clear - G5 Hhl Hlsp RNG Hcs; slia|].
          intros a Hcl Hna Hnx Ha. pose proof (proj1 (Forall_forall _ _) XGnew g Hg) as [Hn0 | [Hfr _]].
          * apply Hna. exists g. split; [exact Hn0|]. left. rewrite <- Hleng. clear - Ha Ho RNG. slia.
          * apply (proj1 (Hfr a Hcl Hna)). rewrite <- Hleng. clear - Ha Ho RNG. slia.
        + rewrite XFF, map_map in Hf. cbn [fst] in Hf. apply in_map_iff in Hf as (f & Etg & Hf).
          pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
          rewrite Etg in *. assert (Ergd : rgf = rgd) by (clear - Hgf Hrgd; congruence). subst rgf.
          destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
          pose proof (fsz_eq _ Hkf) as EFZ. pose proof (fsz_fshn (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as [E1 E2].
          destruct (Xkinds td rgd Hrgd Htd0) as [_ Hkdd].
          assert (SHF : Z.to_nat (to_Z n) <> 0%nat -> exists rgs', iget ts (f_mem F) = Some rgs' /\ rho ts = wa (sh (f_ff f)) /\ 8 * to_Z (rg_len rgs') <= to_Z (rg_len rgd) + 7
                         /\ to_Z (rg_len rgd) <= 8 * to_Z (rg_len rgs')).
          { intros _. exists rgs. subst ts. rewrite (proj2 (Uint63.eqb_false_spec _ _) Ntd1). split; [exact Hgs|]. split; [exact Hf1|]. rewrite Hlens, Hlenf, EFZ, E2. clear. split; slia0. }
          assert (RNG : to_Z o + to_Z n <= to_Z (rg_len rgd)) by (apply SHD; intros Hk; destruct (SHF Hk) as (rgs' & A1 & _ & A3 & _); exists rgs'; split; assumption).
          exists (f_ff f). split; [exact Hf0|]. split; [clear - K2' F1; unfold AFS_HDR, AIMG_TOP in *; slia|]. split; [exact (frame_al8 H _ _ _ (conj K1 (conj K2' (conj K3 (conj K4 K5)))))|].
          split; [clear - K2' F1; unfold AFS_HDR in *; slia|]. split; [exact Hlof|]. split; [exact Hdff|]. split; [exact Hkdd|]. split; [exact RNG|].
          rewrite Hlenf, EFZ in *. split; [clear - K3 F2 ACEILB; unfold AAPP_HI; slia|].
          split; [intros E; exfalso; exact (Ntd1 E)|].
          pose proof (aapp_sub (as_FSB H) AFS_SIZE (f_ff f) (AsIface.fsz (to_Z (f_k f))) F4 ltac:(clear - K2'; unfold AFS_HDR in *; slia) K3) as APf.
          split; [intros _; split; [clear - K3 F2; slia|]; split; [exact APf|];
                 split; [clear - FPf; slia|]; right; exists f; split; [exact Hf|]; split; [exact Etg|]; split; [reflexivity|]; first [reflexivity| symmetry; exact Hlenf]|].
          split; [| exact SHF].
          split; [eapply shvis_sub; [exact (ah_frm_shvis H HH _ _ (ff_of f) Xrfs ltac:(unfold LF_of; apply in_or_app; left; apply in_map; exact Hf))| cbn [ff_addr ff_of fst snd]; clear - K2' F1; unfold AFS_HDR, AIMG_TOP in *; slia| cbn [ff_addr ff_of fst snd]; clear - Ho; slia| cbn [ff_addr ff_class ff_of fst snd]; clear - RNG; slia| clear - Hn; slia| cbn [ff_addr ff_class ff_of fst snd]; clear - K2' F1 FPf; unfold AFS_HDR, AIMG_TOP in *; slia]|].
          split; [destruct F4 as [[Q1 Q2]|[Q1 Q2]]; [left; clear - Q1 Q2 K2' K3 F1 Ho Hn RNG; unfold ALOWSH_LO, AFS_HDR, AIMG_TOP in *; rewrite ASHADOW_BASE_val; slia| right; clear - Q1 Q2 K2' K3 F2 Ho Hn RNG ACEILB; unfold AAPP_HI, AFS_HDR in *; slia]|].
          split; [eapply aconst_ok_aapp; [exact APf| clear - Ho; slia| clear - RNG; slia]|].
          split; [do 4 right; left; cbn [fst snd]; clear - K2' K3 Ho RNG; unfold AFS_HDR in *; slia|].
          split; [eapply stack0_ok_aapp; [exact APf| cbn [fst]; clear - Ho; slia| cbn [snd]; clear - RNG; slia]|].
          split; [right; exists (ff_of f); split; [unfold LF_of; apply in_or_app; left; apply in_map; exact Hf| cbn [ff_addr ff_class ff_of fst snd]; clear - Ho RNG; slia]|].
          split; [left; clear - K3 F2 Hhl RNG; slia|].
          split; [clear - K3 F2 Hhl Hlsp RNG Hcs; slia|].
          intros a Hcl Hna Hnx Ha. apply Hnx. apply X2. clear - Ha Ho RNG. slia. }
    destruct OBJ as (D & ErD & HD0 & HD8 & HDtop & Hlod & Hdfd & Hkdd & RNG & HDhi & STK & OBJF & (SHV & IAM & ACO & CWD & S0D & AFD & LOD & SP0D & EXD) & SHF).
    pose proof (proj1 (proj1 Hmem td rgd Hrgd)) as (_ & Hlen62' & _).

    pose proof (i63_range (rg_len rgd)) as Hld.
    set (d := D + to_Z o) in *.
    assert (Edv : rv rho F 10 = wa d) by (rewrite Ea0v; subst d; apply (adr_eq_wa rho); [exact ErD| exact HD0| clear - Ho; slia0| clear - RNG HDhi Ho Hn; unfold AAPP_HI in HDhi; slia0]).
    assert (Edu : bv_unsigned (rv rho F 10) = d) by (rewrite Edv; apply wa_unsigned; clear - HD0 RNG HDhi Ho Hn; unfold AAPP_HI in HDhi; slia0).
    assert (Enu : bv_unsigned (rv rho F 12) = to_Z n) by (rewrite Ea2v, Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); clear - Hn; slia0).
    set (W := [(d, d + to_Z n); (SP - 4096, SP)]) in *.
    (* [comment removed for export] *)
    destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
    assert (INB1 : rg_inb (drop_below off rg1)).
    { intros pn p' ci cc Hp' Hc'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->). unfold drop_below. cbn [rg_len].
      unfold drop_page in Hc'. cbn [fst snd] in Hc'. destruct (pn =? off >> 12)%uint63.
      - cbn [pg_cells] in Hc'. destruct (keep_cells_ge_inv _ _ _ _ Hc') as [_ Hc'']. exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'').
      - exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'). }
    assert (UNK1 : rg_unk (drop_below off rg1)).
    { split; [exact Hlo1|]. split; [exact Hd1|]. intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
      unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hkd1 _ _ Hp0). }
    set (rgd1 := if (td =? 1)%uint63 then drop_below off rg1 else rgd).
    assert (Hrgd1 : iget td (iset 1 (drop_below off rg1) (f_mem F)) = Some rgd1).
    { subst rgd1. rewrite iget_iset. destruct (td =? 1)%uint63; [reflexivity| exact Hrgd]. }
    assert (GEO1 : rg_len rgd1 = rg_len rgd /\ rg_lo rgd1 = 0%uint63 /\ rg_unk rgd1 /\ rg_inb rgd1 /\ rg_align rgd1 = rg_align rgd /\ rg_kind rgd1 = rg_kind rgd /\ rg_dflt rgd1 = Some PKUnk).
    { subst rgd1. destruct (td =? 1)%uint63 eqn:E1.
      - apply Uint63.eqb_spec in E1. destruct (STK E1) as (_ & -> & _). split; [reflexivity|]. split; [exact Hlo1|]. split; [exact UNK1|]. split; [exact INB1|]. split; [reflexivity|]. split; [reflexivity|]. cbn [drop_below rg_dflt]. exact Hd1.
      - split; [reflexivity|]. split; [exact Hlod|]. split; [split; [exact Hlod| split; [exact Hdfd| exact Hkdd]]|]. split; [exact (fun pn p ci cc Hp Hc => Xinb td rgd pn p ci cc Hrgd Hp Hc)|]. repeat split; try reflexivity. exact Hdfd. }
    destruct GEO1 as (G1len & G1lo & G1unk & G1inb & G1al & G1kd & G1df).
    (* [comment removed for export] *)
    assert (PART1m : mem_part asegs IM rho (ms_mem ms) td rgd1).
    { subst rgd1. destruct (td =? 1)%uint63 eqn:E1.
      - apply Uint63.eqb_spec in E1. rewrite E1.
        apply (stack_part asegs IM rho (ms_mem ms) (ms_mem ms) rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q));
          [exact Xr1| exact Hlo1| exact Hd1| exact Hkd1| rewrite Hlen1; reflexivity| rewrite Hlen1; clear - Hoff Hoff2; slia| clear - Hoff16 Hoff; Z.div_mod_to_equations; slia
          | exact (mem_part_of _ _ _ _ _ _ _ Hmem Hrg1)| exact Xstk| clear - Hhl Hlsp ACEILB; slia| rewrite <- Espu; exact Hstk_lo| intros a Ha; split; [reflexivity| intros Wv; exact Wv]].
      - exact (mem_part_of _ _ _ _ _ _ _ Hmem Hrgd). }
    destruct (fill_bytes_sound asegs IM rho Xr0 (Z.to_nat (to_Z n)) _ td o (c land 255)%uint63 M2 rgd1 (ms_mem ms) HM2 Hrgd1 PART1m Htd0 G1unk G1inb
                ltac:(rewrite G1len, Z2Nat.id by (clear - Hn; slia0); exact RNG) ltac:(rewrite to_Z_land255; clear - Hc; Z.div_mod_to_equations; slia0))
      as (rgd' & Hrgd' & Hoth2 & _ & UNK' & INB' & (F1lo & F1len & F1al & F1kd & F1df) & WRD).
    assert (STKD : stk asegs (ms_mem ms) d (d + to_Z n)).
    { apply stk_of_wview_high; [clear - HDtop Ho; subst d; slia| clear - HDhi RNG Hn Ho; subst d; unfold AAPP_HI in HDhi; slia|].
      intros a Ha. specialize (WRD (a - d) ltac:(rewrite Z2Nat.id by (clear - Hn; slia0); clear - Ha; slia)).
      rewrite (adr_eq_wa rho td D (to_Z o + (a - d)) ErD HD0) in WRD by (clear - Ha Ho HDhi RNG Hn; subst d; unfold AAPP_HI in HDhi; slia0).
      replace (D + (to_Z o + (a - d))) with a in WRD by (subst d; clear; slia0). exact WRD. }
    destruct (stk_carve asegs (ms_mem ms) d (d + to_Z n) (Z.to_nat (to_Z n)) STKD ltac:(rewrite Z2Nat.id by (clear - Hn; slia0); clear; slia)) as [_ [junk RWJ]].
    rewrite Z2Nat.id in RWJ by (clear - Hn; slia0). replace (d + to_Z n - to_Z n) with d in RWJ by (clear; slia0).
    (* [comment removed for export] *)
    assert (ACC : accessible (ms_mem ms) d (to_Z n)).
    { split; [clear - HD0 Ho; subst d; slia|]. split; [clear - HDhi RNG Ho; subst d; slia|].
      destruct (Z.to_nat (to_Z n)) as [|k] eqn:En; [intros z Hz; exfalso; clear - Hz En Hn; slia0|].
      destruct (SHF ltac:(discriminate)) as (rgs & Hrgs & Ers & Hls1 & Hls2). pose proof (i63_range (rg_len rgs)) as Hlsr.
      intros z Hz. apply (acc_bytes_sound IM (S k) (f_mem F) td o D (ms_mem ms) ts); [first [exact Hacc| rewrite <- En; exact Hacc]| exact Htd0| reflexivity| exact HD8| exact HD0
        | rewrite <- En, Z2Nat.id by (clear - Hn; slia0); clear - RNG Hld Hlen62' Ho; slia0| | subst d; rewrite <- En, Z2Nat.id by (clear - Hn; slia0); exact Hz].
      intros os b Hos1 Hos2 Hb. pose proof (i63_range os) as Hos.
      rewrite <- (adr_eq_wa rho ts (sh D) (to_Z os) Ers) by (first [clear - HD0 HDhi Hos Hos2 Hls2 RNG En Hn Hlsr; pose proof (sh_above_image D HD0); unfold sh, AIMG_TOP, AAPP_HI in *; rewrite ?ASHADOW_BASE_val in *; Z.div_mod_to_equations; slia0]).
      assert (Hts0 : ts <> 0%uint63).
      { subst ts. destruct (td =? 1)%uint63; [intros E; discriminate E|]. intros E. apply (f_equal to_Z) in E. rewrite Uint63.add_spec in E.
        change (to_Z 1%uint63) with 1 in E. change (to_Z 0%uint63) with 0 in E. change wB with (2 ^ 63) in E. rewrite Z.mod_small in E by (clear - Htd Htd_lt Hn59; slia0). clear - E Htd. slia0. }
      exact (byte_at_SK_sound asegs IM rho Xr0 (f_mem F) (ms_mem ms) ts os rgs b Hmem Hts0 Hrgs (fun pn p ci cc Hp Hc => Xinb ts rgs pn p ci cc Hrgs Hp Hc)
               ltac:(rewrite <- En, Z2Nat.id in Hos2 by (clear - Hn; slia0); clear - Hos2 Hls2 RNG; Z.div_mod_to_equations; slia0) Hb). }
    (* [comment removed for export] *)
    pose proof Xvis as Xvis0. rewrite Ems in Xvis0.
    pose proof (ah_memset H HH) as MS0. unfold asan_memset_stmt in MS0.
    assert (Hc256 : 0 <= to_Z c < 256) by (clear - Hc Hc255; slia0).
    eapply (ah_lift H HH _ _ s msF _ mo Xak Xvis0).
    { eapply MS0; [exact Ea1v| exact Hc256| rewrite Edu, Enu; exact RWJ| rewrite Edu, Enu; exact ACC| rewrite Edu, Enu; exact SHV| exact Hstk_lo| exact SB1
        | unfold AINTRIN_STACK; clear - Hlsp Espu Hoff1 Ef2; slia| exact Xinv| exact Xac| rewrite Enu; clear - Hn64k; slia0| rewrite Edu, Enu; exact IAM| rewrite Edu, Enu; exact ACO
        | rewrite Edu, Enu; exact LOD]. }
    intros msF' mo' Hak' Hmp' Hpost. unfold amemset_post in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Evis' & MU & WM & Hinv' & Hstk' & RWD & Hac').
    apply (ah_done H HH). cbn [cfg_ms cfg_model].
    rewrite Edu, Enu in MU, RWD. unfold AINTRIN_STACK in MU. change (munch W (ms_mem ms) m') in MU.
    (* [comment removed for export] *)
    destruct Hstk_hi as (SPge0 & SP064 & STKHI).
    assert (Hkeep0 : forall a, 0 <= a < 2 ^ 64 -> outside W a -> m' (wa a) = ms_mem ms (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hou. split; [apply MU; rewrite wa_unsigned by (clear - Ha; slia0); exact Hou| intros Wv; apply WM; exact Wv]. }
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> outside W a ->
                     rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hou. apply pw_keep. exact (proj1 (Hkeep0 a Ha Hou)). }
    assert (DST : forall a, d <= a < d + to_Z n -> m' (wa a) = Some (b8 (to_Z c))).
    { intros a Ha. pose proof (u8arr_of_rw_cells asegs _ _ _ _ RWD) as [(B0 & B1 & BY) _].
      rewrite <- (mrd_overlay_high m' a) by (clear - Ha HDtop Ho HDhi RNG Hn; subst d; unfold AAPP_HI in HDhi; slia0).
      replace a with (d + Z.of_nat (Z.to_nat (a - d))) by (clear - Ha; slia0). rewrite BY by (unfold poison_bytes; rewrite repeat_length; clear - Ha Hn; slia0).
      unfold poison_bytes. apply nth_error_repeat. clear - Ha Hn. slia0. }
    (* [comment removed for export] *)
    set (mH := fun w : word => if ((SP - 4096 <=? bv_unsigned w) && (bv_unsigned w <? SP))%Z then m' w else ms_mem ms w).
    assert (SPLO : q_lo Q <= SP - 4096) by (clear - Hlsp Espu Hoff1 Ef2; slia).
    assert (SPB : aceil <= SP - 4096 /\ SP <= q_sp0 Q /\ q_sp0 Q < 2 ^ 64) by (clear - SPLO SB1 Espu Hoff2 HB64; slia).
    assert (MHin : forall a, SP - 4096 <= a < SP -> mH (wa a) = m' (wa a)).
    { intros a Ha. subst mH. cbv beta. rewrite wa_unsigned by (clear - Ha SPB ACEILB; slia0).
      destruct (Z.leb_spec0 (SP - 4096) a) as [L1|L1]; [| exfalso; clear - Ha L1; slia0]. destruct (Z.ltb_spec0 a SP) as [L2|L2]; [reflexivity| exfalso; clear - Ha L2; slia0]. }
    assert (MHout : forall a, 0 <= a < 2 ^ 64 -> ~ (SP - 4096 <= a < SP) -> mH (wa a) = ms_mem ms (wa a)).
    { intros a Ha Hna. subst mH. cbv beta. rewrite wa_unsigned by (clear - Ha; slia0).
      destruct (Z.leb_spec0 (SP - 4096) a) as [L1|L1]; [| reflexivity]. destruct (Z.ltb_spec0 a SP) as [L2|L2]; [exfalso; clear - Hna L1 L2; slia0| reflexivity]. }
    assert (MH1 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + to_Z n) -> m' (wa a) = mH (wa a)).
    { intros a Ha Hna. destruct (Z.leb_spec0 (SP - 4096) a) as [L1|L1]; [destruct (Z.ltb_spec0 a SP) as [L2|L2]|].
      - rewrite MHin by (clear - L1 L2; slia0). reflexivity.
      - rewrite MHout by (first [exact Ha| clear - L2; slia0]). apply Hkeep0; [exact Ha| subst W; cbn [outside]; clear - Hna L2; repeat split; slia0].
      - rewrite MHout by (first [exact Ha| clear - L1; slia0]). apply Hkeep0; [exact Ha| subst W; cbn [outside]; clear - Hna L1; repeat split; slia0]. }
    assert (MH2 : forall w : word, m' w = write_to_mem mH (wa d) (repeat (Z_to_bv 8 (to_Z (c land 255)%uint63)) (Z.to_nat (to_Z n))) w).
    { intros w. pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
      rewrite write_to_mem_spec by (rewrite ?repeat_length, ?Z2Nat.id by (clear - Hn; slia0); clear - HD0 Ho HDhi RNG Hn; subst d; unfold AAPP_HI in HDhi; slia0).
      rewrite repeat_length, Z2Nat.id by (clear - Hn; slia0). rewrite <- (wa_id w).
      rewrite wa_unsigned by (clear - Hw; slia0).
      destruct (Z.leb_spec0 d (bv_unsigned w)) as [L1|L1]; [destruct (Z.ltb_spec0 (bv_unsigned w) (d + to_Z n)) as [L2|L2]|]; cbn [andb].
      - rewrite (DST (bv_unsigned w)) by (clear - L1 L2; slia0). rewrite nth_error_repeat by (clear - L1 L2 Hn; slia0).
        rewrite to_Z_land255, (Z.mod_small (to_Z c) 256) by (clear - Hc256; slia0). reflexivity.
      - apply MH1; [clear - Hw; slia0| clear - L2; slia0].
      - apply MH1; [clear - Hw; slia0| clear - L1; slia0]. }
    assert (STKH : stk asegs mH (q_lo Q) SP).
    { apply (stk_merge asegs mH (q_lo Q) (SP - 4096) SP); [| | clear - SPLO; slia0].
      - apply (stk_pres asegs (ms_mem ms)); [exact (proj1 (stk_split asegs _ _ (SP - 4096) _ Hstk_lo ltac:(clear - SPLO; slia0)))|].
        intros a Ha. apply pw_keep'. apply MHout; [clear - Ha SB1 SPB ACEILB; slia0| clear - Ha; slia0].
      - apply (stk_pres asegs m'); [exact (proj2 (stk_split asegs _ _ (SP - 4096) _ Hstk' ltac:(clear - SPLO; slia0)))|].
        intros a Ha. apply pw_keep'. apply MHin. exact Ha. }
    (* [comment removed for export] *)
    set (L14 := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
    set (rho' := rho_ext rho tn L14).
    exists rho'.
    assert (Hag' : agree tn rho rho') by (apply agree_ext; [clear; slia0| clear - Hn2; slia0| exact Xr0]).
    assert (EL14 : forall x (kk : nat), (kk < 14)%nat -> to_Z x = to_Z tn + Z.of_nat kk -> rho' x = nth kk L14 w0).
    { intros x kk Hk Hx. subst rho'. apply (rho_ext_at rho tn L14 x kk); [subst L14; cbn; clear - Hk; slia0| exact Hx]. }
    (* [comment removed for export] *)
    assert (TDG : forall g, In g G -> (g_tag g + 1)%uint63 <> td).
    { intros g Hg E. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & Htg1 & Htg2 & _). pose proof (i63_range (g_tag g)) as Htg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      destruct (Uint63.eqb td 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. rewrite E1 in E. apply (f_equal to_Z) in E. rewrite Etg1 in E. change (to_Z 1%uint63) with 1 in E. clear - E Htg1. slia.
      - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
        + destruct XTsep as (S1 & _). destruct (S1 g g0 Hg Hg0) as [DD|DD].
          * intros Egg. subst g0. rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd. slia.
          * rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd DD. slia.
          * rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd DD. slia.
        + destruct XTsep as (_ & S2 & _). destruct (S2 g f0 Hg Hf0) as [DD|DD]; rewrite <- E in Etd; apply (f_equal to_Z) in Etd; rewrite Etg1 in Etd; clear - Etd DD; slia. }
    assert (TDF : forall f, In f FF -> (f_tag f + 1)%uint63 <> td /\ (f_tag f + 2)%uint63 <> td).
    { intros f Hf. pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & Htg1 & Htg2 & _). pose proof (i63_range (f_tag f)) as Htg.
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Hn59; slia0).
      assert (GEN : forall x, to_Z x = to_Z (f_tag f) + 1 \/ to_Z x = to_Z (f_tag f) + 2 -> x <> td).
      { intros x Hx E. subst x. destruct (Uint63.eqb td 1) eqn:E1.
        - apply Uint63.eqb_spec in E1. rewrite E1 in Hx. change (to_Z 1%uint63) with 1 in Hx. clear - Hx Htg1. slia.
        - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
          + destruct XTsep as (_ & S2 & _). destruct (S2 g0 f Hg0 Hf) as [DD|DD]; rewrite Etd in DD; clear - Hx DD; slia.
          + destruct XTsep as (_ & _ & S3). destruct (S3 f f0 Hf Hf0) as [DD|DD].
            * intros Eff. subst f0. rewrite Etd in Hx. clear - Hx. slia.
            * rewrite Etd in DD. clear - Hx DD. slia.
            * rewrite Etd in DD. clear - Hx DD. slia. }
      split; apply GEN; [left; exact Etg1| right; exact Etg2]. }
    assert (TD2 : td <> 2%uint63 /\ td <> 3%uint63 /\ td <> 0%uint63).
    { destruct (Uint63.eqb td 1) eqn:E1; [apply Uint63.eqb_spec in E1; rewrite E1; repeat split; intros E; discriminate E|].
      apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
      - pose proof (proj1 (Forall_forall _ _) XGin g0 Hg0) as (_ & _ & _ & Htg1 & _). rewrite Etd in Htg1.
        repeat split; intros E; rewrite E in Htg1; [change (to_Z 2%uint63) with 2 in Htg1| change (to_Z 3%uint63) with 3 in Htg1| change (to_Z 0%uint63) with 0 in Htg1]; clear - Htg1; slia.
      - pose proof (proj1 (Forall_forall _ _) XFFin f0 Hf0) as (_ & _ & _ & _ & Htg1 & _). rewrite Etd in Htg1.
        repeat split; intros E; rewrite E in Htg1; [change (to_Z 2%uint63) with 2 in Htg1| change (to_Z 3%uint63) with 3 in Htg1| change (to_Z 0%uint63) with 0 in Htg1]; clear - Htg1; slia. }
    destruct TD2 as (TD2 & TD3 & TD0).
    (* [comment removed for export] *)
    assert (BACK : forall x r, iget x M2 = Some r -> exists r0, iget x (f_mem F) = Some r0 /\ rg_lo r0 = rg_lo r /\ rg_len r0 = rg_len r
                     /\ (x <> td -> x <> 1%uint63 -> r0 = r)).
    { intros x r Hx. destruct (Uint63.eqb x td) eqn:Ex.
      - apply Uint63.eqb_spec in Ex. subst x. rewrite Hrgd' in Hx. injection Hx as <-. exists rgd. split; [exact Hrgd|]. rewrite F1lo, F1len, G1lo, G1len, Hlod.
        split; [reflexivity|]. split; [reflexivity|]. intros NE _. exfalso. exact (NE eq_refl).
      - apply Uint63.eqb_false_spec in Ex. rewrite (Hoth2 x Ex), iget_iset in Hx. destruct (Uint63.eqb x 1) eqn:Ex1.
        + apply Uint63.eqb_spec in Ex1. subst x. injection Hx as <-. exists rg1. split; [exact Hrg1|]. unfold drop_below. cbn [rg_lo rg_len].
          split; [reflexivity|]. split; [reflexivity|]. intros _ NE. exfalso. exact (NE eq_refl).
        + exists r. split; [exact Hx|]. repeat split; reflexivity. }
    assert (KEEPx : forall x, x <> td -> x <> 1%uint63 -> iget x M2 = iget x (f_mem F)).
    { intros x NEx NE1. rewrite (Hoth2 x NEx), iget_iset, (proj2 (Uint63.eqb_false_spec _ _) NE1). reflexivity. }
    (* [comment removed for export] *)
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    assert (HRn' : Rn asegs IM (tn + 14)%uint63 rho' (FS (ret_of l) (iset 10 (FxState.rget F 10) (clobber clob14 tn (f_regs F))) M2 None) ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree tn rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Etn14; clear; slia0]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z tn + 14 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Etn14; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''old : forall x, to_Z x < to_Z tn -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by (clear - Hx; slia0). subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia); exact Xr1).
      assert (Erho''d : rho'' td = wa D) by (rewrite Erho''old by exact Htd_lt; exact ErD).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; rv rho F 10;
                      a1'; a2'; a3'; a4'; a5'; a6'; a7'; rv rho F 18; rv rho F 19; rv rho F 20; rv rho F 21; rv rho F 22; rv rho F 23;
                      rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; t3'; t4'; t5'; t6']).
        apply R_regs_of_match; [exact Hrho''0 | reflexivity |].
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 5) (rv rho F 6) (rv rho F 7) (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     (rv rho F 11) (rv rho F 12) (rv rho F 13) (rv rho F 14) (rv rho F 15) (rv rho F 16) (rv rho F 17) (rv rho F 18) (rv rho F 19) (rv rho F 20)
                     (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) (rv rho F 28) (rv rho F 29) (rv rho F 30) (rv rho F 31))
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; rv rho F 5; rv rho F 6; rv rho F 7; rv rho F 8; rv rho F 9; rv rho F 10;
                      rv rho F 11; rv rho F 12; rv rho F 13; rv rho F 14; rv rho F 15; rv rho F 16; rv rho F 17; rv rho F 18; rv rho F 19; rv rho F 20;
                      rv rho F 21; rv rho F 22; rv rho F 23; rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; rv rho F 28; rv rho F 29; rv rho F 30; rv rho F 31]) in HR''.
        pose proof (regs_match_of_R _ _ _ _ _ _ _ _ _ _ _ HR'') as Hpre.
        assert (Hnd14 : List.NoDup clob14) by (apply nodupb_spec; reflexivity).
        assert (Hcl : forall kr : int, iget kr (clobber clob14 tn (f_regs F)) =
                      match index_of kr clob14 with
                      | Some i => Some (FV (of_Z (to_Z tn + Z.of_nat i)) w_zero)
                      | None => iget kr (f_regs F) end).
        { intros kr. apply iget_clobber; [exact Hnd14 | cbn [length clob14]; clear - Hn59; slia0]. }
        apply regs_match_intro. cbn [seq].
        repeat (apply Forall_cons || apply Forall_nil);
          cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ];
          match goal with |- _ = dv _ (FxState.rget ?FF' ?kr) =>
            let kk := eval vm_compute in kr in change kr with kk; rewrite (rget_regs' FF' kk eq_refl) end;
          cbn [f_regs]; rewrite iget_iset;
          match goal with |- _ = dv _ match (if ?b then _ else _) with _ => _ end => let bb := eval vm_compute in b in change b with bb end;
          cbv iota.
        all: try (rewrite Hcl;
                  match goal with |- _ = dv _ match match ?ix with _ => _ end with _ => _ end =>
                    let ii := eval vm_compute in ix in change ix with ii end; cbv iota).
        all: first
          [ match goal with |- rv _ _ 10 = dv ?rr _ => rewrite (dv_agree tn rho rr _ HagF) by (rewrite Ea0; cbn [vtag]; exact Htd_lt); rewrite Erv; reflexivity end
          | match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); clear - Hn59 Htn; slia0);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Htn; slia0);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Htn; slia0);
              rewrite (EL14 (of_Z (to_Z t1 + Z.of_nat i)) i); [reflexivity | clear; slia0 | rewrite Etag; clear; slia0]
            end
          | match goal with |- rv _ _ ?kz = dv _ match iget ?ki (f_regs ?FF') with _ => _ end =>
              rewrite <- (rget_regs' FF' ki eq_refl);
              let kn := eval vm_compute in (Z.to_nat kz) in
              let HP := fresh "HP" in
              pose proof (Hpre kn ltac:(slia)) as HP; cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in HP; exact HP
            end
          ].
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        cbn [f_mem ms_mem].
        (* [comment removed for export] *)
        assert (PARTS1 : forall t' rg', iget t' (iset 1 (drop_below off rg1) (f_mem F)) = Some rg' -> mem_part asegs IM rho'' mH t' rg').
        { intros t' rg' Ht'. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
          - apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
            apply (stack_part asegs IM rho'' (ms_mem ms) mH rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q));
              [exact Erho''1| exact Hlo1| exact Hd1| exact Hkd1| rewrite Hlen1; reflexivity| rewrite Hlen1; clear - Hoff Hoff2; slia| clear - Hoff16 Hoff; Z.div_mod_to_equations; slia
              | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1)| exact Xstk| clear - Hhl Hlsp ACEILB; slia| rewrite <- Espu; exact STKH|].
            intros a Ha. apply pw_keep. apply MHout; [clear - Ha Espu SPB SPge0; slia0| clear - Ha Espu; slia0].
          - apply Uint63.eqb_false_spec in E1. pose proof (OLDLT _ _ Ht') as Hlt'.
            destruct (t' =? 0)%uint63 eqn:E0.
            + apply Uint63.eqb_spec in E0. subst t'. rewrite Hrg0 in Ht'. injection Ht' as <-.
              apply (mem_part_transfer0 IMX rho'' (ms_mem ms) mH rg0 Hrho''0); [rewrite Hlen0; unfold AIMG_TOP; clear; slia0| | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0)].
              intros a Ha. rewrite Hlo0, Hlen0 in Ha. apply pw_keep. apply MHout; [clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia0| clear - Ha SPB ACEILB; unfold AIMG_LO, AIMG_TOP in Ha; slia0].
            + apply Uint63.eqb_false_spec in E0. destruct (REGLO t' rg' Ht' E1) as [RL1 RL2]. pose proof (proj1 (proj1 Hmem'' t' rg' Ht')) as (_ & _ & RO3 & _).
              rewrite (Erho''old t' Hlt') in RO3.
              apply (mem_part_transfer asegs IM rho'' (ms_mem ms) mH t' rg' (bv_unsigned (rho'' t')));
                [symmetry; apply wa_id| clear; pose proof (bv_unsigned_in_range 64 (rho'' t')); slia0| rewrite (Erho''old t' Hlt'); clear - RO3; slia0| | intros _ _ _; exact E0
                | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Ht')].
              intros a Ha. rewrite (Erho''old t' Hlt') in Ha. apply pw_keep. apply MHout; [clear - Ha RL1 RL2 ACEILB; slia0| clear - Ha RL2 SPB; slia0]. }
        (* [comment removed for export] *)
        destruct (fill_bytes_sound asegs IM rho'' Hrho''0 (Z.to_nat (to_Z n)) _ td o (c land 255)%uint63 M2 rgd1 mH HM2 Hrgd1 (PARTS1 td rgd1 Hrgd1) Htd0 G1unk G1inb
                    ltac:(rewrite G1len, Z2Nat.id by (clear - Hn; slia0); exact RNG) ltac:(rewrite to_Z_land255; clear - Hc; Z.div_mod_to_equations; slia0))
          as (rgd'' & Hrgd'' & _ & PARTF & _).
        assert (Ergd'' : rgd'' = rgd') by (clear - Hrgd' Hrgd''; congruence). subst rgd''.
        rewrite (adr_eq_wa rho'' td D (to_Z o) Erho''d HD0) in PARTF by (first [clear - Ho; slia0| clear - Ho HDhi RNG Hn; unfold AAPP_HI in HDhi; slia0]).
        apply mem_ok_parts.
        + intros t' rg' Ht'. destruct (t' =? td)%uint63 eqn:Etd'.
          * apply Uint63.eqb_spec in Etd'. subst t'. rewrite Hrgd' in Ht'. injection Ht' as <-.
            apply (mem_part_transfer asegs IM rho'' (write_to_mem mH (wa d) (repeat (Z_to_bv 8 (to_Z (c land 255)%uint63)) (Z.to_nat (to_Z n)))) m' td rgd' D Erho''d HD0);
              [rewrite F1len, G1len; clear - HDhi; unfold AAPP_HI in HDhi; slia0| intros a Ha; apply pw_keep; apply MH2| intros _ _ _; exact Htd0| exact PARTF].
          * apply Uint63.eqb_false_spec in Etd'. pose proof Ht' as Ht2. rewrite (Hoth2 t' Etd') in Ht'. pose proof (PARTS1 t' rg' Ht') as P1.
            pose proof (proj1 P1) as (_ & _ & RO3 & RO4 & _).
            assert (FP : forall a, bv_unsigned (rho'' t') + to_Z (rg_lo rg') <= a < bv_unsigned (rho'' t') + to_Z (rg_len rg') -> ~ (d <= a < d + to_Z n)).
            { intros a Ha Hin. destruct (BACK t' rg' Ht2) as (r0 & Hr0 & Lo0 & Le0 & _). rewrite <- Lo0, <- Le0 in Ha.
              destruct (proj2 Hmem'' t' td r0 rgd Etd' Hr0 Hrgd) as [SEP|SEP]; rewrite Erho''d, ?Hlod in SEP;
                rewrite (wa_unsigned D) in SEP by (clear - HD0 HDhi Hld; unfold AAPP_HI in HDhi; slia0); [change (to_Z 0%uint63) with 0 in SEP|];
                clear - SEP Ha Hin RNG Ho; subst d; slia0. }
            destruct (t' =? 0)%uint63 eqn:E0.
            -- apply Uint63.eqb_spec in E0. subst t'. rewrite iget_iset in Ht'. change ((0 =? 1)%uint63) with false in Ht'. cbv iota in Ht'. rewrite Hrg0 in Ht'. injection Ht' as <-.
               apply (mem_part_transfer0 IMX rho'' mH m' rg0 Hrho''0); [rewrite Hlen0; unfold AIMG_TOP; clear; slia0| | exact P1].
               intros a Ha. apply pw_keep. apply MH1; [rewrite Hlo0, Hlen0 in Ha; clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia0|].
               apply FP. rewrite Hrho''0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. clear - Ha. slia0.
            -- apply Uint63.eqb_false_spec in E0.
               apply (mem_part_transfer asegs IM rho'' mH m' t' rg' (bv_unsigned (rho'' t')));
                 [symmetry; apply wa_id| clear; pose proof (bv_unsigned_in_range 64 (rho'' t')); slia0| clear - RO3; slia0| | intros _ _ _; exact E0| exact P1].
               intros a Ha. apply pw_keep. apply MH1; [pose proof (RO4 E0) as RO4'; clear - Ha RO3 RO4'; slia0| exact (FP a Ha)].
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2.
          destruct (BACK t1 r1 Hi1) as (q1 & Hq1 & Lo1 & Le1 & _). destruct (BACK t2 r2 Hi2) as (q2 & Hq2 & Lo2 & Le2 & _).
          rewrite <- Lo1, <- Le1, <- Lo2, <- Le2. exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
    (* [comment removed for export] *)
    assert (CW : Forall (aclient_write_ok H LB) W).
    { subst W. apply Forall_cons; [exact CWD|]. apply Forall_cons; [left; cbn [fst snd]; clear - SPB; slia| apply Forall_nil]. }
    assert (SW : Forall stack0_ok W).
    { subst W. apply Forall_cons; [exact S0D|]. apply Forall_cons; [apply stack0_ok_app; clear - SPB ACEILB; unfold AHI_LO; slia| apply Forall_nil]. }
    assert (AFW : Forall (afs_write_ok H (LF_of Q FF)) W).
    { subst W. apply Forall_cons; [exact AFD|]. apply Forall_cons; [| apply Forall_nil].
      left. cbn [fst snd]. clear - F1 F2 SPB ACEILB. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. split; slia. }
    (* [comment removed for export] *)
    assert (GDJ : forall g, In g G -> disjoint_from W (sh (g_addr g)) (nsh (to_Z (g_size g)))).
    { intros g Hg. pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (i63_range (g_size g)) as Hgs0.
      pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 ltac:(clear - Hgs0; slia0)) as (U1 & U2 & U3).
      assert (SHA : sh aceil < aceil) by (clear - ACEILB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; slia).
      subst W. cbn [disjoint_from]. split; [| split; [clear - U2 U3 SHA SPB; slia| exact I]].
      destruct (Uint63.eqb td 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. destruct (STK E1) as (_ & _ & SPd & _). left. clear - U2 SHA SPB SPd. slia.
      - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & APD & _).
        destruct (app_vs_shX D (to_Z (rg_len rgd)) (g_addr g) (to_Z (g_size g)) APD ltac:(clear - Hld; slia0) G7 ltac:(clear - Hgs0; slia0)) as [DD|DD];
          [right; clear - DD RNG Ho; subst d; slia| left; clear - DD Ho; subst d; slia]. }
    destruct Xnamed as [XG0in XLB0nd].
    exists s, LB, G, FF, XS, ms1.
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mk f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS ms1].
    - exact Evis'.
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr2 | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr3 | change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia].
    - eapply agree_trans; [exact Xag | exact Hag' | clear - Xn0a Xn0b; slia].
    - rewrite Etn14. clear - Xn0a Xn0b Hn59. slia.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmp').
    - eapply (ah_RHEAP_frame H HH); [exact Xheap| exact MU| exact WM| exact CW].
    - eapply (ah_RFS_frame H HH); [exact Xrfs| exact MU| exact WM| exact AFW].
    - exact Hac'.
    - eapply stack0_transport; [exact Xst0| exact MU| exact WM| exact SW].
    - eapply (chain_via_munch H HH); [exact Xch| exact MU|]. intros fp' ra' Hin. specialize (XCH0 fp' ra' Hin).
      subst W. cbn [disjoint_from]. clear - XCH0 SP0D SPB. repeat split; slia.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - exact XAL.
    - exact XAL0.
    - exact XG.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
      pose proof (i63_range (g_tag g)) as Htg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (NG1 : g_tag g <> 1%uint63) by (intros E; rewrite E in Htg1; change (to_Z 1%uint63) with 1 in Htg1; clear - Htg1; slia).
      assert (NS1 : (g_tag g + 1)%uint63 <> 1%uint63) by (intros E; apply (f_equal to_Z) in E; rewrite Etg1 in E; change (to_Z 1%uint63) with 1 in E; clear - E Htg1; slia).
      split; [exact Hin|]. split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
      split; [rewrite Etn14; clear - Htg2; slia|]. split.
      + destruct (Uint63.eqb (g_tag g) td) eqn:Egt.
        * apply Uint63.eqb_spec in Egt. exists rgd'. rewrite Egt, Hrgd'. split; [reflexivity|]. rewrite Egt in Hgg. assert (rgg = rgd) by (clear - Hgg Hrgd; congruence). subst rgg.
          rewrite F1lo, F1len, F1al, F1kd, F1df, G1lo, G1len, G1al, G1kd, G1df. repeat split; assumption || reflexivity.
        * apply Uint63.eqb_false_spec in Egt. exists rgg. rewrite (KEEPx _ Egt NG1). split; [exact Hgg|]. repeat split; assumption.
      + intros rg' Hrg'. rewrite (KEEPx _ (TDG g Hg) NS1) in Hrg'.
        destruct (Hshg rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hrs|].
        eapply addressable_transport; [exact Had'| exact MU| exact WM| exact (GDJ g Hg)].
    - exact XGnd.
    - exact XGtnd.
    - exact XGnew.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
      apply (stk_keep (ms_mem ms) m'); [exact Hs| exact WM|]. intros a Ha.
      destruct (Z.leb_spec0 d a) as [L1|L1]; [destruct (Z.ltb_spec0 a (d + to_Z n)) as [L2|L2]|].
      + right. exists (b8 (to_Z c)). rewrite (mrd_overlay_high m' a) by (clear - Ha G4 G5 ACEILB; slia). apply DST. clear - L1 L2. slia0.
      + left. apply Hkeep0; [clear - Ha G4 G5 ACEILB; unfold AIMG_TOP in G4; slia|]. subst W. cbn [outside]. clear - L2 Ha G5 SPB. repeat split; slia.
      + left. apply Hkeep0; [clear - Ha G4 G5 ACEILB; unfold AIMG_TOP in G4; slia|]. subst W. cbn [outside]. clear - L1 Ha G5 SPB. repeat split; slia.
    - exact XFF.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)) as Htg.
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Hn59; slia0).
      assert (NF1 : f_tag f <> 1%uint63) by (intros E; rewrite E in Htg1; change (to_Z 1%uint63) with 1 in Htg1; clear - Htg1; slia).
      assert (NS1 : (f_tag f + 1)%uint63 <> 1%uint63) by (intros E; apply (f_equal to_Z) in E; rewrite Etg1 in E; change (to_Z 1%uint63) with 1 in E; clear - E Htg1; slia).
      assert (NL1 : (f_tag f + 2)%uint63 <> 1%uint63) by (intros E; apply (f_equal to_Z) in E; rewrite Etg2 in E; change (to_Z 1%uint63) with 1 in E; clear - E Htg1; slia).
      destruct (TDF f Hf) as [TDs TDl].
      split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hf1|].
      split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; clear - Htg2; slia); exact Hf2|]. split; [exact Hkf|]. split; [exact Htg1|]. split; [rewrite Etn14; clear - Htg2; slia|].
      split.
      { destruct (Uint63.eqb (f_tag f) td) eqn:Eft.
        - apply Uint63.eqb_spec in Eft. exists rgd'. rewrite Eft, Hrgd'. split; [reflexivity|]. rewrite Eft in Hgf. assert (rgf = rgd) by (clear - Hgf Hrgd; congruence). subst rgf.
          rewrite F1lo, F1len, F1al, F1kd, F1df, G1lo, G1len, G1al, G1kd, G1df. repeat split; assumption || reflexivity.
        - apply Uint63.eqb_false_spec in Eft. exists rgf. rewrite (KEEPx _ Eft NF1). split; [exact Hgf|]. repeat split; assumption. }
      split; [exists rgs; rewrite (KEEPx _ TDs NS1); split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite (KEEPx _ TDl NL1); exact Hflg|].
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. exact X4.
    - exact XFFnd.
    - exact XFFtnd.
    - exact XTsep.
    - exact XFFlen.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. destruct (BACK t' rg' Ht') as (r0 & Hr0 & _). exact (Xdom t' r0 Hr0).
    - (* [comment removed for export] *) exists rg0. rewrite (KEEPx _ ltac:(intros E; exact (TD0 (eq_sym E))) ltac:(intros E; discriminate E)). split; [exact Hrg0|]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0| exact Hpg0].
    - (* [comment removed for export] *) destruct (Uint63.eqb td 1) eqn:E1.
      + apply Uint63.eqb_spec in E1. exists rgd'. rewrite <- E1, Hrgd'. split; [reflexivity|]. destruct (STK E1) as (_ & Ergd & _).
        rewrite F1lo, F1len, F1al, F1kd, F1df, G1lo, G1len, G1al, G1kd, G1df, Ergd. repeat split; assumption || reflexivity.
      + apply Uint63.eqb_false_spec in E1. exists (drop_below off rg1). rewrite (Hoth2 1%uint63 ltac:(intros E; exact (E1 (eq_sym E)))), iget_iset, Uint63.eqb_refl.
        split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite (KEEPx _ ltac:(intros E; exact (TD2 (eq_sym E))) ltac:(intros E; discriminate E)). exact Xreg2.
    - (* [comment removed for export] *) rewrite (KEEPx _ ltac:(intros E; exact (TD3 (eq_sym E))) ltac:(intros E; discriminate E)). exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc). exists rg0_. rewrite (KEEPx _ ltac:(intros E; exact (TD0 (eq_sym E))) ltac:(intros E; discriminate E)). split; [exact Hrg0_| exact Hroc].
    - (* [comment removed for export] *) intros t' rg' pn p' ci cc Ht' Hp' Hc'.
      destruct (Uint63.eqb t' td) eqn:Etd'.
      + apply Uint63.eqb_spec in Etd'. subst t'. rewrite Hrgd' in Ht'. injection Ht' as <-. exact (INB' pn p' ci cc Hp' Hc').
      + apply Uint63.eqb_false_spec in Etd'. rewrite (Hoth2 t' Etd'), iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
        * injection Ht' as <-. exact (INB1 pn p' ci cc Hp' Hc').
        * exact (Xinb t' rg' pn p' ci cc Ht' Hp' Hc').
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0.
      destruct (Uint63.eqb t' td) eqn:Etd'.
      + apply Uint63.eqb_spec in Etd'. subst t'. rewrite Hrgd' in Ht'. injection Ht' as <-. destruct UNK' as (_ & Hdu & Hku). split; [left; exact Hdu| exact Hku].
      + apply Uint63.eqb_false_spec in Etd'. rewrite (Hoth2 t' Etd'), iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
        * injection Ht' as <-. destruct UNK1 as (_ & Hdu & Hku). split; [left; exact Hdu| exact Hku].
        * exact (Xkinds t' rg' Ht' Ht'0).
    - exact Xcost.
    - exact Xcnt.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) SP (q_sp0 Q)); [exact Hstk' | | clear - SPLO SPB; slia].
      apply (stk_keep (ms_mem ms) m'); [split; [exact SPge0| split; [exact SP064| exact STKHI]]| exact WM|]. intros a Ha.
      destruct (Z.leb_spec0 d a) as [L1|L1]; [destruct (Z.ltb_spec0 a (d + to_Z n)) as [L2|L2]|].
      + right. exists (b8 (to_Z c)). rewrite (mrd_overlay_high m' a) by (clear - Ha SPB ACEILB; unfold AIMG_TOP; slia). apply DST. clear - L1 L2. slia0.
      + left. apply Hkeep0; [clear - Ha SPB ACEILB; slia|]. subst W. cbn [outside]. clear - L2 Ha. repeat split; slia.
      + left. apply Hkeep0; [clear - Ha SPB ACEILB; slia|]. subst W. cbn [outside]. clear - L1 Ha. repeat split; slia.
    - repeat split; assumption.
    - eapply (ah_rauxv_frame H HH); [exact Xaux| exact MU| exact WM| exact CW].
    - exact Hinv'.
    - apply (stk_pres asegs (ms_mem ms)); [exact Xerr|]. intros a Ha. apply Hkeep0; [clear - Ha Eerr H0 H1; unfold errA, AERRNO, ATP in *; slia|].
      subst W. cbn [outside]. clear - Ha Eerr H0 H1 HDtop Ho SPB ACEILB. subst d. unfold errA, AERRNO, ATP, AIMG_TOP in *. repeat split; slia.
    - exact (HSH0 _ Hac' Hinv').
    - exact XLB0.
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - exact XLBsub.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      pose proof (EXD a Hcl Hna Hnxs) as NA.
      assert (LOW : SP <= a \/ a < aceil).
      { unfold client0, aclient_addr in Hcl. destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        - left. clear - Hs SPB. slia.
        - right. clear - Hst ACEILB. unfold aimg_client, AIMG_LO, AIMG_TOP in *. slia.
        - right. destruct (XLB0h b Hb) as [_ Bh]. clear - Hr Bh. slia.
        - right. destruct (XLB0h b Hb) as [B0 Bh]. pose proof (sh_nsh_high (blk_addr b) (blk_size b) B0 ltac:(clear - Hr; unfold nsh in Hr; Z.div_mod_to_equations; slia) ltac:(clear - Bh ACEILB; unfold AAPP_HI; slia)) as SB.
          clear - Hr SB ACEILB. unfold AHI_LO in *. slia.
        - right. clear - Hfs F2. slia.
        - right. pose proof (sh_below_app (as_FSB H + AFS_SIZE) ltac:(clear - F1 F2 ACEILB; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; slia)) as SB.
          pose proof (sh_mono a). clear - Hfss SB ACEILB. unfold AHI_LO, sh in *. rewrite ?ASHADOW_BASE_val in *. Z.div_mod_to_equations. slia.
        - right. clear - Hss ACEILB. unfold AHI_LO in *. slia. }
      apply Hkeep0; [exact Ha|]. subst W. cbn [outside]. clear - NA LOW SPB. repeat split; slia.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) XFFstk f Hf) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(KF1 & KF2 & KF3 & KF4 & KF5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - KF1; slia0)) as FPf.
      apply (stk_keep (ms_mem ms) m'); [exact HsF| exact WM|]. intros a Ha.
      destruct (Z.leb_spec0 d a) as [L1|L1]; [destruct (Z.ltb_spec0 a (d + to_Z n)) as [L2|L2]|].
      + right. exists (b8 (to_Z c)). rewrite (mrd_overlay_high m' a) by (clear - Ha KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia). apply DST. clear - L1 L2. slia0.
      + left. apply Hkeep0; [clear - Ha KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia|]. subst W. cbn [outside]. clear - L2 Ha KF3 F2 SPB. repeat split; slia.
      + left. apply Hkeep0; [clear - Ha KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia|]. subst W. cbn [outside]. clear - L1 Ha KF3 F2 SPB. repeat split; slia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (a0 a2 : word) (src : list byte) (lo : Z) (m : AsShadow.mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned a0) [Cells.CB (Z.to_nat (bv_unsigned a2)) src]
      /\ ACONST m'.

  Theorem anode_memcpy_sound : anode_memcpy_sig H IMX A.
  Proof.
    unfold anode_memcpy_sig, anode_concl.
    intros Q st st' rho msF mo Hnode Hpc Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_memcpy in Hnode.
    destruct (call_okn K (ka_istack A) st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) 12)) as [n|] eqn:Hnn; [|discriminate].
    destruct (n <=? 65536)%uint63 eqn:Hn64k; [|discriminate].
    destruct (ptr_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) n) as [[td od]|] eqn:Hpa; [|discriminate].
    destruct (src_arg (f_mem (a_F st)) (FxState.rget (a_F st) 11) n) as [[ts os]|] eqn:Hsa; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hg; [|discriminate] end.
    destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
    destruct (copy_bytes IM (Z.to_nat (to_Z n)) M1 td od ts os) as [M2|] eqn:HM2; [|discriminate].
    injection Hnode as <-.
    destruct (call_okn_inv A _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv A _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv.
    apply Uint63.leb_spec in Hn64k. change (to_Z 65536%uint63) with 65536 in Hn64k.
    pose proof (conc63_inv _ _ Hnn) as Ea2.
    apply andb_true_iff in Hg as [Hg Hdisj]. apply andb_true_iff in Hg as [Hrod Hros].
    unfold range_okb in Hrod, Hros. apply andb_true_iff in Hrod as [Hlocd Haccd]. apply andb_true_iff in Hros as [Hlocs Haccs].
    destruct (ptr_arg_inv _ _ _ _ _ Hpa) as (Ea0 & Htd0 & rgd & Hrgd & Hloo & Hon & Hnlen).
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (tn := a_n st) in *.
    pose proof (i63_range tn) as Htn. change (to_Z two59) with (2 ^ 59) in Hn59. destruct Xn0 as [Xn0a Xn0b].
    pose proof (i63_range n) as Hn. pose proof (i63_range od) as Ho. pose proof (i63_range os) as Hos0. pose proof (i63_range td) as Htd. pose proof (i63_range ts) as Hts.
    assert (Etn14 : to_Z (tn + 14)%uint63 = to_Z tn + 14) by (rewrite to_Z_add_small; change (to_Z 14%uint63) with 14; clear - Htn Hn59; slia0).
    assert (Hag : agree tn rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR. pose proof (R_mem _ _ _ _ _ HR) as Hmem. cbn [f_mem] in Hmem. fold F in Hmem.
    pose proof (canonR_R asegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); clear - Hhl Hlsp HspB HB64 Hcs Hoff Hoff2 ACEILB; slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 ATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    assert (Ea2v : rv rho F 12 = Z_to_bv 64 (to_Z n)).
    { rewrite Erv. change (of_Z 12) with 12%uint63. fold F in Ea2. rewrite Ea2. apply dv_conc63. exact Xr0. }
    set (SP := bv_unsigned (rv rho F 2)) in *.
    destruct (stk_split asegs _ (q_lo Q) SP (q_sp0 Q) Xstk ltac:(clear - Espu Hhl Hlsp Hoff Hoff2; slia)) as [Hstk_lo Hstk_hi].
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0.
    destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. assert (Erg1 : rg1_ = rg1) by (clear - Hrg1 Hrg1_; congruence). subst rg1_.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
    assert (OLDLT : forall x rg, iget x (f_mem F) = Some rg -> to_Z x < to_Z tn).
    { intros x rg Hx. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]];
        [change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia| change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia
        | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia| change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia| ..].
      - apply in_map_iff in Hb as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). pose proof (i63_range (g_tag g)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hf as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 2%uint63) with 2; clear - Htg2 H0 Hn59; slia0). change (to_Z 2%uint63) with 2. clear - Htg2. slia. }
    assert (SR : sh aceil <= sh (q_sp0 Q - to_Z (c_stack K)) /\ sh (q_sp0 Q - to_Z (c_stack K)) + nsh (to_Z (c_stack K)) <= sh (q_sp0 Q)
                 /\ sh (q_sp0 Q) <= AHI_LO /\ AIMG_TOP <= sh (q_sp0 Q - to_Z (c_stack K))).
    { split; [apply sh_mono; clear - Hlsp Hhl; slia|]. split; [| split].
      - clear - Hsp32 Hcs Est16. unfold nsh, sh. Z.div_mod_to_equations. slia.
      - clear - SB2 Hshi. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
      - apply sh_above_image. clear - Hlsp Hhl ACEILB. slia. }
    assert (REGLO : forall x rg, iget x (f_mem F) = Some rg -> x <> 1%uint63 ->
              0 <= bv_unsigned (rho x) + to_Z (rg_lo rg) /\ bv_unsigned (rho x) + to_Z (rg_len rg) <= aceil).
    { intros x rg Hx Hne1. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]].
      - rewrite Hrg0 in Hx. injection Hx as <-. rewrite Xr0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0. clear - ACEILB. unfold AIMG_LO, AIMG_TOP. slia.
      - exfalso. exact (Hne1 eq_refl).
      - rewrite Xreg2 in Hx. injection Hx as <-. rewrite Xr2. unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (c_stack K)) by (clear - Hcs Est40; slia).
        change (to_Z 0%uint63) with 0. fold (nsh (to_Z (c_stack K))).
        rewrite wa_unsigned by (clear - SR Hcs; unfold AIMG_TOP, AHI_LO, nsh in SR; Z.div_mod_to_equations; slia). clear - SR ACEILB. unfold AHI_LO, AIMG_TOP in *. slia.
      - rewrite Xreg3 in Hx. injection Hx as <-. rewrite Xr3, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold abs_region. cbn [rg_lo rg_len].
        destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
        apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. rewrite Hslo, Hslen. clear - ACEILB. unfold sh, AIMG_LO, AIMG_TOP. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
      - apply in_map_iff in Hb as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
        rewrite Hgg in Hx. injection Hx as <-. rewrite Hlog, Hleng, Hrg. change (to_Z 0%uint63) with 0.
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
        rewrite wa_unsigned by (clear - G1 G3 G5 ACEILB; slia). clear - G1 G5. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hshg). destruct (Hshg rg Hx) as (-> & Hrs & _).
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 ACEILB; slia). change (to_Z 0%uint63) with 0. fold (nsh (to_Z (g_size g))).
        rewrite Hrs. pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 G3) as (U1 & U2 & U3). pose proof (sh_above_image (g_addr g) ltac:(clear - G1; slia)) as SAg.
        rewrite wa_unsigned by (clear - U2 U3 SAg G1 Hsz; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        clear - U2 U3 SAg Hsz ACEILB. unfold AIMG_TOP, AHI_LO, nsh in *. Z.div_mod_to_equations. slia.
      - apply in_map_iff in Hf as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
        rewrite Hgf in Hx. injection Hx as <-. rewrite Hlof, Hlenf, Hf0, (fsz_eq _ Hkf). change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
        rewrite wa_unsigned by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE in *; slia). clear - K2' K3 F1 F2 FPf. unfold AIMG_TOP, AFS_HDR in *. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
        rewrite Hgs in Hx. injection Hx as <-. rewrite Hlos, Hlens, Hf1. change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as [E1 E2].
        assert (B : AIMG_TOP <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) <= AAPP_HI) by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE, AAPP_HI in *; slia).
        pose proof (sh_above_image (f_ff f) ltac:(unfold AIMG_TOP in B; clear - B; slia)) as SA1.
        pose proof (sh_nsh_high (f_ff f) (AsIface.fsz (to_Z (f_k f))) ltac:(unfold AIMG_TOP in B; clear - B; slia) ltac:(clear - FPf; slia) (proj2 B)) as SA2.
        rewrite wa_unsigned by (clear - B SA1 SA2 FPf E1; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        rewrite E1. clear - SA1 SA2 ACEILB. unfold AIMG_TOP, AHI_LO in *. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & _ & Hflg & _).
        rewrite Hflg in Hx. injection Hx as <-. unfold flag_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. rewrite Hf2.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _].
        rewrite wa_unsigned by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia). clear - K5 F1 F2. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *. slia. }
    assert (KSH : to_Z (ka_sh0lo A) = sh AIMG_LO /\ to_Z (ka_sh0len A) = sh AIMG_TOP).
    { destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
      apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. split; [exact Hslo| exact Hslen]. }
    (* [comment removed for export] *)
    assert (Htd_lt : to_Z td < to_Z tn) by exact (OLDLT td rgd Hrgd).
    assert (Ea0v : rv rho F 10 = adr rho td (to_Z od)).
    { rewrite Erv. change (of_Z 10) with 10%uint63. fold F in Ea0. rewrite Ea0. apply dv_adr; [clear - Htd_lt Hn59; slia0| reflexivity]. }
    destruct (range_obj Q st rho msF mo s LB G FF XS ms false td od n off rgd X Esp2 Hoff1 Hoff2 Hn59 Htd0 Hrgd Hloo Hon Hnlen Hn64k Hlocd Haccd)
      as (D & (ErD & HD0 & HD8 & HDtop & Hlod & Hdfd & Hkdd & RNG & HDhi & STK & OBJF & (SHV & IAM & ACO & CWD & S0D & AFD & LOD & SP0D & EXD) & SHF) & ACC & SRD).
    fold F tn in STK, OBJF, SHF, EXD |- *. rewrite <- ?Espu in STK, LOD.
    pose proof (proj1 (proj1 Hmem td rgd Hrgd)) as (_ & Hlen62' & _). pose proof (i63_range (rg_len rgd)) as Hld.
    set (d := D + to_Z od) in *.
    assert (Edv : rv rho F 10 = wa d) by (rewrite Ea0v; subst d; apply (adr_eq_wa rho); [exact ErD| exact HD0| clear - Ho; slia0| clear - RNG HDhi Ho Hn; unfold AAPP_HI in HDhi; slia0]).
    assert (Edu : bv_unsigned (rv rho F 10) = d) by (rewrite Edv; apply wa_unsigned; clear - HD0 RNG HDhi Ho Hn; unfold AAPP_HI in HDhi; slia0).
    assert (Enu : bv_unsigned (rv rho F 12) = to_Z n) by (rewrite Ea2v, Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); clear - Hn; slia0).
    (* [comment removed for export] *)
    assert (SRC : exists sA : Z,
      rv rho F 11 = wa sA /\ 0 <= sA /\ sA + to_Z n <= AAPP_HI
      /\ shvis (ms_mem ms) sA (sA + to_Z n) /\ in_app_mem sA (sA + to_Z n) /\ accessible (ms_mem ms) sA (to_Z n)
      /\ (sA + to_Z n <= q_lo Q \/ SP <= sA)
      /\ (sA + to_Z n <= d \/ d + to_Z n <= sA)
      /\ (forall i, 0 <= i <= to_Z n -> adr rho ts (to_Z os + i) = wa (sA + i))
      /\ (ts <> 0%uint63 -> stk asegs (ms_mem ms) sA (sA + to_Z n)
           /\ exists rgs0, iget ts (f_mem F) = Some rgs0 /\ rho ts = wa (sA - to_Z os) /\ 0 <= sA - to_Z os /\ rg_lo rgs0 = 0%uint63
                /\ to_Z os + to_Z n <= to_Z (rg_len rgs0) /\ sA - to_Z os + to_Z (rg_len rgs0) <= AAPP_HI /\ to_Z (rg_len rgs0) <= 2 ^ 62)
      /\ (ts = 0%uint63 -> sA = to_Z os /\ AIMG_LO + 64 <= sA /\ sA + to_Z n + 64 <= AIMG_TOP)).
    { destruct (src_arg_inv _ _ _ _ _ Hsa) as [[Ets0 Ea1]|[Nts0 Hpas]].
      - (* [comment removed for export] *)
        fold F in Ea1. exists (to_Z os).
        rewrite Ets0 in Haccs. unfold loc_okb in Hlocs. rewrite Ets0, Uint63.eqb_refl in Hlocs. cbn [andb] in Hlocs. apply andb_true_iff in Hlocs as [HL1 HL2].
        apply Z.leb_le in HL1. apply Z.leb_le in HL2. unfold img_lo in HL1. unfold img_hi in HL2. rewrite (proj1 KSH) in HL1. rewrite (proj2 KSH) in HL2.
        change (to_Z shadow_K) with 2147450880 in HL1, HL2. unfold sh in HL1, HL2. rewrite ASHADOW_BASE_val in HL1, HL2.
        assert (BL : AIMG_LO + 64 <= to_Z os /\ to_Z os + to_Z n + 64 <= AIMG_TOP) by (clear - HL1 HL2; unfold AIMG_LO, AIMG_TOP in *; Z.div_mod_to_equations; slia0). clear HL1 HL2.
        assert (E11 : rv rho F 11 = wa (to_Z os)).
        { rewrite Erv. change (of_Z 11) with 11%uint63. rewrite Ea1, (dv_conc63 rho _ Xr0). reflexivity. }
        assert (Elen3 : to_Z (rg_len (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A))) = sh AIMG_TOP) by (unfold abs_region; cbn [rg_len]; exact (proj2 KSH)).
        split; [exact E11|]. split; [clear - BL; unfold AIMG_LO in BL; slia0|]. split; [clear - BL ACEILB; unfold AIMG_TOP, AAPP_HI in *; slia0|].
        split; [apply (ACONST_shvis _ _ _ Xac); clear - BL Hn; slia0|].
        split; [unfold in_app_mem; left; clear - BL Hn; unfold AIMG_LO, AIMG_TOP in *; rewrite ASHADOW_BASE_val; slia0|].
        split.
        { split; [clear - BL; unfold AIMG_LO in BL; slia0|]. split; [clear - BL ACEILB; unfold AIMG_TOP, AAPP_HI in *; slia0|].
          destruct (Z.to_nat (to_Z n)) as [|k] eqn:En; [intros z Hz; exfalso; clear - Hz En Hn; slia0|].
          intros z Hz. apply (acc_bytes_sound0 IM (S k) (f_mem F) os (ms_mem ms)); [first [exact Haccs| rewrite <- En; exact Haccs]
            | rewrite <- En, Z2Nat.id by (clear - Hn; slia0); clear - BL; unfold AIMG_TOP in BL; slia0| | rewrite <- En, Z2Nat.id by (clear - Hn; slia0); exact Hz].
          intros o3 b Ho1 Ho2 Hb. pose proof (i63_range o3) as Ho3. change (to_Z shadow_K) with 2147450880 in Ho1, Ho2.
          assert (Xr3' : rho 3%uint63 = wa 0) by exact Xr3.
          rewrite <- (adr_eq_wa rho 3%uint63 0 (to_Z o3) Xr3' ltac:(clear; slia0) ltac:(clear - Ho3; slia0) ltac:(clear - Ho3; slia0)).
          rewrite <- rview_mrd.
          exact (byte_at_SK_sound asegs IM rho Xr0 (f_mem F) (ms_mem ms) 3%uint63 o3 _ b Hmem ltac:(intros E; discriminate E) Xreg3
                   (fun pn p ci cc Hp Hc => Xinb 3%uint63 _ pn p ci cc Xreg3 Hp Hc)
                   ltac:(rewrite Elen3; rewrite <- En, Z2Nat.id in Ho2 by (clear - Hn; slia0); clear - Ho2 BL; unfold sh, AIMG_TOP in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; slia0) Hb). }
        split; [left; clear - BL Hhl ACEILB; unfold AIMG_TOP in *; slia0|].
        split; [left; clear - BL HDtop Ho; subst d; unfold AIMG_TOP in *; slia0|].
        split; [intros i Hi; rewrite Ets0; unfold adr; rewrite Xr0; apply bv_add_0_Z_to_bv|].
        split; [intros NE; exfalso; exact (NE Ets0)|].
        intros _. split; [reflexivity| exact BL].
      - (* [comment removed for export] *)
        destruct (ptr_arg_inv _ _ _ _ _ Hpas) as (Ea1 & _ & rgs0 & Hrgs0 & Hloos & Hons & Hnlens). fold F in Ea1, Hrgs0.
        assert (Hts_lt : to_Z ts < to_Z tn) by exact (OLDLT ts rgs0 Hrgs0).
        destruct (range_obj Q st rho msF mo s LB G FF XS ms true ts os n off rgs0 X Esp2 Hoff1 Hoff2 Hn59 Nts0 Hrgs0 Hloos Hons Hnlens Hn64k Hlocs Haccs)
          as (Ds & (ErDs & HDs0 & HDs8 & HDstop & Hlods & Hdfds & Hkdds & RNGs & HDshi & STKs & OBJFs & (SHVs & IAMs & _ & _ & _ & _ & LODs & SP0Ds & _) & SHFs) & ACCs & SRDs).
        fold F tn in STKs, OBJFs, SHFs |- *. rewrite <- ?Espu in STKs, LODs.
        pose proof (proj1 (proj1 Hmem ts rgs0 Hrgs0)) as (_ & Hlens62 & _). pose proof (i63_range (rg_len rgs0)) as Hlds.
        exists (Ds + to_Z os).
        assert (E11 : rv rho F 11 = wa (Ds + to_Z os)).
        { rewrite Erv. change (of_Z 11) with 11%uint63. rewrite Ea1. rewrite (dv_adr rho ts) by (first [clear - Hts_lt Hn59; slia0| reflexivity]).
          apply (adr_eq_wa rho); [exact ErDs| exact HDs0| clear - Hos0; slia0| clear - RNGs HDshi Hos0 Hn; unfold AAPP_HI in HDshi; slia0]. }
        split; [exact E11|]. split; [clear - HDs0 Hos0; slia0|]. split; [clear - RNGs HDshi Hos0; slia0|].
        split; [exact SHVs|]. split; [exact IAMs|]. split; [exact ACCs|]. split; [exact LODs|].
        split.
        { destruct (Uint63.eqb td ts) eqn:Etdts.
          - apply Uint63.eqb_spec in Etdts. cbn [negb orb] in Hdisj.
            assert (EDD : D = Ds).
            { rewrite Etdts in ErD. rewrite ErD in ErDs. apply (f_equal bv_unsigned) in ErDs.
              rewrite !wa_unsigned in ErDs by (first [clear - HD0 HDhi Hld; unfold AAPP_HI in HDhi; slia0| clear - HDs0 HDshi Hlds; unfold AAPP_HI in HDshi; slia0]). exact ErDs. }
            assert (Eodn : to_Z (od + n)%uint63 = to_Z od + to_Z n) by (rewrite to_Z_add_small; [reflexivity| clear - Ho Hn RNG Hlen62'; slia0]).
            assert (Eosn : to_Z (os + n)%uint63 = to_Z os + to_Z n) by (rewrite to_Z_add_small; [reflexivity| clear - Hos0 Hn RNGs Hlens62; slia0]).
            apply orb_true_iff in Hdisj. destruct Hdisj as [E|E]; apply Uint63.leb_spec in E; [rewrite Eodn in E; right| rewrite Eosn in E; left]; clear - E EDD; subst d; slia0.
          - apply Uint63.eqb_false_spec in Etdts.
            destruct (proj2 Hmem td ts rgd rgs0 Etdts Hrgd Hrgs0) as [SEP|SEP]; rewrite ErD, ErDs, ?Hlod, ?Hlods in SEP;
              rewrite !wa_unsigned in SEP by (first [clear - HD0 HDhi Hld; unfold AAPP_HI in HDhi; slia0| clear - HDs0 HDshi Hlds; unfold AAPP_HI in HDshi; slia0]);
              rewrite ?Hlod, ?Hlods in SEP; change (to_Z 0%uint63) with 0 in SEP; [right; clear - SEP RNG Ho Hos0; subst d; slia0| left; clear - SEP RNGs Ho Hos0; subst d; slia0]. }
        split; [intros i Hi; rewrite (adr_eq_wa rho ts Ds (to_Z os + i) ErDs HDs0) by (first [clear - Hos0 Hi; slia0| clear - RNGs HDshi Hos0 Hi Hn; unfold AAPP_HI in HDshi; slia0]); f_equal; clear; slia0|].
        split.
        { intros _. split; [exact (SRDs (Ds + to_Z os + to_Z n) ltac:(clear - Hn RNGs; slia))|]. exists rgs0. split; [exact Hrgs0|]. split; [replace (Ds + to_Z os - to_Z os) with Ds by (clear; slia0); exact ErDs|].
          split; [clear - HDs0; slia0|]. split; [exact Hlods|]. split; [exact RNGs|]. split; [clear - HDshi; slia0| exact Hlens62]. }
        intros E0. exfalso. exact (Nts0 E0). }
    destruct SRC as (sA & Ea1v & HsA0 & HsAhi & SHVs & IAMs & ACCs & LODs & DISJ & Eadr & SOBJ & SIMG).
    assert (Ea1u : bv_unsigned (rv rho F 11) = sA) by (rewrite Ea1v; apply wa_unsigned; clear - HsA0 HsAhi Hn ACEILB; unfold AAPP_HI in HsAhi; slia0).
    set (nN := Z.to_nat (to_Z n)) in *.
    assert (EnN : Z.of_nat nN = to_Z n) by (subst nN; clear - Hn; slia0).
    set (W := [(d, d + to_Z n); (SP - 4096, SP)]) in *.
    pose proof (im_ro_ok asegs IMX HIMX : image_ok asegs IM) as IMOK.
    (* [comment removed for export] *)
    destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
    assert (INB1 : rg_inb (drop_below off rg1)).
    { intros pn p' ci cc Hp' Hc'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->). unfold drop_below. cbn [rg_len].
      unfold drop_page in Hc'. cbn [fst snd] in Hc'. destruct (pn =? off >> 12)%uint63.
      - cbn [pg_cells] in Hc'. destruct (keep_cells_ge_inv _ _ _ _ Hc') as [_ Hc'']. exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'').
      - exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'). }
    assert (UNK1 : rg_unk (drop_below off rg1)).
    { split; [exact Hlo1|]. split; [exact Hd1|]. intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
      unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hkd1 _ _ Hp0). }
    set (rgd1 := if (td =? 1)%uint63 then drop_below off rg1 else rgd).
    assert (Hrgd1 : iget td (iset 1 (drop_below off rg1) (f_mem F)) = Some rgd1).
    { subst rgd1. rewrite iget_iset. destruct (td =? 1)%uint63; [reflexivity| exact Hrgd]. }
    assert (GEO1 : rg_len rgd1 = rg_len rgd /\ rg_lo rgd1 = 0%uint63 /\ rg_unk rgd1 /\ rg_inb rgd1 /\ rg_align rgd1 = rg_align rgd /\ rg_kind rgd1 = rg_kind rgd /\ rg_dflt rgd1 = Some PKUnk).
    { subst rgd1. destruct (td =? 1)%uint63 eqn:E1.
      - apply Uint63.eqb_spec in E1. assert (Ergd : rgd = rg1) by (rewrite E1 in Hrgd; clear - Hrgd Hrg1; congruence). rewrite Ergd.
        split; [reflexivity|]. split; [exact Hlo1|]. split; [exact UNK1|]. split; [exact INB1|]. split; [reflexivity|]. split; [reflexivity|]. cbn [drop_below rg_dflt]. exact Hd1.
      - split; [reflexivity|]. split; [exact Hlod|]. split; [split; [exact Hlod| split; [exact Hdfd| exact Hkdd]]|]. split; [exact (fun pn p ci cc Hp Hc => Xinb td rgd pn p ci cc Hrgd Hp Hc)|]. repeat split; try reflexivity. exact Hdfd. }
    destruct GEO1 as (G1len & G1lo & G1unk & G1inb & G1al & G1kd & G1df).
    (* [comment removed for export] *)
    assert (M1REG : forall t' rg', iget t' (iset 1 (drop_below off rg1) (f_mem F)) = Some rg' -> t' <> td ->
              exists r0, iget t' (f_mem F) = Some r0 /\ rg_lo r0 = rg_lo rg' /\ rg_len r0 = rg_len rg' /\ rg_inb rg').
    { intros t' rg' Ht' NE. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
      - apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-. exists rg1. split; [exact Hrg1|]. unfold drop_below at 1 2. cbn [rg_lo rg_len]. split; [reflexivity|]. split; [reflexivity| exact INB1].
      - exists rg'. split; [exact Ht'|]. split; [reflexivity|]. split; [reflexivity|]. exact (fun pn p ci cc Hp Hc => Xinb t' rg' pn p ci cc Ht' Hp Hc). }
    (* [comment removed for export] *)
    assert (HSVgen : forall (rhoX : int -> word) (mB : AsShadow.mem) (HX0 : rhoX 0%uint63 = Z_to_bv 64 0),
      (forall x, to_Z x < to_Z tn -> rhoX x = rho x) ->
      (forall t' rg', iget t' (iset 1 (drop_below off rg1) (f_mem F)) = Some rg' -> mem_part asegs IM rhoX mB t' rg') ->
      forall (i : nat) (so : int) Mi rgi (mX : AsShadow.mem), (i < nN)%nat -> to_Z so = (to_Z os + Z.of_nat i) mod wB ->
        iget td Mi = Some rgi -> (forall t', t' <> td -> iget t' Mi = iget t' (iset 1 (drop_below off rg1) (f_mem F))) ->
        mem_part asegs IM rhoX mX td rgi -> rg_unk rgi -> rg_inb rgi -> rg_len rgi = rg_len rgd1 ->
        (forall w, (forall j, (j < nN)%nat -> w <> aoff (adr rhoX td (to_Z od)) j) -> mX w = mB w) ->
        mem_inv asegs mX ->
        slot_val rhoX (byte_at IM Mi ts so) (rview asegs mX (adr rhoX ts (to_Z so)))).
    { intros rhoX mB HX0 HXold PARTSB i so Mi rgi mX Hi Hso HMi Hothi HpX HunkX HinbX HlenX HmX HinvX.
      destruct (Uint63.eqb ts 0) eqn:Ets.
      - apply Uint63.eqb_spec in Ets. rewrite Ets. exact (byte_at_img_sound asegs IM rhoX HX0 Mi mX so IMOK (im_ro_find_seg IMX) HinvX).
      - apply Uint63.eqb_false_spec in Ets. destruct (SOBJ Ets) as (_ & rgs0 & Hrgs0 & ErDs & HDs0 & Hlods & RNGs & HDshi & Hlens62).
        assert (Hts_lt : to_Z ts < to_Z tn) by exact (OLDLT ts rgs0 Hrgs0).
        assert (Eso : to_Z so = to_Z os + Z.of_nat i) by (rewrite Hso; apply Z.mod_small; change wB with (2 ^ 63); clear - Hi Hos0 Hn RNGs Hlens62 EnN; slia0).
        destruct (Uint63.eqb ts td) eqn:Etd.
        + apply Uint63.eqb_spec in Etd. rewrite Etd in Hrgs0 |- *. assert (Ergs : rgs0 = rgd) by (clear - Hrgs0 Hrgd; congruence).
          apply (byte_at_slot_sound asegs IM rhoX HX0 Mi mX td so rgi HpX Htd0 HMi HinbX). rewrite HlenX, G1len, <- Ergs, Eso. clear - Hi RNGs EnN. slia0.
        + apply Uint63.eqb_false_spec in Etd. pose proof (Hothi ts Etd) as Hts'.
          destruct (iget ts (iset 1 (drop_below off rg1) (f_mem F))) as [rgs1|] eqn:Hts1.
          2: { exfalso. rewrite iget_iset in Hts1. destruct (ts =? 1)%uint63; [discriminate Hts1| rewrite Hrgs0 in Hts1; discriminate Hts1]. }
          destruct (M1REG ts rgs1 Hts1 Etd) as (r0 & Hr0 & Lo1 & Le1 & INBs). rewrite Hrgs0 in Hr0. injection Hr0 as <-. (* [comment removed for export] *)
          assert (PX : mem_part asegs IM rhoX mX ts rgs1).
          { apply (mem_part_transfer asegs IM rhoX mB mX ts rgs1 (sA - to_Z os));
              [rewrite (HXold ts Hts_lt); exact ErDs| exact HDs0| rewrite <- Le1; clear - HDshi; unfold AAPP_HI in HDshi; slia0| | intros _ _ _; exact Ets
              | exact (PARTSB ts rgs1 Hts1)].
            intros a Ha. apply pw_keep. apply HmX. intros j Hj. rewrite <- Le1, <- Lo1, Hlods in Ha. change (to_Z 0%uint63) with 0 in Ha.
            rewrite aoff_adr, (adr_eq_wa rhoX td D (to_Z od + Z.of_nat j)); [| rewrite (HXold td Htd_lt); exact ErD| exact HD0| clear - Ho; slia0| clear - Ho Hj RNG HDhi EnN; unfold AAPP_HI in HDhi; slia0].
            intros E. apply (f_equal bv_unsigned) in E.
            rewrite !wa_unsigned in E by (first [clear - Ha HDs0 HDshi; unfold AAPP_HI in HDshi; slia0| clear - HD0 Ho Hj RNG HDhi EnN; unfold AAPP_HI in HDhi; slia0]).
            (* [comment removed for export] *)
            destruct (proj2 Hmem td ts rgd rgs0 (fun EE => Etd (eq_sym EE)) Hrgd Hrgs0) as [SEP|SEP]; rewrite ErD, ErDs, ?Hlod, ?Hlods in SEP;
              rewrite !wa_unsigned in SEP by (first [clear - HD0 HDhi Hld; unfold AAPP_HI in HDhi; slia0| clear - HDs0 HDshi Hlens62; unfold AAPP_HI in HDshi; pose proof (i63_range (rg_len rgs0)); slia0]);
              rewrite ?Hlod, ?Hlods in SEP; change (to_Z 0%uint63) with 0 in SEP; clear - SEP E Ha Hj RNG Ho EnN; slia0. }
          apply (byte_at_slot_sound asegs IM rhoX HX0 Mi mX ts so rgs1 PX Ets Hts' INBs). rewrite <- Le1, Eso. clear - Hi RNGs EnN. slia0. }
    (* [comment removed for export] *)
    assert (EadrX : forall rhoX : int -> word, rhoX 0%uint63 = Z_to_bv 64 0 -> (forall x, to_Z x < to_Z tn -> rhoX x = rho x) ->
              forall (i : nat) (so : int), (i < nN)%nat -> to_Z so = (to_Z os + Z.of_nat i) mod wB -> adr rhoX ts (to_Z so) = wa (sA + Z.of_nat i)).
    { intros rhoX HX0 HXold i so Hi Hso.
      assert (Hts_lt : to_Z ts < to_Z tn).
      { destruct (Uint63.eqb ts 0) eqn:Ets; [apply Uint63.eqb_spec in Ets; rewrite Ets; change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia|].
        apply Uint63.eqb_false_spec in Ets. destruct (SOBJ Ets) as (_ & rgs0 & Hrgs0 & _). exact (OLDLT ts rgs0 Hrgs0). }
      assert (Eso : to_Z so = to_Z os + Z.of_nat i).
      { rewrite Hso. apply Z.mod_small. change wB with (2 ^ 63).
        destruct (Uint63.eqb ts 0) eqn:Ets; [apply Uint63.eqb_spec in Ets; destruct (SIMG Ets) as (EsA & BL1 & BL2); clear - Hi Hos0 Hn EnN EsA BL2; unfold AIMG_TOP in BL2; slia0|].
        apply Uint63.eqb_false_spec in Ets. destruct (SOBJ Ets) as (_ & rgs0 & _ & _ & _ & _ & RNGs & _ & Hlens62). clear - Hi Hos0 Hn RNGs Hlens62 EnN; slia0. }
      rewrite Eso. unfold adr. rewrite (HXold ts Hts_lt). fold (adr rho ts (to_Z os + Z.of_nat i)). apply Eadr. clear - Hi EnN; slia0. }
    assert (HDJX : forall rhoX : int -> word, rhoX 0%uint63 = Z_to_bv 64 0 -> (forall x, to_Z x < to_Z tn -> rhoX x = rho x) ->
              forall (i j : nat) (so : int), (i < nN)%nat -> (j < nN)%nat -> to_Z so = (to_Z os + Z.of_nat i) mod wB ->
              adr rhoX ts (to_Z so) <> aoff (adr rhoX td (to_Z od)) j).
    { intros rhoX HX0 HXold i j so Hi Hj Hso. rewrite (EadrX rhoX HX0 HXold i so Hi Hso).
      rewrite aoff_adr, (adr_eq_wa rhoX td D (to_Z od + Z.of_nat j)); [| rewrite (HXold td Htd_lt); exact ErD| exact HD0| clear - Ho; slia0| clear - Ho Hj RNG HDhi EnN; unfold AAPP_HI in HDhi; slia0].
      intros E. apply (f_equal bv_unsigned) in E.
      rewrite !wa_unsigned in E by (first [clear - Hi HsA0 HsAhi EnN ACEILB; unfold AAPP_HI in HsAhi; slia0| clear - HD0 Ho Hj RNG HDhi EnN; unfold AAPP_HI in HDhi; slia0]).
      clear - E DISJ Hi Hj EnN. subst d. slia0. }
    (* [comment removed for export] *)
    assert (PARTSms : forall t' rg', iget t' (iset 1 (drop_below off rg1) (f_mem F)) = Some rg' -> mem_part asegs IM rho (ms_mem ms) t' rg').
    { intros t' rg' Ht'. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1; [| exact (mem_part_of _ _ _ _ _ _ _ Hmem Ht')].
      apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
      apply (stack_part asegs IM rho (ms_mem ms) (ms_mem ms) rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q));
        [exact Xr1| exact Hlo1| exact Hd1| exact Hkd1| rewrite Hlen1; reflexivity| rewrite Hlen1; clear - Hoff Hoff2; slia| clear - Hoff16 Hoff; Z.div_mod_to_equations; slia
        | exact (mem_part_of _ _ _ _ _ _ _ Hmem Hrg1)| exact Xstk| clear - Hhl Hlsp ACEILB; slia| rewrite <- Espu; exact Hstk_lo| intros a Ha; split; [reflexivity| intros Wv; exact Wv]]. }
    (* [comment removed for export] *)
    destruct (copy_bytes_sound asegs IM rho Xr0 nN _ td od ts os M2 rgd1 (ms_mem ms) (b8 0) HM2 Hrgd1 (PARTSms td rgd1 Hrgd1) Htd0 G1unk G1inb
                ltac:(rewrite G1len, EnN; exact RNG) Xinv)
      as (rgd' & src & Hrgd' & Hoth2 & Hsl & Hsrc & _ & UNK' & INB' & (F1lo & F1len & F1al & F1kd & F1df) & _).
    { (* [comment removed for export] *)
      intros i so Hi Hso Hts0. rewrite (EadrX rho Xr0 ltac:(intros; reflexivity) i so Hi Hso). destruct (SOBJ Hts0) as ((_ & _ & SS) & _).
      destruct (SS (sA + Z.of_nat i) ltac:(clear - Hi EnN; slia0)) as [_ [b Hb]]. exists b. rewrite rview_mrd. exact Hb. }
    { exact (HDJX rho Xr0 ltac:(intros; reflexivity)). }
    { exact (HSVgen rho (ms_mem ms) Xr0 ltac:(intros; reflexivity) PARTSms). }
    assert (BY : bytes_at asegs (ms_mem ms) sA src).
    { split; [exact HsA0|]. split; [rewrite Hsl, EnN; clear - HsAhi ACEILB; unfold AAPP_HI in HsAhi; slia0|].
      intros i Hi. rewrite Hsl in Hi. rewrite <- rview_mrd, <- (EadrX rho Xr0 ltac:(intros; reflexivity) i (os + Uint63.of_Z (Z.of_nat i))%uint63 Hi).
      - rewrite (Hsrc i (os + Uint63.of_Z (Z.of_nat i))%uint63 Hi); [symmetry; apply nth_error_nth'; rewrite Hsl; exact Hi|].
        rewrite Uint63.add_spec, Uint63.of_Z_spec. rewrite Zplus_mod_idemp_r. reflexivity.
      - rewrite Uint63.add_spec, Uint63.of_Z_spec. rewrite Zplus_mod_idemp_r. reflexivity. }
    destruct (stk_carve asegs (ms_mem ms) d (d + to_Z n) nN (SRD (d + to_Z n) ltac:(clear - Hn RNG; subst d; slia)) ltac:(rewrite EnN; clear; slia)) as [_ [junk RWJ]].
    rewrite EnN in RWJ. replace (d + to_Z n - to_Z n) with d in RWJ by (clear; slia0).
    (* [comment removed for export] *)
    pose proof Xvis as Xvis0. rewrite Ems in Xvis0.
    assert (SPLO : q_lo Q <= SP - 4096) by (clear - Hlsp Espu Hoff1 Ef2; slia).
    assert (SPB : aceil <= SP - 4096 /\ SP <= q_sp0 Q /\ q_sp0 Q < 2 ^ 64) by (clear - SPLO SB1 Espu Hoff2 HB64; slia).
    assert (EVT : evt asegs (cpy_post (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 8) (rv rho F 9)
                                      (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27)
                                      (q_F Q) (q_fc Q) (rv rho F 10) (rv rho F 12) src (q_lo Q) (ms_mem ms))
                    (MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 5) (rv rho F 6) (rv rho F 7) (rv rho F 8) (rv rho F 9) (rv rho F 10)
                         (rv rho F 11) (rv rho F 12) (rv rho F 13) (rv rho F 14) (rv rho F 15) (rv rho F 16) (rv rho F 17) (rv rho F 18) (rv rho F 19) (rv rho F 20)
                         (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) (rv rho F 28) (rv rho F 29) (rv rho F 30) (rv rho F 31))
                        (q_F Q) (Z_to_bv 64 (to_Z (f_pc F))) (q_fc Q) None (ms_mem ms) (seg_rom asegs))).
    { assert (LEN : length src = Z.to_nat (bv_unsigned (rv rho F 12))) by (rewrite Enu; exact Hsl).
      assert (G11 : q_lo Q <= SP - 4096) by exact SPLO. assert (G14 : to_Z n <= 2 ^ 40) by (clear - Hn64k; slia0).
      (* [comment removed for export] *)
      Ltac viaG G Ea1u Edu Enu := let T := type of G in enough (GG : T); [clear - GG Ea1u Edu Enu; rewrite <- ?Ea1u, <- ?Edu, <- ?Enu in GG; first [exact GG| unfold AINTRIN_STACK; exact GG]| exact G].
      Ltac cpy_pre MS0 BY LEN RWJ DISJ ACCs ACC SHVs SHV Hstk_lo SB1 G11 Xinv Xac G14 IAMs IAM ACO LOD LODs Ea1u Edu Enu :=
        eapply MS0;
        [> viaG BY Ea1u Edu Enu| exact LEN| rewrite Edu, Enu; exact RWJ| viaG DISJ Ea1u Edu Enu| viaG ACCs Ea1u Edu Enu| viaG ACC Ea1u Edu Enu
        | viaG SHVs Ea1u Edu Enu| viaG SHV Ea1u Edu Enu| exact Hstk_lo| exact SB1| viaG G11 Ea1u Edu Enu| exact Xinv| exact Xac
        | viaG G14 Ea1u Edu Enu| viaG IAMs Ea1u Edu Enu| viaG IAM Ea1u Edu Enu| viaG ACO Ea1u Edu Enu| viaG LOD Ea1u Edu Enu| viaG LODs Ea1u Edu Enu].
      destruct (HK_parts A HK) as (_ & _ & Hpcs & _). unfold K_pcs_ok in Hpcs. rewrite !andb_true_iff in Hpcs. destruct Hpcs as [[[[[[[[[[_ _] _] _] Hcpy] Hmm] _] _] _] _] _].
      destruct Hpc as [Hin|Emm].
      - unfold inl in Hin. apply existsb_exists in Hin as (y & Hy & Ey). apply Uint63.eqb_spec in Ey. fold F in Ey. subst y.
        pose proof (proj1 (forallb_forall _ _) Hcpy _ Hy) as E2. apply orb_true_iff in E2. destruct E2 as [E|E]; apply Z.eqb_eq in E; rewrite E.
        + pose proof (ah_memcpy H HH) as MS0. unfold asan_memcpy_stmt, amemcpy_stmt_at in MS0.
          eapply evt_mono; [cpy_pre MS0 BY LEN RWJ DISJ ACCs ACC SHVs SHV Hstk_lo SB1 G11 Xinv Xac G14 IAMs IAM ACO LOD LODs Ea1u Edu Enu|].
          intros ms' P. unfold amemcpy_post in P. destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & P1 & P2 & P3 & P4 & P5 & P6 & _ & P8).
          exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6| exact P8].
        + pose proof (ah_memcpy_icpt H HH) as MS0. unfold memcpy_icpt_stmt, amemcpy_stmt_at in MS0.
          eapply evt_mono; [cpy_pre MS0 BY LEN RWJ DISJ ACCs ACC SHVs SHV Hstk_lo SB1 G11 Xinv Xac G14 IAMs IAM ACO LOD LODs Ea1u Edu Enu|].
          intros ms' P. unfold amemcpy_post in P. destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & P1 & P2 & P3 & P4 & P5 & P6 & _ & P8).
          exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6| exact P8].
      - fold F in Emm. rewrite Emm. apply Z.eqb_eq in Hmm. rewrite Hmm.
        pose proof (ah_memmove H HH) as MS0. unfold asan_memmove_stmt, amemmove_stmt_at in MS0.
        cpy_pre MS0 BY LEN RWJ DISJ ACCs ACC SHVs SHV Hstk_lo SB1 G11 Xinv Xac G14 IAMs IAM ACO LOD LODs Ea1u Edu Enu. }
    eapply (ah_lift H HH _ _ s msF _ mo Xak Xvis0); [exact EVT|].
    intros msF' mo' Hak' Hmp' Hpost. unfold cpy_post in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Evis' & MU & WM & Hinv' & Hstk' & RWD & Hac').
    apply (ah_done H HH). cbn [cfg_ms cfg_model].
    rewrite Edu, Enu in MU, RWD. unfold AINTRIN_STACK in MU. change (munch W (ms_mem ms) m') in MU.
    (* [comment removed for export] *)
    destruct Hstk_hi as (SPge0 & SP064 & STKHI).
    assert (Hkeep0 : forall a, 0 <= a < 2 ^ 64 -> outside W a -> m' (wa a) = ms_mem ms (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hou. split; [apply MU; rewrite wa_unsigned by (clear - Ha; slia0); exact Hou| intros Wv; apply WM; exact Wv]. }
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> outside W a ->
                     rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hou. apply pw_keep. exact (proj1 (Hkeep0 a Ha Hou)). }
    assert (DST : forall a, d <= a < d + to_Z n -> m' (wa a) = Some (nth (Z.to_nat (a - d)) src (b8 0))).
    { intros a Ha. pose proof (u8arr_of_rw_cells asegs _ _ _ _ RWD) as [(B0 & B1 & BY') _].
      rewrite <- (mrd_overlay_high m' a) by (clear - Ha HDtop Ho HDhi RNG Hn; subst d; unfold AAPP_HI in HDhi; slia0).
      replace a with (d + Z.of_nat (Z.to_nat (a - d))) at 1 by (clear - Ha; slia0). rewrite BY' by (rewrite Hsl; clear - Ha Hn; slia0).
      apply nth_error_nth'. rewrite Hsl. clear - Ha Hn. slia0. }
    (* [comment removed for export] *)
    set (mH := fun w : word => if ((SP - 4096 <=? bv_unsigned w) && (bv_unsigned w <? SP))%Z then m' w else ms_mem ms w).
    assert (MHin : forall a, SP - 4096 <= a < SP -> mH (wa a) = m' (wa a)).
    { intros a Ha. subst mH. cbv beta. rewrite wa_unsigned by (clear - Ha SPB ACEILB; slia0).
      destruct (Z.leb_spec0 (SP - 4096) a) as [L1|L1]; [| exfalso; clear - Ha L1; slia0]. destruct (Z.ltb_spec0 a SP) as [L2|L2]; [reflexivity| exfalso; clear - Ha L2; slia0]. }
    assert (MHout : forall a, 0 <= a < 2 ^ 64 -> ~ (SP - 4096 <= a < SP) -> mH (wa a) = ms_mem ms (wa a)).
    { intros a Ha Hna. subst mH. cbv beta. rewrite wa_unsigned by (clear - Ha; slia0).
      destruct (Z.leb_spec0 (SP - 4096) a) as [L1|L1]; [| reflexivity]. destruct (Z.ltb_spec0 a SP) as [L2|L2]; [exfalso; clear - Hna L1 L2; slia0| reflexivity]. }
    assert (MH1 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + to_Z n) -> m' (wa a) = mH (wa a)).
    { intros a Ha Hna. destruct (Z.leb_spec0 (SP - 4096) a) as [L1|L1]; [destruct (Z.ltb_spec0 a SP) as [L2|L2]|].
      - rewrite MHin by (clear - L1 L2; slia0). reflexivity.
      - rewrite MHout by (first [exact Ha| clear - L2; slia0]). apply Hkeep0; [exact Ha| subst W; cbn [outside]; clear - Hna L2; repeat split; slia0].
      - rewrite MHout by (first [exact Ha| clear - L1; slia0]). apply Hkeep0; [exact Ha| subst W; cbn [outside]; clear - Hna L1; repeat split; slia0]. }
    assert (STKH : stk asegs mH (q_lo Q) SP).
    { apply (stk_merge asegs mH (q_lo Q) (SP - 4096) SP); [| | clear - SPLO; slia0].
      - apply (stk_pres asegs (ms_mem ms)); [exact (proj1 (stk_split asegs _ _ (SP - 4096) _ Hstk_lo ltac:(clear - SPLO; slia0)))|].
        intros a Ha. apply pw_keep'. apply MHout; [clear - Ha SB1 SPB ACEILB; slia0| clear - Ha; slia0].
      - apply (stk_pres asegs m'); [exact (proj2 (stk_split asegs _ _ (SP - 4096) _ Hstk' ltac:(clear - SPLO; slia0)))|].
        intros a Ha. apply pw_keep'. apply MHin. exact Ha. }
    (* [comment removed for export] *)
    set (L14 := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
    set (rho' := rho_ext rho tn L14).
    exists rho'.
    assert (Hag' : agree tn rho rho') by (apply agree_ext; [clear; slia0| clear - Hn2; slia0| exact Xr0]).
    assert (EL14 : forall x (kk : nat), (kk < 14)%nat -> to_Z x = to_Z tn + Z.of_nat kk -> rho' x = nth kk L14 w0).
    { intros x kk Hk Hx. subst rho'. apply (rho_ext_at rho tn L14 x kk); [subst L14; cbn; clear - Hk; slia0| exact Hx]. }
    (* [comment removed for export] *)
    assert (TDG : forall g, In g G -> (g_tag g + 1)%uint63 <> td).
    { intros g Hg E. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & Htg1 & Htg2 & _). pose proof (i63_range (g_tag g)) as Htg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      destruct (Uint63.eqb td 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. rewrite E1 in E. apply (f_equal to_Z) in E. rewrite Etg1 in E. change (to_Z 1%uint63) with 1 in E. clear - E Htg1. slia.
      - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
        + destruct XTsep as (S1 & _). destruct (S1 g g0 Hg Hg0) as [DD|DD].
          * intros Egg. subst g0. rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd. slia.
          * rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd DD. slia.
          * rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd DD. slia.
        + destruct XTsep as (_ & S2 & _). destruct (S2 g f0 Hg Hf0) as [DD|DD]; rewrite <- E in Etd; apply (f_equal to_Z) in Etd; rewrite Etg1 in Etd; clear - Etd DD; slia. }
    assert (TDF : forall f, In f FF -> (f_tag f + 1)%uint63 <> td /\ (f_tag f + 2)%uint63 <> td).
    { intros f Hf. pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & Htg1 & Htg2 & _). pose proof (i63_range (f_tag f)) as Htg.
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Hn59; slia0).
      assert (GEN : forall x, to_Z x = to_Z (f_tag f) + 1 \/ to_Z x = to_Z (f_tag f) + 2 -> x <> td).
      { intros x Hx E. subst x. destruct (Uint63.eqb td 1) eqn:E1.
        - apply Uint63.eqb_spec in E1. rewrite E1 in Hx. change (to_Z 1%uint63) with 1 in Hx. clear - Hx Htg1. slia.
        - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
          + destruct XTsep as (_ & S2 & _). destruct (S2 g0 f Hg0 Hf) as [DD|DD]; rewrite Etd in DD; clear - Hx DD; slia.
          + destruct XTsep as (_ & _ & S3). destruct (S3 f f0 Hf Hf0) as [DD|DD].
            * intros Eff. subst f0. rewrite Etd in Hx. clear - Hx. slia.
            * rewrite Etd in DD. clear - Hx DD. slia.
            * rewrite Etd in DD. clear - Hx DD. slia. }
      split; apply GEN; [left; exact Etg1| right; exact Etg2]. }
    assert (TD2 : td <> 2%uint63 /\ td <> 3%uint63 /\ td <> 0%uint63).
    { destruct (Uint63.eqb td 1) eqn:E1; [apply Uint63.eqb_spec in E1; rewrite E1; repeat split; intros E; discriminate E|].
      apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
      - pose proof (proj1 (Forall_forall _ _) XGin g0 Hg0) as (_ & _ & _ & Htg1 & _). rewrite Etd in Htg1.
        repeat split; intros E; rewrite E in Htg1; [change (to_Z 2%uint63) with 2 in Htg1| change (to_Z 3%uint63) with 3 in Htg1| change (to_Z 0%uint63) with 0 in Htg1]; clear - Htg1; slia.
      - pose proof (proj1 (Forall_forall _ _) XFFin f0 Hf0) as (_ & _ & _ & _ & Htg1 & _). rewrite Etd in Htg1.
        repeat split; intros E; rewrite E in Htg1; [change (to_Z 2%uint63) with 2 in Htg1| change (to_Z 3%uint63) with 3 in Htg1| change (to_Z 0%uint63) with 0 in Htg1]; clear - Htg1; slia. }
    destruct TD2 as (TD2 & TD3 & TD0).
    (* [comment removed for export] *)
    assert (BACK : forall x r, iget x M2 = Some r -> exists r0, iget x (f_mem F) = Some r0 /\ rg_lo r0 = rg_lo r /\ rg_len r0 = rg_len r
                     /\ (x <> td -> x <> 1%uint63 -> r0 = r)).
    { intros x r Hx. destruct (Uint63.eqb x td) eqn:Ex.
      - apply Uint63.eqb_spec in Ex. subst x. rewrite Hrgd' in Hx. injection Hx as <-. exists rgd. split; [exact Hrgd|]. rewrite F1lo, F1len, G1lo, G1len, Hlod.
        split; [reflexivity|]. split; [reflexivity|]. intros NE _. exfalso. exact (NE eq_refl).
      - apply Uint63.eqb_false_spec in Ex. rewrite (Hoth2 x Ex), iget_iset in Hx. destruct (Uint63.eqb x 1) eqn:Ex1.
        + apply Uint63.eqb_spec in Ex1. subst x. injection Hx as <-. exists rg1. split; [exact Hrg1|]. unfold drop_below. cbn [rg_lo rg_len].
          split; [reflexivity|]. split; [reflexivity|]. intros _ NE. exfalso. exact (NE eq_refl).
        + exists r. split; [exact Hx|]. repeat split; reflexivity. }
    assert (KEEPx : forall x, x <> td -> x <> 1%uint63 -> iget x M2 = iget x (f_mem F)).
    { intros x NEx NE1. rewrite (Hoth2 x NEx), iget_iset, (proj2 (Uint63.eqb_false_spec _ _) NE1). reflexivity. }
    (* [comment removed for export] *)
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    assert (HRn' : Rn asegs IM (tn + 14)%uint63 rho' (FS (ret_of l) (iset 10 (FxState.rget F 10) (clobber clob14 tn (f_regs F))) M2 None) ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree tn rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Etn14; clear; slia0]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z tn + 14 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Etn14; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''old : forall x, to_Z x < to_Z tn -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by (clear - Hx; slia0). subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia); exact Xr1).
      assert (Erho''d : rho'' td = wa D) by (rewrite Erho''old by exact Htd_lt; exact ErD).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; rv rho F 10;
                      a1'; a2'; a3'; a4'; a5'; a6'; a7'; rv rho F 18; rv rho F 19; rv rho F 20; rv rho F 21; rv rho F 22; rv rho F 23;
                      rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; t3'; t4'; t5'; t6']).
        apply R_regs_of_match; [exact Hrho''0 | reflexivity |].
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 5) (rv rho F 6) (rv rho F 7) (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     (rv rho F 11) (rv rho F 12) (rv rho F 13) (rv rho F 14) (rv rho F 15) (rv rho F 16) (rv rho F 17) (rv rho F 18) (rv rho F 19) (rv rho F 20)
                     (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) (rv rho F 28) (rv rho F 29) (rv rho F 30) (rv rho F 31))
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; rv rho F 5; rv rho F 6; rv rho F 7; rv rho F 8; rv rho F 9; rv rho F 10;
                      rv rho F 11; rv rho F 12; rv rho F 13; rv rho F 14; rv rho F 15; rv rho F 16; rv rho F 17; rv rho F 18; rv rho F 19; rv rho F 20;
                      rv rho F 21; rv rho F 22; rv rho F 23; rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; rv rho F 28; rv rho F 29; rv rho F 30; rv rho F 31]) in HR''.
        pose proof (regs_match_of_R _ _ _ _ _ _ _ _ _ _ _ HR'') as Hpre.
        assert (Hnd14 : List.NoDup clob14) by (apply nodupb_spec; reflexivity).
        assert (Hcl : forall kr : int, iget kr (clobber clob14 tn (f_regs F)) =
                      match index_of kr clob14 with
                      | Some i => Some (FV (of_Z (to_Z tn + Z.of_nat i)) w_zero)
                      | None => iget kr (f_regs F) end).
        { intros kr. apply iget_clobber; [exact Hnd14 | cbn [length clob14]; clear - Hn59; slia0]. }
        apply regs_match_intro. cbn [seq].
        repeat (apply Forall_cons || apply Forall_nil);
          cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ];
          match goal with |- _ = dv _ (FxState.rget ?FF' ?kr) =>
            let kk := eval vm_compute in kr in change kr with kk; rewrite (rget_regs' FF' kk eq_refl) end;
          cbn [f_regs]; rewrite iget_iset;
          match goal with |- _ = dv _ match (if ?b then _ else _) with _ => _ end => let bb := eval vm_compute in b in change b with bb end;
          cbv iota.
        all: try (rewrite Hcl;
                  match goal with |- _ = dv _ match match ?ix with _ => _ end with _ => _ end =>
                    let ii := eval vm_compute in ix in change ix with ii end; cbv iota).
        all: first
          [ match goal with |- rv _ _ 10 = dv ?rr _ => rewrite (dv_agree tn rho rr _ HagF) by (rewrite Ea0; cbn [vtag]; exact Htd_lt); rewrite Erv; reflexivity end
          | match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); clear - Hn59 Htn; slia0);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Htn; slia0);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Htn; slia0);
              rewrite (EL14 (of_Z (to_Z t1 + Z.of_nat i)) i); [reflexivity | clear; slia0 | rewrite Etag; clear; slia0]
            end
          | match goal with |- rv _ _ ?kz = dv _ match iget ?ki (f_regs ?FF') with _ => _ end =>
              rewrite <- (rget_regs' FF' ki eq_refl);
              let kn := eval vm_compute in (Z.to_nat kz) in
              let HP := fresh "HP" in
              pose proof (Hpre kn ltac:(slia)) as HP; cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in HP; exact HP
            end
          ].
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        cbn [f_mem ms_mem].
        (* [comment removed for export] *)
        assert (PARTS1 : forall t' rg', iget t' (iset 1 (drop_below off rg1) (f_mem F)) = Some rg' -> mem_part asegs IM rho'' mH t' rg').
        { intros t' rg' Ht'. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
          - apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
            apply (stack_part asegs IM rho'' (ms_mem ms) mH rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q));
              [exact Erho''1| exact Hlo1| exact Hd1| exact Hkd1| rewrite Hlen1; reflexivity| rewrite Hlen1; clear - Hoff Hoff2; slia| clear - Hoff16 Hoff; Z.div_mod_to_equations; slia
              | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1)| exact Xstk| clear - Hhl Hlsp ACEILB; slia| rewrite <- Espu; exact STKH|].
            intros a Ha. apply pw_keep. apply MHout; [clear - Ha Espu SPB SPge0; slia0| clear - Ha Espu; slia0].
          - apply Uint63.eqb_false_spec in E1. pose proof (OLDLT _ _ Ht') as Hlt'.
            destruct (t' =? 0)%uint63 eqn:E0.
            + apply Uint63.eqb_spec in E0. subst t'. rewrite Hrg0 in Ht'. injection Ht' as <-.
              apply (mem_part_transfer0 IMX rho'' (ms_mem ms) mH rg0 Hrho''0); [rewrite Hlen0; unfold AIMG_TOP; clear; slia0| | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0)].
              intros a Ha. rewrite Hlo0, Hlen0 in Ha. apply pw_keep. apply MHout; [clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia0| clear - Ha SPB ACEILB; unfold AIMG_LO, AIMG_TOP in Ha; slia0].
            + apply Uint63.eqb_false_spec in E0. destruct (REGLO t' rg' Ht' E1) as [RL1 RL2]. pose proof (proj1 (proj1 Hmem'' t' rg' Ht')) as (_ & _ & RO3 & _).
              rewrite (Erho''old t' Hlt') in RO3.
              apply (mem_part_transfer asegs IM rho'' (ms_mem ms) mH t' rg' (bv_unsigned (rho'' t')));
                [symmetry; apply wa_id| clear; pose proof (bv_unsigned_in_range 64 (rho'' t')); slia0| rewrite (Erho''old t' Hlt'); clear - RO3; slia0| | intros _ _ _; exact E0
                | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Ht')].
              intros a Ha. rewrite (Erho''old t' Hlt') in Ha. apply pw_keep. apply MHout; [clear - Ha RL1 RL2 ACEILB; slia0| clear - Ha RL2 SPB; slia0]. }
        (* [comment removed for export] *)
        assert (HinvH : mem_inv asegs mH).
        { intros a bb Ha. subst mH. cbv beta in Ha. destruct ((SP - 4096 <=? bv_unsigned a) && (bv_unsigned a <? SP))%Z; [exact (Hinv' _ _ Ha)| exact (Xinv _ _ Ha)]. }
        assert (SRCH : forall (i : nat) (so : int), (i < nN)%nat -> to_Z so = (to_Z os + Z.of_nat i) mod wB ->
                  rview asegs mH (adr rho'' ts (to_Z so)) = Some (nth i src (b8 0))).
        { intros i so Hi Hso. rewrite (EadrX rho'' Hrho''0 Erho''old i so Hi Hso). unfold rview. rewrite MHout; [| clear - Hi HsA0 HsAhi EnN ACEILB; unfold AAPP_HI in HsAhi; slia0| clear - Hi LODs SPLO EnN; slia0].
          fold (rview asegs (ms_mem ms) (wa (sA + Z.of_nat i))). rewrite <- (EadrX rho Xr0 ltac:(intros; reflexivity) i so Hi Hso). exact (Hsrc i so Hi Hso). }
        destruct (copy_bytes_sound asegs IM rho'' Hrho''0 nN _ td od ts os M2 rgd1 mH (b8 0) HM2 Hrgd1 (PARTS1 td rgd1 Hrgd1) Htd0 G1unk G1inb
                    ltac:(rewrite G1len, EnN; exact RNG) HinvH)
          as (rgd'' & src2 & Hrgd'' & _ & Hsl2 & Hsrc2 & PARTF & _).
        { intros i so Hi Hso _. eexists. exact (SRCH i so Hi Hso). }
        { exact (HDJX rho'' Hrho''0 Erho''old). }
        { exact (HSVgen rho'' mH Hrho''0 Erho''old PARTS1). }
        assert (Ergd'' : rgd'' = rgd') by (clear - Hrgd' Hrgd''; congruence). subst rgd''.
        assert (SRCEQ : forall i : nat, (i < nN)%nat -> nth i src2 (b8 0) = nth i src (b8 0)).
        { intros i Hi. pose proof (Hsrc2 i (os + Uint63.of_Z (Z.of_nat i))%uint63 Hi ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) as S2.
          rewrite (SRCH i (os + Uint63.of_Z (Z.of_nat i))%uint63 Hi ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) in S2. injection S2 as S2'. symmetry. exact S2'. }
        rewrite (adr_eq_wa rho'' td D (to_Z od) Erho''d HD0) in PARTF by (first [clear - Ho; slia0| clear - Ho HDhi RNG Hn; unfold AAPP_HI in HDhi; slia0]).
        assert (MH2 : forall w : word, m' w = write_to_mem mH (wa d) src2 w).
        { intros w. pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
          rewrite write_to_mem_spec by (rewrite ?Hsl2, ?EnN; clear - HD0 Ho HDhi RNG Hn; subst d; unfold AAPP_HI in HDhi; slia0).
          rewrite Hsl2, EnN. rewrite <- (wa_id w). rewrite wa_unsigned by (clear - Hw; slia0).
          destruct (Z.leb_spec0 d (bv_unsigned w)) as [L1|L1]; [destruct (Z.ltb_spec0 (bv_unsigned w) (d + to_Z n)) as [L2|L2]|]; cbn [andb].
          - rewrite (DST (bv_unsigned w)) by (clear - L1 L2; slia0). symmetry. rewrite <- SRCEQ by (clear - L1 L2 EnN; slia0). apply nth_error_nth'. rewrite Hsl2. clear - L1 L2 EnN; slia0.
          - apply MH1; [clear - Hw; slia0| clear - L2; slia0].
          - apply MH1; [clear - Hw; slia0| clear - L1; slia0]. }
        apply mem_ok_parts.
        + intros t' rg' Ht'. destruct (t' =? td)%uint63 eqn:Etd'.
          * apply Uint63.eqb_spec in Etd'. subst t'. rewrite Hrgd' in Ht'. injection Ht' as <-.
            apply (mem_part_transfer asegs IM rho'' (write_to_mem mH (wa d) src2) m' td rgd' D Erho''d HD0);
              [rewrite F1len, G1len; clear - HDhi; unfold AAPP_HI in HDhi; slia0| intros a Ha; apply pw_keep; apply MH2| intros _ _ _; exact Htd0| exact PARTF].
          * apply Uint63.eqb_false_spec in Etd'. pose proof Ht' as Ht2. rewrite (Hoth2 t' Etd') in Ht'. pose proof (PARTS1 t' rg' Ht') as P1.
            pose proof (proj1 P1) as (_ & _ & RO3 & RO4 & _).
            assert (FP : forall a, bv_unsigned (rho'' t') + to_Z (rg_lo rg') <= a < bv_unsigned (rho'' t') + to_Z (rg_len rg') -> ~ (d <= a < d + to_Z n)).
            { intros a Ha Hin. destruct (BACK t' rg' Ht2) as (r0 & Hr0 & Lo0 & Le0 & _). rewrite <- Lo0, <- Le0 in Ha.
              destruct (proj2 Hmem'' t' td r0 rgd Etd' Hr0 Hrgd) as [SEP|SEP]; rewrite Erho''d, ?Hlod in SEP;
                rewrite (wa_unsigned D) in SEP by (clear - HD0 HDhi Hld; unfold AAPP_HI in HDhi; slia0); [change (to_Z 0%uint63) with 0 in SEP|];
                clear - SEP Ha Hin RNG Ho; subst d; slia0. }
            destruct (t' =? 0)%uint63 eqn:E0.
            -- apply Uint63.eqb_spec in E0. subst t'. rewrite iget_iset in Ht'. change ((0 =? 1)%uint63) with false in Ht'. cbv iota in Ht'. rewrite Hrg0 in Ht'. injection Ht' as <-.
               apply (mem_part_transfer0 IMX rho'' mH m' rg0 Hrho''0); [rewrite Hlen0; unfold AIMG_TOP; clear; slia0| | exact P1].
               intros a Ha. apply pw_keep. apply MH1; [rewrite Hlo0, Hlen0 in Ha; clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia0|].
               apply FP. rewrite Hrho''0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. clear - Ha. slia0.
            -- apply Uint63.eqb_false_spec in E0.
               apply (mem_part_transfer asegs IM rho'' mH m' t' rg' (bv_unsigned (rho'' t')));
                 [symmetry; apply wa_id| clear; pose proof (bv_unsigned_in_range 64 (rho'' t')); slia0| clear - RO3; slia0| | intros _ _ _; exact E0| exact P1].
               intros a Ha. apply pw_keep. apply MH1; [pose proof (RO4 E0) as RO4'; clear - Ha RO3 RO4'; slia0| exact (FP a Ha)].
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2.
          destruct (BACK t1 r1 Hi1) as (q1 & Hq1 & Lo1 & Le1 & _). destruct (BACK t2 r2 Hi2) as (q2 & Hq2 & Lo2 & Le2 & _).
          rewrite <- Lo1, <- Le1, <- Lo2, <- Le2. exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
    (* [comment removed for export] *)
    assert (CW : Forall (aclient_write_ok H LB) W).
    { subst W. apply Forall_cons; [exact CWD|]. apply Forall_cons; [left; cbn [fst snd]; clear - SPB; slia| apply Forall_nil]. }
    assert (SW : Forall stack0_ok W).
    { subst W. apply Forall_cons; [exact S0D|]. apply Forall_cons; [apply stack0_ok_app; clear - SPB ACEILB; unfold AHI_LO; slia| apply Forall_nil]. }
    assert (AFW : Forall (afs_write_ok H (LF_of Q FF)) W).
    { subst W. apply Forall_cons; [exact AFD|]. apply Forall_cons; [| apply Forall_nil].
      left. cbn [fst snd]. clear - F1 F2 SPB ACEILB. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. split; slia. }
    (* [comment removed for export] *)
    assert (GDJ : forall g, In g G -> disjoint_from W (sh (g_addr g)) (nsh (to_Z (g_size g)))).
    { intros g Hg. pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (i63_range (g_size g)) as Hgs0.
      pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 ltac:(clear - Hgs0; slia0)) as (U1 & U2 & U3).
      assert (SHA : sh aceil < aceil) by (clear - ACEILB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; slia).
      subst W. cbn [disjoint_from]. split; [| split; [clear - U2 U3 SHA SPB; slia| exact I]].
      destruct (Uint63.eqb td 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. destruct (STK E1) as (_ & SPd & _). left. clear - U2 SHA SPB SPd. slia.
      - apply Uint63.eqb_false_spec in E1. destruct (OBJF E1) as (_ & APD & _).
        destruct (app_vs_shX D (to_Z (rg_len rgd)) (g_addr g) (to_Z (g_size g)) APD ltac:(clear - Hld; slia0) G7 ltac:(clear - Hgs0; slia0)) as [DD|DD];
          [right; clear - DD RNG Ho; subst d; slia| left; clear - DD Ho; subst d; slia]. }
    destruct Xnamed as [XG0in XLB0nd].
    exists s, LB, G, FF, XS, ms1.
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mk f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS ms1].
    - exact Evis'.
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr2 | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr3 | change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia].
    - eapply agree_trans; [exact Xag | exact Hag' | clear - Xn0a Xn0b; slia].
    - rewrite Etn14. clear - Xn0a Xn0b Hn59. slia.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmp').
    - eapply (ah_RHEAP_frame H HH); [exact Xheap| exact MU| exact WM| exact CW].
    - eapply (ah_RFS_frame H HH); [exact Xrfs| exact MU| exact WM| exact AFW].
    - exact Hac'.
    - eapply stack0_transport; [exact Xst0| exact MU| exact WM| exact SW].
    - eapply (chain_via_munch H HH); [exact Xch| exact MU|]. intros fp' ra' Hin. specialize (XCH0 fp' ra' Hin).
      subst W. cbn [disjoint_from]. clear - XCH0 SP0D SPB. repeat split; slia.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - exact XAL.
    - exact XAL0.
    - exact XG.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
      pose proof (i63_range (g_tag g)) as Htg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (NG1 : g_tag g <> 1%uint63) by (intros E; rewrite E in Htg1; change (to_Z 1%uint63) with 1 in Htg1; clear - Htg1; slia).
      assert (NS1 : (g_tag g + 1)%uint63 <> 1%uint63) by (intros E; apply (f_equal to_Z) in E; rewrite Etg1 in E; change (to_Z 1%uint63) with 1 in E; clear - E Htg1; slia).
      split; [exact Hin|]. split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
      split; [rewrite Etn14; clear - Htg2; slia|]. split.
      + destruct (Uint63.eqb (g_tag g) td) eqn:Egt.
        * apply Uint63.eqb_spec in Egt. exists rgd'. rewrite Egt, Hrgd'. split; [reflexivity|]. rewrite Egt in Hgg. assert (rgg = rgd) by (clear - Hgg Hrgd; congruence). subst rgg.
          rewrite F1lo, F1len, F1al, F1kd, F1df, G1lo, G1len, G1al, G1kd, G1df. repeat split; assumption || reflexivity.
        * apply Uint63.eqb_false_spec in Egt. exists rgg. rewrite (KEEPx _ Egt NG1). split; [exact Hgg|]. repeat split; assumption.
      + intros rg' Hrg'. rewrite (KEEPx _ (TDG g Hg) NS1) in Hrg'.
        destruct (Hshg rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hrs|].
        eapply addressable_transport; [exact Had'| exact MU| exact WM| exact (GDJ g Hg)].
    - exact XGnd.
    - exact XGtnd.
    - exact XGnew.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
      apply (stk_keep (ms_mem ms) m'); [exact Hs| exact WM|]. intros a Ha.
      destruct (Z.leb_spec0 d a) as [L1|L1]; [destruct (Z.ltb_spec0 a (d + to_Z n)) as [L2|L2]|].
      + right. eexists. rewrite (mrd_overlay_high m' a) by (clear - Ha G4 G5 ACEILB; slia). apply DST. clear - L1 L2. slia0.
      + left. apply Hkeep0; [clear - Ha G4 G5 ACEILB; unfold AIMG_TOP in G4; slia|]. subst W. cbn [outside]. clear - L2 Ha G5 SPB. repeat split; slia.
      + left. apply Hkeep0; [clear - Ha G4 G5 ACEILB; unfold AIMG_TOP in G4; slia|]. subst W. cbn [outside]. clear - L1 Ha G5 SPB. repeat split; slia.
    - exact XFF.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)) as Htg.
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Hn59; slia0).
      assert (NF1 : f_tag f <> 1%uint63) by (intros E; rewrite E in Htg1; change (to_Z 1%uint63) with 1 in Htg1; clear - Htg1; slia).
      assert (NS1 : (f_tag f + 1)%uint63 <> 1%uint63) by (intros E; apply (f_equal to_Z) in E; rewrite Etg1 in E; change (to_Z 1%uint63) with 1 in E; clear - E Htg1; slia).
      assert (NL1 : (f_tag f + 2)%uint63 <> 1%uint63) by (intros E; apply (f_equal to_Z) in E; rewrite Etg2 in E; change (to_Z 1%uint63) with 1 in E; clear - E Htg1; slia).
      destruct (TDF f Hf) as [TDs TDl].
      split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hf1|].
      split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; clear - Htg2; slia); exact Hf2|]. split; [exact Hkf|]. split; [exact Htg1|]. split; [rewrite Etn14; clear - Htg2; slia|].
      split.
      { destruct (Uint63.eqb (f_tag f) td) eqn:Eft.
        - apply Uint63.eqb_spec in Eft. exists rgd'. rewrite Eft, Hrgd'. split; [reflexivity|]. rewrite Eft in Hgf. assert (rgf = rgd) by (clear - Hgf Hrgd; congruence). subst rgf.
          rewrite F1lo, F1len, F1al, F1kd, F1df, G1lo, G1len, G1al, G1kd, G1df. repeat split; assumption || reflexivity.
        - apply Uint63.eqb_false_spec in Eft. exists rgf. rewrite (KEEPx _ Eft NF1). split; [exact Hgf|]. repeat split; assumption. }
      split; [exists rgs; rewrite (KEEPx _ TDs NS1); split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite (KEEPx _ TDl NL1); exact Hflg|].
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. exact X4.
    - exact XFFnd.
    - exact XFFtnd.
    - exact XTsep.
    - exact XFFlen.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. destruct (BACK t' rg' Ht') as (r0 & Hr0 & _). exact (Xdom t' r0 Hr0).
    - (* [comment removed for export] *) exists rg0. rewrite (KEEPx _ ltac:(intros E; exact (TD0 (eq_sym E))) ltac:(intros E; discriminate E)). split; [exact Hrg0|]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0| exact Hpg0].
    - (* [comment removed for export] *) destruct (Uint63.eqb td 1) eqn:E1.
      + apply Uint63.eqb_spec in E1. exists rgd'. rewrite <- E1, Hrgd'. split; [reflexivity|]. assert (Ergd : rgd = rg1) by (rewrite E1 in Hrgd; clear - Hrgd Hrg1; congruence).
        rewrite F1lo, F1len, F1al, F1kd, F1df, G1lo, G1len, G1al, G1kd, G1df, Ergd. repeat split; assumption || reflexivity.
      + apply Uint63.eqb_false_spec in E1. exists (drop_below off rg1). rewrite (Hoth2 1%uint63 ltac:(intros E; exact (E1 (eq_sym E)))), iget_iset, Uint63.eqb_refl.
        split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite (KEEPx _ ltac:(intros E; exact (TD2 (eq_sym E))) ltac:(intros E; discriminate E)). exact Xreg2.
    - (* [comment removed for export] *) rewrite (KEEPx _ ltac:(intros E; exact (TD3 (eq_sym E))) ltac:(intros E; discriminate E)). exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc). exists rg0_. rewrite (KEEPx _ ltac:(intros E; exact (TD0 (eq_sym E))) ltac:(intros E; discriminate E)). split; [exact Hrg0_| exact Hroc].
    - (* [comment removed for export] *) intros t' rg' pn p' ci cc Ht' Hp' Hc'.
      destruct (Uint63.eqb t' td) eqn:Etd'.
      + apply Uint63.eqb_spec in Etd'. subst t'. rewrite Hrgd' in Ht'. injection Ht' as <-. exact (INB' pn p' ci cc Hp' Hc').
      + apply Uint63.eqb_false_spec in Etd'. rewrite (Hoth2 t' Etd'), iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
        * injection Ht' as <-. exact (INB1 pn p' ci cc Hp' Hc').
        * exact (Xinb t' rg' pn p' ci cc Ht' Hp' Hc').
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0.
      destruct (Uint63.eqb t' td) eqn:Etd'.
      + apply Uint63.eqb_spec in Etd'. subst t'. rewrite Hrgd' in Ht'. injection Ht' as <-. destruct UNK' as (_ & Hdu & Hku). split; [left; exact Hdu| exact Hku].
      + apply Uint63.eqb_false_spec in Etd'. rewrite (Hoth2 t' Etd'), iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
        * injection Ht' as <-. destruct UNK1 as (_ & Hdu & Hku). split; [left; exact Hdu| exact Hku].
        * exact (Xkinds t' rg' Ht' Ht'0).
    - exact Xcost.
    - exact Xcnt.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) SP (q_sp0 Q)); [exact Hstk' | | clear - SPLO SPB; slia].
      apply (stk_keep (ms_mem ms) m'); [split; [exact SPge0| split; [exact SP064| exact STKHI]]| exact WM|]. intros a Ha.
      destruct (Z.leb_spec0 d a) as [L1|L1]; [destruct (Z.ltb_spec0 a (d + to_Z n)) as [L2|L2]|].
      + right. eexists. rewrite (mrd_overlay_high m' a) by (clear - Ha SPB ACEILB; unfold AIMG_TOP; slia). apply DST. clear - L1 L2. slia0.
      + left. apply Hkeep0; [clear - Ha SPB ACEILB; slia|]. subst W. cbn [outside]. clear - L2 Ha. repeat split; slia.
      + left. apply Hkeep0; [clear - Ha SPB ACEILB; slia|]. subst W. cbn [outside]. clear - L1 Ha. repeat split; slia.
    - repeat split; assumption.
    - eapply (ah_rauxv_frame H HH); [exact Xaux| exact MU| exact WM| exact CW].
    - exact Hinv'.
    - apply (stk_pres asegs (ms_mem ms)); [exact Xerr|]. intros a Ha. apply Hkeep0; [clear - Ha Eerr H0 H1; unfold errA, AERRNO, ATP in *; slia|].
      subst W. cbn [outside]. clear - Ha Eerr H0 H1 HDtop Ho SPB ACEILB. subst d. unfold errA, AERRNO, ATP, AIMG_TOP in *. repeat split; slia.
    - exact (HSH0 _ Hac' Hinv').
    - exact XLB0.
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - exact XLBsub.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      pose proof (EXD a Hcl Hna Hnxs) as NA.
      assert (LOW : SP <= a \/ a < aceil).
      { unfold client0, aclient_addr in Hcl. destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        - left. clear - Hs SPB. slia.
        - right. clear - Hst ACEILB. unfold aimg_client, AIMG_LO, AIMG_TOP in *. slia.
        - right. destruct (XLB0h b Hb) as [_ Bh]. clear - Hr Bh. slia.
        - right. destruct (XLB0h b Hb) as [B0 Bh]. pose proof (sh_nsh_high (blk_addr b) (blk_size b) B0 ltac:(clear - Hr; unfold nsh in Hr; Z.div_mod_to_equations; slia) ltac:(clear - Bh ACEILB; unfold AAPP_HI; slia)) as SB.
          clear - Hr SB ACEILB. unfold AHI_LO in *. slia.
        - right. clear - Hfs F2. slia.
        - right. pose proof (sh_below_app (as_FSB H + AFS_SIZE) ltac:(clear - F1 F2 ACEILB; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; slia)) as SB.
          pose proof (sh_mono a). clear - Hfss SB ACEILB. unfold AHI_LO, sh in *. rewrite ?ASHADOW_BASE_val in *. Z.div_mod_to_equations. slia.
        - right. clear - Hss ACEILB. unfold AHI_LO in *. slia. }
      apply Hkeep0; [exact Ha|]. subst W. cbn [outside]. clear - NA LOW SPB. repeat split; slia.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) XFFstk f Hf) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(KF1 & KF2 & KF3 & KF4 & KF5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - KF1; slia0)) as FPf.
      apply (stk_keep (ms_mem ms) m'); [exact HsF| exact WM|]. intros a Ha.
      destruct (Z.leb_spec0 d a) as [L1|L1]; [destruct (Z.ltb_spec0 a (d + to_Z n)) as [L2|L2]|].
      + right. eexists. rewrite (mrd_overlay_high m' a) by (clear - Ha KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia). apply DST. clear - L1 L2. slia0.
      + left. apply Hkeep0; [clear - Ha KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia|]. subst W. cbn [outside]. clear - L2 Ha KF3 F2 SPB. repeat split; slia.
      + left. apply Hkeep0; [clear - Ha KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia|]. subst W. cbn [outside]. clear - L1 Ha KF3 F2 SPB. repeat split; slia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma scan_strlen_inv : forall IMz (fuel : nat) M t o acc len,
    scan_strlen IMz fuel M t o acc = Some len -> to_Z acc + Z.of_nat fuel < wB ->
    exists k : nat, (k < fuel)%nat /\ to_Z len = to_Z acc + Z.of_nat k
      /\ (forall (i : nat) (oi : int), (i < k)%nat -> to_Z oi = (to_Z o + Z.of_nat i) mod wB -> exists b, byte_at IMz M t oi = SK b /\ to_Z (b land 255)%uint63 <> 0)
      /\ (forall oi : int, to_Z oi = (to_Z o + Z.of_nat k) mod wB -> exists b, byte_at IMz M t oi = SK b /\ to_Z (b land 255)%uint63 = 0).
  Proof.
    intros IMz fuel. induction fuel as [|fuel IH]; intros M t o acc len Hs Hacc; [discriminate Hs|].
    cbn [scan_strlen] in Hs. pose proof (i63_range o) as Ho. pose proof (i63_range acc) as Hac.
    assert (Eo0 : forall oi, to_Z oi = (to_Z o + Z.of_nat 0) mod wB -> oi = o).
    { intros oi Hoi. apply to_Z_inj. rewrite Hoi, Z.add_0_r. apply Z.mod_small. change wB with (2 ^ 63). exact Ho. }
    destruct (byte_at IMz M t o) as [b| |] eqn:Hb; [| discriminate Hs| discriminate Hs].
    destruct ((b land 255) =? 0)%uint63 eqn:Ez.
    - injection Hs as <-. apply Uint63.eqb_spec in Ez. exists 0%nat. split; [clear; slia0|]. split; [clear; slia0|].
      split; [intros i oi Hi; exfalso; clear - Hi; slia0|]. intros oi Hoi. rewrite (Eo0 oi Hoi). exists b. split; [exact Hb| rewrite Ez; reflexivity].
    - apply Uint63.eqb_false_spec in Ez.
      assert (Eacc1 : to_Z (acc + 1)%uint63 = to_Z acc + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; [reflexivity| change wB with (2 ^ 63) in Hacc; slia0]).
      destruct (IH M t (o + 1)%uint63 (acc + 1)%uint63 len Hs ltac:(rewrite Eacc1; clear - Hacc; slia0)) as (k & Hk & Elen & STR & NUL).
      assert (Esuc : forall i : nat, (to_Z (o + 1)%uint63 + Z.of_nat i) mod wB = (to_Z o + Z.of_nat (S i)) mod wB).
      { intros i. rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. rewrite Nat2Z.inj_succ, Zplus_mod_idemp_l. f_equal. clear; slia0. }
      exists (S k). split; [clear - Hk; slia0|]. split; [rewrite Elen, Eacc1, Nat2Z.inj_succ; clear; slia0|]. split.
      + intros i oi Hi Hoi. destruct i as [|i].
        * rewrite (Eo0 oi Hoi). exists b. split; [exact Hb|]. intros E. apply Ez. apply to_Z_inj. rewrite E. reflexivity.
        * apply (STR i oi ltac:(clear - Hi; slia0)). rewrite Esuc. exact Hoi.
      + intros oi Hoi. apply NUL. rewrite Esuc. exact Hoi.
  Qed.

  (* [comment removed for export] *)
  Definition rd_list (m : AsShadow.mem) (a : Z) (k : nat) : list byte :=
    map (fun i : nat => match mrd asegs m (wa (a + Z.of_nat i)) with Some b => b | None => b8 0 end) (seq 0 k).
  Lemma rd_list_length : forall m a k, length (rd_list m a k) = k.
  Proof. intros. unfold rd_list. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma rd_list_nth : forall m a k i, (i < k)%nat -> nth_error (rd_list m a k) i = Some match mrd asegs m (wa (a + Z.of_nat i)) with Some b => b | None => b8 0 end.
  Proof. intros m a k i Hi. unfold rd_list. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i k); [reflexivity| exfalso; slia0]. Qed.
  Lemma map_seq_shift : forall {T} (f : nat -> T) k2 k1 st, map f (seq (k1 + st) k2) = map (fun i => f (k1 + i)%nat) (seq st k2).
  Proof.
    intros T f k2. induction k2 as [|k2 IH]; intros k1 st; [reflexivity|]. cbn [seq map]. f_equal. rewrite <- Nat.add_succ_r. apply IH.
  Qed.
  Lemma rd_list_app : forall m a k1 k2, rd_list m a (k1 + k2) = rd_list m a k1 ++ rd_list m (a + Z.of_nat k1) k2.
  Proof.
    intros m a k1 k2. unfold rd_list. rewrite seq_app, map_app. f_equal. cbn [Nat.add].
    rewrite <- (Nat.add_0_r k1) at 1. rewrite map_seq_shift. apply map_ext. intros i.
    replace (a + Z.of_nat (k1 + i)) with (a + Z.of_nat k1 + Z.of_nat i) by slia0. reflexivity.
  Qed.
  Lemma rd_list_bytes_at : forall m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
    (forall i : nat, (i < k)%nat -> exists b, mrd asegs m (wa (a + Z.of_nat i)) = Some b) -> bytes_at asegs m a (rd_list m a k).
  Proof.
    intros m a k Ha Hk RD. split; [exact Ha|]. rewrite rd_list_length. split; [exact Hk|].
    intros i Hi. rewrite rd_list_nth by exact Hi. destruct (RD i Hi) as [b Hb]. rewrite Hb. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma img_cell_readable : forall (m : AsShadow.mem) a8 v, mem_inv asegs m -> image_cell IM a8 = Some v -> to_Z a8 mod 8 = 0 ->
    forall j : nat, (j < 8)%nat -> exists b, mrd asegs m (wa (to_Z a8 + Z.of_nat j)) = Some b.
  Proof.
    intros m a8 v Hinv Hc Hal j Hj. pose proof (im_ro_ok asegs IMX HIMX : image_ok asegs IM) as HIM.
    destruct (image_cell_tag _ _ _ Hc) as [w ->]. pose proof (image_cell_sound asegs IM a8 w HIM Hal Hc j Hj) as Hrd.
    pose proof Hc as Hc'. unfold image_cell in Hc'. destruct (find_seg IM a8) as [sg|] eqn:Hf; [| discriminate Hc']. clear Hc'.
    destruct (find_seg_spec _ _ _ Hf) as (Hin & Hb1 & Hb2). apply Uint63.leb_spec in Hb1. apply Uint63.ltb_spec in Hb2.
    pose proof (proj1 (Forall_forall _ _) HIM sg Hin) as (seg & Hseg & Eb & Es & _ & _ & Ewr & Mb & Ms & Hle & Hfind).
    pose proof (i63_range (sg_base sg)) as Rb. pose proof (i63_range (sg_size sg)) as Rs. pose proof (i63_range a8) as Ra.
    rewrite Uint63.add_spec in Hb2. change wB with (2 ^ 63) in Hb2. rewrite Z.mod_small in Hb2 by (clear - Rb Rs Hle; slia0).
    assert (Hin8 : to_Z (sg_base sg) <= to_Z a8 + Z.of_nat j < to_Z (sg_base sg) + to_Z (sg_size sg)) by (clear - Hb1 Hb2 Hal Mb Ms Hj; Z.div_mod_to_equations; slia0).
    unfold mrd. unfold wa. destruct (m (Z_to_bv 64 (to_Z a8 + Z.of_nat j))) as [b|] eqn:Em; [exists b; reflexivity|].
    unfold seg_rom. rewrite Hrd. destruct (nth_error (Z_to_le_bytes 8 (wZ w)) j) as [b|] eqn:En; [exists b; reflexivity|].
    exfalso. apply nth_error_None in En. rewrite length_Z_to_le_bytes in En. clear - En Hj. slia0.
  Qed.

  Theorem anode_strlen_sound : anode_strlen_sig H IMX A.
  Proof.
    unfold anode_strlen_sig, anode_concl.
    intros Q st st' rho msF mo Hnode Hpc Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_strlen in Hnode.
    destruct (call_okn K (ka_istack A) st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (src_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) 1) as [[ts os]|] eqn:Hsa; [|discriminate].
    destruct (scan_strlen IM 4096 (f_mem (a_F st)) ts os 0) as [len|] eqn:Hscan; [|discriminate].
    destruct (src_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) (strlen_span os len)) as [[ts2 os2]|] eqn:Hsa2; [|discriminate].
    destruct (range_okb IM A st true ts os (len + 1)) eqn:Hro; [|discriminate].
    destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
    injection Hnode as <-.
    destruct (call_okn_inv A _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv A _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv.
    unfold range_okb in Hro. apply andb_true_iff in Hro as [Hlocs Haccs].
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    (* [comment removed for export] *)
    destruct (scan_strlen_inv IM 4096 _ ts os 0%uint63 len Hscan ltac:(change wB with (2 ^ 63); change (to_Z 0%uint63) with 0; clear; slia0)) as (k & Hk4096 & Elen & STR & NUL).
    change (to_Z 0%uint63) with 0 in Elen. rewrite Z.add_0_l in Elen.
    pose proof (i63_range len) as Hlen. pose proof (i63_range os) as Hos0. pose proof (i63_range ts) as Hts.
    set (n := (len + 1)%uint63) in *.
    assert (En : to_Z n = to_Z len + 1) by (subst n; rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; [reflexivity| clear - Elen Hk4096; slia0]).
    pose proof (i63_range n) as Hn. assert (Hn64k : to_Z n <= 65536) by (rewrite En, Elen; clear - Hk4096; slia0).
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (tn := a_n st) in *.
    pose proof (i63_range tn) as Htn. change (to_Z two59) with (2 ^ 59) in Hn59. destruct Xn0 as [Xn0a Xn0b].
    assert (Etn14 : to_Z (tn + 14)%uint63 = to_Z tn + 14) by (rewrite to_Z_add_small; change (to_Z 14%uint63) with 14; clear - Htn Hn59; slia0).
    assert (Hag : agree tn rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR. pose proof (R_mem _ _ _ _ _ HR) as Hmem. cbn [f_mem] in Hmem. fold F in Hmem.
    pose proof (canonR_R asegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    assert (Epc : to_Z (f_pc F) = ASTRLEN_STUB).
    { destruct (HK_parts A HK) as (_ & _ & Hpcs & _). unfold K_pcs_ok in Hpcs. rewrite !andb_true_iff in Hpcs. destruct Hpcs as [[[[[[[[[[_ _] _] _] _] _] Hsl] _] _] _] _].
      apply Z.eqb_eq in Hsl. rewrite <- Hsl. fold F in Hpc. rewrite Hpc. reflexivity. }
    rewrite Epc in Ems.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); clear - Hhl Hlsp HspB HB64 Hcs Hoff Hoff2 ACEILB; slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 ATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    set (SP := bv_unsigned (rv rho F 2)) in *.
    destruct (stk_split asegs _ (q_lo Q) SP (q_sp0 Q) Xstk ltac:(clear - Espu Hhl Hlsp Hoff Hoff2; slia)) as [Hstk_lo Hstk_hi].
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0.
    destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. assert (Erg1 : rg1_ = rg1) by (clear - Hrg1 Hrg1_; congruence). subst rg1_.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
    assert (OLDLT : forall x rg, iget x (f_mem F) = Some rg -> to_Z x < to_Z tn).
    { intros x rg Hx. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]];
        [change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia| change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia
        | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia| change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia| ..].
      - apply in_map_iff in Hb as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). pose proof (i63_range (g_tag g)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hf as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 2%uint63) with 2; clear - Htg2 H0 Hn59; slia0). change (to_Z 2%uint63) with 2. clear - Htg2. slia. }
    assert (SR : sh aceil <= sh (q_sp0 Q - to_Z (c_stack K)) /\ sh (q_sp0 Q - to_Z (c_stack K)) + nsh (to_Z (c_stack K)) <= sh (q_sp0 Q)
                 /\ sh (q_sp0 Q) <= AHI_LO /\ AIMG_TOP <= sh (q_sp0 Q - to_Z (c_stack K))).
    { split; [apply sh_mono; clear - Hlsp Hhl; slia|]. split; [| split].
      - clear - Hsp32 Hcs Est16. unfold nsh, sh. Z.div_mod_to_equations. slia.
      - clear - SB2 Hshi. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
      - apply sh_above_image. clear - Hlsp Hhl ACEILB. slia. }
    assert (KSH : to_Z (ka_sh0lo A) = sh AIMG_LO /\ to_Z (ka_sh0len A) = sh AIMG_TOP).
    { destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
      apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. split; [exact Hslo| exact Hslen]. }
    assert (REGLO : forall x rg, iget x (f_mem F) = Some rg -> x <> 1%uint63 ->
              0 <= bv_unsigned (rho x) + to_Z (rg_lo rg) /\ bv_unsigned (rho x) + to_Z (rg_len rg) <= aceil).
    { intros x rg Hx Hne1. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]].
      - rewrite Hrg0 in Hx. injection Hx as <-. rewrite Xr0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0. clear - ACEILB. unfold AIMG_LO, AIMG_TOP. slia.
      - exfalso. exact (Hne1 eq_refl).
      - rewrite Xreg2 in Hx. injection Hx as <-. rewrite Xr2. unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (c_stack K)) by (clear - Hcs Est40; slia).
        change (to_Z 0%uint63) with 0. fold (nsh (to_Z (c_stack K))).
        rewrite wa_unsigned by (clear - SR Hcs; unfold AIMG_TOP, AHI_LO, nsh in SR; Z.div_mod_to_equations; slia). clear - SR ACEILB. unfold AHI_LO, AIMG_TOP in *. slia.
      - rewrite Xreg3 in Hx. injection Hx as <-. rewrite Xr3, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold abs_region. cbn [rg_lo rg_len].
        destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
        apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. rewrite Hslo, Hslen. clear - ACEILB. unfold sh, AIMG_LO, AIMG_TOP. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
      - apply in_map_iff in Hb as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
        rewrite Hgg in Hx. injection Hx as <-. rewrite Hlog, Hleng, Hrg. change (to_Z 0%uint63) with 0.
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
        rewrite wa_unsigned by (clear - G1 G3 G5 ACEILB; slia). clear - G1 G5. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hshg). destruct (Hshg rg Hx) as (-> & Hrs & _).
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 ACEILB; slia). change (to_Z 0%uint63) with 0. fold (nsh (to_Z (g_size g))).
        rewrite Hrs. pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 G3) as (U1 & U2 & U3). pose proof (sh_above_image (g_addr g) ltac:(clear - G1; slia)) as SAg.
        rewrite wa_unsigned by (clear - U2 U3 SAg G1 Hsz; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        clear - U2 U3 SAg Hsz ACEILB. unfold AIMG_TOP, AHI_LO, nsh in *. Z.div_mod_to_equations. slia.
      - apply in_map_iff in Hf as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
        rewrite Hgf in Hx. injection Hx as <-. rewrite Hlof, Hlenf, Hf0, (fsz_eq _ Hkf). change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
        rewrite wa_unsigned by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE in *; slia). clear - K2' K3 F1 F2 FPf. unfold AIMG_TOP, AFS_HDR in *. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
        rewrite Hgs in Hx. injection Hx as <-. rewrite Hlos, Hlens, Hf1. change (to_Z 0%uint63) with 0.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as FPf.
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(clear - Hkf; slia)) as [E1 E2].
        assert (B : AIMG_TOP <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) <= AAPP_HI) by (clear - K2' K3 F1 F2 ACEILB FPf; unfold AIMG_TOP, AFS_HDR, AFS_SIZE, AAPP_HI in *; slia).
        pose proof (sh_above_image (f_ff f) ltac:(unfold AIMG_TOP in B; clear - B; slia)) as SA1.
        pose proof (sh_nsh_high (f_ff f) (AsIface.fsz (to_Z (f_k f))) ltac:(unfold AIMG_TOP in B; clear - B; slia) ltac:(clear - FPf; slia) (proj2 B)) as SA2.
        rewrite wa_unsigned by (clear - B SA1 SA2 FPf E1; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
        rewrite E1. clear - SA1 SA2 ACEILB. unfold AIMG_TOP, AHI_LO in *. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & _ & _ & Hflg & _).
        rewrite Hflg in Hx. injection Hx as <-. unfold flag_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1. rewrite Hf2.
        destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2' & K3 & K4 & K5) _].
        rewrite wa_unsigned by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia). clear - K5 F1 F2. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *. slia. }
    assert (Hos62 : to_Z os + 4200 < 2 ^ 63).
    { destruct (src_arg_inv _ _ _ _ _ Hsa) as [[Ets0 _]|[Nts0 Hpas]].
      - unfold loc_okb in Hlocs. rewrite Ets0, Uint63.eqb_refl in Hlocs. cbn [andb] in Hlocs. apply andb_true_iff in Hlocs as [_ HL2].
        apply Z.leb_le in HL2. unfold img_hi in HL2. rewrite (proj2 KSH) in HL2. change (to_Z shadow_K) with 2147450880 in HL2. unfold sh in HL2. rewrite ASHADOW_BASE_val in HL2.
        clear - HL2 Hn; unfold AIMG_TOP in *; Z.div_mod_to_equations; slia0.
      - destruct (ptr_arg_inv _ _ _ _ _ Hpas) as (_ & _ & rgs0 & Hrgs0 & _ & Ho1 & _). fold F in Hrgs0. pose proof (proj1 (proj1 Hmem ts rgs0 Hrgs0)) as (_ & Hl62s & _).
        change (to_Z 1%uint63) with 1 in Ho1. clear - Ho1 Hl62s. slia0. }
    assert (Espan : to_Z (strlen_span os len) = (to_Z os + to_Z len + 8) / 8 * 8 - to_Z os).
    { assert (E1 : to_Z (os + len)%uint63 = to_Z os + to_Z len) by (rewrite to_Z_add_small; [reflexivity| clear - Hos0 Hos62 Elen Hk4096; slia0]).
      assert (E2 : to_Z (os + len + 8)%uint63 = to_Z os + to_Z len + 8) by (rewrite to_Z_add_small; rewrite E1; change (to_Z 8%uint63) with 8; [reflexivity| clear - Hos0 Hos62 Elen Hk4096; slia0]).
      assert (E3 : to_Z ((os + len + 8) >> 3)%uint63 = (to_Z os + to_Z len + 8) / 8) by (rewrite to_Z_lsr3, E2; reflexivity).
      assert (E4 : to_Z (((os + len + 8) >> 3) << 3)%uint63 = (to_Z os + to_Z len + 8) / 8 * 8).
      { rewrite Uint63.lsl_spec, E3. change (2 ^ to_Z 3%uint63) with 8. change wB with (2 ^ 63). apply Z.mod_small. clear - Hos0 Hos62 Hlen Elen Hk4096. Z.div_mod_to_equations. slia0. }
      unfold strlen_span. rewrite to_Z_sub_small; rewrite E4; [reflexivity| clear - Hos0 Hlen; Z.div_mod_to_equations; slia0]. }
    set (nsl := (to_Z os + to_Z len + 8) / 8 * 8 - (to_Z os + to_Z len + 1)).   (* [comment removed for export] *)
    assert (Hnsl : 0 <= nsl < 8 /\ to_Z (strlen_span os len) = to_Z len + 1 + nsl) by (subst nsl; rewrite Espan; clear - Hos0 Hlen; Z.div_mod_to_equations; slia0).
    (* [comment removed for export] *)
    assert (SRC : exists sA : Z,
      rv rho F 10 = wa sA /\ 0 <= sA /\ sA + to_Z n + nsl <= AAPP_HI
      /\ shvis (ms_mem ms) sA (sA + to_Z n) /\ in_app_mem sA (sA + to_Z n) /\ accessible (ms_mem ms) sA (to_Z n)
      /\ (sA + to_Z n + nsl <= q_lo Q \/ SP <= sA)
      /\ (- (sA + to_Z len + 1)) mod 8 = nsl
      /\ (forall i, 0 <= i <= to_Z n -> adr rho ts (to_Z os + i) = wa (sA + i))
      /\ (forall i : nat, Z.of_nat i < to_Z n + nsl -> exists b, mrd asegs (ms_mem ms) (wa (sA + Z.of_nat i)) = Some b)
      /\ (ts <> 0%uint63 -> exists rgs0, iget ts (f_mem F) = Some rgs0 /\ rho ts = wa (sA - to_Z os) /\ 0 <= sA - to_Z os /\ rg_lo rgs0 = 0%uint63
                /\ to_Z os + to_Z n <= to_Z (rg_len rgs0) /\ sA - to_Z os + to_Z (rg_len rgs0) <= AAPP_HI /\ to_Z (rg_len rgs0) <= 2 ^ 62)
      /\ (ts = 0%uint63 -> sA = to_Z os)).
    { destruct (src_arg_inv _ _ _ _ _ Hsa) as [[Ets0 Ea0]|[Nts0 Hpas]].
      - (* [comment removed for export] *)
        fold F in Ea0. exists (to_Z os). rewrite Ets0 in Haccs, STR, NUL. unfold loc_okb in Hlocs. rewrite Ets0, Uint63.eqb_refl in Hlocs. cbn [andb] in Hlocs. apply andb_true_iff in Hlocs as [HL1 HL2].
        apply Z.leb_le in HL1. apply Z.leb_le in HL2. unfold img_lo in HL1. unfold img_hi in HL2. rewrite (proj1 KSH) in HL1. rewrite (proj2 KSH) in HL2.
        change (to_Z shadow_K) with 2147450880 in HL1, HL2. unfold sh in HL1, HL2. rewrite ASHADOW_BASE_val in HL1, HL2.
        assert (BL : AIMG_LO + 64 <= to_Z os /\ to_Z os + to_Z n + 64 <= AIMG_TOP) by (clear - HL1 HL2; unfold AIMG_LO, AIMG_TOP in *; Z.div_mod_to_equations; slia0). clear HL1 HL2.
        assert (E10 : rv rho F 10 = wa (to_Z os)).
        { rewrite Erv. change (of_Z 10) with 10%uint63. rewrite Ea0, (dv_conc63 rho _ Xr0). reflexivity. }
        assert (Elen3 : to_Z (rg_len (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A))) = sh AIMG_TOP) by (unfold abs_region; cbn [rg_len]; exact (proj2 KSH)).
        split; [exact E10|]. split; [clear - BL; unfold AIMG_LO in BL; slia0|]. split; [clear - BL Hnsl ACEILB; unfold AIMG_TOP, AAPP_HI in *; slia0|].
        split; [apply (ACONST_shvis _ _ _ Xac); clear - BL Hn; slia0|].
        split; [unfold in_app_mem; left; clear - BL Hn; unfold AIMG_LO, AIMG_TOP in *; rewrite ASHADOW_BASE_val; slia0|].
        split.
        { split; [clear - BL; unfold AIMG_LO in BL; slia0|]. split; [clear - BL ACEILB; unfold AIMG_TOP, AAPP_HI in *; slia0|].
          destruct (Z.to_nat (to_Z n)) as [|kk] eqn:Ekk; [intros z Hz; exfalso; clear - Hz Ekk Hn; slia0|].
          intros z Hz. apply (acc_bytes_sound0 IM (S kk) (f_mem F) os (ms_mem ms)); [first [exact Haccs| rewrite <- Ekk; exact Haccs]
            | rewrite <- Ekk, Z2Nat.id by (clear - Hn; slia0); clear - BL; unfold AIMG_TOP in BL; slia0| | rewrite <- Ekk, Z2Nat.id by (clear - Hn; slia0); exact Hz].
          intros o3 b Ho1 Ho2 Hb. pose proof (i63_range o3) as Ho3. change (to_Z shadow_K) with 2147450880 in Ho1, Ho2.
          assert (Xr3' : rho 3%uint63 = wa 0) by exact Xr3.
          rewrite <- (adr_eq_wa rho 3%uint63 0 (to_Z o3) Xr3' ltac:(clear; slia0) ltac:(clear - Ho3; slia0) ltac:(clear - Ho3; slia0)).
          rewrite <- rview_mrd.
          exact (byte_at_SK_sound asegs IM rho Xr0 (f_mem F) (ms_mem ms) 3%uint63 o3 _ b Hmem ltac:(intros E; discriminate E) Xreg3
                   (fun pn p ci cc Hp Hc => Xinb 3%uint63 _ pn p ci cc Xreg3 Hp Hc)
                   ltac:(rewrite Elen3; rewrite <- Ekk, Z2Nat.id in Ho2 by (clear - Hn; slia0); clear - Ho2 BL; unfold sh, AIMG_TOP in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; slia0) Hb). }
        split; [left; clear - BL Hhl Hnsl ACEILB; unfold AIMG_TOP in *; slia0|].
        split; [subst nsl; clear - Hos0 Hlen; Z.div_mod_to_equations; slia0|].
        split; [intros i Hi; rewrite Ets0; unfold adr; rewrite Xr0; apply bv_add_0_Z_to_bv|].
        split.
        { (* [comment removed for export] *)
          intros i Hi. destruct (NUL (os + len)%uint63 ltac:(rewrite Uint63.add_spec, <- Elen; reflexivity)) as (bN & HbN & _).
          pose proof HbN as HbN'. unfold byte_at in HbN'. rewrite Uint63.eqb_refl in HbN'.
          destruct (image_cell IM (((os + len) >> 3) << 3)%uint63) as [v|] eqn:Hcell; [| discriminate HbN'].
          assert (EoN : to_Z (os + len)%uint63 = to_Z os + to_Z len) by (rewrite to_Z_add_small; [reflexivity| clear - Hos0 Hos62 Elen Hk4096; slia0]).
          assert (Eg8 : to_Z (((os + len) >> 3) << 3)%uint63 = to_Z os + to_Z len - (to_Z os + to_Z len) mod 8).
          { rewrite Uint63.lsl_spec, to_Z_lsr3, EoN. change (2 ^ to_Z 3%uint63) with 8. change wB with (2 ^ 63). rewrite Z.mod_small by (clear - Hos0 Hos62 Hlen Elen Hk4096; Z.div_mod_to_equations; slia0).
            clear - Hos0 Hlen. Z.div_mod_to_equations. slia0. }
          destruct (Z.lt_ge_cases (Z.of_nat i) (to_Z n)) as [Hin|Hin].
          - (* [comment removed for export] *)
            assert (SV : exists b, byte_at IM (f_mem F) 0%uint63 (os + Uint63.of_Z (Z.of_nat i))%uint63 = SK b).
            { destruct (Z.lt_ge_cases (Z.of_nat i) (to_Z len)) as [Hil|Hil].
              - destruct (STR i (os + Uint63.of_Z (Z.of_nat i))%uint63 ltac:(clear - Hil Elen; slia0) ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) as (b & Hb & _). exists b. exact Hb.
              - replace (Z.of_nat i) with (Z.of_nat k) by (clear - Hil Hin En Elen; slia0).
                destruct (NUL (os + Uint63.of_Z (Z.of_nat k))%uint63 ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) as (b & Hb & _). exists b.
                replace (Z.of_nat i) with (Z.of_nat k) in * by (clear - Hil Hin En Elen; slia0). exact Hb. }
            destruct SV as [b Hb]. pose proof (byte_at_img_sound asegs IM rho Xr0 (f_mem F) (ms_mem ms) (os + Uint63.of_Z (Z.of_nat i))%uint63 (im_ro_ok asegs IMX HIMX) (im_ro_find_seg IMX) Xinv) as SVb.
            rewrite Hb in SVb. cbn [slot_val] in SVb. unfold adr in SVb. rewrite Xr0, bv_add_0_Z_to_bv in SVb.
            rewrite to_Z_add_small, Uint63.of_Z_spec in SVb; [| rewrite Uint63.of_Z_spec; change wB with (2 ^ 63); rewrite Z.mod_small by (clear - Hin Hn; slia0); clear - Hos0 Hin Hn BL; unfold AIMG_TOP in BL; slia0].
            change wB with (2 ^ 63) in SVb. rewrite Z.mod_small in SVb by (clear - Hin Hn; slia0). fold (wa (to_Z os + Z.of_nat i)) in SVb. rewrite rview_mrd in SVb. eexists. exact SVb.
          - (* [comment removed for export] *)
            pose proof (img_cell_readable (ms_mem ms) _ v Xinv Hcell ltac:(rewrite Eg8; clear - Hos0 Hlen; Z.div_mod_to_equations; slia0)
                          (Z.to_nat (to_Z os + Z.of_nat i - (to_Z os + to_Z len - (to_Z os + to_Z len) mod 8))) ltac:(subst nsl; clear - Hi Hin En Hos0 Hlen; Z.div_mod_to_equations; slia0)) as [b Hb].
            rewrite Eg8, Z2Nat.id in Hb by (clear - Hin En Hos0 Hlen; Z.div_mod_to_equations; slia0).
            replace (to_Z os + to_Z len - (to_Z os + to_Z len) mod 8 + (to_Z os + Z.of_nat i - (to_Z os + to_Z len - (to_Z os + to_Z len) mod 8))) with (to_Z os + Z.of_nat i) in Hb by (clear; slia0).
            exists b. exact Hb. }
        split; [intros NE; exfalso; exact (NE Ets0)|].
        intros _. reflexivity.
      - (* [comment removed for export] *)
        destruct (ptr_arg_inv _ _ _ _ _ Hpas) as (Ea0 & _ & rgs0 & Hrgs0 & Hloos & _ & _). fold F in Ea0, Hrgs0.
        destruct (src_arg_inv _ _ _ _ _ Hsa2) as [[Ets2 Ea0']|[Nts2 Hpas2]]; [exfalso; fold F in Ea0'; rewrite Ea0 in Ea0'; injection Ea0' as E1 E2; exact (Nts0 ltac:(first [exact E1| exact (eq_sym E1)]))|].
        destruct (ptr_arg_inv _ _ _ _ _ Hpas2) as (Ea0' & _ & rgs2 & Hrgs2 & _ & Hons2 & Hnlens2). fold F in Ea0', Hrgs2. rewrite Ea0 in Ea0'. injection Ea0' as Eos2 Ets2. subst ts2 os2.
        rewrite Hrgs0 in Hrgs2. injection Hrgs2 as <-.
        assert (Hts_lt : to_Z ts < to_Z tn) by exact (OLDLT ts rgs0 Hrgs0).
        destruct (range_obj Q st rho msF mo s LB G FF XS ms true ts os n off rgs0 X Esp2 Hoff1 Hoff2 Hn59 Nts0 Hrgs0 Hloos ltac:(rewrite En; clear - Hons2 Hnsl; slia0) ltac:(rewrite En; clear - Hons2 Hnsl Hos0; slia0) Hn64k Hlocs Haccs)
          as (Ds & (ErDs & HDs0 & HDs8 & HDstop & Hlods & Hdfds & Hkdds & RNGs & HDshi & STKs & OBJFs & (SHVs & IAMs & _ & _ & _ & _ & LODs & SP0Ds & _) & SHFs) & ACCs & SRDs).
        fold F tn in STKs, OBJFs, SHFs |- *. rewrite <- ?Espu in STKs, LODs.
        pose proof (proj1 (proj1 Hmem ts rgs0 Hrgs0)) as (_ & Hlens62 & _). pose proof (i63_range (rg_len rgs0)) as Hlds.
        exists (Ds + to_Z os).
        assert (E10 : rv rho F 10 = wa (Ds + to_Z os)).
        { rewrite Erv. change (of_Z 10) with 10%uint63. rewrite Ea0. rewrite (dv_adr rho ts) by (first [clear - Hts_lt Hn59; slia0| reflexivity]).
          apply (adr_eq_wa rho); [exact ErDs| exact HDs0| clear - Hos0; slia0| clear - RNGs HDshi Hos0 Hn; unfold AAPP_HI in HDshi; slia0]. }
        split; [exact E10|]. split; [clear - HDs0 Hos0; slia0|]. split; [clear - Hons2 Hnsl HDshi Hos0 En; slia0|].
        split; [exact SHVs|]. split; [exact IAMs|]. split; [exact ACCs|].
        split.
        { (* [comment removed for export] *)
          destruct (Uint63.eqb ts 1) eqn:E1; [apply Uint63.eqb_spec in E1; destruct (STKs E1) as (_ & SPd & _); right; exact SPd|].
          apply Uint63.eqb_false_spec in E1. destruct (OBJFs E1) as (Dce & _). left. clear - Dce Hons2 Hnsl Hhl En Hos0; slia0. }
        split; [subst nsl; clear - HDs8 Hos0 Hlen HDs0; Z.div_mod_to_equations; slia0|].
        split; [intros i Hi; rewrite (adr_eq_wa rho ts Ds (to_Z os + i) ErDs HDs0) by (first [clear - Hos0 Hi; slia0| clear - RNGs HDshi Hos0 Hi Hn; unfold AAPP_HI in HDshi; slia0]); f_equal; clear; slia0|].
        split.
        { intros i Hi. destruct (SRDs (Ds + to_Z os + to_Z n + nsl) ltac:(clear - Hn Hnsl Hons2 Hos0 En; slia0)) as (_ & _ & SS).
          destruct (SS (Ds + to_Z os + Z.of_nat i) ltac:(clear - Hi; slia0)) as [_ [b Hb]]. exists b. exact Hb. }
        split.
        { intros _. exists rgs0. split; [exact Hrgs0|]. split; [replace (Ds + to_Z os - to_Z os) with Ds by (clear; slia0); exact ErDs|].
          split; [clear - HDs0; slia0|]. split; [exact Hlods|]. split; [exact RNGs|]. split; [clear - HDshi; slia0| exact Hlens62]. }
        intros E0. exfalso. exact (Nts0 E0). }
    destruct SRC as (sA & Ea0v & HsA0 & HsAhi & SHVs & IAMs & ACCs & LODs & Ensl & Eadr & RD & SOBJ & SIMG).
    assert (Ea0u : bv_unsigned (rv rho F 10) = sA) by (rewrite Ea0v; apply wa_unsigned; clear - HsA0 HsAhi Hn Hnsl ACEILB; unfold AAPP_HI in HsAhi; slia0).
    (* [comment removed for export] *)
    assert (SLOTV : forall (i : nat) (oi : int), (Z.of_nat i < to_Z n) -> to_Z oi = (to_Z os + Z.of_nat i) mod wB ->
              slot_val rho (byte_at IM (f_mem F) ts oi) (mrd asegs (ms_mem ms) (wa (sA + Z.of_nat i)))).
    { intros i oi Hi Hoi.
      assert (Eoi : to_Z oi = to_Z os + Z.of_nat i).
      { rewrite Hoi. apply Z.mod_small. change wB with (2 ^ 63).
        destruct (Uint63.eqb ts 0) eqn:Ets; [apply Uint63.eqb_spec in Ets; pose proof (SIMG Ets) as EsA; clear - Hi Hos0 Hn EsA HsAhi Hnsl ACEILB; unfold AAPP_HI in HsAhi; slia0|].
        apply Uint63.eqb_false_spec in Ets. destruct (SOBJ Ets) as (rgs0 & _ & _ & _ & _ & RNGs & _ & Hlens62). clear - Hi Hos0 Hn RNGs Hlens62; slia0. }
      rewrite <- (Eadr (Z.of_nat i)) by (clear - Hi; slia0). rewrite <- Eoi, <- rview_mrd.
      destruct (Uint63.eqb ts 0) eqn:Ets.
      - apply Uint63.eqb_spec in Ets. rewrite Ets. exact (byte_at_img_sound asegs IM rho Xr0 (f_mem F) (ms_mem ms) oi (im_ro_ok asegs IMX HIMX) (im_ro_find_seg IMX) Xinv).
      - apply Uint63.eqb_false_spec in Ets. destruct (SOBJ Ets) as (rgs0 & Hrgs0 & _ & _ & _ & RNGs & _).
        apply (byte_at_slot_sound asegs IM rho Xr0 (f_mem F) (ms_mem ms) ts oi rgs0 (mem_part_of _ _ _ _ _ _ _ Hmem Hrgs0) Ets Hrgs0 (fun pn p ci cc Hp Hc => Xinb ts rgs0 pn p ci cc Hrgs0 Hp Hc)).
        rewrite Eoi. clear - Hi RNGs. slia0. }
    set (str := rd_list (ms_mem ms) sA k). set (slack := rd_list (ms_mem ms) (sA + Z.of_nat k + 1) (Z.to_nat nsl)).
    assert (Hstrlen : length str = k) by (subst str; apply rd_list_length).
    assert (Hsllen : Z.of_nat (length slack) = nsl) by (subst slack; rewrite rd_list_length; clear - Hnsl; slia0).
    assert (STRB : forall i : nat, (i < k)%nat -> exists b : int, to_Z (b land 255)%uint63 <> 0 /\ mrd asegs (ms_mem ms) (wa (sA + Z.of_nat i)) = Some (Z_to_bv 8 (to_Z b))).
    { intros i Hi. destruct (STR i (os + Uint63.of_Z (Z.of_nat i))%uint63 Hi ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) as (b & Hb & Hnz).
      pose proof (SLOTV i (os + Uint63.of_Z (Z.of_nat i))%uint63 ltac:(rewrite En, Elen; clear - Hi; slia0) ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) as SV.
      rewrite Hb in SV. cbn [slot_val] in SV. exists b. split; [exact Hnz| first [exact SV| symmetry; exact SV]]. }
    assert (NULB : mrd asegs (ms_mem ms) (wa (sA + Z.of_nat k)) = Some (Z_to_bv 8 0)).
    { destruct (NUL (os + Uint63.of_Z (Z.of_nat k))%uint63 ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) as (b & Hb & Hz).
      pose proof (SLOTV k (os + Uint63.of_Z (Z.of_nat k))%uint63 ltac:(rewrite En, Elen; clear; slia0) ltac:(rewrite Uint63.add_spec, Uint63.of_Z_spec, Zplus_mod_idemp_r; reflexivity)) as SV.
      rewrite Hb in SV. cbn [slot_val] in SV. rewrite SV. f_equal. rewrite <- Z_to_bv8_mod, <- to_Z_land255, Hz. reflexivity. }
    assert (BY : bytes_at asegs (ms_mem ms) sA (str ++ Z_to_bv 8 0 :: slack)).
    { assert (RL : rd_list (ms_mem ms) sA (k + (1 + Z.to_nat nsl)) = str ++ Z_to_bv 8 0 :: slack).
      { rewrite rd_list_app. f_equal. rewrite rd_list_app. subst slack. replace (sA + Z.of_nat k + Z.of_nat 1) with (sA + Z.of_nat k + 1) by (clear; slia0).
        change (rd_list (ms_mem ms) (sA + Z.of_nat k) 1) with ([match mrd asegs (ms_mem ms) (wa (sA + Z.of_nat k + Z.of_nat 0)) with Some b => b | None => b8 0 end]).
        rewrite Z.add_0_r, NULB. reflexivity. }
      rewrite <- RL. apply rd_list_bytes_at; [exact HsA0| clear - HsAhi Hnsl En Elen ACEILB; unfold AAPP_HI in HsAhi; slia0|].
      intros i Hi. apply RD. rewrite En, Elen. clear - Hi Hnsl. slia0. }
    assert (NOTIN : ~ In (Z_to_bv 8 0) str).
    { intros Hin. apply In_nth_error in Hin as [i Hi]. pose proof (nth_error_lt _ _ _ Hi) as Hik. rewrite Hstrlen in Hik.
      subst str. rewrite rd_list_nth in Hi by exact Hik. destruct (STRB i Hik) as (b & Hnz & Hb). rewrite Hb in Hi.
      assert (E : Z_to_bv 8 (to_Z b) = Z_to_bv 8 0) by (clear - Hi; congruence).
      apply Hnz. rewrite to_Z_land255. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. change (bv_wrap 8 (to_Z b)) with (to_Z b mod 256) in E.
      rewrite E. reflexivity. }
    (* [comment removed for export] *)
    pose proof Xvis as Xvis0. rewrite Ems in Xvis0.
    assert (SPLO : q_lo Q <= SP - 4096) by (clear - Hlsp Espu Hoff1 Ef2; slia).
    assert (SPB : aceil <= SP - 4096 /\ SP <= q_sp0 Q /\ q_sp0 Q < 2 ^ 64) by (clear - SPLO SB1 Espu Hoff2 HB64; slia).
    assert (Ek : Z.of_nat (length str) = to_Z len) by (rewrite Hstrlen; symmetry; exact Elen).
    assert (G3 : (- (sA + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)) by (rewrite Hsllen, Ek, <- Ensl; clear; slia0).
    assert (G4 : accessible (ms_mem ms) sA (Z.of_nat (length str) + 1)) by (rewrite Ek, <- En; exact ACCs).
    assert (G5 : shvis (ms_mem ms) sA (sA + Z.of_nat (length str) + 1)) by (rewrite Ek; replace (sA + to_Z len + 1) with (sA + to_Z n) by (rewrite En; clear; slia0); exact SHVs).
    assert (G8 : q_lo Q <= SP - 4096) by exact SPLO.
    assert (G11 : Z.of_nat (length str) + 1 <= 2 ^ 40) by (rewrite Ek; clear - Hn64k En; slia0).
    assert (G12 : in_app_mem sA (sA + Z.of_nat (length str) + 1)) by (rewrite Ek; replace (sA + to_Z len + 1) with (sA + to_Z n) by (rewrite En; clear; slia0); exact IAMs).
    assert (G13 : sA + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= q_lo Q \/ SP <= sA) by (rewrite Ek, Hsllen; rewrite En in LODs; clear - LODs; slia0).
    Ltac viaL G Ea0u := let T := type of G in enough (GG : T); [clear - GG Ea0u; rewrite <- ?Ea0u in GG; first [exact GG| unfold AINTRIN_STACK; exact GG]| exact G].
    pose proof (ah_strlen H HH) as MS0. unfold strlen_icpt_stmt in MS0.
    eapply (ah_lift H HH _ _ s msF _ mo Xak Xvis0).
    { eapply MS0; [> viaL BY Ea0u| exact NOTIN| viaL G3 Ea0u| viaL G4 Ea0u| viaL G5 Ea0u| exact Hstk_lo| exact SB1| viaL G8 Ea0u| exact Xinv| exact Xac| exact G11| viaL G12 Ea0u| viaL G13 Ea0u]. }
    intros msF' mo' Hak' Hmp' Hpost. unfold astrlen_post in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Evis' & MU & WM & Hinv' & Hstk' & _ & Hac').
    apply (ah_done H HH). cbn [cfg_ms cfg_model].
    unfold AINTRIN_STACK in MU. set (W := [(SP - 4096, SP)]) in *. change (munch W (ms_mem ms) m') in MU.
    (* [comment removed for export] *)
    destruct Hstk_hi as (SPge0 & SP064 & STKHI).
    assert (Hkeep0 : forall a, 0 <= a < 2 ^ 64 -> outside W a -> m' (wa a) = ms_mem ms (wa a) /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hou. split; [apply MU; rewrite wa_unsigned by (clear - Ha; slia0); exact Hou| intros Wv; apply WM; exact Wv]. }
    assert (Mout : forall a, 0 <= a < 2 ^ 64 -> ~ (SP - 4096 <= a < SP) -> m' (wa a) = ms_mem ms (wa a)).
    { intros a Ha Hna. apply Hkeep0; [exact Ha|]. subst W. cbn [outside]. split; [clear - Hna; slia0| exact I]. }
    (* [comment removed for export] *)
    set (L14 := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
    set (rho' := rho_ext rho tn L14).
    exists rho'.
    assert (Hag' : agree tn rho rho') by (apply agree_ext; [clear; slia0| clear - Hn2; slia0| exact Xr0]).
    assert (EL14 : forall x (kk : nat), (kk < 14)%nat -> to_Z x = to_Z tn + Z.of_nat kk -> rho' x = nth kk L14 w0).
    { intros x kk Hk Hx. subst rho'. apply (rho_ext_at rho tn L14 x kk); [subst L14; cbn; clear - Hk; slia0| exact Hx]. }
    assert (NE1 : forall x, 4 <= to_Z x -> (x =? 1)%uint63 = false).
    { intros x Hx. destruct (x =? 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. subst x. exfalso. change (to_Z 1%uint63) with 1 in Hx. clear - Hx. slia. }
    (* [comment removed for export] *)
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 (Z.of_nat (length str)))
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    assert (HRn' : Rn asegs IM (tn + 14)%uint63 rho' (FS (ret_of l) (iset 10 (FV 0 (W64 0 len)) (clobber clob14 tn (f_regs F))) (iset 1 (drop_below off rg1) (f_mem F)) None) ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree tn rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Etn14; clear; slia0]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z tn + 14 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Etn14; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''old : forall x, to_Z x < to_Z tn -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by (clear - Hx; slia0). subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia); exact Xr1).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 (Z.of_nat (length str)))
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; Z_to_bv 64 (Z.of_nat (length str));
                      a1'; a2'; a3'; a4'; a5'; a6'; a7'; rv rho F 18; rv rho F 19; rv rho F 20; rv rho F 21; rv rho F 22; rv rho F 23;
                      rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; t3'; t4'; t5'; t6']).
        apply R_regs_of_match; [exact Hrho''0 | reflexivity |].
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 5) (rv rho F 6) (rv rho F 7) (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     (rv rho F 11) (rv rho F 12) (rv rho F 13) (rv rho F 14) (rv rho F 15) (rv rho F 16) (rv rho F 17) (rv rho F 18) (rv rho F 19) (rv rho F 20)
                     (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) (rv rho F 28) (rv rho F 29) (rv rho F 30) (rv rho F 31))
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; rv rho F 5; rv rho F 6; rv rho F 7; rv rho F 8; rv rho F 9; rv rho F 10;
                      rv rho F 11; rv rho F 12; rv rho F 13; rv rho F 14; rv rho F 15; rv rho F 16; rv rho F 17; rv rho F 18; rv rho F 19; rv rho F 20;
                      rv rho F 21; rv rho F 22; rv rho F 23; rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; rv rho F 28; rv rho F 29; rv rho F 30; rv rho F 31]) in HR''.
        pose proof (regs_match_of_R _ _ _ _ _ _ _ _ _ _ _ HR'') as Hpre.
        assert (Hnd14 : List.NoDup clob14) by (apply nodupb_spec; reflexivity).
        assert (Hcl : forall kr : int, iget kr (clobber clob14 tn (f_regs F)) =
                      match index_of kr clob14 with
                      | Some i => Some (FV (of_Z (to_Z tn + Z.of_nat i)) w_zero)
                      | None => iget kr (f_regs F) end).
        { intros kr. apply iget_clobber; [exact Hnd14 | cbn [length clob14]; clear - Hn59; slia0]. }
        apply regs_match_intro. cbn [seq].
        repeat (apply Forall_cons || apply Forall_nil);
          cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ];
          match goal with |- _ = dv _ (FxState.rget ?FF' ?kr) =>
            let kk := eval vm_compute in kr in change kr with kk; rewrite (rget_regs' FF' kk eq_refl) end;
          cbn [f_regs]; rewrite iget_iset;
          match goal with |- _ = dv _ match (if ?b then _ else _) with _ => _ end => let bb := eval vm_compute in b in change b with bb end;
          cbv iota.
        all: try (rewrite Hcl;
                  match goal with |- _ = dv _ match match ?ix with _ => _ end with _ => _ end =>
                    let ii := eval vm_compute in ix in change ix with ii end; cbv iota).
        all: first
          [ match goal with |- Z_to_bv 64 _ = dv ?rr (FV 0%uint63 (W64 0 ?ln)) => rewrite (dv_conc63 rr ln Hrho''0); f_equal; rewrite rd_list_length; symmetry; exact Elen end
          | match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); clear - Hn59 Htn; slia0);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Htn; slia0);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; clear - Hn59 Htn; slia0);
              rewrite (EL14 (of_Z (to_Z t1 + Z.of_nat i)) i); [reflexivity | clear; slia0 | rewrite Etag; clear; slia0]
            end
          | match goal with |- rv _ _ ?kz = dv _ match iget ?ki (f_regs ?FF') with _ => _ end =>
              rewrite <- (rget_regs' FF' ki eq_refl);
              let kn := eval vm_compute in (Z.to_nat kz) in
              let HP := fresh "HP" in
              pose proof (Hpre kn ltac:(slia)) as HP; cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in HP; exact HP
            end
          ].
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        cbn [f_mem ms_mem].
        destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
        apply mem_ok_parts.
        + intros t' rg' Ht'. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1.
          * apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
            apply (stack_part asegs IM rho'' (ms_mem ms) m' rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q));
              [exact Erho''1| exact Hlo1| exact Hd1| exact Hkd1| rewrite Hlen1; reflexivity| rewrite Hlen1; clear - Hoff Hoff2; slia| clear - Hoff16 Hoff; Z.div_mod_to_equations; slia
              | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1)| exact Xstk| clear - Hhl Hlsp ACEILB; slia| rewrite <- Espu; exact Hstk'|].
            intros a Ha. apply pw_keep. apply Mout; [clear - Ha Espu SPB SPge0; slia0| clear - Ha Espu; slia0].
          * apply Uint63.eqb_false_spec in E1. pose proof (OLDLT _ _ Ht') as Hlt'.
            destruct (t' =? 0)%uint63 eqn:E0.
            -- apply Uint63.eqb_spec in E0. subst t'. rewrite Hrg0 in Ht'. injection Ht' as <-.
               apply (mem_part_transfer0 IMX rho'' (ms_mem ms) m' rg0 Hrho''0); [rewrite Hlen0; unfold AIMG_TOP; clear; slia0| | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0)].
               intros a Ha. rewrite Hlo0, Hlen0 in Ha. apply pw_keep. apply Mout; [clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia0| clear - Ha SPB ACEILB; unfold AIMG_LO, AIMG_TOP in Ha; slia0].
            -- apply Uint63.eqb_false_spec in E0. destruct (REGLO t' rg' Ht' E1) as [RL1 RL2]. pose proof (proj1 (proj1 Hmem'' t' rg' Ht')) as (_ & _ & RO3 & _).
               rewrite (Erho''old t' Hlt') in RO3.
               apply (mem_part_transfer asegs IM rho'' (ms_mem ms) m' t' rg' (bv_unsigned (rho'' t')));
                 [symmetry; apply wa_id| clear; pose proof (bv_unsigned_in_range 64 (rho'' t')); slia0| rewrite (Erho''old t' Hlt'); clear - RO3; slia0| | intros _ _ _; exact E0
                 | exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Ht')].
               intros a Ha. rewrite (Erho''old t' Hlt') in Ha. apply pw_keep. apply Mout; [clear - Ha RL1 RL2 ACEILB; slia0| clear - Ha RL2 SPB; slia0].
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2. rewrite iget_iset in Hi1, Hi2.
          assert (BK : forall x r, (if (x =? 1)%uint63 then Some (drop_below off rg1) else iget x (f_mem F)) = Some r ->
                    exists r0, iget x (f_mem F) = Some r0 /\ rg_lo r0 = rg_lo r /\ rg_len r0 = rg_len r).
          { intros x r Hx. destruct (x =? 1)%uint63 eqn:Ex; [apply Uint63.eqb_spec in Ex; subst x; injection Hx as <-; exists rg1; split; [exact Hrg1| split; reflexivity]| exists r; split; [exact Hx| split; reflexivity]]. }
          destruct (BK t1 r1 Hi1) as (q1 & Hq1 & Lo1 & Le1). destruct (BK t2 r2 Hi2) as (q2 & Hq2 & Lo2 & Le2).
          rewrite <- Lo1, <- Le1, <- Lo2, <- Le2. exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
    (* [comment removed for export] *)
    assert (CW : Forall (aclient_write_ok H LB) W) by (subst W; apply Forall_cons; [left; cbn [fst snd]; clear - SPB; slia| apply Forall_nil]).
    assert (SW : Forall stack0_ok W) by (subst W; apply Forall_cons; [apply stack0_ok_app; clear - SPB ACEILB; unfold AHI_LO; slia| apply Forall_nil]).
    assert (AFW : Forall (afs_write_ok H (LF_of Q FF)) W).
    { subst W. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. clear - F1 F2 SPB ACEILB. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. split; slia. }
    assert (GDJ : forall g, In g G -> disjoint_from W (sh (g_addr g)) (nsh (to_Z (g_size g)))).
    { intros g Hg. pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (i63_range (g_size g)) as Hgs0.
      pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) B7 ltac:(clear - Hgs0; slia0)) as (U1 & U2 & U3).
      assert (SHA : sh aceil < aceil) by (clear - ACEILB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; slia).
      subst W. cbn [disjoint_from]. split; [clear - U2 U3 SHA SPB; slia| exact I]. }
    assert (INB1 : rg_inb (drop_below off rg1)).
    { intros pn p' ci cc Hp' Hc'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->). unfold drop_below. cbn [rg_len].
      unfold drop_page in Hc'. cbn [fst snd] in Hc'. destruct (pn =? off >> 12)%uint63.
      - cbn [pg_cells] in Hc'. destruct (keep_cells_ge_inv _ _ _ _ Hc') as [_ Hc'']. exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'').
      - exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'). }
    destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [Hdu1 Hkd1].
    destruct Xnamed as [XG0in XLB0nd].
    exists s, LB, G, FF, XS, ms1.
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mk f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS ms1].
    - exact Evis'.
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr2 | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr3 | change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia].
    - eapply agree_trans; [exact Xag | exact Hag' | clear - Xn0a Xn0b; slia].
    - rewrite Etn14. clear - Xn0a Xn0b Hn59. slia.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmp').
    - eapply (ah_RHEAP_frame H HH); [exact Xheap| exact MU| exact WM| exact CW].
    - eapply (ah_RFS_frame H HH); [exact Xrfs| exact MU| exact WM| exact AFW].
    - exact Hac'.
    - eapply stack0_transport; [exact Xst0| exact MU| exact WM| exact SW].
    - eapply (chain_via_munch H HH); [exact Xch| exact MU|]. intros fp' ra' Hin. specialize (XCH0 fp' ra' Hin).
      subst W. cbn [disjoint_from]. clear - XCH0 SPB. repeat split; slia.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - exact XAL.
    - exact XAL0.
    - exact XG.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hshg).
      pose proof (i63_range (g_tag g)) as Htg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      split; [exact Hin|]. split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
      split; [rewrite Etn14; clear - Htg2; slia|]. split.
      + exists rgg. rewrite iget_iset, (NE1 _ Htg1). split; [exact Hgg|]. repeat split; assumption.
      + intros rg' Hrg'. rewrite iget_iset, (NE1 _ ltac:(rewrite Etg1; clear - Htg1; slia)) in Hrg'.
        destruct (Hshg rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hrs|].
        eapply addressable_transport; [exact Had'| exact MU| exact WM| exact (GDJ g Hg)].
    - exact XGnd.
    - exact XGtnd.
    - exact XGnew.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (B1 & B2 & B3 & B4 & B5 & _).
      apply (stk_pres asegs (ms_mem ms)); [exact Hs|]. intros a Ha. apply Hkeep0; [clear - Ha B4 B5 ACEILB; unfold AIMG_TOP in B4; slia|].
      subst W. cbn [outside]. clear - Ha B5 SPB. repeat split; slia.
    - exact XFF.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hkf & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkdf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)) as Htg.
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Hn59; slia0).
      split; [subst rho'; rewrite rho_ext_old by (clear - Htg2; slia); exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; clear - Htg2; slia); exact Hf1|].
      split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; clear - Htg2; slia); exact Hf2|]. split; [exact Hkf|]. split; [exact Htg1|]. split; [rewrite Etn14; clear - Htg2; slia|].
      split; [exists rgf; rewrite iget_iset, (NE1 _ Htg1); split; [exact Hgf|]; repeat split; assumption|].
      split; [exists rgs; rewrite iget_iset, (NE1 _ ltac:(rewrite Etg1; clear - Htg1; slia)); split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite iget_iset, (NE1 _ ltac:(rewrite Etg2; clear - Htg1; slia)); exact Hflg|].
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. exact X4.
    - exact XFFnd.
    - exact XFFtnd.
    - exact XTsep.
    - exact XFFlen.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; right; left; exact E1| exact (Xdom t' rg' Ht')].
    - (* [comment removed for export] *) exists rg0. rewrite iget_iset. change ((0 =? 1)%uint63) with false. cbv iota. split; [exact Hrg0|]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0| exact Hpg0].
    - (* [comment removed for export] *) exists (drop_below off rg1). rewrite iget_iset, Uint63.eqb_refl. split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite iget_iset. change ((2 =? 1)%uint63) with false. exact Xreg2.
    - (* [comment removed for export] *) rewrite iget_iset. change ((3 =? 1)%uint63) with false. exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc). exists rg0_. rewrite iget_iset. change ((0 =? 1)%uint63) with false. split; [exact Hrg0_| exact Hroc].
    - (* [comment removed for export] *) intros t' rg' pn p' ci cc Ht' Hp' Hc'. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1; [injection Ht' as <-; exact (INB1 pn p' ci cc Hp' Hc')| exact (Xinb t' rg' pn p' ci cc Ht' Hp' Hc')].
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0. rewrite iget_iset in Ht'. destruct (t' =? 1)%uint63 eqn:E1; [| exact (Xkinds t' rg' Ht' Ht'0)].
      injection Ht' as <-. unfold drop_below. cbn [rg_dflt rg_pages]. split; [exact Hdu1|].
      intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->). unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hkd1 _ _ Hp0).
    - exact Xcost.
    - exact Xcnt.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) SP (q_sp0 Q)); [exact Hstk' | | clear - SPLO SPB; slia].
      apply (stk_pres asegs (ms_mem ms)); [split; [exact SPge0| split; [exact SP064| exact STKHI]]|]. intros a Ha. apply Hkeep0; [clear - Ha SPB ACEILB; slia|].
      subst W. cbn [outside]. clear - Ha. repeat split; slia.
    - repeat split; assumption.
    - eapply (ah_rauxv_frame H HH); [exact Xaux| exact MU| exact WM| exact CW].
    - exact Hinv'.
    - apply (stk_pres asegs (ms_mem ms)); [exact Xerr|]. intros a Ha. apply Hkeep0; [clear - Ha Eerr H0 H1; unfold errA, AERRNO, ATP in *; slia|].
      subst W. cbn [outside]. clear - Ha Eerr H0 H1 SPB ACEILB. unfold errA, AERRNO, ATP, AIMG_TOP in *. repeat split; slia.
    - exact (HSH0 _ Hac' Hinv').
    - exact XLB0.
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - exact XLBsub.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      assert (LOW : SP <= a \/ a < aceil).
      { unfold client0, aclient_addr in Hcl. destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        - left. clear - Hs SPB. slia.
        - right. clear - Hst ACEILB. unfold aimg_client, AIMG_LO, AIMG_TOP in *. slia.
        - right. destruct (XLB0h b Hb) as [_ Bh]. clear - Hr Bh. slia.
        - right. destruct (XLB0h b Hb) as [B0 Bh]. pose proof (sh_nsh_high (blk_addr b) (blk_size b) B0 ltac:(clear - Hr; unfold nsh in Hr; Z.div_mod_to_equations; slia) ltac:(clear - Bh ACEILB; unfold AAPP_HI; slia)) as SB.
          clear - Hr SB ACEILB. unfold AHI_LO in *. slia.
        - right. clear - Hfs F2. slia.
        - right. pose proof (sh_below_app (as_FSB H + AFS_SIZE) ltac:(clear - F1 F2 ACEILB; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; slia)) as SB.
          pose proof (sh_mono a). clear - Hfss SB ACEILB. unfold AHI_LO, sh in *. rewrite ?ASHADOW_BASE_val in *. Z.div_mod_to_equations. slia.
        - right. clear - Hss ACEILB. unfold AHI_LO in *. slia. }
      apply Hkeep0; [exact Ha|]. subst W. cbn [outside]. clear - LOW SPB. repeat split; slia.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) XFFstk f Hf) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(KF1 & KF2 & KF3 & KF4 & KF5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(clear - KF1; slia0)) as FPf.
      apply (stk_pres asegs (ms_mem ms)); [exact HsF|]. intros a Ha. apply Hkeep0; [clear - Ha KF2 KF3 F1 F2 FPf ACEILB; unfold AFS_HDR, AIMG_TOP in *; slia|].
      subst W. cbn [outside]. clear - Ha KF3 F2 SPB. repeat split; slia.
  Qed.
End NodeX.
