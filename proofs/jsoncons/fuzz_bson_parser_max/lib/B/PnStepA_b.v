(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmModelFactsA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMKA.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.

(* [comment removed for export] *)
Lemma S_in_shadow y : 0 <= y < 2 ^ 47 -> BIGSHADOW_LO <= S y < BIGSHADOW_HI.
Proof. intros Hy. unfold S, SB, BIGSHADOW_LO, BIGSHADOW_HI. assert (0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia). lia. Qed.
Lemma S_mono x y : x <= y -> S x <= S y.
Proof. intros H. unfold S. assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia. Qed.

Lemma mod16_8' x : x mod 16 = 0 -> x mod 8 = 0.
Proof. intros H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult. Qed.
(* [comment removed for export] *)
Lemma shadow_zero_sub (M : word -> option byte) a g a' g' :
  a mod 8 = 0 -> a' mod 8 = 0 -> a <= a' -> a' + 8 * g' <= a + 8 * g -> 0 <= g' -> shadow_zero M a g -> shadow_zero M a' g'.
Proof.
  intros Ha Ha' H1 H2 Hg SZ j Hj. unfold byte_at.
  assert (E : S a' + j = S a + ((a' - a) / 8 + j)).
  { unfold S. assert (a = 8 * (a / 8)) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia). assert (a' = 8 * (a' / 8)) by (pose proof (Z.div_mod a' 8 ltac:(lia)); lia).
    assert ((a' - a) / 8 = a' / 8 - a / 8). { replace (a' - a) with ((a' / 8 - a / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. } lia. }
  rewrite E. apply SZ. assert (a = 8 * (a / 8)) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia). assert (a' = 8 * (a' / 8)) by (pose proof (Z.div_mod a' 8 ltac:(lia)); lia).
  assert ((a' - a) / 8 = a' / 8 - a / 8). { replace (a' - a) with ((a' / 8 - a / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. } lia.
Qed.
(* [comment removed for export] *)
Definition wapp (W : list L5.range) : Prop := forall r, In r W -> fst r + snd r <= BIGSHADOW_LO \/ BIGSHADOW_HI <= fst r.
Lemma wapp_outside_shadow W x : wapp W -> BIGSHADOW_LO <= x < BIGSHADOW_HI -> L5.outside W x.
Proof. intros WA Hx r Hr Hin. destruct r as [b n]. specialize (WA _ Hr). unfold L5.in_rng in Hin. cbn [fst snd] in *. lia. Qed.
Lemma wapp_nil : wapp [].
Proof. intros r []. Qed.
Lemma wapp_cons r W : fst r + snd r <= BIGSHADOW_LO \/ BIGSHADOW_HI <= fst r -> wapp W -> wapp (r :: W).
Proof. intros H WA r' [<-|Hr]; [exact H| exact (WA r' Hr)]. Qed.
Lemma wapp_app W1 W2 : wapp W1 -> wapp W2 -> wapp (W1 ++ W2).
Proof. intros A B r Hr. apply in_app_or in Hr. destruct Hr; [apply A|apply B]; assumption. Qed.

Section Stk.
Variables (L : asan_layout) (ar : asan_run).
(* [comment removed for export] *)
Lemma astk_after_ahpres LB FF M1 M2 sp scr sp' scr' W :
  L5CA.astk ar M1 sp scr -> L5CA.ahpres L ar LB FF sp' scr' W M1 M2 -> sp - scr <= sp' - scr' -> sp' <= sp -> 0 <= scr' ->
  ar_stack_top ar <= 2 ^ 47 -> L5CA.astk ar M2 sp scr.
Proof.
  intros (A16 & SLO & SHI & SPT & D1 & D2) (_ & DS & DK) H1 H2 H3 TOP.
  assert (DEF : forall a, ahl_ceil ar <= a < 2 ^ 47 -> M1 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
  { intros a Ha Hd. destruct (Z_lt_le_dec a (sp' - scr')) as [X|X]; [| destruct (Z_lt_le_dec a sp') as [Y|Y]].
    - apply DK; [lia| |exact Hd]. unfold aclient, aclient_g. right; left. split; [lia| intros Z; lia].
    - replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply DS. lia.
    - apply DK; [lia| |exact Hd]. unfold aclient, aclient_g. right; left. split; [lia| intros Z; lia]. }
  split; [exact A16|]. split; [exact SLO|]. split; [exact SHI|]. split; [exact SPT|]. split.
  - intros i Hi. apply DEF; [lia|]. apply D1. exact Hi.
  - intros i Hi. apply DEF; [lia|]. apply D2. exact Hi.
Qed.
End Stk.

Section Along.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variables (L : asan_layout) (ar : asan_run).
Variables (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis E : L5SAR.ek L ar LB FF sp scr W M M'.
Hypothesis WAPP : wapp W.

Lemma agA_frame o n : PMSPA.aobjA FF o n -> 0 <= o -> o + n <= 2 ^ 47 -> (forall i, o <= i < o + n -> L5.outside W i) -> PMFA.agA M M' o n.
Proof.
  intros (f & Hf & H1 & H2) Ho Hon OW. split.
  - intros i Hi. apply E. split; [lia|]. split; [|apply OW; lia].
    destruct f as [[F k] rs]. cbn [ff_addr ff_class fst snd] in *.
    unfold aclient, aclient_g. right; right; right; left. exists (F, k, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. lia.
  - intros x Hx. pose proof (S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
    apply E. split; [lia|]. split.
    + destruct f as [[F k] rs]. cbn [ff_addr ff_class fst snd] in *.
      unfold aclient, aclient_g. do 5 right. left. exists (F, k, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd].
      unfold in_shadow_of. split; apply S_mono; lia.
    + apply (wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.

Lemma agA_block q m : In (q, m) LB -> 0 <= q -> q + m <= 2 ^ 47 -> (forall i, q <= i < q + m -> L5.outside W i) -> PMFA.agA M M' q m.
Proof.
  intros Hin Hq Hqm OW. split.
  - intros i Hi. apply E. split; [lia|]. split; [|apply OW; lia]. unfold aclient, aclient_g. left. exists (q, m). split; [exact Hin|]. cbn [fst snd]. lia.
  - intros x Hx. pose proof (S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
    apply E. split; [lia|]. split.
    + unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply S_mono; lia.
    + apply (wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.

(* [comment removed for export] *)
Lemma ag_img a n : hl_img_lo L <= a -> a + n <= hl_img_hi L -> (forall i, a <= i < a + n -> ~ hl_rt_static L i) ->
  0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> L5.outside W i) -> L5C.agree_on M M' a n.
Proof.
  intros H1 H2 NS Ha Han OW i Hi. apply E. split; [lia|]. split; [|apply OW; lia].
  unfold aclient, aclient_g. right; right; left. split; [lia|]. apply NS. lia.
Qed.
(* [comment removed for export] *)
Hypothesis FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47.
Hypothesis BRB : forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47.

Lemma aobjA_bounds o n : PMSPA.aobjA FF o n -> 0 <= o /\ o + n <= 2 ^ 47.
Proof. intros (f & Hf & H1 & H2). destruct (FRB f Hf) as [B1 B2]. lia. Qed.
Lemma agA_obj o n : PMSPA.aobjA FF o n -> (forall i, o <= i < o + n -> L5.outside W i) -> PMFA.agA M M' o n.
Proof. intros AO OW. destruct (aobjA_bounds o n AO). apply agA_frame; assumption. Qed.
Lemma agA_blk q m : In (q, m) LB -> (forall i, q <= i < q + m -> L5.outside W i) -> PMFA.agA M M' q m.
Proof. intros Hin OW. destruct (BRB _ Hin) as [B1 B2]. cbn [fst snd] in *. apply agA_block; assumption. Qed.

(* [comment removed for export] *)
Lemma u64_keepA a v : PMSPA.aobjA FF a 8 -> (forall i, a <= i < a + 8 -> L5.outside W i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros AO OW. destruct (aobjA_bounds a 8 AO). apply (L5C.u64_at_agree segs M M'); [exact (proj1 (agA_obj a 8 AO OW))|lia|lia]. Qed.
Lemma u32_keepA a v : PMSPA.aobjA FF a 4 -> (forall i, a <= i < a + 4 -> L5.outside W i) -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof. intros AO OW. destruct (aobjA_bounds a 4 AO). apply (PMF.u32_at_agree segs M M'); [exact (proj1 (agA_obj a 4 AO OW))|lia|lia]. Qed.
Lemma u8_keepA a v : PMSPA.aobjA FF a 1 -> (forall i, a <= i < a + 1 -> L5.outside W i) -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros AO OW. destruct (aobjA_bounds a 1 AO). apply (L5C.u8_at_agree segs M M'); [exact (proj1 (agA_obj a 1 AO OW))|lia|lia]. Qed.
Lemma defined_keepA a n : PMSPA.aobjA FF a n -> (forall i, a <= i < a + n -> L5.outside W i) -> L5.defined M a n -> L5.defined M' a n.
Proof. intros AO OW. apply (L5C.defined_agree M M' a n). exact (proj1 (agA_obj a n AO OW)). Qed.
Lemma acc_keepA a n : PMSPA.aobjA FF a n -> (forall i, a <= i < a + n -> L5.outside W i) -> accA M a n -> accA M' a n.
Proof. intros AO OW. apply PMFA.accA_agree. exact (proj2 (agA_obj a n AO OW)). Qed.

Definition blk_out (q m : Z) : Prop := forall i, q <= i < q + m -> L5.outside W i.

Lemma vstr_keepA o s : PMSPA.aobjA FF o 24 -> incl (PM.vs_own s) LB -> (forall i, o <= i < o + 24 -> L5.outside W i) ->
  (forall c n p, s = PM.VLong c n p -> blk_out p c) ->
  PM.vstr_at segs accA M o s -> PM.vstr_at segs accA M' o s.
Proof.
  intros AO INC OW OB. destruct (aobjA_bounds o 24 AO).
  apply PMFA.vstr_at_agreeA; [lia|lia| apply agA_obj; assumption|].
  intros c n p ->. apply agA_blk; [apply INC; left; reflexivity| exact (OB c n p eq_refl)].
Qed.

Lemma ec_keepA o v c : PMSPA.aobjA FF o 16 -> (forall i, o <= i < o + 16 -> L5.outside W i) -> PMSPA.ec_at segs M o v c -> PMSPA.ec_at segs M' o v c.
Proof.
  intros AO OW (U & W8 & D & CC). destruct (aobjA_bounds o 16 AO). pose proof (agA_obj o 16 AO OW) as [AG SH].
  split; [apply (PMF.u32_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact U]|].
  split; [apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact W8]|].
  split; [exact (L5C.defined_agree M M' o 16 AG D)| exact (PMFA.accA_agree M M' o 16 SH CC)].
Qed.

Lemma visitor_keepA o : PMSPA.aobjA FF o 8 -> (forall i, o <= i < o + 8 -> L5.outside W i) -> PMSPA.visitor_at segs A M o -> PMSPA.visitor_at segs A M' o.
Proof. intros AO OW (V & CC). split; [apply u64_keepA; assumption| apply acc_keepA; assumption]. Qed.

Lemma iss_keepA ois str sm : PMSPA.aobjA FF ois 272 -> incl (PM.vs_own str) LB -> (forall i, ois <= i < ois + 272 -> L5.outside W i) ->
  (forall c n p, str = PM.VLong c n p -> blk_out p c) ->
  PM.iss_at segs A accA M ois str sm -> PM.iss_at segs A accA M' ois str sm.
Proof.
  intros AO INC OW OB. destruct (aobjA_bounds ois 272 AO).
  apply PMFA.iss_at_agreeA; [lia|lia| apply agA_obj; assumption|].
  intros c n p ->. apply agA_blk; [apply INC; left; reflexivity| exact (OB c n p eq_refl)].
Qed.

Lemma parser_keepA op ois s : PMSPA.aobjA FF op 384 -> incl (PM.parser_own s) LB -> (forall i, op <= i < op + 384 -> L5.outside W i) ->
  blk_out (PM.sr_qc (PM.p_src s)) PM.CHUNK -> blk_out (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> blk_out p c) ->
  PM.parser_at segs A accA annA M op ois s -> PM.parser_at segs A accA annA M' op ois s.
Proof.
  intros AO INC OW OQ OV OT. destruct (aobjA_bounds op 384 AO).
  assert (IQ : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (apply INC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (IV : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (apply INC; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  destruct (BRB _ IQ) as [Q1 Q2]. destruct (BRB _ IV) as [V1 V2]. cbn [fst snd] in *.
  apply PMFA.parser_at_agreeA; [lia|lia| apply agA_obj; assumption| lia| lia| apply agA_blk; assumption| lia| lia| apply agA_blk; assumption|].
  intros c n p E1. apply agA_blk; [| exact (OT c n p E1)]. apply INC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ls_okA_keep g : PMST.addrs_wf A ->
  (forall a, PMST.dep A a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a) ->
  (forall a, 65536 <= a < pa_rw_lo A -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a) ->
  PMSTA.ls_okA segs A AA g M -> PMSTA.ls_okA segs A AA g M'.
Proof.
  intros WF SD SR. pose proof (PMST.aw_rw A WF) as Hrw. apply (PMSTA.ls_okA_frame segs A AA WF M M').
  - intros a Ha D. destruct (SD a D) as (I1 & I2 & I3). apply E. split; [exact Ha|]. split; [|exact I3].
    unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
  - intros a Ha N. destruct (SR a Ha) as (I1 & I2 & I3). rewrite E; [exact N|]. split; [lia|]. split; [|exact I3].
    unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
Qed.
Lemma err_okA_keep b : PMST.addrs_wf A ->
  (forall a, PMST.dep A a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a) ->
  PMSTA.err_okA segs A AA M b -> PMSTA.err_okA segs A AA M' b.
Proof.
  intros WF SD. apply (PMSTA.err_okA_frame segs A AA WF M M').
  intros a Ha D. destruct (SD a D) as (I1 & I2 & I3). apply E. split; [exact Ha|]. split; [|exact I3].
  unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
Qed.

(* [comment removed for export] *)
Lemma agsh_obj o n : PMSPA.aobjA FF o n -> PMFA.agsh M M' o n.
Proof.
  intros AO. destruct (aobjA_bounds o n AO) as [Ho Hon]. destruct AO as (f & Hf & H1 & H2).
  intros x Hx. pose proof (S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
  apply E. split; [lia|]. split.
  - destruct f as [[F k] rs]. cbn [ff_addr ff_class fst snd] in *.
    unfold aclient, aclient_g. do 5 right. left. exists (F, k, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd].
    unfold in_shadow_of. split; apply S_mono; lia.
  - apply (wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma acc_keepA' a n : PMSPA.aobjA FF a n -> accA M a n -> accA M' a n.
Proof. intros AO. apply PMFA.accA_agree. exact (agsh_obj a n AO). Qed.
Lemma base_ok_keepA : PMST.addrs_wf A ->
  (forall a, PMST.dep A a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a) ->
  (forall a, 65536 <= a < pa_rw_lo A -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a) ->
  PMSTA.base_okA segs A M -> PMSTA.base_okA segs A M'.
Proof.
  intros WF SD SR (RO0 & (can & Hcan & CAN) & NL & LL).
  pose proof (PMST.aw_rw A WF) as Hrw. pose proof (PMST.aw_canary A WF) as Hcn. pose proof (PMST.aw_nl A WF) as Hnl. pose proof (PMST.aw_ll A WF) as Hll.
  assert (AG : forall a, 0 <= a < 2 ^ 64 -> PMST.dep A a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha D. destruct (SD a D) as (I1 & I2 & I3). apply E. split; [exact Ha|]. split; [|exact I3].
    unfold aclient, aclient_g. right; right; left. split; [lia| exact I2]. }
  split; [|split; [|split]].
  - intros i Hi. destruct (SR i Hi) as (I1 & I2 & I3). rewrite E; [apply RO0; exact Hi|]. split; [lia|]. split; [|exact I3].
    unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree segs M M'); [|lia|lia| exact CAN]. intros i Hi. apply AG; [lia|]. right; left. exact Hi.
  - apply (L5C.u8_at_agree segs M M'); [|lia|lia| exact NL]. intros i Hi. apply AG; [lia| apply PMST.in_foot_nl; lia].
  - unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat (pa_locale_lock A)); [exact LL|lia|cbn; lia|].
    intros i Hi. apply AG; [cbn in Hi; lia| apply PMST.in_foot_ll; cbn in Hi; lia].
Qed.
(* [comment removed for export] *)
Lemma stksh_keepA lo g : 0 <= lo -> ahl_ceil ar <= lo -> lo + 8 * g <= 2 ^ 47 -> lo mod 8 = 0 -> 0 <= g -> shadow_zero M lo g -> shadow_zero M' lo g.
Proof.
  intros H0 H1 H2 H3 H4 SZ j Hj. unfold byte_at in *.
  assert (L8 : lo = 8 * (lo / 8)) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
  assert (SJ : S lo + j = S (lo + 8 * j)).
  { unfold S. replace (lo + 8 * j) with (j * 8 + lo) by lia. rewrite Z.div_add_l by lia. lia. }
  pose proof (S_in_shadow (lo + 8 * j) ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
  rewrite E; [apply SZ; exact Hj|]. split; [rewrite SJ; lia|]. split.
  - unfold aclient, aclient_g. do 4 right. left. unfold in_shadow_of. rewrite SJ. split; apply S_mono; lia.
  - apply (wapp_outside_shadow W _ WAPP). rewrite SJ. unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
(* [comment removed for export] *)
Lemma img_clear_keepA lo hi : 0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a) ->
  L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof.
  intros Hlo Hhi IMG CL i Hi. destruct (IMG i Hi) as (I1 & I2 & I3). rewrite E; [apply CL; exact Hi|].
  split; [lia|]. split; [|exact I3]. unfold aclient, aclient_g. right; right; left. split; [lia| exact I2].
Qed.
End Along.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zeros_of_aacc (M : word -> option byte) o n : aacc M o n -> o mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> L5KA.zeros_at M (o / 8 + SB) (n / 8).
Proof.
  intros C Ho Hn Hn0 i Hi.
  assert (N8 : 8 * (n / 8) = n) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
  assert (O8 : 8 * (o / 8) = o) by (pose proof (Z.div_mod o 8 ltac:(lia)); lia).
  destruct (C (o + 8 * i + 7) ltac:(lia)) as [B|(v & B & V1 & V2)].
  - unfold byte_at, S in B. replace ((o + 8 * i + 7) / 8) with (o / 8 + i) in B; [replace (o / 8 + SB + i) with (o / 8 + i + SB) by lia; exact B|].
    replace (o + 8 * i + 7) with (7 + (o / 8 + i) * 8) by lia. rewrite Z.div_add by lia. reflexivity.
  - exfalso. replace ((o + 8 * i + 7) mod 8) with 7 in V2; [lia|].
    replace (o + 8 * i + 7) with (7 + (o / 8 + i) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Section Vis.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : L5A.as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Lemma aobj_of_aobjA FF o n : PMSPA.aobjA FF o n -> o mod 8 = 0 -> L5CA.aobj FF o n.
Proof. intros (f & Hf & H1 & H2) H8. exists f. split; [exact Hf|]. split; [exact H1|]. split; [exact H2| exact H8]. Qed.

(* [comment removed for export] *)
Lemma obj_shadow_vis LB FF LK cr Aw M model o n :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSPA.aobjA FF o n -> o mod 8 = 0 -> 0 < n -> n mod 8 = 0 -> accA M o n ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) (o / 8 + SB) (n / 8).
Proof.
  intros HH AO O8 Hn N8 CC.
  pose proof (L5SAR.aobj_facts L ar C HI LY HIok LB FF LK cr Aw M model o n 0 0 HH (aobj_of_aobjA FF o n AO O8) Hn N8) as (_ & _ & _ & _ & VS & _).
  apply (proj2 (L5A.zeros_at_vis (ahid Aw model) M (o / 8 + SB) (n / 8) VS)). apply zeros_of_aacc; [exact CC|exact O8|exact N8|lia].
Qed.

(* [comment removed for export] *)
Lemma blk_shadow_vis LB FF LK cr Aw M model q m o n :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> In (q, m) LB -> q <= o -> o + n <= q + m -> o mod 8 = 0 -> 0 < n -> n mod 8 = 0 -> accA M o n ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) (o / 8 + SB) (n / 8).
Proof.
  intros HH Hin H1 H2 O8 Hn N8 CC.
  pose proof (L5SAR.vis_pack L ar C HI LY HIok LB FF LK cr Aw M model HH) as (_ & _ & _ & _ & _ & VBSH & _).
  assert (VS : L5A.avis (ahid Aw model) (o / 8 + SB) (n / 8)).
  { apply (VBSH q m). exact Hin. intros i Hi. unfold in_shadow_of. assert (N8' : 8 * (n / 8) = n) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
    assert (O8' : 8 * (o / 8) = o) by (pose proof (Z.div_mod o 8 ltac:(lia)); lia).
    split.
    - replace (o / 8 + SB + i) with (S (o + 8 * i)). apply S_mono. lia. unfold S. replace (o + 8 * i) with (i * 8 + o) by lia. rewrite Z.div_add_l by lia. lia.
    - replace (o / 8 + SB + i) with (S (o + 8 * i)). apply S_mono. lia. unfold S. replace (o + 8 * i) with (i * 8 + o) by lia. rewrite Z.div_add_l by lia. lia. }
  apply (proj2 (L5A.zeros_at_vis (ahid Aw model) M (o / 8 + SB) (n / 8) VS)). apply zeros_of_aacc; [exact CC|exact O8|exact N8|lia].
Qed.
(* [comment removed for export] *)
Lemma ek_sublb LB LB' FF sp scr W M M' : incl LB' LB -> L5SAR.ek L ar LB FF sp scr W M M' -> L5SAR.ek L ar LB' FF sp scr W M M'.
Proof.
  intros I E a (Ha & Hc & Ho). apply E. split; [exact Ha|]. split; [|exact Ho].
  unfold aclient, aclient_g in *. destruct Hc as [(b & Hb & X)|[X|[X|[X|[X|[X|(b & Hb & X)]]]]]].
  - left. exists b. split; [apply I; exact Hb| exact X].
  - right; left; exact X. - right; right; left; exact X. - do 3 right; left; exact X. - do 4 right; left; exact X. - do 5 right; left; exact X.
  - do 6 right. exists b. split; [apply I; exact Hb| exact X].
Qed.
Lemma dk_sublb LB LB' FF sp scr M M' : incl LB' LB -> L5SAR.dk L ar LB FF sp scr M M' -> L5SAR.dk L ar LB' FF sp scr M M'.
Proof.
  intros I D a Ha Hc HM. apply D; [exact Ha| |exact HM].
  unfold aclient, aclient_g in *. destruct Hc as [(b & Hb & X)|[X|[X|[X|[X|[X|(b & Hb & X)]]]]]].
  - left. exists b. split; [apply I; exact Hb| exact X].
  - right; left; exact X. - right; right; left; exact X. - do 3 right; left; exact X. - do 4 right; left; exact X. - do 5 right; left; exact X.
  - do 6 right. exists b. split; [apply I; exact Hb| exact X].
Qed.
(* [comment removed for export] *)
Lemma ek_own_frame LB FF LK cr Aw M M' V sp scr W lo hi :
  ri_inv HI LB FF LK cr Aw M V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 -> ahl_ceil ar <= lo -> sp - scr <= lo -> hi <= sp ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> L5SAR.ek L ar LB FF sp scr W M M'.
Proof.
  intros HH SPT H0 H1 H2 FR. apply (L5SAR.ek_piece L ar LB FF sp scr W M M' (fun a => lo <= a < hi) FR).
  intros a Ha Hc _ X. destruct (L5SAR.aclient_cases L ar C HI LY HIok LB FF LK cr Aw M V sp scr a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia|].
  exfalso. lia.
Qed.
End Vis.
End PMKA.
