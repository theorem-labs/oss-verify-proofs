(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape SpinAlg Hoare Frame RefMemcpyLib MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesArgSound MallocDefs EnframeArith ImgParams MallocSpec MallocNodes MallocNodesSound MallocNodes2 SlotProp.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma decode_W_lit : forall We Se c, MN2.decode_W We = Some (Se, c) -> 0 <= c < 4096.
Proof.
  intros We Se c H. unfold MN2.decode_W in H.
  destruct We as [w | v | op a b | op a b | mo a b | mo a b | sx lo n e | sx kk i n]; try discriminate.
  - injection H as <- <-. pose proof (Z.mod_pos_bound (w mod two64) 4096 ltac:(lia)). lia.
  - destruct op; try discriminate. destruct a as [w | v | op' a1 a2 | op' a1 a2 | mo a1 a2 | mo a1 a2 | sx lo n e | sx kk i n]; try discriminate.
    destruct mo; try discriminate. destruct a1 as [m | v | op' a3 a4 | op' a3 a4 | mo a3 a4 | mo a3 a4 | sx lo n e | sx kk i n]; try discriminate.
    destruct b as [c' | v | op' a3 a4 | op' a3 a4 | mo' a3 a4 | mo' a3 a4 | sx lo n e | sx kk i n]; try discriminate.
    destruct (Z.eqb_spec m 4096); [|discriminate]. destruct (Z.leb_spec 0 c'); [|discriminate]. destruct (Z.ltb_spec c' 4096); [|discriminate].
    injection H as <- <-. lia.
  - destruct mo; try discriminate. destruct a as [m | v | op' a1 a2 | op' a1 a2 | mo a1 a2 | mo a1 a2 | sx lo n e | sx kk i n]; try discriminate.
    destruct (Z.eqb_spec m 4096); [|discriminate]. injection H as <- <-. lia.
Qed.

(* [comment removed for export] *)
Lemma decode_W_val : forall E We Se c,
  MN2.decode_W We = Some (Se, c) -> 0 <= uE E Se < 2 ^ 51 ->
  uE E We = 4096 * uE E Se + c.
Proof.
  intros E We Se c H HS. pose proof (decode_W_lit We Se c H) as Hc. unfold MN2.decode_W in H. unfold uE in *.
  destruct We as [w | v | op a b | op a b | mo a b | mo a b | sx lo n e | sx kk i n]; try discriminate.
  - injection H as <- <-. rewrite !edenot_lit, !u_lit64a. unfold two64.
    pose proof (Z.mod_pos_bound w (2 ^ 64) ltac:(lia)) as Hw.
    rewrite (Z.mod_small (w mod 2 ^ 64 / 4096)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (Z_div_mod_eq_full (w mod 2 ^ 64) 4096). lia.
  - destruct op; try discriminate. destruct a as [w | v | op' a1 a2 | op' a1 a2 | mo a1 a2 | mo a1 a2 | sx lo n e | sx kk i n]; try discriminate.
    destruct mo; try discriminate. destruct a1 as [m | v | op' a3 a4 | op' a3 a4 | mo a3 a4 | mo a3 a4 | sx lo n e | sx kk i n]; try discriminate.
    destruct b as [c' | v | op' a3 a4 | op' a3 a4 | mo' a3 a4 | mo' a3 a4 | sx lo n e | sx kk i n]; try discriminate.
    destruct (Z.eqb_spec m 4096); [|discriminate]. destruct (Z.leb_spec 0 c'); [|discriminate]. destruct (Z.ltb_spec c' 4096); [|discriminate].
    injection H as <- <-. subst m.
    change (edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 4096) a2) (ELit c'))) with
      (alu64 ALU_ADD (mul_div M_MUL (edenot E (ELit 4096)) (edenot E a2)) (edenot E (ELit c'))).
    rewrite u_add64, u_mul64, !edenot_lit, !u_lit64a.
    rewrite (Z.mod_small 4096), (Z.mod_small c') by lia. rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. lia.
  - destruct mo; try discriminate. destruct a as [m | v | op' a1 a2 | op' a1 a2 | mo a1 a2 | mo a1 a2 | sx lo n e | sx kk i n]; try discriminate.
    destruct (Z.eqb_spec m 4096); [|discriminate]. injection H as <- <-. subst m.
    change (edenot E (EMd M_MUL (ELit 4096) b)) with (mul_div M_MUL (edenot E (ELit 4096)) (edenot E b)).
    rewrite u_mul64, edenot_lit, u_lit64a. rewrite (Z.mod_small 4096) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma w_fields : forall S c, 0 <= c < 4096 -> 0 <= S ->
  w_maplen (4096 * S + c) = S /\ w_lastidx (4096 * S + c) = c mod 32 /\ w_sizeclass (4096 * S + c) = (c / 64) mod 64.
Proof.
  intros S c Hc HS. unfold w_maplen, w_lastidx, w_sizeclass.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split; [nia|]. split; nia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma len_eqb_sound' : forall segs E M k n m,
  know_ok segs E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros segs E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound segs E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound segs E M k _ _ HK H2) as B1.
    cbn [xt_den] in A1, B1. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma add_lit_word : forall (x : word) (c v : Z),
  0 <= bv_unsigned x + c < 2 ^ 64 -> v = bv_unsigned x + c -> (Z_to_bv 64 v : word) = alu64 ALU_ADD x (Z_to_bv 64 c).
Proof.
  intros x c v Hr ->. apply bv_eq. rewrite u_add64, (u_lit64a c), u_small by lia.
  rewrite Z.add_mod_idemp_r by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma find_slot_in : forall k pa ss s,
  MN2.find_slot k pa ss = Some s ->
  In s ss /\ exists a1 a2 a3 a4 a5 a6 p, s = [a1; a2; a3; a4; a5; a6; p] /\ (expr_eqb p pa = true \/ len_eqb k p pa = true).
Proof.
  intros k pa ss. induction ss as [|x rest IH]; intros s H; [discriminate|].
  cbn [MN2.find_slot] in H.
  destruct x as [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|p7 [|]]]]]]]];
    try (destruct (IH s H) as [Hin Hex]; split; [right; exact Hin | exact Hex]).
  destruct (expr_eqb p7 pa || len_eqb k p7 pa)%bool eqn:Hb.
  - injection H as <-. split; [left; reflexivity|]. exists a1, a2, a3, a4, a5, a6, p7. split; [reflexivity|].
    apply orb_prop in Hb. exact Hb.
  - destruct (IH s H) as [Hin Hex]. split; [right; exact Hin | exact Hex].
Qed.

Lemma slots_of_in : forall cs s, In s (MN2.slots_of cs) -> exists g, In g (a_props cs) /\ g_id g = MN2.SLOT_ID /\ g_args g = s.
Proof.
  intros cs s H. unfold MN2.slots_of in H. apply in_map_iff in H as (g & Hg & Hin). apply filter_In in Hin as [Hin Hid].
  exists g. split; [exact Hin|]. split; [apply Nat.eqb_eq; exact Hid | exact Hg].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  Context {fx : FPState}.
  Variable ip : imgparams.
  #[local] Notation SEGS := (ip_segs ip).
  #[local] Notation A := (ip_A ip).
  #[local] Notation MTB := (ip_M ip).
  Variable nx0 : nat.
  Hypothesis NX0_min : APS.nx0_min_ok nx0.   (* [comment removed for export] *)
  Variable LIMIT : Z.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Variable FS0 : Fs.Fs.
  (* [comment removed for export] *)
  Variable GP : nat -> list Z -> (word -> option byte) -> Prop.
  Hypothesis GP50 : forall vs M, GP MN2.SLOT_ID vs M <-> slot_sem SEGS vs M.
  (* [comment removed for export] *)
  Variable G : gparams.
  Hypothesis GPfr : forall id args E M M',
    (forall a, in_fp E (g_fp G id args) a = true -> M' a = M a) -> GP id (map (uE E) args) M -> GP id (map (uE E) args) M'.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
  #[local] Notation MR := (Mr A argH) (only parsing).
  #[local] Notation cfg := (cfg_of SEGS) (only parsing).
  #[local] Notation HID := (hid A argH) (only parsing).

  Hypothesis ENF : ENFRAME_STMT ip.
  Hypothesis FRP : FREEPRO_STMT ip.

  (* [comment removed for export] *)
  Lemma call_core_p : forall (P : (word -> option byte) -> Prop) cs E E' R FULL model T (ret : Z) sr2 k' nx2 ps regs' MR',
    CSOK E cs R FULL model ->
    fresh_ok nx0 cs = true ->
    env_agree (nxt cs) E E' ->
    msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
                (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
    regs_ok E' sr2 regs' ->
    know_ok SEGS E' MR' k' ->
    P MR' ->
    (forall R' FULL' model',
        CSOK E' (set_props (with_ss cs (mk_ss ret sr2 k' nx2)) ps) R' FULL' model' -> m_fs model' = m_fs model ->
        P (MR E' (set_props (with_ss cs (mk_ss ret sr2 k' nx2)) ps) model' FULL') ->
        srealizes SEGS (cfg R' ret FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.
  Proof.
    intros P cs E E' R FULL model T ret sr2 k' nx2 ps regs' MR' HC Hfresh Hag Hms HR' HK' HP Hk.
    destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (H := HID E cs model).
    unfold cfg_of.
    apply (srz_msteps_restricted_T SEGS H
             (w_H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) SEGS_wx (allowA A E cs)
             (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
             (w_lazy_cover_cs SEGS A nx0 LIMIT HULL_ok SINV argH FS0 E cs R FULL model HC)
             (w_A_wf_allowA A nx0 E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC)).
    - rewrite restrict_mkst. exact Hms.
    - intros model' Hinv' Hsame Hclean.
      set (FULL' := munrestrict H FULL MR').
      change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
        with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
      pose proof (w_cs_ok_agree SEGS A nx0 NX0_min LIMIT SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC1.
      pose proof (w_hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
      assert (HMR : MR E' (set_props (with_ss cs (mk_ss ret sr2 k' nx2)) ps) model' FULL' = MR').
      { unfold Mr. rewrite (hid_ext A argH E' cs (set_props (with_ss cs (mk_ss ret sr2 k' nx2)) ps) model' eq_refl).
        rewrite (hid_same A argH E' cs model model' Hsame), HH.
        fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)). reflexivity. }
      apply (Hk regs' FULL' model').
      + apply cs_ok_set_props.
        eapply (w_cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0 E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
        * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
        * exact HR'.
        * reflexivity.
        * cbn [s_know mk_ss]. unfold Mr. rewrite HH. fold H. unfold FULL'.
          rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)). exact HK'.
        * intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
      + apply (same_but_materialized_frame _ _ Hsame).
      + rewrite HMR. exact HP.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_ext_facts : forall E cs R FULL model (val : word) kf,
    CSOK E cs R FULL model -> fresh_ok nx0 cs = true ->
    know_ok SEGS (ext1 E (nxt cs) val) (MR (ext1 E (nxt cs) val) cs model FULL) kf ->
    CSOK (ext1 E (nxt cs) val) (bump (add_kn cs kf) 1) R FULL model.
  Proof.
    intros E cs R FULL model val kf HC Hf HK.
    set (v := nxt cs) in *. set (E' := ext1 E v val) in *.
    assert (Hag : env_agree v E E') by apply ext1_agree.
    pose proof (cs_ok_agree SEGS A nx0 NX0_min LIMIT SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hf HC) as HC'.
    set (cs' := bump (add_kn cs kf) 1).
    assert (HMr : MR E' cs' model FULL = MR E' cs model FULL) by reflexivity.
    assert (HA : allowA A E' cs' = allowA A E' cs) by reflexivity.
    destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
      cbn [bump add_kn set_kn with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_props kn mk_ss s_regs s_log s_know s_pc s_next] in *;
      try assumption; try reflexivity.
    - (* [comment removed for export] *) apply Forall_app. split; [exact HK | exact co_know0].
  Qed.

  (* [comment removed for export] *)
  Lemma keep_props_sound : forall E E' M M' Mk k W nx l,
    props_ok GP E M l -> env_agree nx E E' -> know_ok SEGS E' Mk k ->
    (forall a : word, (forall w, In w W -> bv_unsigned a < estart E' (fst w) \/ estart E' (fst w) + elenZ E' (snd w) <= bv_unsigned a) ->
                      M' a = M a) ->
    props_ok GP E' M' (MN2.keep_props G k W nx l).
  Proof.
    intros E E' M M' Mk k W nx l HP Hag HK Hfr. unfold MN2.keep_props, props_ok in *. apply Forall_forall. intros g Hg.
    apply filter_In in Hg as [Hin Hk1]. unfold MN2.keep1 in Hk1. apply andb_prop in Hk1 as [Hv Hap].
    pose proof (proj1 (Forall_forall _ _) HP g Hin) as G0. apply (proj1 (gholds_agree GP _ E E' M g Hag Hv)) in G0.
    destruct g as [i args]. unfold gholds in *. cbn [g_id g_args] in *.
    eapply GPfr; [|exact G0]. intros a Ha. apply Hfr. intros [wa wl] Hw. cbn [fst snd].
    unfold in_fp in Ha. apply existsb_exists in Ha as ([rb rl] & Hr & Ha). cbn [fst snd] in Ha.
    apply andb_prop in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2.
    pose proof (proj1 (forallb_forall _ _) Hap (rb, rl) Hr) as Hw1. unfold MN2.wapart in Hw1.
    pose proof (proj1 (forallb_forall _ _) Hw1 (wa, wl) Hw) as Hx. cbn [fst snd] in Hx.
    pose proof (ranges_apart_x_sound SEGS E' Mk k (a_base wa) (a_off wa) wl rb 0 rl HK Hx) as X.
    replace (estart E' wa) with (estart E' (SA (a_base wa) (a_off wa))) by (destruct wa; reflexivity). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gpures_sound : forall E E' M M' cs cs',
    props_ok GP E M (a_props cs) -> env_agree (nxt cs) E E' -> props_ok GP E' M' (a_props (gpures G cs cs')).
  Proof.
    intros E E' M M' cs cs' HP Hag. unfold gpures, set_props. cbn [a_props]. unfold nxt in Hag.
    destruct (forallb (gvars_lt (s_next (a_ss cs))) (List.filter (gpure G) (a_props cs))) eqn:Hv; [|constructor].
    unfold props_ok in *. apply Forall_forall. intros g Hg. apply filter_In in Hg as [Hin Hp].
    pose proof (proj1 (Forall_forall _ _) HP g Hin) as G0.
    apply (proj1 (gholds_agree GP _ E E' M g Hag (proj1 (forallb_forall _ _) Hv g ltac:(apply filter_In; split; assumption)))) in G0.
    destruct g as [i args]. unfold gholds in *. cbn [g_id g_args] in *. unfold gpure in Hp. cbn [g_id g_args] in Hp.
    eapply GPfr; [|exact G0]. intros a Ha. destruct (g_fp G i args); [discriminate Ha | discriminate Hp].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rdn1_out_image : forall M (a : word) b,
    (bv_unsigned a < img_lo A \/ img_hi A <= bv_unsigned a) ->
    rdn SEGS M a 1 = Some [b] -> M a = Some b.
  Proof.
    intros M a b Ha H. cbn [rdn] in H.
    destruct (M a) as [b'|] eqn:EM.
    - injection H as ->. reflexivity.
    - unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H. rewrite (SEGS_in_hull a) in H; [discriminate|].
      unfold in_hull. destruct Ha as [Ha|Ha].
      + apply andb_false_iff. left. apply Z.leb_gt. exact Ha.
      + apply andb_false_iff. right. apply Z.ltb_ge. exact Ha.
  Qed.

  Lemma store_ok_defined_out_image : forall M (a : Z) (n : nat),
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall z, a <= z < a + Z.of_nat n -> z < img_lo A \/ img_hi A <= z) ->
    store_ok SEGS M (Z_to_bv 64 a) n = true ->
    forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None.
  Proof.
    intros M a n Ha Han Hout Hso i Hi.
    assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_lit; unfold two64; lia).
    assert (Hui : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply u_lit; unfold two64; lia).
    pose proof (store_ok_all SEGS M n (Z_to_bv 64 a) ltac:(rewrite Hu; lia) Hso (Z_to_bv 64 (a + i)) ltac:(rewrite Hu, Hui; lia)) as W.
    unfold wview in W. destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:HM; [discriminate|].
    rewrite (SEGS_in_hull (Z_to_bv 64 (a + i))) in W; [exact W|].
    unfold in_hull. rewrite Hui. destruct (Hout (a + i) ltac:(lia)) as [Ho|Ho].
    - apply andb_false_iff. left. apply Z.leb_gt. exact Ho.
    - apply andb_false_iff. right. apply Z.ltb_ge. exact Ho.
  Qed.

  (* [comment removed for export] *)
  Lemma apart_hull_out : forall E lo n,
    0 <= lo -> lo + n <= 2 ^ 64 ->
    (estart E (SA (ELit 0) (img_lo A)) + elenZ E (ELit (img_hi A - img_lo A)) <= lo
     \/ lo + n <= estart E (SA (ELit 0) (img_lo A))) ->
    forall z, lo <= z < lo + n -> z < img_lo A \/ img_hi A <= z.
  Proof.
    intros E lo n Hlo Hn DJ z Hz.
    unfold estart in DJ. cbn [a_base a_off] in DJ. unfold elenZ in DJ. rewrite !edenot_lit, !u_lit64a, (Z.mod_small 0) in DJ by lia.
    pose proof HULL_ok as HU. unfold hull_ok, KHI in HU. destruct HU as (HU0 & _ & _ & HU3).
    destruct (Z_lt_le_dec (img_hi A) (img_lo A)) as [Hhl|Hhl]; [lia|].
    rewrite Z.mod_small in DJ by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma inside_maps_witness : forall k ms b off len,
    inside_maps k ms b off len = true ->
    exists m, In m ms /\ is_fog m = false /\ xinside k b off len (am_base m) 0 (am_len m) = true.
  Proof.
    intros k ms b off len. induction ms as [|m ms IH]; cbn [inside_maps]; intros H; [discriminate|].
    apply orb_prop in H as [H|H].
    - apply andb_prop in H as [Hnf H]. apply negb_true_iff in Hnf. exists m. split; [left; reflexivity|]. split; assumption.
    - destruct (IH H) as (m' & Hin & Hnf & Hx). exists m'. split; [right; exact Hin|]. split; assumption.
  Qed.

  Lemma inside_maps_below_top : forall E cs R FULL model b off len,
    CSOK E cs R FULL model ->
    inside_maps (kn cs) (a_maps cs) b off len = true ->
    estart E (SA b off) + elenZ E len <= bv_unsigned (edenot E e_sp0) - STK_BELOW.
  Proof.
    intros E cs R FULL model b off len HC H.
    destruct (inside_maps_witness _ _ _ _ _ H) as (m & Hin & Hnf & Hx).
    pose proof HC as HK. apply co_know in HK.
    pose proof HC as HM. apply co_maps in HM.
    pose proof HC as HB. apply co_bounds in HB.
    pose proof HC as HI. apply co_isp in HI.
    pose proof (xinside_sound SEGS E _ (kn cs) b off len (am_base m) 0 (am_len m) HK Hx) as [I1 I2].
    pose proof (maps_match_In E (a_maps cs) _ m HM Hin Hnf) as Hin'.
    pose proof (proj1 (Forall_forall _ _) HB _ Hin') as (_ & _ & _ & BT & _). cbn [amap_den fst snd] in BT.
    unfold alloc_top in BT. rewrite HI, stack_max_size_val in BT. unfold STK_BELOW.
    unfold estart in I1, I2 |- *. cbn [a_base a_off] in I1, I2 |- *. unfold elenZ in I1, I2 |- *. lia.
  Qed.

  Theorem node_enframe2_sound : forall args cs cs' E R FULL model T,
    CSOK E cs R FULL model ->
    props_ok GP E (MR E cs model FULL) (a_props cs) ->
    MN2.node_enframe2 SEGS A nx0 MTB G cs args = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' ->
        props_ok GP E' (MR E' cs' model' FULL') (a_props cs') -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.
  Proof.
    intros args cs cs' E R FULL model T HC HPR Hn Hk.
    pose proof HC as HKN. apply co_know in HKN.
    set (M := MR E cs model FULL) in *.
    unfold MN2.node_enframe2, MN2.res_opt, MN2.node_enframe2r in Hn.
    destruct (Z.eqb (pc cs) (mt_enframe MTB)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (reg_lit cs 11) as [idx|] eqn:H11; [|discriminate].
    destruct (reg_lit cs 13) as [ctr|] eqn:H13; [|discriminate].
    destruct (split_lit (reg cs 10)) as [Gb gk] eqn:HsplG.
    destruct (kread8e SEGS (kn cs) Gb (gk + 16)) as [Me|] eqn:HMe; [|discriminate].
    destruct (kread8e SEGS (kn cs) Gb (gk + 32)) as [We|] eqn:HWe; [|discriminate].
    destruct (MN2.decode_W We) as [[Se c]|] eqn:Hdec; [|discriminate].
    cbv zeta in Hn.
    set (li := c mod 32) in Hn. set (sc := (c / 64) mod 64) in Hn.
    set (stl := MN2.stride_lit Se li sc) in Hn.
    set (ste := MN2.stride_e Se stl) in Hn.
    set (si := MN2.si_of stl idx) in Hn.
    destruct (split_lit Me) as [Mb Mk] eqn:HsplM.
    set (sk := Mk + 16 + si) in Hn.
    set (e_e := mkAlu ALU_ADD (eaddz Mb (sk - 4)) ste) in Hn.
    destruct (split_lit e_e) as [eb ek] eqn:HsplE.
    set (hlen := mkAlu ALU_ADD ste (ELit (-1))) in Hn.
    destruct (MN.kz SEGS (kn cs) Mb (sk - 4) 1) as [z4|] eqn:Hz4; [|discriminate].
    destruct (MN.kz SEGS (kn cs) eb ek 1) as [zend|] eqn:Hzend; [|destruct (MN.kz SEGS (kn cs) Mb (sk - 3) 1); discriminate].
    cbv zeta in Hn.
    destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
    destruct (xlo (kn cs) Se) as [Slo|] eqn:HSlo; [|discriminate].
    destruct (xhi (kn cs) Se) as [Shi|] eqn:HShi; [|discriminate].
    destruct (xlo (kn cs) Mb) as [mlo|] eqn:Hmlo; [|discriminate].
    destruct (xhi (kn cs) Mb) as [mhi|] eqn:Hmhi; [|discriminate].
    destruct (xlo (kn cs) Gb) as [glo|] eqn:Hglo; [|discriminate].
    destruct (xhi (kn cs) Gb) as [ghi|] eqn:Hghi; [|discriminate].
    destruct (xlo (kn cs) eb) as [elo|] eqn:Helo; [|discriminate].
    destruct (xhi (kn cs) eb) as [ehi|] eqn:Hehi; [|discriminate].
    set (shi := MN2.sbound stl Shi) in Hn.
    set (slo := MN2.sbound stl Slo) in Hn.
    set (v := nxt cs) in Hn.
    set (p := mkAlu ALU_ADD (eaddz Mb sk) (MN2.times16 (EVar v))) in Hn.
    set (pn := mkAlu ALU_ADD p (reg cs 12)) in Hn.
    set (r4 := mkAlu ALU_SUB ste (mkAlu ALU_ADD (reg cs 12) (MN2.times16 (EVar v)))) in Hn.
    set (len1 := mkAlu ALU_ADD (MN2.times16 (EVar v)) (ELit 3)) in Hn.
    set (len2 := mkAlu ALU_ADD r4 (ELit (-4))) in Hn.
    set (kf := [KRange (EVar v) 0 (Z.min 255 ((shi - 4 - nlo) / 16)); KRange r4 4 (shi - nlo)]) in Hn.
    set (sargs := MN2.slot_args (eaddz Mb sk) ste (reg cs 12) (EVar v) We idx p) in Hn.
    match type of Hn with context [if ?cnd then _ else MN2.RConj _] => destruct cnd eqn:Hcond; [|discriminate] end.
    unfold MN2.all_true in Hcond. cbn [fold_right] in Hcond.
    apply andb_prop in Hcond as [C1 Hcond]. apply andb_prop in Hcond as [C2 Hcond]. apply andb_prop in Hcond as [C3 Hcond]. apply andb_prop in Hcond as [C4 Hcond].
    apply andb_prop in Hcond as [C5 Hcond]. apply andb_prop in Hcond as [C6 Hcond]. apply andb_prop in Hcond as [C7 Hcond]. apply andb_prop in Hcond as [C8 Hcond].
    apply andb_prop in Hcond as [C9 Hcond]. apply andb_prop in Hcond as [C10 Hcond]. apply andb_prop in Hcond as [C11 Hcond]. apply andb_prop in Hcond as [C12 Hcond].
    apply andb_prop in Hcond as [C13 Hcond]. apply andb_prop in Hcond as [C14 Hcond]. apply andb_prop in Hcond as [C15 Hcond]. apply andb_prop in Hcond as [C16 Hcond].
    apply andb_prop in Hcond as [C17 Hcond]. apply andb_prop in Hcond as [C18 Hcond]. apply andb_prop in Hcond as [C19 Hcond]. apply andb_prop in Hcond as [CE1 Hcond].
    apply andb_prop in Hcond as [CE2 Hcond]. apply andb_prop in Hcond as [C20 Hcond]. apply andb_prop in Hcond as [C21 Hcond]. apply andb_prop in Hcond as [C22 Hcond].
    apply andb_prop in Hcond as [C23 Hcond]. apply andb_prop in Hcond as [C24 Hcond]. apply andb_prop in Hcond as [C25 Hcond]. apply andb_prop in Hcond as [C26 Hcond].
    apply andb_prop in Hcond as [C27 Hcond]. apply andb_prop in Hcond as [C28 Hcond]. apply andb_prop in Hcond as [C29 Hcond]. apply andb_prop in Hcond as [C30 _].
    apply Z.eqb_eq in C3. apply Z.eqb_eq in C4. apply Z.leb_le in C5. apply Z.ltb_lt in C6. apply Z.leb_le in C7.
    apply Z.leb_le in C8. apply Z.leb_le in C9. apply Z.ltb_lt in C10. apply Z.leb_le in C11. apply Z.leb_le in C12.
    apply Z.leb_le in C14. apply Z.leb_le in C16. apply Z.ltb_lt in C17. apply Z.leb_le in C18. apply Z.ltb_lt in C19.
    unfold two64 in C17, C19. apply Z.leb_le in CE1. apply Z.ltb_lt in CE2. unfold two64 in CE2.   (* [comment removed for export] *)
    set (cs1 := bump (add_kn cs kf) 1) in Hn.
    set (k3 := KUnk (SA Mb (sk - 3)) len1 :: KUnk (SA pn 0) len2 :: KUnk (SA Mb (sk - 3)) hlen :: kn_havoc (kn_havoc (kn cs1) Mb (sk - 3) len1) pn 0 len2) in Hn.
    destruct (after_call nx0 cs1 ret (Some p) k3) as [csa|] eqn:Hac; [|discriminate].
    cbv beta iota in Hn. injection Hn as <-.
    assert (Estl : stl = MN2.stride_lit Se li sc) by reflexivity. assert (Este : ste = MN2.stride_e Se stl) by reflexivity.
    assert (Esi0 : si = MN2.si_of stl idx) by reflexivity.
    assert (Eshi : shi = MN2.sbound stl Shi) by reflexivity. assert (Eslo : slo = MN2.sbound stl Slo) by reflexivity.
    clearbody stl ste si shi slo.
    (* [comment removed for export] *)
    destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
    destruct (w_reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 idx HC ltac:(lia) H11) as [R11 _].
    destruct (w_reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 13 ctr HC ltac:(lia) H13) as [R13 Hctr].
    pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
    pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 HC ltac:(lia)) as R12.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN HSlo) as HSlo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN HShi) as HShi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hmlo) as Hmlo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hmhi) as Hmhi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hglo) as Hglo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hghi) as Hghi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Helo) as Helo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hehi) as Hehi'.
    set (gw := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *.
    set (ug := bv_unsigned (edenot E Gb)) in *. set (um := bv_unsigned (edenot E Mb)) in *. set (n := bv_unsigned nw) in *.
    set (Sm := bv_unsigned (edenot E Se)) in *. set (ue := bv_unsigned (edenot E eb)) in *.
    pose proof (w_split_lit_denot E (reg cs 10) Gb gk HsplG) as HGd. fold gw in HGd. fold ug in HGd.
    pose proof (w_split_lit_denot E Me Mb Mk HsplM) as HMd. fold um in HMd.
    set (g := ug + gk) in *. set (Mv := um + Mk) in *. set (start := um + sk).
    assert (Eg : g = ug + gk) by reflexivity. assert (EMv : Mv = um + Mk) by reflexivity. assert (Est : start = um + sk) by reflexivity.
    clearbody g Mv start.
    assert (Hnb : nlo <= n <= nhi) by (subst n; lia).
    assert (HSb : Slo <= Sm <= Shi) by (subst Sm; lia).
    pose proof (u64_range (edenot E Gb)) as Hugr. fold ug in Hugr. pose proof (u64_range (edenot E Mb)) as Humr. fold um in Humr.
    pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range (edenot E Se)) as HSr. fold Sm in HSr.
    pose proof (u64_range (edenot E eb)) as Huer. fold ue in Huer. fold ue in Helo', Hehi'.
    (* [comment removed for export] *)
    pose proof (decode_W_lit We Se c Hdec) as Hc.
    pose proof (decode_W_val E We Se c Hdec ltac:(unfold uE; fold Sm; lia)) as HWv. unfold uE in HWv. fold Sm in HWv.
    set (W := 4096 * Sm + c) in *.
    destruct (w_fields Sm c Hc ltac:(lia)) as (Fml & Fli & Fsc). fold W in Fml, Fli, Fsc. fold li in Fli. fold sc in Fsc.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LITW : forall m, Se = ELit m -> Sm = m mod two64).
    { intros m Hm. subst Sm. rewrite Hm, edenot_lit, u_lit64a. reflexivity. }
    assert (CASES : (exists m, Se = ELit m /\ stl = Some (slot_stride Sm li sc))
                    \/ (stl = None /\ li = 0 /\ idx = 0 /\ 1 <= Slo)).
    { rewrite Estl. unfold MN2.stride_lit. unfold MN2.single_ok in C1. unfold MN2.sc_ok in C2. rewrite Estl in C1.
      destruct Se as [m | vv | op a b | op a b | mo a b | mo a b | sx lo0 n0 e0 | sx kk i0 n0];
        [left; exists m; split; [reflexivity | rewrite (LITW m eq_refl); reflexivity] | ..];
        (right; cbn in C1; apply andb_prop in C1 as [L0 L1]; apply Z.eqb_eq in L0; apply Z.eqb_eq in L1; apply Z.leb_le in C2; repeat split; assumption). }
    set (st := match stl with Some z => z | None => 4096 * Sm - 16 end).
    assert (Hst : slo <= st <= shi /\ 16 <= st < 2 ^ 31).
    { subst st shi slo. destruct CASES as [(m & HSe & Hstl)|(Hstl & L0 & L1 & LS)]; rewrite Hstl in *; cbn [MN2.sbound] in *; lia. }
    assert (Hstride : st = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)).
    { rewrite Fml, Fli, Fsc. subst st. destruct CASES as [(m & HSe & Hstl)|(Hstl & L0 & L1 & LS)]; rewrite Hstl; [reflexivity|].
      unfold slot_stride, UNIT. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec Sm 0); [lia | cbn; lia]. }
    assert (Hsc' : (w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48).
    { rewrite Fml, Fli, Fsc. intros X. unfold MN2.sc_ok in C2.
      destruct CASES as [(m & HSe & Hstl)|(Hstl & L0 & L1 & LS)].
      - rewrite HSe in C2. rewrite <- (LITW m HSe) in C2. apply Bool.orb_prop in C2 as [C2|C2].
        + exfalso. apply Bool.negb_true_iff in C2. apply Bool.orb_false_iff in C2 as [Y1 Y2]. apply Z.eqb_neq in Y1.
          apply Bool.negb_false_iff in Y2. apply Z.eqb_eq in Y2. lia.
        + apply Z.ltb_lt in C2. exact C2.
      - exfalso. lia. }
    assert (Hsd16 : st mod 16 = 0).
    { rewrite Hstride. unfold slot_stride, UNIT. destruct (negb (w_maplen W =? 0) && (w_lastidx W =? 0))%bool.
      - replace (w_maplen W * 4096 - 16) with ((w_maplen W * 256 - 1) * 16) by lia. apply Z_mod_mult.
      - rewrite Z.mul_comm. apply Z_mod_mult. }
    assert (Hsi : si = st * idx /\ 0 <= si /\ si mod 16 = 0).
    { assert (Esi : si = st * idx).
      { rewrite Esi0. subst st. unfold MN2.si_of. destruct CASES as [(m & HSe & Hstl)|(Hstl & L0 & L1 & LS)]; rewrite Hstl; [reflexivity | subst idx; lia]. }
      split; [exact Esi|]. split; [rewrite Esi; apply Z.mul_nonneg_nonneg; lia|].
      rewrite Esi, Zmult_mod, Hsd16. reflexivity. }
    destruct Hsi as (Esi & Hsi0 & Hsi16).
    (* [comment removed for export] *)
    assert (Dste : forall E1, edenot E1 Se = edenot E Se -> bv_unsigned (edenot E1 ste) = st).
    { intros E1 HE1. rewrite Este. subst st. unfold MN2.stride_e. destruct stl as [z|].
      - rewrite edenot_lit. apply u_small. lia.
      - rewrite mkAlu_denot, u_add64, mkMd_denot, u_mul64, !edenot_lit, !u_lit64a, HE1. fold Sm.
        rewrite (Z.mod_small 4096) by lia. rewrite (Z.mod_small (4096 * Sm)) by lia.
        replace ((-16) mod 2 ^ 64) with (2 ^ 64 - 16) by reflexivity.
        replace (4096 * Sm + (2 ^ 64 - 16)) with ((4096 * Sm - 16) + 1 * 2 ^ 64) by lia.
        rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    assert (Dhlen : forall E1, edenot E1 Se = edenot E Se -> elenZ E1 hlen = st - 1).
    { intros E1 HE1. unfold elenZ. subst hlen. rewrite mkAlu_denot, u_add64, (Dste E1 HE1), edenot_lit, u_lit64a.
      replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
      replace (st + (2 ^ 64 - 1)) with ((st - 1) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    (* [comment removed for export] *)
    assert (ESTG : forall k, estart E (SA Gb k) = ug + k) by (intros; reflexivity).
    assert (ESTM : forall k, estart E (SA Mb k) = um + k) by (intros; reflexivity).
    assert (ESTE : forall k, estart E (SA eb k) = ue + k) by (intros; reflexivity).
    (* [comment removed for export] *)
    assert (OFF : forall z, start - 4 <= z < start - 4 + st -> z < img_lo A \/ img_hi A <= z).
    { apply Bool.orb_prop in C21. destruct C21 as [C21|C21].
      - apply Z.leb_le in C21. intros z Hz. right. subst start. lia.
      - pose proof (ranges_apart_x_sound SEGS E M (kn cs) (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) Mb (sk - 4)
                      (mkAlu ALU_ADD hlen (ELit 1)) HKN C21) as DJ.
        rewrite ESTM in DJ.
        assert (LS : elenZ E (mkAlu ALU_ADD hlen (ELit 1)) = st).
        { unfold elenZ. rewrite mkAlu_denot, u_add64, edenot_lit, u_lit64a.
          change (bv_unsigned (edenot E hlen)) with (elenZ E hlen). rewrite (Dhlen E eq_refl).
          rewrite (Z.mod_small 1) by lia. replace (st - 1 + 1) with st by lia. apply Z.mod_small. lia. }
        rewrite LS in DJ. subst start.
        intros z Hz. apply (apart_hull_out E (um + (sk - 4)) st); [lia | lia | exact DJ | lia]. }
    pose proof (kread8e_rdn SEGS E M (kn cs) Gb (gk + 32) We HKN HWe ltac:(unfold flat; rewrite ESTG; lia)) as RW.
    rewrite adenot_SA, ESTG in RW.
    replace (edenot E We) with (Z_to_bv 64 W : word) in RW by (rewrite <- HWv; apply Z_to_bv_bv_unsigned).
    pose proof (kread8e_rdn SEGS E M (kn cs) Gb (gk + 16) Me HKN HMe ltac:(unfold flat; rewrite ESTG; lia)) as RM.
    rewrite adenot_SA, ESTG, HMd in RM.
    destruct (kreadZ_rdn SEGS E M (kn cs) Mb (sk - 4) 1 z4 HKN Hz4 ltac:(lia) ltac:(unfold flat; rewrite ESTM; cbn [Z.of_nat]; lia)) as (R4 & _ & _).
    rewrite adenot_SA, ESTM, C3, N_to_le_bytes_1_small in R4.
    apply rdn1_out_image in R4; [| rewrite u_lit by (unfold two64; lia); apply OFF; lia].
    (* [comment removed for export] *)
    pose proof (w_split_lit_denot E e_e eb ek HsplE) as HEd. fold ue in HEd.
    assert (Ee : start + st - 4 = ue + ek).
    { assert (X : bv_unsigned (edenot E e_e) = start + st - 4).
      { subst e_e. rewrite mkAlu_denot, u_add64, edenot_eaddz, u_lit64a, (Dste E eq_refl). fold um.
        rewrite (Z.mod_small (um + (sk - 4))) by lia. subst start. rewrite Z.mod_small by lia. lia. }
      rewrite HEd, u_small in X by lia. lia. }
    destruct (kreadZ_rdn SEGS E M (kn cs) eb ek 1 zend HKN Hzend ltac:(lia) ltac:(unfold flat; rewrite ESTE; cbn [Z.of_nat]; lia)) as (RE & _ & _).
    rewrite adenot_SA, ESTE, C4, N_to_le_bytes_1_small, <- Ee in RE.
    (* [comment removed for export] *)
    pose proof (kimg_cover_none SEGS E M (kn cs) _ _ HKN C23) as TBL.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) Mb (sk - 3) hlen HKN HKN C20) as (WST & _ & _).
    rewrite ESTM, (Dhlen E eq_refl) in WST.
    (* [comment removed for export] *)
    assert (HDR : exists h3 o16, 0 <= h3 < 256 /\ 0 <= o16 < 65536 /\ M (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 h3)
                  /\ (h3 <> 0 -> rdn SEGS M (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 o16)) /\ 0 <= o16 < 65536)).
    { pose proof (store_ok_defined_out_image M (start - 3) 3%nat ltac:(subst start; lia) ltac:(subst start; cbn [Z.of_nat]; lia) ltac:(intros z Hz; apply OFF; cbn [Z.of_nat] in Hz; lia)
                    ltac:(subst start; replace (um + sk - 3) with (um + (sk - 3)) by lia; apply WST; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as DEF.
      destruct (M (Z_to_bv 64 (start - 3))) as [b3|] eqn:HB3; [|exfalso; apply (DEF 0 ltac:(cbn; lia)); rewrite Z.add_0_r; exact HB3].
      destruct (M (Z_to_bv 64 (start - 2))) as [b2|] eqn:HB2; [|exfalso; apply (DEF 1 ltac:(cbn; lia)); replace (start - 3 + 1) with (start - 2) by lia; exact HB2].
      destruct (M (Z_to_bv 64 (start - 1))) as [b1|] eqn:HB1; [|exfalso; apply (DEF 2 ltac:(cbn; lia)); replace (start - 3 + 2) with (start - 1) by lia; exact HB1].
      exists (bv_unsigned b3), (bytes_le_to_Z [b2; b1]).
      pose proof (u8_range b3). pose proof (bytes_le_to_Z_bound [b2; b1]) as Hb. change (2 ^ (8 * Z.of_nat (length [b2; b1]))) with 65536 in Hb.
      split; [lia|]. split; [lia|]. split; [rewrite Z_to_bv_bv_unsigned; reflexivity|]. intros _. split; [|lia].
      cbn [rdn]. rewrite HB2.
      rewrite (w_add_1 (Z_to_bv 64 (start - 2))), (u_lit (start - 2)) by (unfold two64; subst start; lia).
      replace (start - 2 + 1) with (start - 1) by lia.
      rewrite HB1. f_equal. symmetry. exact (word_to_le_bytes_extz false 2 [b2; b1] eq_refl ltac:(lia) ltac:(lia)). }
    destruct HDR as (h3 & o16 & Hh3r & Ho16r & R3 & R2). clear C30.
    pose proof (ranges_apart_x_sound SEGS E M (kn cs) Gb (gk + 16) (ELit 24) Mb (sk - 3) hlen HKN C22) as DISJ.
    rewrite ESTG, ESTM, (Dhlen E eq_refl) in DISJ. change (elenZ E (ELit 24)) with 24 in DISJ.
    pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN C15) as LIN. cbn [xt_den] in LIN.
    rewrite (Dste E eq_refl) in LIN. fold nw n in LIN.
    destruct (ealign_sound SEGS E M (kn cs) Me HKN) as [_ [qa Hqa]].
    assert (HMv64 : bv_unsigned (edenot E Me) = Mv).
    { rewrite HMd. subst Mv. apply u_small. lia. }
    assert (Hst16 : start mod 16 = 0).
    { rewrite HMv64 in Hqa. assert (H16 : (16 | 2 ^ ealign (kn cs) Me)).
      { exists (2 ^ (ealign (kn cs) Me - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      destruct H16 as [t Ht]. subst start sk Mv.
      rewrite Hqa in *. replace (um + (Mk + 16 + si)) with ((qa * 2 ^ ealign (kn cs) Me) + 16 + si) by lia.
      rewrite Ht. rewrite Z.add_mod, (Z.add_mod (qa * (t * 16)) 16) by lia.
      replace (qa * (t * 16)) with ((qa * t) * 16) by lia. rewrite Z_mod_mult, Hsi16. reflexivity. }
    (* [comment removed for export] *)
    set (off0 := (if h3 =? 0 then ctr mod two64 else o16 + 1) mod 256).
    set (offv := enframe_off (slack_of st n) off0).
    assert (Hoff0 : 0 <= off0 < 256) by (subst off0; apply Z.mod_pos_bound; lia).
    assert (Hslk : 0 <= slack_of st n <= (shi - 4 - nlo) / 16).
    { unfold slack_of, IB, UNIT. split; [apply Z.div_pos; (first [solve [try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - LIN Esi Hst Hc Hnb Est Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as LIN; try pose proof I as __sat79; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - LIN __sat79 heq_sk Esi Hst Hc Hnb Est Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia]) | apply Z.div_le_mono; (first [solve [try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - LIN Esi Hst Hc Hnb Est Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as LIN; try pose proof I as __sat79; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - LIN __sat79 heq_sk Esi Hst Hc Hnb Est Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia])]. }
    assert (Hoffr : 0 <= offv <= slack_of st n) by (subst offv; apply enframe_off_le; lia).
    assert (Hoff255 : offv <= 255) by (subst offv; apply enframe_off_255; lia).
    assert (Hoff16 : 16 * offv + n + 4 <= st).
    { pose proof (Z.mul_div_le (st - 4 - n) 16 ltac:(lia)). unfold slack_of, IB, UNIT in Hoffr. (first [solve [try pose proof I as H; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - H Hoffr LIN Esi Hst Fml Hc HSr Hnb Est Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as heq_sk; try pose proof I as heq_offv; try pose proof I as H; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat272 heq_sk heq_offv H Hoffr LIN Esi Hst Fml Hc HSr Hnb Est Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia]). }
    set (E1 := ext1 E v (Z_to_bv 64 offv)).
    assert (Hag1 : env_agree v E E1) by apply ext1_agree.
    assert (Hv1 : bv_unsigned (edenot E1 (EVar v)) = offv).
    { cbn [edenot]. unfold E1. rewrite ext1_at. apply u_small. lia. }
    assert (AG : forall e, expr_vars_lt v e = true -> edenot E1 e = edenot E e).
    { intros e He. symmetry. exact (edenot_agree' v E E1 e Hag1 He). }
    pose proof (split_lit_vars (reg cs 10) Gb gk v HsplG C27) as VGb. pose proof (split_lit_vars Me Mb Mk v HsplM C24) as VMb.
    destruct (w_fresh_ok_parts nx0 cs C13) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle). fold v in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle.
    assert (D1ste : bv_unsigned (edenot E1 ste) = st) by (apply Dste; apply AG; exact C28).
    assert (D1n : bv_unsigned (edenot E1 (reg cs 12)) = n) by (rewrite (AG _ C25); reflexivity).
    assert (D1off16 : bv_unsigned (edenot E1 (MN2.times16 (EVar v))) = 16 * offv).
    { unfold MN2.times16. rewrite mkMd_denot, u_mul64, edenot_lit, u_lit64a, Hv1. rewrite (Z.mod_small 16) by lia. apply Z.mod_small. (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - Hoff16 Hoffr LIN Esi Hst Fml Hc HSr Hnr Hnb Est Hglo' Hmlo' C18 C16 C14 C12 C10 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - __sat271 heq_sk Hoff16 Hoffr LIN Esi Hst Fml Hc HSr Hnr Hnb Est Hglo' Hmlo' C18 C16 C14 C12 C10 C5; xlia zchecker] | lia]). }
    assert (D1r4 : bv_unsigned (edenot E1 r4) = st - n - 16 * offv).
    { subst r4. rewrite mkAlu_denot, u_sub64, D1ste, mkAlu_denot, u_add64, D1n, D1off16.
      rewrite (Z.mod_small (n + 16 * offv)) by (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; clear - Hoff16 Hoffr LIN; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as heq_offv; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; clear - __sat271 heq_sk heq_offv Hoff16 Hoffr LIN; xlia zchecker] | lia]). rewrite Z.mod_small by (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; clear - Hoff16 Hoffr Hst Hc Hnr Hnb C14 C12 C10; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; clear - __sat271 Hoff16 Hoffr Hst Hc Hnr Hnb C14 C12 C10; xlia zchecker] | lia]). lia. }
    assert (D1p : edenot E1 p = Z_to_bv 64 (start + 16 * offv)).
    { subst p. rewrite mkAlu_denot. apply bv_eq. rewrite u_add64, edenot_eaddz, (AG _ VMb), u_lit64a, D1off16, u_lit64a. fold um. subst start.
      rewrite (Z.mod_small (um + sk)) by (first [solve [try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - DISJ Esi Hst Hc Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat271 heq_sk DISJ Esi Hst Hc Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C12 C5; xlia zchecker] | lia]). rewrite !Z.mod_small by (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - Hoff16 Hoffr DISJ Esi Hst Hc Hnr Hnb Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - __sat271 heq_sk Hoff16 Hoffr DISJ Esi Hst Hc Hnr Hnb Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C5; xlia zchecker] | lia]). reflexivity. }
    assert (D1hlen : elenZ E1 hlen = st - 1) by (apply Dhlen; apply AG; exact C28).
    assert (D1len1 : elenZ E1 len1 = 16 * offv + 3).
    { unfold elenZ. subst len1. rewrite mkAlu_denot, u_add64, D1off16, edenot_lit, u_lit64a.
      rewrite (Z.mod_small 3) by lia. rewrite Z.mod_small by (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - Hoff16 Hoffr LIN Esi Hst Fml Hc HSr Hnr Hnb Est Hglo' Hmlo' C18 C16 C14 C12 C10 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - __sat271 heq_sk Hoff16 Hoffr LIN Esi Hst Fml Hc HSr Hnr Hnb Est Hglo' Hmlo' C18 C16 C14 C12 C10 C5; xlia zchecker] | lia]). lia. }
    assert (D1len2 : elenZ E1 len2 = st - n - 16 * offv - 4).
    { unfold elenZ. subst len2. rewrite mkAlu_denot, u_add64, D1r4, edenot_lit, u_lit64a.
      replace ((-4) mod 2 ^ 64) with (2 ^ 64 - 4) by reflexivity.
      replace (st - n - 16 * offv + (2 ^ 64 - 4)) with ((st - n - 16 * offv - 4) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; clear - Hoff16 Hoffr Hst Hc Hnr Hnb C14 C12 C10; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; clear - __sat271 Hoff16 Hoffr Hst Hc Hnr Hnb C14 C12 C10; xlia zchecker] | lia]). }
    (* [comment removed for export] *)
    assert (D1pn : bv_unsigned (edenot E1 pn) = start + 16 * offv + n).
    { subst pn. rewrite mkAlu_denot, u_add64, D1p, u_lit64a, D1n. rewrite (Z.mod_small (start + 16 * offv)) by (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - Hoff16 Hoffr DISJ Esi Hst Hc Hnr Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - __sat271 heq_sk Hoff16 Hoffr DISJ Esi Hst Hc Hnr Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C5; xlia zchecker] | lia]). apply Z.mod_small. (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C9; try pose proof I as C5; clear - Hoff16 Hoffr DISJ Esi Hst Hc Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C9 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C9; try pose proof I as C5; clear - __sat271 heq_sk Hoff16 Hoffr DISJ Esi Hst Hc Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C9 C5; xlia zchecker] | lia]). }
    assert (EST1 : estart E1 (SA Mb (sk - 3)) = um + (sk - 3)).
    { unfold estart. cbn [a_base a_off]. rewrite (AG _ VMb). reflexivity. }
    assert (EST2 : estart E1 (SA pn 0) = start + 16 * offv + n).
    { unfold estart. cbn [a_base a_off]. rewrite D1pn. lia. }
    (* [comment removed for export] *)
    assert (HC1 : CSOK E1 cs1 R FULL model).
    { subst cs1 kf. apply cs_ok_ext_facts; [exact HC | exact C13 |]. fold v. fold E1.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok].
      - rewrite Hv1. (first [solve [try pose proof I as H256; try pose proof I as Hoff16; try pose proof I as Hoff255; try pose proof I as Hoffr; clear - H256 Hoff16 Hoff255 Hoffr; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as H256; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoff255; try pose proof I as Hoffr; clear - __sat272 H256 heq_sk Hoff16 Hoff255 Hoffr; xlia zchecker] | lia]).
      - rewrite D1r4. (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - Hoff16 Hoffr LIN Esi Hst Fml Hc HSr Hnb Est Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat272 heq_sk Hoff16 Hoffr LIN Esi Hst Fml Hc HSr Hnb Est Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia]). }
    assert (HMR1 : MR E1 cs1 model FULL = M).
    { subst M cs1. unfold Mr. rewrite (hid_ext A argH E1 cs (bump (add_kn cs kf) 1) model eq_refl).
      rewrite (w_hid_agree A nx0 argH argH_agree v E E1 cs model Hag1 Fle Fallow). reflexivity. }
    pose proof HC1 as HKN1. apply co_know in HKN1. rewrite HMR1 in HKN1.
    (* [comment removed for export] *)
    assert (EH : efH_g SEGS (mt_sct MTB) M (Z_to_bv 64 ctr) g Mv W idx n h3 o16 st start offv).
    { constructor.
      - exact Hstride.
      - unfold slot_start, UNIT. subst start sk Mv. (first [solve [try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - LIN Esi Hst Hc Hnb Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat271 LIN Esi Hst Hc Hnb Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia]).
      - subst offv off0. rewrite u_lit64. destruct (Z.eqb_spec h3 0); [|reflexivity].
        unfold two64. rewrite (Z.mod_small ctr (2 ^ 64)) by (unfold two64 in Hctr; lia). reflexivity.
      - unfold two64 in *; (first [solve [try pose proof I as LIN; try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Eg; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - LIN DISJ Ee Esi Hst Hc Hnb Est Eg Hehi' Hghi' Hglo' Hmlo' CE2 C19 C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat270; try pose proof I as heq_sk; try pose proof I as LIN; try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Eg; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat270 heq_sk LIN DISJ Ee Esi Hst Hc Hnb Est Eg Hehi' Hghi' Hglo' Hmlo' CE2 C19 C18 C16 C12 C5; xlia zchecker] | lia]).
      - (first [solve [try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as EMv; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C7; try pose proof I as C5; clear - LIN Esi Hst Fli Hc Hnb Est EMv Hglo' Hmlo' C18 C16 C12 C7 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as heq_st; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as EMv; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C7; try pose proof I as C5; clear - __sat271 heq_sk heq_st LIN Esi Hst Fli Hc Hnb Est EMv Hglo' Hmlo' C18 C16 C12 C7 C5; xlia zchecker] | lia]).
      - subst W. (first [solve [try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as HSb; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C11; try pose proof I as C5; clear - LIN Esi Hst Fml Hc HSr HSb Hnb Est Hglo' Hmlo' C18 C16 C12 C11 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as LIN; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as HSb; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C11; try pose proof I as C5; clear - __sat271 heq_sk LIN Esi Hst Fml Hc HSr HSb Hnb Est Hglo' Hmlo' C18 C16 C12 C11 C5; xlia zchecker] | lia]).
      - lia.
      - lia.
      - exact Hsc'.
      - lia.
      - (first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hmlo'; try pose proof I as C16; try pose proof I as C12; try pose proof I as C8; try pose proof I as C7; clear - Esi Hst Fli Hc Est Hmlo' C16 C12 C8 C7; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as heq_st; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hmlo'; try pose proof I as C16; try pose proof I as C12; try pose proof I as C8; try pose proof I as C7; clear - __sat271 heq_sk heq_st Esi Hst Fli Hc Est Hmlo' C16 C12 C8 C7; xlia zchecker] | lia]).
      - unfold two64 in *; (first [solve [try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C12; try pose proof I as C10; clear - Hst Hc Est Hghi' Hmhi' C19 C17 C12 C10; lia] | solve [Zify.zify; try pose proof I as __sat270; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C12; try pose proof I as C10; clear - __sat270 Hst Hc Est Hghi' Hmhi' C19 C17 C12 C10; xlia zchecker] | lia]).
      - subst start. (first [solve [try pose proof I as LIN; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Eg; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - LIN DISJ Esi Hst Hc Hnb Eg Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as LIN; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Eg; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat271 heq_sk LIN DISJ Esi Hst Hc Hnb Eg Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia]).
      - lia.
      - lia.
      - subst g. replace (ug + gk + 16) with (ug + (gk + 16)) by lia. exact RM.
      - subst g. replace (ug + gk + 32) with (ug + (gk + 32)) by lia. exact RW.
      - subst start. replace (um + sk - 4) with (um + (sk - 4)) by lia. exact R4.
      - exact R3.
      - intros Hh. apply R2. exact Hh.
      - subst start. replace (um + sk - 3) with (um + (sk - 3)) by lia. apply WST. lia.
      - intros j0 Hj. apply TBL. lia. }
    (* [comment removed for export] *)
    assert (R13' : getr R 13%bv = Z_to_bv 64 ctr) by (rewrite <- R13; f_equal; apply bv_eq; reflexivity).
    assert (R10' : getr R 10%bv = Z_to_bv 64 g).
    { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite R10. subst g. exact HGd. }
    assert (R11' : getr R 11%bv = Z_to_bv 64 idx) by (rewrite <- R11; f_equal; apply bv_eq; reflexivity).
    assert (R12' : getr R 12%bv = Z_to_bv 64 n).
    { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). rewrite R12. subst n nw. symmetry. apply Z_to_bv_bv_unsigned. }
    assert (R1' : getr R 1%bv = Z_to_bv 64 ret) by (rewrite <- R1; f_equal; apply bv_eq; reflexivity).
    destruct (ENF R M (seg_rom SEGS) (Z_to_bv 64 ret) (Z_to_bv 64 ctr) g Mv W idx n h3 o16 st start offv EH R1' Hrok R10' R11' R12' R13')
      as (regs' & mem' & RUN & KEPT & A0 & FR & PO & FR2).
    rewrite <- Hpc in RUN.
    (* [comment removed for export] *)
    unfold after_call in Hac.
    match type of Hac with context [if ?c0 then _ else _] => destruct c0 eqn:Hacc; [|discriminate] end.
    apply andb_prop in Hacc as [Hacc Hrvv]. apply andb_prop in Hacc as [Hfresh1 Hkv].
    injection Hac as <-.
    destruct (w_fresh_ok_parts nx0 cs1 Hfresh1) as (F1sr & F1kn & F1maps & F1allow & F1brk & F1fd & F1le).
    set (E' := ext_call E1 (nxt cs1) regs').
    pose proof (ext_call_agree E1 (nxt cs1) regs') as Hag'. fold E' in Hag'.
    assert (AG' : forall e, expr_vars_lt (nxt cs1) e = true -> edenot E' e = edenot E1 e).
    { intros e He. symmetry. exact (edenot_agree' (nxt cs1) E1 E' e Hag' He). }
    assert (Hnx1 : nxt cs1 = S v).
    { subst cs1 v. unfold bump, add_kn, set_kn, nxt. cbn [with_ss a_ss s_next mk_ss]. lia. }
    (* [comment removed for export] *)
    destruct FR2 as [FRout FRgrows].
    (* [comment removed for export] *)
    set (Mmid := fun x : word => if ((um + (sk - 3) <=? bv_unsigned x) && (bv_unsigned x <? um + (sk - 3) + (16 * offv + 3)))%bool
                                 then mem' x else M x).
    assert (OUT2 : forall x : word, bv_unsigned x < start + 16 * offv + n \/ start + 16 * offv + n + (st - n - 16 * offv - 4) <= bv_unsigned x -> mem' x = Mmid x).
    { intros x Hx. unfold Mmid. destruct ((um + (sk - 3) <=? bv_unsigned x) && (bv_unsigned x <? um + (sk - 3) + (16 * offv + 3)))%bool eqn:Hb; [reflexivity|].
      apply FRout. cbn [Frame.outside]. unfold Frame.in_rng. rewrite !u_small by (unfold two64 in *; (first [solve [try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as Hb; try pose proof I as Hx; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Hmhi'; try pose proof I as C17; try pose proof I as C14; try pose proof I as C10; try pose proof I as C9; clear - DISJ Ee Esi Hst Hc Est Hehi' Hghi' Hglo' Hmlo' CE2 C19 C18 C16 C12 C5 Hb Hx Hoff16 Hoffr Hnr Hnb Hmhi' C17 C14 C10 C9; lia] | solve [Zify.zify; try pose proof I as __sat270; try pose proof I as heq_sk; try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as Hb; try pose proof I as Hx; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Hmhi'; try pose proof I as C17; try pose proof I as C14; try pose proof I as C10; try pose proof I as C9; clear - __sat270 heq_sk DISJ Ee Esi Hst Hc Est Hehi' Hghi' Hglo' Hmlo' CE2 C19 C18 C16 C12 C5 Hb Hx Hoff16 Hoffr Hnr Hnb Hmhi' C17 C14 C10 C9; xlia zchecker] | lia])).
      apply Bool.andb_false_iff in Hb. destruct Hb as [Hb|Hb]; [apply Z.leb_gt in Hb | apply Z.ltb_ge in Hb]; subst start; repeat split; try exact I; (first [solve [try pose proof I as Hb; try pose proof I as Hx; clear - Hb Hx; lia] | solve [Zify.zify; try pose proof I as Hb; try pose proof I as Hx; clear - Hb Hx; xlia zchecker] | lia]). }
    assert (OUT1 : forall x : word, bv_unsigned x < um + (sk - 3) \/ um + (sk - 3) + (16 * offv + 3) <= bv_unsigned x -> Mmid x = M x).
    { intros x Hx. unfold Mmid. destruct ((um + (sk - 3) <=? bv_unsigned x) && (bv_unsigned x <? um + (sk - 3) + (16 * offv + 3)))%bool eqn:Hb; [|reflexivity].
      apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2. lia. }
    assert (GR1 : mem_grows M Mmid).
    { intros x Hx. unfold Mmid. destruct (_ && _)%bool; [apply FRgrows; exact Hx | exact Hx]. }
    assert (GR2 : mem_grows Mmid mem').
    { intros x Hx. unfold Mmid in Hx. destruct (_ && _)%bool; [exact Hx | apply FRgrows; exact Hx]. }
    set (KW := [(SA Mb (sk - 3), len1); (SA pn 0, len2)]).
    set (P := fun Mx : word -> option byte => slot_sem SEGS (map (uE E') sargs) Mx /\ props_ok GP E' Mx (MN2.keep_props G (kn cs1) KW v (a_props cs))).
    change (MR E cs model FULL) with M in RUN. rewrite <- HMR1 in RUN.
    replace (pc cs) with (pc cs1) in RUN |- * by reflexivity.
    eapply (call_core_p P cs1 E1 E' R FULL model T ret _ k3 _ (MN2.slot_atom sargs :: MN2.keep_props G (kn cs1) KW v (a_props cs)) regs' mem' HC1 Hfresh1 Hag' RUN).
    - (* [comment removed for export] *)
      apply (regs_after_call E1 _ R regs' (nxt cs1) (Some p) (co_regs _ _ _ _ _ _ _ _ _ _ _ HC1) F1sr).
      + apply kept_regs. intros kk Hin. apply KEPT. unfold RefMemcpyLib.callee_saved.
        cbn [In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; repeat (first [left; apply bv_eq; reflexivity | right]) |]). destruct Hin.
      + split; [exact Hrvv|]. cbn beta iota. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite A0, D1p. reflexivity.
    - (* [comment removed for export] *)
      apply (know_ok_agree' SEGS (nxt cs1) E1 E'); [exact Hag' | exact Hkv |].
      subst k3. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]].
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EST1, D1len1. split; [unfold flat; rewrite EST1; (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - Hoff16 Hoffr LIN DISJ Ee Esi Hst Fml Hc HSr Hnr Hnb Est Hehi' Hghi' Hglo' Hmhi' Hmlo' CE2 C19 C18 C17 C16 C14 C12 C10 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as LIN; try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fml; try pose proof I as Hc; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - __sat271 heq_sk Hoff16 Hoffr LIN DISJ Ee Esi Hst Fml Hc HSr Hnr Hnb Est Hehi' Hghi' Hglo' Hmhi' Hmlo' CE2 C19 C18 C17 C16 C14 C12 C10 C5; xlia zchecker] | lia])|].
        intros i Hi. apply (mem_grows_defined M mem' _ FRgrows).
        apply (store_ok_defined_out_image M (um + (sk - 3)) (Z.to_nat (st - 1))); try (first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoff16; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoff16 Fml HSr Hnr Hnb C14 C9 Hz; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as __sat272; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoff16; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - __sat271 heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 __sat272 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoff16 Fml HSr Hnr Hnb C14 C9 Hz; xlia zchecker] | lia]); [intros z Hz; apply OFF; (first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoff16; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoff16 Fml HSr Hnr Hnb C14 C9 Hz; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as __sat272; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoff16; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - __sat271 heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 __sat272 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoff16 Fml HSr Hnr Hnb C14 C9 Hz; xlia zchecker] | lia])|].
        apply WST. (first [solve [try pose proof I as H256; try pose proof I as Hst; clear - H256 Hst; lia] | solve [Zify.zify; try pose proof I as H256; try pose proof I as Hst; clear - H256 Hst; xlia zchecker] | lia]).
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EST2, D1len2. split; [unfold flat; rewrite EST2; (first [solve [try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C9; try pose proof I as C5; clear - Hoff16 Hoffr DISJ Esi Hst Hc Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C9 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Hoff16; try pose proof I as Hoffr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C9; try pose proof I as C5; clear - __sat271 heq_sk Hoff16 Hoffr DISJ Esi Hst Hc Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C9 C5; xlia zchecker] | lia])|].
        intros i Hi. apply (mem_grows_defined M mem' _ FRgrows).
        replace (start + 16 * offv + n + i) with (um + (sk - 3) + (16 * offv + n + 3 + i)) by (subst start; lia).
        apply (store_ok_defined_out_image M (um + (sk - 3)) (Z.to_nat (st - 1))); try (first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoffr; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoffr Fml HSr Hnr Hnb C14 C9 Hz; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as __sat272; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoffr; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - __sat271 heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 __sat272 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoffr Fml HSr Hnr Hnb C14 C9 Hz; xlia zchecker] | lia]); [intros z Hz; apply OFF; (first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoffr; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoffr Fml HSr Hnr Hnb C14 C9 Hz; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as __sat272; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hoffr; try pose proof I as Fml; try pose proof I as HSr; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as C14; try pose proof I as C9; try pose proof I as Hz; clear - __sat271 heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 __sat272 H256 Hghi' Hmhi' C19 C17 C10 Hi Hoffr Fml HSr Hnr Hnb C14 C9 Hz; xlia zchecker] | lia])|].
        apply WST. lia.
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EST1, D1hlen. split; [unfold flat; rewrite EST1; (first [solve [try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - DISJ Ee Esi Hst Hc Est Hehi' Hghi' Hglo' Hmhi' Hmlo' CE2 C19 C18 C17 C16 C12 C10 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as DISJ; try pose proof I as Ee; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hehi'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as CE2; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - __sat271 heq_sk DISJ Ee Esi Hst Hc Est Hehi' Hghi' Hglo' Hmhi' Hmlo' CE2 C19 C18 C17 C16 C12 C10 C5; xlia zchecker] | lia])|].
        intros i Hi. apply (mem_grows_defined M mem' _ FRgrows).
        apply (store_ok_defined_out_image M (um + (sk - 3)) (Z.to_nat (st - 1))); try (first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hz; clear - Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 H256 Hghi' Hmhi' C19 C17 C10 Hi Hz; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as __sat272; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hz; clear - __sat271 heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 __sat272 H256 Hghi' Hmhi' C19 C17 C10 Hi Hz; xlia zchecker] | lia]); [intros z Hz; apply OFF; (first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hz; clear - Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 H256 Hghi' Hmhi' C19 C17 C10 Hi Hz; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; try pose proof I as __sat272; try pose proof I as H256; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C10; try pose proof I as Hi; try pose proof I as Hz; clear - __sat271 heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5 __sat272 H256 Hghi' Hmhi' C19 C17 C10 Hi Hz; xlia zchecker] | lia])|].
        apply WST. (first [solve [try pose proof I as H256; try pose proof I as Hst; clear - H256 Hst; lia] | solve [Zify.zify; try pose proof I as H256; try pose proof I as Hst; clear - H256 Hst; xlia zchecker] | lia]).
      + eapply (w_know_ok_havoc SEGS E1 Mmid mem' _ pn 0 len2); [| | exact GR2].
        * eapply (w_know_ok_havoc SEGS E1 M Mmid (kn cs1) Mb (sk - 3) len1 HKN1); [| exact GR1].
          intros x Hx. apply OUT1. rewrite EST1, D1len1 in Hx. lia.
        * intros x Hx. apply OUT2. rewrite EST2, D1len2 in Hx. lia.
    - (* [comment removed for export] *)
      split.
      2:{ eapply (props_ok_agree GP v E1 E'); [| apply MN2.keep_props_vars | eapply env_agree_le; [exact Hag' | (first [solve [try pose proof I as Hnx1; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - Hnx1 Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as Hnx1; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat271 Hnx1 heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia])]].
          apply (keep_props_sound E E1 M mem' M (kn cs1) KW v (a_props cs) HPR Hag1 HKN1).
          intros a Ha.
          pose proof (Ha _ (or_introl eq_refl)) as X1. pose proof (Ha _ (or_intror (or_introl eq_refl))) as X2. cbn [fst snd] in X1, X2.
          rewrite EST1, D1len1 in X1. rewrite EST2, D1len2 in X2.
          rewrite (OUT2 a) by (first [solve [try pose proof I as X2; clear - X2; lia] | solve [Zify.zify; try pose proof I as X2; clear - X2; xlia zchecker] | lia]). apply OUT1. (first [solve [try pose proof I as X1; clear - X1; lia] | solve [Zify.zify; try pose proof I as X1; clear - X1; xlia zchecker] | lia]). }
      destruct PO as [Pp Pe PR Pq P4 P3 P2 Pzr Pe5 Pe4 Ps3 Ps2 Pr].
      unfold MN2.slot_args in C29. cbn [forallb] in C29.
      apply andb_prop in C29 as [V1 C29]. apply andb_prop in C29 as [V2 C29]. apply andb_prop in C29 as [V3 C29].
      apply andb_prop in C29 as [V4 C29]. apply andb_prop in C29 as [V5 C29]. apply andb_prop in C29 as [V6 C29].
      apply andb_prop in C29 as [V7 _].
      rewrite <- Hnx1 in V1, V2, V3, V4, V5, V6, V7.
      subst P sargs. unfold MN2.slot_args. cbn [map]. unfold uE.
      rewrite (AG' _ V1), (AG' _ V2), (AG' _ V3), (AG' _ V4), (AG' _ V5), (AG' _ V6), (AG' _ V7).
      rewrite edenot_eaddz, (AG _ VMb), u_lit64a. fold um. rewrite (Z.mod_small (um + sk)) by (first [solve [try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - DISJ Esi Hst Hc Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as heq_sk; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat272 heq_sk DISJ Esi Hst Hc Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C12 C5; xlia zchecker] | lia]).
      rewrite D1ste, D1n, Hv1, (AG _ C26), HWv, edenot_lit, u_lit64a, D1p, u_lit64a.
      rewrite (Z.mod_small (start + 16 * offv)) by (first [solve [try pose proof I as Pr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - Pr DISJ Esi Hst Hc Hnr Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C5; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as heq_sk; try pose proof I as heq_PR; try pose proof I as Pr; try pose proof I as DISJ; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Hnr; try pose proof I as Hnb; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as C19; try pose proof I as C18; try pose proof I as C17; try pose proof I as C16; try pose proof I as C14; try pose proof I as C12; try pose proof I as C10; try pose proof I as C5; clear - __sat272 heq_sk heq_PR Pr DISJ Esi Hst Hc Hnr Hnb Est Hghi' Hglo' Hmhi' Hmlo' C19 C18 C17 C16 C14 C12 C10 C5; xlia zchecker] | lia]). rewrite (Z.mod_small idx) by (first [solve [try pose proof I as C6; try pose proof I as C5; clear - C6 C5; lia] | solve [Zify.zify; try pose proof I as C6; try pose proof I as C5; clear - C6 C5; xlia zchecker] | lia]).
      cbn [slot_sem]. rewrite <- Est.
      split; [exact (EPOSTG _ _ _ _ _ _ _ P4 P3 P2 Pzr Pe5 Pe4 Ps3 Ps2 Pr)|].
      split; [reflexivity|]. split; [exact Hstride|]. split; [exact Hsc'|].
      split; [(first [solve [try pose proof I as Hst; clear - Hst; lia] | solve [Zify.zify; try pose proof I as Hst; clear - Hst; xlia zchecker] | lia])|]. split; [exact Hsd16|]. split; [exact Hst16|].
      split; [(first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C7; try pose proof I as C5; clear - Esi Hst Fli Hc Est Hglo' Hmlo' C18 C16 C12 C7 C5; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as heq_sk; try pose proof I as heq_st; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C7; try pose proof I as C5; clear - __sat272 heq_sk heq_st Esi Hst Fli Hc Est Hglo' Hmlo' C18 C16 C12 C7 C5; xlia zchecker] | lia])|]. split; [(first [solve [try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C12; try pose proof I as C10; clear - Hst Hc Est Hghi' Hmhi' C19 C17 C12 C10; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hghi'; try pose proof I as Hmhi'; try pose proof I as C19; try pose proof I as C17; try pose proof I as C12; try pose proof I as C10; clear - __sat272 Hst Hc Est Hghi' Hmhi' C19 C17 C12 C10; xlia zchecker] | lia])|]. split; [rewrite Fli; (first [solve [try pose proof I as C7; try pose proof I as C5; clear - C7 C5; lia] | solve [Zify.zify; try pose proof I as C7; try pose proof I as C5; clear - C7 C5; xlia zchecker] | lia])|]. split; [(first [solve [try pose proof I as C6; clear - C6; lia] | solve [Zify.zify; try pose proof I as C6; clear - C6; xlia zchecker] | lia])|]. split; [(first [solve [try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hmlo'; try pose proof I as C16; try pose proof I as C12; try pose proof I as C8; try pose proof I as C7; clear - Esi Hst Fli Hc Est Hmlo' C16 C12 C8 C7; lia] | solve [Zify.zify; try pose proof I as __sat272; try pose proof I as heq_sk; try pose proof I as heq_st; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Fli; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hmlo'; try pose proof I as C16; try pose proof I as C12; try pose proof I as C8; try pose proof I as C7; clear - __sat272 heq_sk heq_st Esi Hst Fli Hc Est Hmlo' C16 C12 C8 C7; xlia zchecker] | lia])|]. split; [(first [solve [try pose proof I as Hnr; clear - Hnr; lia] | solve [Zify.zify; try pose proof I as Hnr; clear - Hnr; xlia zchecker] | lia])|]. (first [solve [try pose proof I as Hoff16; clear - Hoff16; lia] | solve [Zify.zify; try pose proof I as Hoff16; clear - Hoff16; xlia zchecker] | lia]).
    - (* [comment removed for export] *)
      intros R' FULL' model' HC' Hfs HP'. apply (Hk E' R' FULL' model').
      + split.
        * eapply env_agree_trans; [eapply env_agree_le; [exact Hag1 | exact Fle]|]. eapply env_agree_le; [exact Hag' | (first [solve [try pose proof I as F1le; clear - F1le; lia] | solve [Zify.zify; try pose proof I as F1le; clear - F1le; xlia zchecker] | lia])].
        * eapply env_agree_trans; [exact Hag1|]. eapply env_agree_le; [exact Hag' | (first [solve [try pose proof I as Hnx1; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - Hnx1 Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5; lia] | solve [Zify.zify; try pose proof I as __sat271; try pose proof I as Hnx1; try pose proof I as heq_v; try pose proof I as heq_sk; try pose proof I as Esi; try pose proof I as Hst; try pose proof I as Hc; try pose proof I as Est; try pose proof I as Hglo'; try pose proof I as Hmlo'; try pose proof I as C18; try pose proof I as C16; try pose proof I as C12; try pose proof I as C5; clear - __sat271 Hnx1 heq_v heq_sk Esi Hst Hc Est Hglo' Hmlo' C18 C16 C12 C5; xlia zchecker] | lia])].
      + exact HC'.
      + destruct HP' as [HP1 HP2]. unfold set_props. cbn [a_props]. apply Forall_cons; [|exact HP2].
        unfold gholds. cbn [g_id g_args MN2.slot_atom]. apply (proj2 (GP50 _ _)). exact HP1.
      + exact Hfs.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem node_freehead2_sound : forall args cs cs' E R FULL model T,
    CSOK E cs R FULL model ->
    props_ok GP E (MR E cs model FULL) (a_props cs) ->
    MN2.node_freehead2 SEGS A nx0 MTB G cs args = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' ->
        props_ok GP E' (MR E' cs' model' FULL') (a_props cs') -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.
  Proof.
    intros args cs cs' E R FULL model T HC HPR Hn Hk.
    pose proof HC as HKN. apply co_know in HKN.
    set (M := MR E cs model FULL) in *.
    unfold MN2.node_freehead2, MN2.res_opt, MN2.node_freehead2r in Hn.
    destruct (Z.eqb (pc cs) (mt_free MTB)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
    destruct (split_lit (reg cs 2)) as [spb spk] eqn:HsplS.
    destruct (MN2.find_slot (kn cs) (reg cs 10) (MN2.slots_of cs)) as [s|] eqn:Hfs; [|destruct (xlo (kn cs) spb), (xhi (kn cs) spb); discriminate].
    destruct (find_slot_in _ _ _ _ Hfs) as (Hs_in & a1 & a2 & a3 & a4 & a5 & a6 & p7 & -> & Hpa).
    rename a1 into start_e, a2 into ste, a3 into ne, a4 into off_e, a5 into Ws, a6 into ix, p7 into p_e.
    destruct ix as [idx | iv | iop ia ib | iop ia ib | imo ia ib | imo ia ib | isx ilo inn ie | isx ik ii inn];
      try (destruct (xlo (kn cs) spb), (xhi (kn cs) spb); discriminate).
    destruct (xlo (kn cs) spb) as [splo|] eqn:Hsplo; [|discriminate].
    destruct (xhi (kn cs) spb) as [sphi|] eqn:Hsphi; [|discriminate].
    cbv zeta in Hn.
    set (usp := bv_unsigned (edenot E spb)) in *.
    set (sp := usp + spk).                                   (* [comment removed for export] *)
    destruct (MN2.decode_W Ws) as [[Se c]|] eqn:Hdec; [|discriminate].
    destruct (xlo (kn cs) ste) as [slo|] eqn:Hslo; [|discriminate].
    destruct (xhi (kn cs) ste) as [shi|] eqn:Hshi; [|discriminate].
    cbv zeta in Hn.
    destruct (match ste with ELit st0 => Some ((st0 mod two64) * idx) | _ => if Z.eqb idx 0 then Some 0 else None end) as [si|] eqn:Hsi_def; [|discriminate].
    set (Me := mkAlu ALU_ADD start_e (ELit (- (16 + si)))) in Hn.
    destruct (split_lit Me) as [mb mk] eqn:HsplM.
    destruct (kread8e SEGS (kn cs) mb mk) as [ge|] eqn:Hge; [|discriminate].
    destruct (split_lit ge) as [gb gk] eqn:HsplG.
    set (ak := gk - gk mod 4096) in Hn.
    set (e_e := mkAlu ALU_ADD start_e (mkAlu ALU_ADD ste (ELit (-4)))) in Hn.
    destruct (split_lit e_e) as [eb ek] eqn:HsplE.
    destruct (split_lit start_e) as [hb hk] eqn:HsplH.
    destruct (kread8e SEGS (kn cs) gb (gk + 16)) as [Me'|] eqn:HMe'; [|discriminate].
    destruct (kread8e SEGS (kn cs) gb (gk + 32)) as [We|] eqn:HWe; [|discriminate].
    destruct (MN.kz SEGS (kn cs) gb (gk + 24) 4) as [avail|] eqn:Hav; [|discriminate].
    destruct (MN.kz SEGS (kn cs) gb (gk + 28) 4) as [freed|] eqn:Hfr; [|discriminate].
    destruct (kread8e SEGS (kn cs) gb ak) as [sec|] eqn:Hsec; [|discriminate].   (* [comment removed for export] *)
    destruct (kread8e SEGS (kn cs) (ELit 0) (mt_secret MTB)) as [sec'|] eqn:Hsec'; [|discriminate].
    destruct (MN.kz SEGS (kn cs) eb ek 1) as [zend|] eqn:Hzend; [|discriminate].
    destruct (xlo (kn cs) off_e) as [olo|] eqn:Holo; [|discriminate].
    destruct (xhi (kn cs) off_e) as [ohi|] eqn:Hohi; [|discriminate].
    destruct (xlo (kn cs) gb) as [glo|] eqn:Hglo; [|discriminate].
    destruct (xhi (kn cs) gb) as [ghi|] eqn:Hghi; [|discriminate].
    destruct (xlo (kn cs) hb) as [hl|] eqn:Hhl; [|discriminate].
    destruct (xhi (kn cs) hb) as [hh|] eqn:Hhh; [|discriminate].
    destruct (xlo (kn cs) Se) as [Slo|] eqn:HSlo; [|discriminate].
    destruct (xhi (kn cs) Se) as [Shi|] eqn:HShi; [|discriminate].
    destruct (xlo (kn cs) mb) as [mlo|] eqn:Hmlo; [|discriminate].
    destruct (xhi (kn cs) mb) as [mhi|] eqn:Hmhi; [|discriminate].
    destruct (xlo (kn cs) eb) as [elo|] eqn:Helo; [|discriminate].
    destruct (xhi (kn cs) eb) as [ehi|] eqn:Hehi; [|discriminate].
    set (rexp := mkAlu ALU_SUB (mkAlu ALU_ADD ste (ELit (-4))) (mkAlu ALU_ADD ne (MN2.times16 off_e))) in Hn.
    set (e12 := mkAlu ALU_ADD start_e (mkAlu ALU_ADD ste (ELit (-16)))) in Hn.
    set (qlo := si / 16 + olo) in Hn. set (qhi := si / 16 + ohi) in Hn.
    match type of Hn with context [if ?cnd then _ else MN2.RConj _] => destruct cnd eqn:Hc; [|discriminate] end.
    unfold MN2.all_true in Hc. cbn [fold_right] in Hc. subst qlo qhi.
    apply andb_prop in Hc as [D1 Hc]. apply andb_prop in Hc as [D2 Hc]. apply andb_prop in Hc as [D3 Hc]. apply andb_prop in Hc as [D4 Hc].
    apply andb_prop in Hc as [D5 Hc]. apply andb_prop in Hc as [DI1 Hc]. apply andb_prop in Hc as [DI2 Hc]. apply andb_prop in Hc as [DI3 Hc].
    apply andb_prop in Hc as [DI4 Hc]. apply andb_prop in Hc as [D6 Hc]. apply andb_prop in Hc as [D7 Hc]. apply andb_prop in Hc as [D8 Hc].
    apply andb_prop in Hc as [D9 Hc]. apply andb_prop in Hc as [D10 Hc]. apply andb_prop in Hc as [D11 Hc]. apply andb_prop in Hc as [D12 Hc].
    apply andb_prop in Hc as [D13 Hc]. apply andb_prop in Hc as [D14 Hc]. apply andb_prop in Hc as [D15 Hc]. apply andb_prop in Hc as [D16 Hc].
    apply andb_prop in Hc as [D17 Hc]. apply andb_prop in Hc as [D18 Hc]. apply andb_prop in Hc as [D19 Hc]. apply andb_prop in Hc as [D20 Hc].
    apply andb_prop in Hc as [D21 Hc]. apply andb_prop in Hc as [D22 Hc]. apply andb_prop in Hc as [D23 Hc]. apply andb_prop in Hc as [D24 Hc].
    apply andb_prop in Hc as [D25 Hc]. apply andb_prop in Hc as [D26 Hc]. apply andb_prop in Hc as [D27 Hc]. apply andb_prop in Hc as [D28 Hc].
    apply andb_prop in Hc as [D29 Hc]. apply andb_prop in Hc as [D30 Hc]. apply andb_prop in Hc as [D31 Hc]. apply andb_prop in Hc as [D32 Hc].
    apply andb_prop in Hc as [D33 Hc]. apply andb_prop in Hc as [D34 Hc]. apply andb_prop in Hc as [D35 Hc]. apply andb_prop in Hc as [D36 Hc].
    apply andb_prop in Hc as [D37 Hc]. apply andb_prop in Hc as [D38 Hc]. apply andb_prop in Hc as [D39 _].
    apply Z.ltb_lt in D39. unfold two64 in D39.
    match type of Hn with context [if ?cnd then MN2.ROk _ else MN2.RFresh] => destruct cnd eqn:Vk0; [|discriminate] end.
    apply andb_prop in Vk0 as [Vk1 Vsp].
    cbv beta iota in Hn. injection Hn as <-.
    (* [comment removed for export] *)
    apply expr_eqb_eq in D2. subst We. apply Z.eqb_eq in D3. apply Z.leb_le in D4. apply Z.leb_le in D5.
    apply Z.leb_le in D8. apply Bool.negb_true_iff in D9. apply Bool.negb_true_iff in D10.
    apply Z.leb_le in D11. apply Z.ltb_lt in D12. apply Z.leb_le in D13. apply Z.ltb_lt in D14. apply expr_eqb_eq in D16.
    apply Z.leb_le in D17. apply Z.ltb_lt in D18. apply Z.leb_le in D19. apply Z.leb_le in D20. apply Z.ltb_lt in D21.
    apply Z.leb_le in D22. apply Z.ltb_lt in D23. apply Bool.orb_prop in D24. apply Bool.orb_prop in D25. apply Z.leb_le in D26.
    apply Z.leb_le in D27. apply Z.ltb_lt in D28. apply Z.leb_le in D29.   (* [comment removed for export] *)
    unfold two64 in D18, D21, D23, D28.
    apply Z.leb_le in DI1. apply Z.ltb_lt in DI2. apply Z.eqb_eq in DI3. apply Z.leb_le in DI4.
    (* [comment removed for export] *)
    destruct (slots_of_in cs _ Hs_in) as (g0 & Hg0 & Hid0 & Hargs0).
    pose proof (proj1 (Forall_forall _ _) HPR g0 Hg0) as SL. unfold gholds in SL. rewrite Hid0, Hargs0 in SL.
    apply (proj1 (GP50 _ _)) in SL. cbn [map slot_sem] in SL.
    set (st := uE E start_e) in *. set (sd := uE E ste) in *. set (n := uE E ne) in *. set (o := uE E off_e) in *.
    set (W := uE E Ws) in *.
    replace (uE E (ELit idx)) with idx in SL by (unfold uE; rewrite edenot_lit, u_lit64a; symmetry; apply Z.mod_small; lia).
    destruct SL as (EP & Hp & Hsd & Hsc & [Hsd16 Hsd31] & Hsdmod & Hstmod & Hsi & Hnw & [Hidx1 Hidx2] & Hi32 & Hq4096 & Hn0 & Hfit).
    (* [comment removed for export] *)
    pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi'.
    fold usp in Hsplo', Hsphi'.
    (* [comment removed for export] *)
    rename D24 into D24m. rename D25 into D25m. rename D27 into D27m. rename D28 into D28m. rename D29 into D29m.
    (* [comment removed for export] *)
    assert (D24 : hh + hk + shi <= sp - 48 \/ ehi + ek + 4 <= sp - 48
                  \/ bv_unsigned (edenot E hb) + hk + sd <= sp - 48).
    { subst sp. destruct D24m as [X|X].
      - apply Bool.orb_prop in X. destruct X as [X|X]; apply Z.leb_le in X; [left | right; left]; (first [solve [try pose proof I as Hsplo'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as X; clear - Hsplo' Hidx1 Hsi Hsd16 X; lia] | solve [Zify.zify; try pose proof I as Hsplo'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as X; clear - Hsplo' Hidx1 Hsi Hsd16 X; xlia zchecker] | lia]).
      - right; right. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
        apply expr_eqb_eq in X2. apply Z.leb_le in X3.
        pose proof (inside_maps_below_top E cs R FULL model hb hk ste HC X1) as BT.
        rewrite <- X2 in BT. unfold estart, elenZ in BT. cbn [a_base a_off] in BT. fold usp in BT.
        unfold STK_BELOW in BT, X3. subst sd. unfold uE in *. (first [solve [try pose proof I as BT; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as X3; clear - BT Hidx1 Hsi Hsd16 X3; lia] | solve [Zify.zify; try pose proof I as BT; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as X3; clear - BT Hidx1 Hsi Hsd16 X3; xlia zchecker] | lia]). }
    (* [comment removed for export] *)
    assert (GH : exists ghi2, bv_unsigned (edenot E gb) <= ghi2 /\ ghi2 + gk + 40 <= sp - 48).
    { subst sp. destruct D25m as [X|X].
      - apply Z.leb_le in X. exists ghi. split; [exact (xhi_sound SEGS E M (kn cs) _ _ HKN Hghi)|]. lia.
      - apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
        apply expr_eqb_eq in X2. apply Z.leb_le in X3.
        pose proof (inside_maps_below_top E cs R FULL model gb gk (ELit 40) HC X1) as BT.
        rewrite <- X2 in BT. unfold estart, elenZ in BT. cbn [a_base a_off] in BT. fold usp in BT.
        replace (bv_unsigned (edenot E (ELit 40))) with 40 in BT by (rewrite edenot_lit, u_lit64a; reflexivity).
        exists (bv_unsigned (edenot E gb)). split; [lia|]. unfold STK_BELOW in BT, X3. lia. }
    destruct GH as (ghi2 & GH1 & D25).
    assert (D27 : mt_secret MTB + 8 <= sp - 48) by (subst sp; (first [solve [try pose proof I as Hsplo'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as D27m; clear - Hsplo' Hidx1 Hsi Hsd16 D27m; lia] | solve [Zify.zify; try pose proof I as Hsplo'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as D27m; clear - Hsplo' Hidx1 Hsi Hsd16 D27m; xlia zchecker] | lia])). assert (D28 : sp < 2 ^ 64) by (subst sp; unfold two64 in D28m; (first [solve [try pose proof I as Hsphi'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as D28m; clear - Hsphi' Hidx1 Hsi Hsd16 D28m; lia] | solve [Zify.zify; try pose proof I as Hsphi'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as D28m; clear - Hsphi' Hidx1 Hsi Hsd16 D28m; xlia zchecker] | lia])).
    assert (D29 : img_hi A <= sp - 48) by (subst sp; (first [solve [try pose proof I as Hsplo'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as D29m; clear - Hsplo' Hidx1 Hsi Hsd16 D29m; lia] | solve [Zify.zify; try pose proof I as Hsplo'; try pose proof I as Hidx1; try pose proof I as Hsi; try pose proof I as Hsd16; try pose proof I as D29m; clear - Hsplo' Hidx1 Hsi Hsd16 D29m; xlia zchecker] | lia])).
    assert (R2 : getr R (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 sp).
    { rewrite (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)).
      rewrite (split_lit_denot E (reg cs 2) spb spk HsplS). fold usp. subst sp. reflexivity. }
    assert (ESTS : forall k, estart E (SA spb k) = usp + k) by (intros; reflexivity).
    clear D24m D25m D27m D28m D29m Hsplo' Hsphi' Hsplo Hsphi.      (* [comment removed for export] *)
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Holo) as Holo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hohi) as Hohi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hglo) as Hglo'. pose proof GH1 as Hghi'.   (* [comment removed for export] *)
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hhl) as Hhl'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hhh) as Hhh'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN HSlo) as HSlo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN HShi) as HShi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hmlo) as Hmlo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hmhi) as Hmhi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Helo) as Helo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hehi) as Hehi'.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hslo) as Hslo'. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi'.
    fold o in Holo', Hohi'. fold sd in Hslo', Hshi'.
    set (ug := bv_unsigned (edenot E gb)) in *. set (uh := bv_unsigned (edenot E hb)) in *.
    set (um := bv_unsigned (edenot E mb)) in *. set (ue := bv_unsigned (edenot E eb)) in *. set (Sv := bv_unsigned (edenot E Se)) in *.
    pose proof (u64_range (edenot E gb)) as Hugr. fold ug in Hugr. pose proof (u64_range (edenot E hb)) as Huhr. fold uh in Huhr.
    pose proof (u64_range (edenot E mb)) as Humr. fold um in Humr. pose proof (u64_range (edenot E eb)) as Huer. fold ue in Huer.
    pose proof (u64_range (edenot E start_e)) as Hstr. pose proof (u64_range (edenot E ne)) as Hnr. pose proof (u64_range (edenot E off_e)) as Hor.
    unfold uE in st, sd, n, o, W. fold st in Hstr. fold n in Hnr. fold o in Hor.
    assert (Esi : si = sd * idx).
    { destruct ste as [st0 | iv | iop ia ib | iop ia ib | imo ia ib | imo ia ib | isx ilo inn ie | isx ik ii inn];
        first [ injection Hsi_def as <-; subst sd; rewrite edenot_lit, u_lit64a; reflexivity
              | destruct (Z.eqb_spec idx 0); [injection Hsi_def as <-; (first [solve [try pose proof I as e; try pose proof I as Hstr; try pose proof I as Hsd16; clear - e Hstr Hsd16; lia] | solve [Zify.zify; try pose proof I as e; try pose proof I as Hstr; try pose proof I as Hsd16; clear - e Hstr Hsd16; xlia zchecker] | lia]) | discriminate Hsi_def] ]. }
    assert (Hsi0 : 0 <= si <= st - 16) by (rewrite Esi; split; [apply Z.mul_nonneg_nonneg; lia | lia]).
    (* [comment removed for export] *)
    pose proof (w_split_lit_denot E start_e hb hk HsplH) as HHd. fold uh in HHd.
    assert (Est : st = uh + hk).
    { subst st. rewrite HHd. rewrite u_small by (first [solve [try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hhh'; try pose proof I as Hhl'; try pose proof I as D28; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D39; try pose proof I as D19; clear - Esi Hstr Hshi' HShi' HSlo' Hhh' Hhl' D28 Hidx1 Hsd16 D39 D19; lia] | solve [Zify.zify; try pose proof I as heq_sd; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hhh'; try pose proof I as Hhl'; try pose proof I as D28; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D39; try pose proof I as D19; clear - heq_sd Esi Hstr Hshi' HShi' HSlo' Hhh' Hhl' D28 Hidx1 Hsd16 D39 D19; xlia zchecker] | lia]). reflexivity. }
    pose proof (w_split_lit_denot E Me mb mk HsplM) as HMd. fold um in HMd.
    assert (EMe : st - 16 - si = um + mk).
    { assert (X : bv_unsigned (edenot E Me) = st - 16 - si).
      { subst Me. rewrite mkAlu_denot, u_add64, edenot_lit, Z_to_bv_unsigned, bv_wrap64_mod. fold st.
        rewrite Zplus_mod_idemp_r.
        replace (st + - (16 + si)) with (st - 16 - si) by lia. apply Z.mod_small. (first [solve [try pose proof I as Est; try pose proof I as Hsi0; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as Hidx1; try pose proof I as Hsd16; clear - Est Hsi0 Esi Hstr Hshi' Hhh' D28 Hidx1 Hsd16; lia] | solve [Zify.zify; try pose proof I as heq_sd; try pose proof I as Est; try pose proof I as Hsi0; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as Hidx1; try pose proof I as Hsd16; clear - heq_sd Est Hsi0 Esi Hstr Hshi' Hhh' D28 Hidx1 Hsd16; xlia zchecker] | lia]). }
      rewrite HMd, u_small in X by (first [solve [try pose proof I as Hstr; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hsd16; try pose proof I as D21; try pose proof I as D20; clear - Hstr Hmhi' Hmlo' HShi' HSlo' Hsd16 D21 D20; lia] | solve [Zify.zify; try pose proof I as Hstr; try pose proof I as Hmhi'; try pose proof I as Hmlo'; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hsd16; try pose proof I as D21; try pose proof I as D20; clear - Hstr Hmhi' Hmlo' HShi' HSlo' Hsd16 D21 D20; xlia zchecker] | lia]). (first [solve [try pose proof I as X; try pose proof I as Hstr; try pose proof I as Hsd16; clear - X Hstr Hsd16; lia] | solve [Zify.zify; try pose proof I as X; try pose proof I as Hstr; try pose proof I as Hsd16; clear - X Hstr Hsd16; xlia zchecker] | lia]). }
    assert (Dste : bv_unsigned (edenot E (mkAlu ALU_ADD ste (ELit (-4)))) = sd - 4).
    { rewrite mkAlu_denot, u_add64, edenot_lit, u_lit64a. fold sd.
      replace ((-4) mod 2 ^ 64) with (2 ^ 64 - 4) by reflexivity.
      replace (sd + (2 ^ 64 - 4)) with ((sd - 4) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    pose proof (w_split_lit_denot E e_e eb ek HsplE) as HEd. fold ue in HEd.
    assert (Ee : st + sd - 4 = ue + ek).
    { assert (X : bv_unsigned (edenot E e_e) = st + sd - 4).
      { subst e_e. rewrite mkAlu_denot, u_add64, Dste. fold st. rewrite Z.mod_small by (first [solve [try pose proof I as Hsi0; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; clear - Hsi0 Esi Hstr Hidx1 Hnw Hsd16; lia] | solve [Zify.zify; try pose proof I as Hsi0; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; clear - Hsi0 Esi Hstr Hidx1 Hnw Hsd16; xlia zchecker] | lia]). lia. }
      rewrite HEd, u_small in X by (first [solve [try pose proof I as Hstr; try pose proof I as Hehi'; try pose proof I as Helo'; try pose proof I as D28; try pose proof I as Hsd16; try pose proof I as D23; try pose proof I as D22; clear - Hstr Hehi' Helo' D28 Hsd16 D23 D22; lia] | solve [Zify.zify; try pose proof I as Hstr; try pose proof I as Hehi'; try pose proof I as Helo'; try pose proof I as D28; try pose proof I as Hsd16; try pose proof I as D23; try pose proof I as D22; clear - Hstr Hehi' Helo' D28 Hsd16 D23 D22; xlia zchecker] | lia]). (first [solve [try pose proof I as X; try pose proof I as Hstr; try pose proof I as Hsd16; clear - X Hstr Hsd16; lia] | solve [Zify.zify; try pose proof I as X; try pose proof I as Hstr; try pose proof I as Hsd16; clear - X Hstr Hsd16; xlia zchecker] | lia]). }
    pose proof (w_split_lit_denot E ge gb gk HsplG) as HGd. fold ug in HGd.
    set (g := ug + gk) in *. set (Mv := st - 16 - si). set (ev := st + sd - 4). set (pv := st + 16 * o). set (rv := sd - 4 - n - 16 * o).
    set (q := sd * idx / 16 + o).
    assert (Eg : g = ug + gk) by reflexivity. assert (EMv : Mv = st - 16 - si) by reflexivity. assert (Eev : ev = st + sd - 4) by reflexivity.
    assert (Epv : pv = st + 16 * o) by reflexivity. assert (Erv : rv = sd - 4 - n - 16 * o) by reflexivity.
    assert (Eq : q = sd * idx / 16 + o) by reflexivity.
    assert (Hq16 : si / 16 = sd * idx / 16) by (rewrite Esi; reflexivity).
    clearbody g Mv ev pv rv q.
    assert (Hak : 0 <= gk mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    pose proof (u64_range (edenot E Se)) as HSvr. fold Sv in HSvr. fold Sv in HSlo', HShi'.
    pose proof (decode_W_lit Ws Se c Hdec) as Hcr.
    pose proof (decode_W_val E Ws Se c Hdec ltac:(unfold uE; fold Sv; (first [solve [try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hstr; try pose proof I as HShi'; try pose proof I as Hsd16; try pose proof I as D5; clear - Hcr HSvr Hstr HShi' Hsd16 D5; lia] | solve [Zify.zify; try pose proof I as __sat4115; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hstr; try pose proof I as HShi'; try pose proof I as Hsd16; try pose proof I as D5; clear - __sat4115 Hcr HSvr Hstr HShi' Hsd16 D5; xlia zchecker] | lia]))) as HWv. unfold uE in HWv. fold W Sv in HWv.
    destruct (w_fields Sv c Hcr ltac:(lia)) as (Fml & Fli & Fsc). rewrite <- HWv in Fml, Fli, Fsc.
    assert (HWr : 0 <= W < 2 ^ 64) by (subst W; apply u64_range).
    (* [comment removed for export] *)
    assert (HpaV : edenot E (reg cs 10) = Z_to_bv 64 pv).
    { assert (X : edenot E p_e = edenot E (reg cs 10)).
      { destruct Hpa as [X|X]; [apply expr_eqb_eq in X; rewrite X; reflexivity | exact (len_eqb_sound' SEGS E M (kn cs) _ _ HKN X)]. }
      rewrite <- X. subst pv. rewrite <- Hp. symmetry. apply Z_to_bv_bv_unsigned. }
    (* [comment removed for export] *)
    assert (ESTG : forall k, estart E (SA gb k) = ug + k) by (intros; reflexivity).
    assert (ESTM : forall k, estart E (SA mb k) = um + k) by (intros; reflexivity).
    assert (ESTE : forall k, estart E (SA eb k) = ue + k) by (intros; reflexivity).
    pose proof (kread8e_rdn SEGS E M (kn cs) mb mk ge HKN Hge ltac:(unfold flat; rewrite ESTM; (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Ee; try pose proof I as EMe; try pose proof I as Est; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hmlo'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - Fsc Hcr Ee EMe Est Esi Hstr Hshi' Hehi' Hmlo' Hhh' D28 D24 Hidx1 Hsd16 D20; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_sd; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Ee; try pose proof I as EMe; try pose proof I as Est; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hmlo'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - __sat4113 heq_sd Fsc Hcr Ee EMe Est Esi Hstr Hshi' Hehi' Hmlo' Hhh' D28 D24 Hidx1 Hsd16 D20; xlia zchecker] | lia]))) as Fmeta.
    rewrite adenot_SA, ESTM, HGd, <- EMe in Fmeta.
    pose proof (kread8e_rdn SEGS E M (kn cs) gb (gk + 16) Me' HKN HMe' ltac:(unfold flat; rewrite ESTG; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4113 heq_ak Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia]))) as Fmem.
    rewrite adenot_SA, ESTG in Fmem. rewrite (len_eqb_sound' SEGS E M (kn cs) _ _ HKN D1) in Fmem.
    replace (edenot E Me) with (Z_to_bv 64 Mv : word) in Fmem
      by (rewrite HMd; subst Mv; rewrite EMe; reflexivity).
    pose proof (kread8e_rdn SEGS E M (kn cs) gb (gk + 32) Ws HKN HWe ltac:(unfold flat; rewrite ESTG; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4113 heq_ak Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia]))) as FW.
    rewrite adenot_SA, ESTG in FW. replace (edenot E Ws) with (Z_to_bv 64 W : word) in FW by (subst W; apply Z_to_bv_bv_unsigned).
    destruct (kreadZ_rdn SEGS E M (kn cs) gb (gk + 24) 4 avail HKN Hav ltac:((first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4113 heq_ak Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia])) ltac:(unfold flat; rewrite ESTG; cbn [Z.of_nat]; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4113 heq_ak Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia]))) as (Fav & _ & _).
    rewrite adenot_SA, ESTG in Fav.
    destruct (kreadZ_rdn SEGS E M (kn cs) gb (gk + 28) 4 freed HKN Hfr ltac:((first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4113 heq_ak Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia])) ltac:(unfold flat; rewrite ESTG; cbn [Z.of_nat]; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4113 heq_ak Hcr Hak Hstr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia]))) as (Ffr & _ & _).
    rewrite adenot_SA, ESTG in Ffr.
    (* [comment removed for export] *)
    pose proof (kread8e_rdn SEGS E M (kn cs) gb ak sec HKN Hsec ltac:(unfold flat; rewrite ESTG; (first [solve [try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hor; try pose proof I as Hstr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hohi'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as D17; try pose proof I as D7; clear - Fsc Fml Hcr Hak Hor Hstr HShi' HSlo' Hghi' Hglo' Hohi' D28 D25 Hidx1 Hsd16 Hsc D17 D7; lia] | solve [Zify.zify; try pose proof I as __sat4099; try pose proof I as __sat4113; try pose proof I as heq_ak; try pose proof I as heq_o; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hor; try pose proof I as Hstr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as Hohi'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as D17; try pose proof I as D7; clear - __sat4099 __sat4113 heq_ak heq_o Fsc Fml Hcr Hak Hor Hstr HShi' HSlo' Hghi' Hglo' Hohi' D28 D25 Hidx1 Hsd16 Hsc D17 D7; xlia zchecker] | lia]))) as Farea.
    rewrite adenot_SA, ESTG in Farea.
    pose proof (kread8e_rdn SEGS E M (kn cs) (ELit 0) (mt_secret MTB) sec' HKN Hsec'
                ltac:(unfold flat, estart; cbn [a_base a_off]; rewrite edenot_lit, (u_lit 0) by (unfold two64; (first [solve [try pose proof I as Hcr; try pose proof I as Hstr; try pose proof I as D28; try pose proof I as D27; try pose proof I as Hsd16; try pose proof I as D26; clear - Hcr Hstr D28 D27 Hsd16 D26; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Hcr; try pose proof I as Hstr; try pose proof I as D28; try pose proof I as D27; try pose proof I as Hsd16; try pose proof I as D26; clear - __sat4113 Hcr Hstr D28 D27 Hsd16 D26; xlia zchecker] | lia])); (first [solve [try pose proof I as Hcr; try pose proof I as Hstr; try pose proof I as D28; try pose proof I as D27; try pose proof I as Hsd16; try pose proof I as D26; clear - Hcr Hstr D28 D27 Hsd16 D26; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Hcr; try pose proof I as Hstr; try pose proof I as D28; try pose proof I as D27; try pose proof I as Hsd16; try pose proof I as D26; clear - __sat4113 Hcr Hstr D28 D27 Hsd16 D26; xlia zchecker] | lia]))) as Fsec.
    rewrite adenot_SA in Fsec. unfold estart in Fsec. cbn [a_base a_off] in Fsec. rewrite edenot_lit, (u_lit 0), Z.add_0_l in Fsec by (unfold two64; lia).
    destruct (kreadZ_rdn SEGS E M (kn cs) eb ek 1 zend HKN Hzend ltac:((first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Ee; try pose proof I as EMe; try pose proof I as Est; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hmlo'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - Fsc Hcr Ee EMe Est Esi Hstr Hshi' Hehi' Hmlo' Hhh' D28 D24 Hidx1 Hsd16 D20; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_sd; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Ee; try pose proof I as EMe; try pose proof I as Est; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hmlo'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - __sat4113 heq_sd Fsc Hcr Ee EMe Est Esi Hstr Hshi' Hehi' Hmlo' Hhh' D28 D24 Hidx1 Hsd16 D20; xlia zchecker] | lia])) ltac:(unfold flat; rewrite ESTE; cbn [Z.of_nat]; (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Ee; try pose proof I as EMe; try pose proof I as Est; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hmlo'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - Fsc Hcr Ee EMe Est Esi Hstr Hshi' Hehi' Hmlo' Hhh' D28 D24 Hidx1 Hsd16 D20; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as heq_sd; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Ee; try pose proof I as EMe; try pose proof I as Est; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hmlo'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - __sat4113 heq_sd Fsc Hcr Ee EMe Est Esi Hstr Hshi' Hehi' Hmlo' Hhh' D28 D24 Hidx1 Hsd16 D20; xlia zchecker] | lia]))) as (Fend & _ & _).
    rewrite adenot_SA, ESTE, D3, N_to_le_bytes_1_small, <- Ee in Fend.
    (* [comment removed for export] *)
    assert (OFFM : forall z, st - 16 - si <= z < st - 16 - si + (sd + 13 + si) -> z < img_lo A \/ img_hi A <= z).
    { apply Bool.orb_prop in D30. destruct D30 as [D30|D30].
      - apply Z.leb_le in D30. intros z Hz. right. (first [solve [try pose proof I as Hz; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Est; try pose proof I as Hstr; try pose proof I as Hhl'; try pose proof I as Hsd16; try pose proof I as D30; clear - Hz Fsc Hcr Est Hstr Hhl' Hsd16 D30; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Hz; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Est; try pose proof I as Hstr; try pose proof I as Hhl'; try pose proof I as Hsd16; try pose proof I as D30; clear - __sat4113 Hz Fsc Hcr Est Hstr Hhl' Hsd16 D30; xlia zchecker] | lia]).
      - pose proof (ranges_apart_x_sound SEGS E M (kn cs) (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) hb (hk - 16 - si)
                      (mkAlu ALU_ADD ste (ELit (13 + si))) HKN D30) as DJ.
        assert (LS : elenZ E (mkAlu ALU_ADD ste (ELit (13 + si))) = sd + 13 + si).
        { unfold elenZ. rewrite mkAlu_denot, u_add64, edenot_lit, u_lit64a. fold sd.
          rewrite (Z.mod_small (13 + si)) by (first [solve [try pose proof I as Hcr; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hq4096; try pose proof I as Hsd16; try pose proof I as DI4; clear - Hcr Esi Hstr Hq4096 Hsd16 DI4; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Hcr; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hq4096; try pose proof I as Hsd16; try pose proof I as DI4; clear - __sat4113 Hcr Esi Hstr Hq4096 Hsd16 DI4; xlia zchecker] | lia]).
          match goal with |- (?x mod _ = _) => replace x with (sd + 13 + si) by (subst sd; lia) end.
          apply Z.mod_small. subst sd. (first [solve [try pose proof I as Hcr; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hq4096; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; clear - Hcr Esi Hstr Hq4096 Hidx1 Hsd31 Hsd16; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Hcr; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hq4096; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; clear - __sat4113 Hcr Esi Hstr Hq4096 Hidx1 Hsd31 Hsd16; xlia zchecker] | lia]). }
        rewrite LS in DJ. replace (estart E (SA hb (hk - 16 - si))) with (st - 16 - si) in DJ by (unfold estart; cbn [a_base a_off]; fold uh; (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Est; try pose proof I as Hstr; try pose proof I as Hsd16; clear - Fsc Hcr Est Hstr Hsd16; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Est; try pose proof I as Hstr; try pose proof I as Hsd16; clear - __sat4113 Fsc Hcr Est Hstr Hsd16; xlia zchecker] | lia])).
        intros z Hz. apply (apart_hull_out E (st - 16 - si) (sd + 13 + si)); [(first [solve [try pose proof I as Hsi0; try pose proof I as Hnw; try pose proof I as Hz; clear - Hsi0 Hnw Hz; lia] | solve [Zify.zify; try pose proof I as Hsi0; try pose proof I as Hnw; try pose proof I as Hz; clear - Hsi0 Hnw Hz; xlia zchecker] | lia]) | (first [solve [try pose proof I as Hsi0; try pose proof I as Hnw; try pose proof I as Hz; clear - Hsi0 Hnw Hz; lia] | solve [Zify.zify; try pose proof I as Hsi0; try pose proof I as Hnw; try pose proof I as Hz; clear - Hsi0 Hnw Hz; xlia zchecker] | lia]) | exact DJ | (first [solve [try pose proof I as Hsi0; try pose proof I as Hnw; try pose proof I as Hz; clear - Hsi0 Hnw Hz; lia] | solve [Zify.zify; try pose proof I as Hsi0; try pose proof I as Hnw; try pose proof I as Hz; clear - Hsi0 Hnw Hz; xlia zchecker] | lia])]. }
    apply rdn1_out_image in Fend; [| rewrite u_lit by (unfold two64; (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMe; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; try pose proof I as D20; clear - Fsc Hcr EMe Esi Hstr Hmlo' Hidx1 Hnw Hsd16 D20; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMe; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; try pose proof I as D20; clear - __sat4113 Fsc Hcr EMe Esi Hstr Hmlo' Hidx1 Hnw Hsd16 D20; xlia zchecker] | lia])); apply OFFM; (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMe; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; try pose proof I as D20; clear - Fsc Hcr EMe Esi Hstr Hmlo' Hidx1 Hnw Hsd16 D20; lia] | solve [Zify.zify; try pose proof I as __sat4113; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMe; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; try pose proof I as D20; clear - __sat4113 Fsc Hcr EMe Esi Hstr Hmlo' Hidx1 Hnw Hsd16 D20; xlia zchecker] | lia])].
    pose proof (page_aligned_sound' ip _ _ _ _ HKN D15) as HGal. fold ug in HGal.
    pose proof (kimg_cover_none SEGS E M (kn cs) _ _ HKN D32) as TBL.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) spb (spk - 48) (ELit 48) HKN HKN D31) as (WST & _ & _).
    rewrite ESTS in WST. replace (usp + (spk - 48)) with (sp - 48) in WST by (subst sp; lia).
    change (elenZ E (ELit 48)) with (48 mod two64) in WST. rewrite Z.mod_small in WST by (unfold two64; lia).
    (* [comment removed for export] *)
    destruct EP as [Pp Pe PR Pq P4 P3 P2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. subst Pp Pe PR Pq.
    assert (PRE : free_pre_g SEGS (mt_sct MTB) (mt_secret MTB) M sp pv ev Mv g idx o n sd rv q W avail freed (edenot E sec)).
    { constructor.
      - exact Hsd.
      - (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Epv; try pose proof I as EMv; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - Fsc Hcr Epv EMv Esi Hstr Hugr Hsd16; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Epv; try pose proof I as EMv; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - __sat4114 Fsc Hcr Epv EMv Esi Hstr Hugr Hsd16; xlia zchecker] | lia]).
      - (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Eev; try pose proof I as EMv; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - Fsc Hcr Eev EMv Esi Hstr Hugr Hsd16; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Eev; try pose proof I as EMv; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - __sat4114 Fsc Hcr Eev EMv Esi Hstr Hugr Hsd16; xlia zchecker] | lia]).
      - (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Erv; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - Fsc Hcr Erv Hstr Hugr Hsd16; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Erv; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - __sat4114 Fsc Hcr Erv Hstr Hugr Hsd16; xlia zchecker] | lia]).
      - exact Eq.
      - subst pv. rewrite Z.add_mod, Hstmod by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
      - (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMv; try pose proof I as EMe; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - Fsc Hcr EMv EMe Hstr Hugr Hmlo' Hidx1 Hsd16 D20; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMv; try pose proof I as EMe; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D20; clear - __sat4114 Fsc Hcr EMv EMe Hstr Hugr Hmlo' Hidx1 Hsd16 D20; xlia zchecker] | lia]).
      - rewrite Fli. (first [solve [try pose proof I as Fsc; try pose proof I as Fli; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Hidx2; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D7; try pose proof I as DI1; clear - Fsc Fli Fml Hcr Hq16 Hstr Hugr HShi' HSlo' Hohi' Hidx2 Hidx1 Hsd16 Hsc Pr D7 DI1; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_o; try pose proof I as Fsc; try pose proof I as Fli; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Hidx2; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D7; try pose proof I as DI1; clear - __sat4114 heq_o Fsc Fli Fml Hcr Hq16 Hstr Hugr HShi' HSlo' Hohi' Hidx2 Hidx1 Hsd16 Hsc Pr D7 DI1; xlia zchecker] | lia]).
      - lia.
      - lia.
      - (first [solve [try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Erv; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Holo'; try pose proof I as Hfit; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D8; try pose proof I as D7; clear - Fsc Fml Hcr Hq16 Erv Hor Hnr Hstr Hugr HShi' HSlo' Hohi' Holo' Hfit Hidx1 Hsd31 Hsd16 Hsc Pr D8 D7; lia] | solve [Zify.zify; try pose proof I as __sat4099; try pose proof I as __sat4114; try pose proof I as heq_o; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Erv; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Holo'; try pose proof I as Hfit; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D8; try pose proof I as D7; clear - __sat4099 __sat4114 heq_o Fsc Fml Hcr Hq16 Erv Hor Hnr Hstr Hugr HShi' HSlo' Hohi' Holo' Hfit Hidx1 Hsd31 Hsd16 Hsc Pr D8 D7; xlia zchecker] | lia]).
      - (first [solve [try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Eq; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D7; clear - Fsc Fml Hcr Hq16 Eq Hstr Hugr HShi' HSlo' Hohi' Hidx1 Hsd16 Hsc Pr D7; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_o; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Eq; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D7; clear - __sat4114 heq_o Fsc Fml Hcr Hq16 Eq Hstr Hugr HShi' HSlo' Hohi' Hidx1 Hsd16 Hsc Pr D7; xlia zchecker] | lia]).
      - exact HWr.
      - (first [solve [try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hq16; try pose proof I as Eg; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hglo'; try pose proof I as Hohi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D17; try pose proof I as D7; clear - Fsc Fml Hcr Hak Hq16 Eg Hstr Hugr HShi' HSlo' Hglo' Hohi' Hidx1 Hsd16 Hsc Pr D17 D7; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as heq_o; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hq16; try pose proof I as Eg; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hglo'; try pose proof I as Hohi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D17; try pose proof I as D7; clear - __sat4114 heq_ak heq_o Fsc Fml Hcr Hak Hq16 Eg Hstr Hugr HShi' HSlo' Hglo' Hohi' Hidx1 Hsd16 Hsc Pr D17 D7; xlia zchecker] | lia]).
      - rewrite Fsc, Fml, Fli. apply Bool.orb_prop in D6 as [X|X]; apply andb_prop in X as [X X2]; apply andb_prop in X as [X1 X3].
        + left. apply Z.ltb_lt in X1. apply Z.leb_le in X3. apply Z.ltb_lt in X2. rewrite Hq16 in X3, X2. (first [solve [try pose proof I as HWr; try pose proof I as Fml; try pose proof I as HWv; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Eq; try pose proof I as Hor; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Holo'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D7; try pose proof I as X2; try pose proof I as X3; try pose proof I as X1; clear - HWr Fml HWv Hcr HSvr Eq Hor Hstr Hugr HShi' HSlo' Hohi' Holo' Hidx1 Hsd16 D7 X2 X3 X1; lia] | solve [Zify.zify; try pose proof I as __sat4099; try pose proof I as __sat4114; try pose proof I as heq_o; try pose proof I as HWr; try pose proof I as Fml; try pose proof I as HWv; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Eq; try pose proof I as Hor; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Holo'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as D7; try pose proof I as X2; try pose proof I as X3; try pose proof I as X1; clear - __sat4099 __sat4114 heq_o HWr Fml HWv Hcr HSvr Eq Hor Hstr Hugr HShi' HSlo' Hohi' Holo' Hidx1 Hsd16 D7 X2 X3 X1; xlia zchecker] | lia]).
        + right. apply Z.eqb_eq in X1. apply Z.leb_le in X3. apply Z.eqb_eq in X2. (first [solve [try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as X2; try pose proof I as X1; clear - Fsc Fml Hcr Hstr Hugr Hsd16 Hsc X2 X1; lia] | solve [Zify.zify; try pose proof I as __sat4098; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as X2; try pose proof I as X1; clear - __sat4098 __sat4114 Fsc Fml Hcr Hstr Hugr Hsd16 Hsc X2 X1; xlia zchecker] | lia]).
      - rewrite Fml. intros Hm. apply Bool.orb_prop in D7 as [X|X]; [apply Z.eqb_eq in X; (first [solve [try pose proof I as Hm; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as X; try pose proof I as Eq; try pose proof I as HSlo'; try pose proof I as Hohi'; clear - Hm Fsc Fml Hcr HSvr Hstr Hugr HShi' Hidx1 Hsd16 Hsc X Eq HSlo' Hohi'; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Hm; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as X; try pose proof I as heq_o; try pose proof I as Eq; try pose proof I as HSlo'; try pose proof I as Hohi'; clear - __sat4114 Hm Fsc Fml Hcr HSvr Hstr Hugr HShi' Hidx1 Hsd16 Hsc X heq_o Eq HSlo' Hohi'; xlia zchecker] | lia]) | apply Z.leb_le in X; rewrite Hq16 in X; (first [solve [try pose proof I as Hm; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as X; try pose proof I as Eq; try pose proof I as HSlo'; try pose proof I as Hohi'; clear - Hm Fsc Fml Hcr HSvr Hstr Hugr HShi' Hidx1 Hsd16 Hsc X Eq HSlo' Hohi'; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Hm; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as X; try pose proof I as heq_o; try pose proof I as Eq; try pose proof I as HSlo'; try pose proof I as Hohi'; clear - __sat4114 Hm Fsc Fml Hcr HSvr Hstr Hugr HShi' Hidx1 Hsd16 Hsc X heq_o Eq HSlo' Hohi'; xlia zchecker] | lia])].
      - lia.
      - exact D9.
      - lia.
      - exact D10.
      - lia.
      - (first [solve [try pose proof I as HWr; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as HWv; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Eev; try pose proof I as Eg; try pose proof I as Ee; try pose proof I as Est; try pose proof I as Hor; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hhh'; try pose proof I as Hghi'; try pose proof I as Hohi'; try pose proof I as D27; try pose proof I as D25; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D7; clear - HWr Fsc Fml HWv Hcr Hq16 Eev Eg Ee Est Hor Hstr Hugr Hshi' Hehi' HShi' HSlo' Hhh' Hghi' Hohi' D27 D25 D24 Hidx1 Hsd16 Hsc Pr D7; lia] | solve [Zify.zify; try pose proof I as __sat4099; try pose proof I as __sat4114; try pose proof I as heq_sd; try pose proof I as heq_o; try pose proof I as HWr; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as HWv; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Eev; try pose proof I as Eg; try pose proof I as Ee; try pose proof I as Est; try pose proof I as Hor; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hhh'; try pose proof I as Hghi'; try pose proof I as Hohi'; try pose proof I as D27; try pose proof I as D25; try pose proof I as D24; try pose proof I as Hidx1; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D7; clear - __sat4099 __sat4114 heq_sd heq_o HWr Fsc Fml HWv Hcr Hq16 Eev Eg Ee Est Hor Hstr Hugr Hshi' Hehi' HShi' HSlo' Hhh' Hghi' Hohi' D27 D25 D24 Hidx1 Hsd16 Hsc Pr D7; xlia zchecker] | lia]).
      - apply WST. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      - subst pv. exact P4.
      - subst pv rv. exact P3.
      - subst pv. rewrite Eq. exact P2.
      - subst pv rv. exact Pzr.
      - subst ev rv. exact Pe5.
      - subst ev rv. exact Pe4.
      - subst ev. exact Fend.
      - subst Mv g. exact Fmeta.
      - subst g. replace (ug + gk + 16) with (ug + (gk + 16)) by lia. exact Fmem.
      - subst g. replace (ug + gk + 32) with (ug + (gk + 32)) by lia. exact FW.
      - subst g. replace (ug + gk + 24) with (ug + (gk + 24)) by lia. exact Fav.
      - subst g. replace (ug + gk + 28) with (ug + (gk + 28)) by lia. exact Ffr.
      - replace (g - g mod 4096) with (ug + ak).
        2:{ subst g ak. rewrite Z.add_mod, HGal, Z.add_0_l, Z.mod_mod by lia. lia. }
        exact Farea.
      - rewrite D16. exact Fsec.
      - intros j Hj. apply TBL. lia. }
    (* [comment removed for export] *)
    assert (R2' : getr R 2%bv = Z_to_bv 64 sp) by (rewrite <- R2; f_equal; apply bv_eq; reflexivity).
    assert (R10' : getr R 10%bv = Z_to_bv 64 pv).
    { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite R10. exact HpaV. }
    destruct (FRP R M (seg_rom SEGS) sp pv ev Mv g idx o n sd rv q W avail freed (edenot E sec) PRE R2' R10')
      as (regs' & RUN & Q2 & Q9 & Q8 & Q10 & Q11 & Q14 & Q15 & Q18 & Q19 & Q3 & Q4 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    rewrite <- Hpc in RUN.
    destruct (w_fresh_ok_parts nx0 cs D33) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := ext_call E (nxt cs) regs').
    pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
    set (MR' := free_mem1 M sp (getr R 1%bv) (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv)) in RUN.
    assert (LEN : forall vv : word, length (word_to_le_bytes 8 vv) = 8%nat) by (intros; apply length_N_to_le_bytes).
    assert (FRM : forall x : word, bv_unsigned x < sp - 40 \/ sp <= bv_unsigned x -> MR' x = M x).
    { intros x Hx. unfold MR', free_mem1.
      rewrite !Frame.wbytes_outside; try (rewrite LEN; first [rewrite u_lit by (unfold two64; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - __sat4114 heq_ak Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; xlia zchecker] | lia])); (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - __sat4114 heq_ak Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; xlia zchecker] | lia])
                                                             | unfold Frame.in_rng; rewrite u_lit by (unfold two64; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - __sat4114 heq_ak Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; xlia zchecker] | lia])); (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; try pose proof I as Hx; clear - __sat4114 heq_ak Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17 Hx; xlia zchecker] | lia])]).
      reflexivity. }
    set (KW := [(SA spb (spk - 48), ELit 48)]).
    set (P := fun Mx : word -> option byte => props_ok GP E' Mx (MN2.keep_props G (kn cs) KW (nxt cs) (a_props cs))).
    eapply (call_core_p P cs E E' R FULL model T (mt_free_k MTB) _ _ (nxt cs + NCS)%nat (MN2.keep_props G (kn cs) KW (nxt cs) (a_props cs))
              regs' MR' HC D33 Hag RUN).
    - (* [comment removed for export] *)
      pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
      assert (AG : forall ex, expr_vars_lt (nxt cs) ex = true -> edenot E' ex = edenot E ex).
      { intros ex Hex. symmetry. apply (edenot_agree' (nxt cs) E E' ex Hag Hex). }
      apply (regs_freehead E (nxt cs) (s_regs (a_ss cs)) R regs' HR Fsr).
      + intros kk Hkin. cbn [In] in Hkin.
        repeat (destruct Hkin as [<-|Hkin]; [first [exact Q3 | exact Q4 | exact Q18 | exact Q19 | exact Q20 | exact Q21 | exact Q22 | exact Q23
                                               | exact Q24 | exact Q25 | exact Q26 | exact Q27] |]). destruct Hkin.
      + fold E'. transitivity (edenot E' (EAlu ALU_ADD spb (ELit (spk - 48)))); [|reflexivity].
        etransitivity; [exact Q2|]. cbn [edenot]. rewrite (AG spb Vsp). apply add_lit_word; subst sp usp; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4114 heq_ak Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia]).
      + fold E'. rewrite AG by exact D37. rewrite HpaV. exact Q9.
      + fold E'. rewrite edenot_lit. exact Q8.
      + fold E'. rewrite AG by exact D34. rewrite HGd. exact Q10.
      + fold E'. rewrite AG by exact D38. replace (edenot E Ws) with (Z_to_bv 64 W : word) by (subst W; apply Z_to_bv_bv_unsigned). exact Q11.
      + fold E'. rewrite AG by exact D35. etransitivity; [exact Q14|]. symmetry. subst rexp. apply bv_eq.
        rewrite mkAlu_denot, u_sub64, Dste, mkAlu_denot, u_add64, u_lit64a. fold n.
        unfold MN2.times16. rewrite mkMd_denot, u_mul64, edenot_lit, u_lit64a. fold o.
        rewrite (Z.mod_small 16) by lia. rewrite (Z.mod_small (16 * o)) by (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hfit; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; clear - Fsc Hcr Hor Hnr Hstr Hugr Hfit Hidx1 Hsd31 Hsd16; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hfit; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; clear - __sat4114 Fsc Hcr Hor Hnr Hstr Hugr Hfit Hidx1 Hsd31 Hsd16; xlia zchecker] | lia]). rewrite (Z.mod_small (n + 16 * o)) by (first [solve [try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hq16; try pose proof I as Hor; clear - Fsc Fml Hcr HSvr Hq16 Hor; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_o; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as HSvr; try pose proof I as Hq16; try pose proof I as Hor; clear - __sat4114 heq_o Fsc Fml Hcr HSvr Hq16 Hor; xlia zchecker] | lia]).
        rewrite (Z.mod_small (sd - 4 - (n + 16 * o))) by (first [solve [try pose proof I as Hcr; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Holo'; try pose proof I as Hsd31; try pose proof I as Hsd16; try pose proof I as Pr; try pose proof I as D8; clear - Hcr Hor Hnr Hstr Hugr Holo' Hsd31 Hsd16 Pr D8; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_o; try pose proof I as Hcr; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Holo'; try pose proof I as Hsd31; try pose proof I as Hsd16; try pose proof I as Pr; try pose proof I as D8; clear - __sat4114 heq_o Hcr Hor Hnr Hstr Hugr Holo' Hsd31 Hsd16 Pr D8; xlia zchecker] | lia]). rewrite (Z.mod_small rv) by (first [solve [try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Erv; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Holo'; try pose proof I as Hfit; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D8; try pose proof I as D7; clear - Fsc Fml Hcr Hq16 Erv Hor Hnr Hstr Hugr HShi' HSlo' Hohi' Holo' Hfit Hidx1 Hsd31 Hsd16 Hsc Pr D8 D7; lia] | solve [Zify.zify; try pose proof I as __sat4099; try pose proof I as __sat4114; try pose proof I as heq_o; try pose proof I as Fsc; try pose proof I as Fml; try pose proof I as Hcr; try pose proof I as Hq16; try pose proof I as Erv; try pose proof I as Hor; try pose proof I as Hnr; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as HShi'; try pose proof I as HSlo'; try pose proof I as Hohi'; try pose proof I as Holo'; try pose proof I as Hfit; try pose proof I as Hidx1; try pose proof I as Hsd31; try pose proof I as Hsd16; try pose proof I as Hsc; try pose proof I as Pr; try pose proof I as D8; try pose proof I as D7; clear - __sat4099 __sat4114 heq_o Fsc Fml Hcr Hq16 Erv Hor Hnr Hstr Hugr HShi' HSlo' Hohi' Holo' Hfit Hidx1 Hsd31 Hsd16 Hsc Pr D8 D7; xlia zchecker] | lia]). (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Erv; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - Fsc Hcr Erv Hstr Hugr Hsd16; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Erv; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hsd16; clear - __sat4114 Fsc Hcr Erv Hstr Hugr Hsd16; xlia zchecker] | lia]).
      + fold E'. rewrite AG by exact D36. etransitivity; [exact Q15|]. symmetry. subst e12. apply bv_eq.
        rewrite mkAlu_denot, u_add64, mkAlu_denot, u_add64, edenot_lit, !u_lit64a. fold st sd.
        replace ((-16) mod 2 ^ 64) with (2 ^ 64 - 16) by reflexivity.
        replace (sd + (2 ^ 64 - 16)) with ((sd - 16) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
        rewrite (Z.mod_small (sd - 16)) by lia. rewrite !Z.mod_small by (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMe; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; try pose proof I as D20; try pose proof I as Eev; try pose proof I as Ee; try pose proof I as Est; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; clear - Fsc Hcr EMe Esi Hstr Hugr Hmlo' Hidx1 Hnw Hsd16 D20 Eev Ee Est Hshi' Hehi' Hhh' D28 D24; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as EMe; try pose proof I as Esi; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hmlo'; try pose proof I as Hidx1; try pose proof I as Hnw; try pose proof I as Hsd16; try pose proof I as D20; try pose proof I as heq_sd; try pose proof I as Eev; try pose proof I as Ee; try pose proof I as Est; try pose proof I as Hshi'; try pose proof I as Hehi'; try pose proof I as Hhh'; try pose proof I as D28; try pose proof I as D24; clear - __sat4114 Fsc Hcr EMe Esi Hstr Hugr Hmlo' Hidx1 Hnw Hsd16 D20 heq_sd Eev Ee Est Hshi' Hehi' Hhh' D28 D24; xlia zchecker] | lia]). subst ev. lia.
    - (* [comment removed for export] *)
      apply (know_ok_agree' SEGS (nxt cs) E E'); [exact Hag | exact Vk1 |].
      assert (GRW : mem_grows M MR').
      { unfold MR', free_mem1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
      assert (HIT : forall m (a vv : word), bv_unsigned a + 8 <= 2 ^ 64 ->
               rdn SEGS (wbytes m a (word_to_le_bytes 8 vv)) a 8 = Some (word_to_le_bytes 8 vv)).
      { intros m a vv Ha. pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 vv) m a) as X. rewrite LEN in X. apply X. exact Ha. }
      assert (SAVE : forall (k : Z) (r : nat) (vv : word), (0 < r < 32)%nat -> 8 <= k <= 40 ->
                getr R (Z_to_bv 5 (Z.of_nat r)) = vv ->
                rdn SEGS MR' (Z_to_bv 64 (sp - k)) 8 = Some (word_to_le_bytes 8 vv) ->
                kentry_ok SEGS E MR' (KWord (SA spb (spk - k)) 8 (reg cs r))).
      { intros k r vv Hr Hkr Hv Hrd. cbn [kentry_ok]. split; [lia|].
        assert (ES : estart E (SA spb (spk - k)) = sp - k) by (rewrite ESTS; subst sp; lia).
        split; [unfold flat; rewrite ES; (first [solve [try pose proof I as Hkr; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hkr Fsc Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as Hkr; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4114 heq_ak Hkr Fsc Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia])|].
        rewrite adenot_SA, ES, <- (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model r HC Hr), Hv. exact Hrd. }
      assert (SPR : 48 <= sp < 2 ^ 64) by lia.   (* [comment removed for export] *)
      #[local] Ltac peel LEN SPR := rewrite rdn_wbytes_out;
        [ | rewrite LEN, !u_lit by (unfold two64; clear - SPR; lia); clear - SPR; lia | rewrite u_lit by (unfold two64; clear - SPR; lia); clear - SPR; lia | rewrite LEN, u_lit by (unfold two64; clear - SPR; lia); clear - SPR; lia ].
      apply Forall_app. split.
      + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
        * apply (SAVE 8 1%nat (getr R 1%bv) ltac:(lia) ltac:(lia) ltac:(f_equal; apply bv_eq; reflexivity)).
          unfold MR', free_mem1. peel LEN SPR. peel LEN SPR. peel LEN SPR. peel LEN SPR. apply HIT. rewrite u_lit by (unfold two64; (first [solve [try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4114 heq_ak Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia])). lia.
        * apply (SAVE 16 8%nat (getr R 8%bv) ltac:(lia) ltac:(lia) ltac:(f_equal; apply bv_eq; reflexivity)).
          unfold MR', free_mem1. peel LEN SPR. peel LEN SPR. peel LEN SPR. apply HIT. rewrite u_lit by (unfold two64; lia). lia.
        * apply (SAVE 24 9%nat (getr R 9%bv) ltac:(lia) ltac:(lia) ltac:(f_equal; apply bv_eq; reflexivity)).
          unfold MR', free_mem1. peel LEN SPR. peel LEN SPR. apply HIT. rewrite u_lit by (unfold two64; lia). lia.
        * apply (SAVE 32 18%nat (getr R 18%bv) ltac:(lia) ltac:(lia) ltac:(f_equal; apply bv_eq; reflexivity)).
          unfold MR', free_mem1. peel LEN SPR. apply HIT. rewrite u_lit by (unfold two64; lia). lia.
        * apply (SAVE 40 19%nat (getr R 19%bv) ltac:(lia) ltac:(lia) ltac:(f_equal; apply bv_eq; reflexivity)).
          unfold MR', free_mem1. apply HIT. rewrite u_lit by (unfold two64; lia). lia.
      + apply Forall_cons.
        * (* [comment removed for export] *)
          cbn [kentry_ok]. rewrite ESTS. replace (usp + (spk - 48)) with (sp - 48) by (subst sp; lia).
          change (elenZ E (ELit 48)) with (48 mod two64). rewrite Z.mod_small by (unfold two64; lia).
          split; [unfold flat; rewrite ESTS; (first [solve [try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - Fsc Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; lia] | solve [Zify.zify; try pose proof I as __sat4114; try pose proof I as heq_ak; try pose proof I as heq_sp; try pose proof I as Fsc; try pose proof I as Hcr; try pose proof I as Hak; try pose proof I as Hstr; try pose proof I as Hugr; try pose proof I as Hghi'; try pose proof I as Hglo'; try pose proof I as D28; try pose proof I as D25; try pose proof I as Hsd16; try pose proof I as D17; clear - __sat4114 heq_ak heq_sp Fsc Hcr Hak Hstr Hugr Hghi' Hglo' D28 D25 Hsd16 D17; xlia zchecker] | lia])|].
          intros i Hi. apply (mem_grows_defined M MR' _ GRW).
          assert (W48 : store_ok SEGS M (Z_to_bv 64 (sp - 48)) 48 = true) by (apply WST; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia).
          clear - D26 D27 D28 D29 W48 Hi SEGS_in_hull.
          exact (store_ok_defined_out_image M (sp - 48) 48%nat ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
                   ltac:(intros z Hz; right; lia) W48 i ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
        * eapply (w_know_ok_havoc SEGS E M MR' (kn cs) spb (spk - 48) (ELit 48) HKN); [|exact GRW].
          intros x Hx. apply FRM. rewrite ESTS in Hx.
          change (elenZ E (ELit 48)) with (48 mod two64) in Hx. rewrite Z.mod_small in Hx by (unfold two64; lia). subst sp. lia.
    - (* [comment removed for export] *)
      subst P. cbv beta. eapply (props_ok_agree GP (nxt cs) E E'); [| apply MN2.keep_props_vars | exact Hag].
      apply (keep_props_sound E E M MR' M (kn cs) KW (nxt cs) (a_props cs) HPR (env_agree_refl _ _) HKN).
      intros a Ha. specialize (Ha _ (or_introl eq_refl)). cbn [fst snd] in Ha.
      rewrite ESTS in Ha.
      change (elenZ E (ELit 48)) with (48 mod two64) in Ha. rewrite Z.mod_small in Ha by (unfold two64; lia).
      apply FRM. subst sp. lia.
    - (* [comment removed for export] *)
      intros R' FULL' model' HC' Hfs1 HP'. apply (Hk E' R' FULL' model'); [| exact HC' | | exact Hfs1].
      + split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
      + unfold set_props. cbn [a_props]. exact HP'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem xn2_soundG : forall id, ext_stmtG SEGS A nx0 LIMIT (MN2.xn SEGS A nx0 MTB G) SINV argH FS0 GP id.
  Proof.
    intros id args cs cs' E R FULL model T HC HPR Hn Hk. unfold MN2.xn in Hn.
    destruct id as [|id]; [discriminate|]. do 19 (destruct id as [|id]; [discriminate|]).
    destruct id as [|id].
    { (* [comment removed for export] *)
      rewrite MN2.node_enframe2M_eq in Hn. exact (node_enframe2_sound args cs cs' E R FULL model T HC HPR Hn Hk). }
    destruct id as [|id].
    { (* [comment removed for export] *)
      rewrite MN2.node_freehead2M_eq in Hn. exact (node_freehead2_sound args cs cs' E R FULL model T HC HPR Hn Hk). }
    discriminate Hn.
  Qed.
End Sound.
