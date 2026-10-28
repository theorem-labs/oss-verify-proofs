(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMX.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.            (* [comment removed for export] *)
Variable WD_SCR : Z.                (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kenc (eg : PMES.eghost) : Z := (PMES.kv_s2 (PMES.g_rep eg) + PMES.kv_st (PMES.g_scap eg)) * hl_k_per_malloc L.
(* [comment removed for export] *)
Definition KEY_STATES : list Z := [ST_EXPECT_MEMBER_NAME_OR_END; ST_EXPECT_MEMBER_NAME; ST_EXPECT_COLON].
Definition key_inv (ps : pstate) : Prop :=
  ps_more ps = true -> (In (ps_st ps) KEY_STATES \/ (exists x, In x (ps_stack ps) /\ In x (ST_MEMBER_NAME :: KEY_STATES))) -> 1 <= ps_level ps.
Definition enc_sync (ps : pstate) (eg : PMES.eghost) : Prop := PMES.depth (PMES.g_es eg) = ps_level ps /\ key_inv ps.
Definition W_parx (P V E S2 : Z) : list L5.range := W_par P E ++ PMES.W_enc V S2.

Lemma key_inv_pos : forall ps, 1 <= ps_level ps -> key_inv ps.
Proof. intros ps H _ _. exact H. Qed.
Lemma key_inv_stopped : forall ps, ps_more ps = false -> key_inv ps.
Proof. intros ps H Hm. rewrite H in Hm. discriminate Hm. Qed.
Lemma key_inv_same : forall ps ps', ps_st ps' = ps_st ps -> ps_stack ps' = ps_stack ps -> ps_level ps' = ps_level ps -> ps_more ps = true -> key_inv ps -> key_inv ps'.
Proof. intros ps ps' H1 H2 H3 H4 K Hm Hx. rewrite H1, H2, H3 in *. exact (K H4 Hx). Qed.
(* [comment removed for export] *)
Lemma key_inv_plain : forall ps, wf_ps ps -> ps_more ps = true -> ~ In (ps_st ps) KEY_STATES -> ~ comment_or_cr (ps_st ps) -> ps_st ps <> ST_STRING -> key_inv ps.
Proof.
  intros ps HW Hm Hk Hc Hs _ [Hx|(x & Hin & Hx)]; [exact (False_ind _ (Hk Hx))|]. exfalso.
  destruct HW as (_ & _ & _ & _ & C & T & Hstk & HC & HM). destruct (HM Hm) as (_ & _ & _ & HT & _).
  assert (HT0 : T = []).
  { destruct HT as [[-> _]|[[-> Hst]|[(S & _ & -> & Hcc)|(S & _ & -> & Hst)]]]; [reflexivity | exact (False_ind _ (Hs Hst)) | exact (False_ind _ (Hc Hcc)) | exfalso; apply Hc; rewrite Hst; right; reflexivity]. }
  rewrite HT0, app_nil_r in Hstk. rewrite Hstk in Hin. destruct Hin as [<-|Hin].
  - unfold ST_ROOT, ST_MEMBER_NAME, KEY_STATES, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON in Hx. cbn in Hx. lia.
  - pose proof (proj1 (Forall_forall _ _) HC x Hin) as Hcx. unfold is_container, ST_OBJECT, ST_ARRAY in Hcx.
    unfold ST_MEMBER_NAME, KEY_STATES, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON in Hx. cbn in Hx. lia.
Qed.
(* [comment removed for export] *)
Lemma key_inv_setwin : forall ps w, key_inv ps -> key_inv (ps_set_win ps w).
Proof. intros ps w H. destruct ps. exact H. Qed.
Lemma key_inv_setnst : forall ps n, key_inv ps -> key_inv (ps_set_nst ps n).
Proof. intros ps n H. destruct ps. exact H. Qed.
(* [comment removed for export] *)
Definition key_ok (ps : pstate) : Prop := forall rest, ps_stack ps = rest ++ [ST_MEMBER_NAME] -> 1 <= ps_level ps.
Lemma key_ok_of_inv : forall ps, key_inv ps -> ps_more ps = true -> key_ok ps.
Proof. intros ps K Hm rest Hs. apply (K Hm). right. exists ST_MEMBER_NAME. split; [rewrite Hs; apply in_or_app; right; left; reflexivity | left; reflexivity]. Qed.
(* [comment removed for export] *)
Lemma key_inv_push : forall ps ps' x, ps_more ps = true -> ps_stack ps' = ps_stack ps ++ [x] -> ps_level ps' = ps_level ps -> key_inv ps ->
  (In (ps_st ps') KEY_STATES \/ In x (ST_MEMBER_NAME :: KEY_STATES) -> In (ps_st ps) KEY_STATES \/ 1 <= ps_level ps) -> key_inv ps'.
Proof.
  intros ps ps' x Hm Hs Hl K Himp Hm' [Hst|(y & Hin & Hy)]; rewrite Hl.
  - destruct (Himp (or_introl Hst)) as [H|H]; [exact (K Hm (or_introl H)) | exact H].
  - rewrite Hs in Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
    + exact (K Hm (or_intror (ex_intro _ y (conj Hin Hy)))).
    + destruct (Himp (or_intror Hy)) as [H|H]; [exact (K Hm (or_introl H)) | exact H].
Qed.
(* [comment removed for export] *)
Lemma key_inv_pop : forall ps ps' x, ps_more ps = true -> ps_stack ps = ps_stack ps' ++ [x] -> ps_level ps' = ps_level ps -> key_inv ps ->
  (In (ps_st ps') KEY_STATES -> In (ps_st ps) KEY_STATES \/ In x KEY_STATES \/ 1 <= ps_level ps) -> key_inv ps'.
Proof.
  intros ps ps' x Hm Hs Hl K Himp Hm' [Hst|(y & Hin & Hy)]; rewrite Hl.
  - destruct (Himp Hst) as [H|[H|H]]; [exact (K Hm (or_introl H)) | | exact H].
    apply (K Hm). right. exists x. split; [rewrite Hs; apply in_or_app; right; left; reflexivity | right; exact H].
  - apply (K Hm). right. exists y. split; [rewrite Hs; apply in_or_app; left; exact Hin | exact Hy].
Qed.
(* [comment removed for export] *)
Lemma key_inv_sub : forall ps ps', ps_more ps = true -> key_inv ps -> (forall x, In x (ps_stack ps') -> In x (ps_stack ps)) -> ps_level ps' = ps_level ps ->
  (ps_more ps' = true -> In (ps_st ps') KEY_STATES -> 1 <= ps_level ps) -> key_inv ps'.
Proof.
  intros ps ps' Hm K Hsub Hl Hst Hm' [Hin|(x & Hin & Hx)]; rewrite Hl; [exact (Hst Hm' Hin)|]. apply (K Hm). right. exists x. exact (conj (Hsub x Hin) Hx).
Qed.
(* [comment removed for export] *)
Lemma key_inv_cont : forall ps C, ps_stack ps = ST_ROOT :: C -> Forall is_container C -> (ps_more ps = true -> In (ps_st ps) KEY_STATES -> 1 <= ps_level ps) -> key_inv ps.
Proof.
  intros ps C Hs HC Hst Hm [Hin|(x & Hin & Hx)]; [exact (Hst Hm Hin)|]. exfalso. rewrite Hs in Hin. destruct Hin as [<-|Hin].
  - unfold ST_ROOT, ST_MEMBER_NAME, KEY_STATES, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON in Hx. cbn in Hx. lia.
  - pose proof (proj1 (Forall_forall _ _) HC x Hin) as Hcx. unfold is_container, ST_OBJECT, ST_ARRAY in Hcx.
    unfold ST_MEMBER_NAME, KEY_STATES, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON in Hx. cbn in Hx. lia.
Qed.
(* [comment removed for export] *)
Lemma key_inv_init : forall sb bptr, key_inv (PMS.ps_init sb bptr).
Proof.
  intros sb bptr _ [H|(x & H & Hx)]; cbn in H.
  - unfold ST_START, KEY_STATES, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON in H. cbn in H. exfalso. lia.
  - destruct H as [<-|[]]. unfold ST_ROOT, ST_MEMBER_NAME, KEY_STATES, ST_EXPECT_MEMBER_NAME_OR_END, ST_EXPECT_MEMBER_NAME, ST_EXPECT_COLON in Hx. cbn in Hx. exfalso. lia.
Qed.
Definition objs_x (sp P V E S2 : Z) : Prop :=
  obj_on_stack L sp P 272 /\ obj_on_stack L sp V PMES.ENC_SIZE /\ obj_on_stack L sp S2 24 /\ obj_on_stack L sp E 16 /\
  apart P 272 V PMES.ENC_SIZE /\ apart P 272 S2 24 /\ apart P 272 E 16 /\ apart V PMES.ENC_SIZE S2 24 /\ apart V PMES.ENC_SIZE E 16 /\ apart S2 24 E 16.
(* [comment removed for export] *)
Lemma objs_x_j : forall sp P V E S2, objs_x sp P V E S2 ->
  obj_on_stack L sp P 272 /\ obj_on_stack L sp V 8 /\ obj_on_stack L sp E 16 /\ apart P 272 V 8 /\ apart P 272 E 16 /\ apart V 8 E 16.
Proof.
  unfold objs_x, obj_on_stack, apart, PMES.ENC_SIZE. intros sp P V E S2 (HP & HV & HS & HE & A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; try tauto; try lia.
Qed.
(* [comment removed for export] *)
Definition pbytes (ps : pstate) : Z := bleft ps + kleft ps * hl_b_overhead L.
Lemma kenc_eq : forall eg, kenc eg = PMES.kenc L eg.
Proof. reflexivity. Qed.
Lemma ecredit_of_pxU : forall cr ps eg kx bx, pcredit_x L cr ps (kx + PMES.kenc L eg) (bx + PMES.benc L eg) -> 0 <= kx -> 0 <= bx ->
  0 <= PMES.kenc L eg -> 0 <= PMES.benc L eg -> 0 <= kleft ps * hl_k_per_malloc L -> 0 <= pbytes ps ->
  PMES.ecreditU L cr eg (kx + kleft ps * hl_k_per_malloc L) (bx + pbytes ps).
Proof.
  unfold pcredit_x, pcredit, PMES.ecreditU, pbytes. cbn [fst snd].
  intros cr ps eg kx bx (H0 & H1 & H2 & H3 & H4) Hk Hb He Hbe Hp Hq. repeat split; lia.
Qed.
Lemma px_of_ecreditU : forall cr cr' ps eg eg' kx bx, pcredit_x L cr ps (kx + PMES.kenc L eg) (bx + PMES.benc L eg) -> 0 <= kx -> 0 <= bx ->
  0 <= PMES.kenc L eg' -> 0 <= PMES.benc L eg' ->
  PMES.ecreditU L cr' eg' (kx + kleft ps * hl_k_per_malloc L) (bx + pbytes ps) ->
  pcredit_x L cr' ps (kx + PMES.kenc L eg') (bx + PMES.benc L eg').
Proof.
  unfold pcredit_x, pcredit, PMES.ecreditU, pbytes. cbn [fst snd].
  intros cr cr' ps eg eg' kx bx (H0 & H1 & H2 & H3 & H4) Hk Hb He Hbe (E0 & E1 & E2 & E3).
  split; [lia|]. split; [lia|]. split; [exact H2|]. split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VIS_SCR : Z := PMES.VIS_SCR WD_SCR.
Definition PFX_SCR : Z := 2048 + Z.max (Z.max PMS.OPNEW_SCR STRTOD_SCR) VIS_SCR.          (* [comment removed for export] *)
Definition ESVX_SCR : Z := 512 + VIS_SCR.                                                   (* [comment removed for export] *)
Definition ENDNUMX_SCR : Z := 512 + Z.max (Z.max 256 STRTOD_SCR) VIS_SCR.                   (* [comment removed for export] *)
Definition PSOMEX_SCR : Z := 128 + PFX_SCR.
Definition READNEXTX_SCR : Z := 80 + 64 + PSOMEX_SCR.
Definition READX_SCR : Z := 32 + READNEXTX_SCR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ptrans_gbx (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : ls_state) (ps : pstate) (eg : PMES.eghost),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr                                                            (* [comment removed for export] *)
      (fun R M => entry L R M sp r scr /\ Args LBo R M P V E ps /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ enc_sync ps eg /\                                                         (* [comment removed for export] *)
                  0 <= kx /\ pcredit_x L cr ps (kx + kenc eg) bx /\                                                                (* [comment removed for export] *)
                  objs_x sp P V E S2)                                                                                              (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ wf_ps ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> enc_sync ps' eg') /\                                              (* [comment removed for export] *)
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = W_parx P V E S2 /\                                      (* [comment removed for export] *)
          pcredit_x L cr' ps' (kx + kenc eg') bx /\ Rel ps ps' code R').                                                           (* [comment removed for export] *)
Definition ptrans_gx := ptrans_gbx wf_ps buf_bound.
Definition ptransx := ptrans_gx parser_at (fun _ => parser_at).
Definition ptrans_curx := ptrans_gx parser_at (fun ps M' P ps' => parser_at M' P (ps_set_win ps' (ps_win ps))).
Definition ptrans_stalex (pc scr : Z) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbx wf_ps_stale (PMS.buf_bound_stale) (fun M P ps => parser_at M P (ps_set_win ps mw)) (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition begin_container_specx (pc kind st' : Z) : Prop :=
  ptransx pc PFX_SCR (fun _ R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps + 1 /\ ps_st ps' = st' /\ ps_more ps' = true /\ ps_stack ps' = ps_stack ps ++ [kind] /\ ps_win ps' = ps_win ps)
            \/ (code = 5 /\ ps_level ps = 1024)).
Definition begin_object_specx := begin_container_specx PC_BEGIN_OBJECT ST_OBJECT ST_EXPECT_MEMBER_NAME_OR_END.
Definition begin_array_specx := begin_container_specx PC_BEGIN_ARRAY ST_ARRAY ST_EXPECT_VALUE_OR_END.
(* [comment removed for export] *)
Definition end_container_specx (pc kind : Z) : Prop :=
  ptransx pc PFX_SCR (fun _ R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps - 1 /\ ps_more ps' = true /\ (exists rest, ps_stack ps = rest ++ [kind] /\ ps_stack ps' = rest) /\
             ps_st ps' = (if Z.eqb (ps_level ps') 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\ ps_win ps' = ps_win ps)
            \/ In code [20; 21; 22; 23]).
Definition end_object_specx := end_container_specx PC_END_OBJECT ST_OBJECT.
Definition end_array_specx := end_container_specx PC_END_ARRAY ST_ARRAY.
(* [comment removed for export] *)
Definition parse_true_specx : Prop :=
  ptrans_curx PC_PARSE_TRUE PFX_SCR (fun _ R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code /\ PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_false_specx : Prop :=
  ptrans_curx PC_PARSE_FALSE PFX_SCR (fun _ R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code /\ PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_null_specx : Prop :=
  ptransx PC_PARSE_NULL PFX_SCR (fun _ R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code).
(* [comment removed for export] *)
Definition end_string_value_specx : Prop :=
  ptrans_stalex PC_END_STRING ESVX_SCR
         (fun LB R M P V E ps => a0 R P /\ a3 R V /\ getr R 14%bv = Z_to_bv 64 E /\ ps_more ps = true /\ ps_st ps = ST_STRING /\ key_ok ps /\      (* [comment removed for export] *)
                              exists s len, a1 R s /\ a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                            4096 <= s /\ s + len <= hl_ceil L /\ PMES.in_blocks (ps_blocks ps ++ LB) s len)      (* [comment removed for export] *)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_more ps' = true /\ ps_level ps' = ps_level ps /\
             In (ps_st ps') [ST_EXPECT_COLON; ST_EXPECT_COMMA_OR_END; ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).
(* [comment removed for export] *)
Definition parse_string_specx : Prop :=
  ptrans_curx PC_PARSE_STRING PFX_SCR (fun _ R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_STRING /\ key_ok ps)      (* [comment removed for export] *)
         (fun ps ps' code R' => PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code <> 0 \/ PMS.consumed ps ps' \/ PMS.win_exhausted ps) /\
                                (code = 0 -> ps_more ps' = true /\ ps_level ps' = ps_level ps)).
(* [comment removed for export] *)
Definition end_number_specx (pc : Z) : Prop :=
  ptrans_stalex pc ENDNUMX_SCR (fun _ R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER /\ num_final (ps_buf ps))
         (fun ps ps' code R' => (code = 0 /\ ps_more ps' = true /\ ps_st ps' = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
                                 ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps) \/ code = 19).
Definition end_integer_value_specx := end_number_specx PC_END_INT.
Definition end_fraction_value_specx := end_number_specx PC_END_FRAC.
(* [comment removed for export] *)
Definition parse_number_specx : Prop :=
  ptrans_curx PC_PARSE_NUMBER PFX_SCR (fun _ R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER)
         (fun ps ps' code R' => PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code = 0 -> ps_level ps' = ps_level ps /\ ps_more ps' = true /\ (ps_st ps' = ST_NUMBER -> PMS.win_exhausted ps') /\
                                             In (ps_st ps') [ST_NUMBER; ST_ACCEPT; ST_EXPECT_COMMA_OR_END])).
(* [comment removed for export] *)
Definition parse_some_specx : Prop :=
  ptransx PC_PARSE_SOME PSOMEX_SCR (fun _ R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true)
         (fun ps ps' code R' =>
            (code <> 0 \/ ps_more ps' = false \/ PMS.win_exhausted ps') /\
            (ps_st ps = ST_ACCEPT -> code = 0 /\ ps_more ps' = false /\ ps_done ps' = true) /\
            (PMS.win_exhausted ps -> code = 0 -> ps_more ps' = true -> In (ps_st ps) [ST_NUMBER; ST_CR] /\ ~ In (ps_st ps') [ST_NUMBER; ST_CR]) /\
            (code = 0 -> ws_ok ps')).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition read_specx : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r Rr IS V E S2 ch gp sb bptr kx bx : Z) (rep : srep) (g : ls_state) (eg : PMES.eghost),
    let ps := PMS.ps_init sb bptr in
    cps_heap L HI PC_READ r sp READX_SCR (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr
      (fun R M => entry L R M sp r READX_SCR /\ a0 R Rr /\ a1 R E /\
                  PMS.reader_pre L M LBo Rr IS V E ch rep gp 0 true ps sp /\ gp = srep_data (IS + 80) rep /\
                  (forall b, In b (srep_blocks rep) -> fst b <> ch) /\
                  Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\ ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ enc_sync ps eg /\
                  0 <= kx /\ pcredit_x L cr ps (kx + kenc eg) bx /\
                  obj_on_stack L sp V PMES.ENC_SIZE /\ obj_on_stack L sp S2 24 /\ apart V PMES.ENC_SIZE S2 24 /\
                  apart Rr 592 V PMES.ENC_SIZE /\ apart Rr 592 S2 24 /\ apart IS 272 V PMES.ENC_SIZE /\ apart IS 272 S2 24 /\ apart V PMES.ENC_SIZE E 16 /\ apart S2 24 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : ls_state) (eg' : PMES.eghost),
          source_at M' Rr ch /\ parser_at M' (Rr + 320) ps' /\ isrc_at M' IS rep gp' rdst' /\ ec_at M' E code /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = lb_remove ch LBo /\ pcredit_x L cr' ps' (kx + kenc eg') bx /\ wf_ps ps' /\
          W = [(Rr, 592); (IS, 272); (E, 16); (0xdb5c0, 2); (0xfd058, 544)] ++ PMES.W_enc V S2).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_SCRX : Z := 1376 + Z.max READX_SCR (Z.max (Z.max PMS.RCTOR_SCR PMS.ISS_SCR) (PMES.ENC_CTOR_SCR)).
Definition pm_staticsx : lib_statics := {| LibIface.ls_state := PML.ls_state; LibIface.ls_ok := PML.ls_okx; LibIface.ls_g0 := LS0 |}.
(* [comment removed for export] *)
Definition pm_creditx (n : Z) : credit := ((28 + 54) * hl_k_per_malloc L, 2 * n + 2 ^ 28 + 32768 + 28 * hl_b_overhead L).
Definition pm_layout_okx (Lay : lib_layout) : Prop :=
  ll_heap Lay = L /\ ll_entry Lay = PC_LIB /\ ll_gp Lay = 0x10800 /\ LIB_SCRX <= ll_stack Lay /\ ll_foot Lay = ll_footx_xsrc /\
  (forall n, ll_credit Lay n = pm_creditx n) /\ IMG_RO_HI <= ll_rw_lo Lay.
Definition lib_specx (Lay : lib_layout) : Prop := pm_layout_okx Lay -> PMS.lib_call_ok_fp HI Lay pm_staticsx.

End Specs.
End PMX.
