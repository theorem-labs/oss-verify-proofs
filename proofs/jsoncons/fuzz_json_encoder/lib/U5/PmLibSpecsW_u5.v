(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive evk : Type :=
  | EkBegin (arr : bool)      (* [comment removed for export] *)
  | EkEnd                     (* [comment removed for export] *)
  | EkKey                     (* [comment removed for export] *)
  | EkStr (quoted : bool)     (* [comment removed for export] *)
  | EkLit                     (* [comment removed for export] *)
  | EkNum.                    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition eev_of (k : evk) : PMES.eev :=
  match k with
  | EkBegin a => PMES.EvBegin a | EkEnd => PMES.EvEnd | EkKey => PMES.EvKey []
  | EkStr true => PMES.EvStr 0 [] | EkStr false => PMES.EvStr 2 [] | EkLit => PMES.EvNull | EkNum => PMES.EvDbl
  end.
Definition ind_k (es : PMES.estate) (k : evk) : Z := PMES.ev_ind es (eev_of k).
Definition step_k (es : PMES.estate) (k : evk) : PMES.estate := PMES.estep es (eev_of k).
Fixpoint es_run (es : PMES.estate) (ks : list evk) : PMES.estate :=
  match ks with [] => es | k :: r => es_run (step_k es k) r end.
Fixpoint ind_run (es : PMES.estate) (ks : list evk) : Z :=
  match ks with [] => 0 | k :: r => ind_k es k + ind_run (step_k es k) r end.
Lemma es_run_app : forall ks1 ks2 es, es_run es (ks1 ++ ks2) = es_run (es_run es ks1) ks2.
Proof. induction ks1 as [|k r IH]; intros; cbn; [reflexivity | apply IH]. Qed.
Lemma ind_run_app : forall ks1 ks2 es, ind_run es (ks1 ++ ks2) = ind_run es ks1 + ind_run (es_run es ks1) ks2.
Proof. induction ks1 as [|k r IH]; intros; cbn; [lia | rewrite IH; lia]. Qed.
(* [comment removed for export] *)
Definition kind_of (ev : PMES.eev) : evk :=
  match ev with
  | PMES.EvBegin a => EkBegin a | PMES.EvEnd => EkEnd | PMES.EvKey _ => EkKey
  | PMES.EvStr tag _ => EkStr (negb ((tag =? 2) || (tag =? 3))) | PMES.EvNull => EkLit | PMES.EvBool _ => EkLit
  | PMES.EvU64 => EkNum | PMES.EvI64 => EkNum | PMES.EvDbl => EkNum
  end.
Lemma ind_k_of : forall es ev, ind_k es (kind_of ev) = PMES.ev_ind es ev.
Proof. intros es ev; destruct ev; cbn -[PMES.ev_ind]; try reflexivity; unfold PMES.ev_ind, PMES.quotes;
  destruct ((tag =? 2) || (tag =? 3)); reflexivity. Qed.
Lemma step_k_of : forall es ev, step_k es (kind_of ev) = PMES.estep es ev.
Proof. intros es ev; destruct ev; cbn -[PMES.estep]; try reflexivity; unfold PMES.estep; destruct ((tag =? 2) || (tag =? 3)); reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive fname : Type :=
  | FSkipSpace | FBeginMember | FAfterValue
  | FBeginObject | FBeginArray | FEndObject | FEndArray | FParseTrue | FParseFalse | FParseNull
  | FEndStringValue | FEndInt | FEndFrac | FParseString | FParseNumber | FParseSome
  | FSkipWs | FCheckDone.
(* [comment removed for export] *)
Record cres (C : Type) : Type := CR {
  r_ctrl : C;            (* [comment removed for export] *)
  r_evs : list evk;      (* [comment removed for export] *)
  r_used : Z;            (* [comment removed for export] *)
  r_code : Z;            (* [comment removed for export] *)
  r_allow : Z            (* [comment removed for export] *) }.
Arguments CR {C} _ _ _ _ _. Arguments r_ctrl {C} _. Arguments r_evs {C} _. Arguments r_used {C} _. Arguments r_code {C} _. Arguments r_allow {C} _.
Record refmodel : Type := RM {
  rm_ctrl : Type;                                         (* [comment removed for export] *)
  rm_match : rm_ctrl -> mem -> Z -> pstate -> Prop;       (* [comment removed for export] *)
  rm_stale : rm_ctrl -> mem -> Z -> pstate -> Prop;       (* [comment removed for export] *)
  rm_step : fname -> rm_ctrl -> list Z -> cres rm_ctrl;   (* [comment removed for export] *)
  rm_validate : list Z -> Z                               (* [comment removed for export] *) }.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.
Variable WD_SCR : Z.
Variable RM : refmodel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition win_bytes (M : mem) (ps : pstate) (w : list Z) : Prop :=
  match ps_win ps with
  | None => w = []
  | Some (p, e) => L5.bytes_at RSEGS M p w /\ Z.of_nat (length w) = e - p /\ Forall (fun b => 0 <= b <= 255) w
  end.
Definition w_after (r : cres (rm_ctrl RM)) (w : list Z) : list Z := skipn (Z.to_nat (r_used r)) w.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ptrans_gbxw (f : fname) (MIn : rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : ls_state) (ps : pstate) (eg : PMES.eghost) (w x : list Z) (c : rm_ctrl RM),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr
      (fun R M => entry L R M sp r scr /\ Args R M P V E ps x /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ PMX.enc_sync ps eg /\
                  0 <= kx /\ pcredit_x L cr ps (kx + PMX.kenc L eg) bx /\
                  PMX.objs_x L sp P V E S2 /\
                  win_bytes M ps w /\ MIn c M P ps)                                                                              (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ wf_ps ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> PMX.enc_sync ps' eg') /\
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = PMX.W_parx P V E S2 /\
          pcredit_x L cr' ps' (kx + PMX.kenc L eg') bx /\ Rel ps ps' code R' /\
          let rr := rm_step RM f c (inp_of ps w x) in                                                                             (* [comment removed for export] *)
          code = r_code rr /\
          PMES.g_es eg' = es_run (PMES.g_es eg) (r_evs rr) /\
          (exists pay, 0 <= pay <= r_allow rr /\ PMES.g_len eg' = PMES.g_len eg + ind_run (PMES.g_es eg) (r_evs rr) + pay) /\
          (code = 0 -> rm_match RM (r_ctrl rr) M' P ps' /\ r_used rr = winlen ps - winlen ps' /\ win_bytes M' ps' (w_after rr w))).
Definition inp_win : pstate -> list Z -> list Z -> list Z := fun _ w _ => w.
Definition inp_aux : pstate -> list Z -> list Z -> list Z := fun _ _ x => x.
Definition inp_buf : pstate -> list Z -> list Z -> list Z := fun ps _ _ => ps_buf ps.
(* [comment removed for export] *)
Definition ax (A : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop) : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop :=
  fun R M P V E ps _ => A R M P V E ps.
Definition ptrans_gxw f inp := ptrans_gbxw f (rm_match RM) inp wf_ps buf_bound.
Definition ptransxw f inp := ptrans_gxw f inp parser_at (fun _ => parser_at).
Definition ptrans_curxw f inp := ptrans_gxw f inp parser_at (fun ps M' P ps' => parser_at M' P (ps_set_win ps' (ps_win ps))).
(* [comment removed for export] *)
Definition ptrans_stalexw f inp (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxw f (rm_stale RM) inp wf_ps_stale (PMS.buf_bound_stale) (fun M P ps => parser_at M P (ps_set_win ps mw))
               (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.
(* [comment removed for export] *)
Definition ptrans_gbxlw (f : fname) (MIn : rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : ls_state) (ps : pstate) (eg : PMES.eghost) (w x : list Z) (c : rm_ctrl RM),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr
      (fun R M => entry L R M sp r scr /\ Args LBo R M P V E ps x /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ PMX.enc_sync ps eg /\
                  0 <= kx /\ pcredit_x L cr ps (kx + PMX.kenc L eg) bx /\
                  PMX.objs_x L sp P V E S2 /\
                  win_bytes M ps w /\ MIn c M P ps)                                                                              (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ wf_ps ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> PMX.enc_sync ps' eg') /\
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = PMX.W_parx P V E S2 /\
          pcredit_x L cr' ps' (kx + PMX.kenc L eg') bx /\ Rel ps ps' code R' /\
          let rr := rm_step RM f c (inp_of ps w x) in                                                                             (* [comment removed for export] *)
          code = r_code rr /\
          PMES.g_es eg' = es_run (PMES.g_es eg) (r_evs rr) /\
          (exists pay, 0 <= pay <= r_allow rr /\ PMES.g_len eg' = PMES.g_len eg + ind_run (PMES.g_es eg) (r_evs rr) + pay) /\
          (code = 0 -> rm_match RM (r_ctrl rr) M' P ps' /\ r_used rr = winlen ps - winlen ps' /\ win_bytes M' ps' (w_after rr w))).
Definition ptrans_stalexlw f inp (pc scr : Z) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxlw f (rm_stale RM) inp wf_ps_stale (PMS.buf_bound_stale) (fun M P ps => parser_at M P (ps_set_win ps mw))
                (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.

(* [comment removed for export] *)
Definition ptrans_gbw (f : fname) (MIn : rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : ls_state) (ps : pstate) (w x : list Z) (c : rm_ctrl RM),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo) cr
      (fun R M => entry L R M sp r scr /\ Args R M P V E ps x /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  pcredit_x L cr ps kx bx /\ obj_on_stack L sp P 272 /\ obj_on_stack L sp V 8 /\ obj_on_stack L sp E 16 /\
                  apart P 272 V 8 /\ apart P 272 E 16 /\ apart V 8 E 16 /\
                  win_bytes M ps w /\ MIn c M P ps)                                                                              (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state),
          PAout ps M' P ps' /\ wf_ps ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          LB' = ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = W_par P E /\ pcredit_x L cr' ps' kx bx /\ Rel ps ps' code R' /\
          let rr := rm_step RM f c (inp_of ps w x) in                                                                             (* [comment removed for export] *)
          code = r_code rr /\ r_evs rr = [] /\
          (code = 0 -> rm_match RM (r_ctrl rr) M' P ps' /\ r_used rr = winlen ps - winlen ps' /\ win_bytes M' ps' (w_after rr w))).
Definition ptrans_gw f inp := ptrans_gbw f (rm_match RM) inp wf_ps buf_bound.
Definition ptransw f inp := ptrans_gw f inp parser_at (fun _ => parser_at).
Definition ptrans_stalew f inp (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbw f (rm_stale RM) inp wf_ps_stale (PMS.buf_bound_stale) (fun M P ps => parser_at M P (ps_set_win ps mw))
              (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition skip_space_specw : Prop :=
  ptransw FSkipSpace inp_win PC_SKIP_SPACE (PMS.PF_SCR STRTOD_SCR)
         (ax (fun R M P V E ps => a0 R P /\ a1 R (P + 200) /\ ws_ok ps /\ (if ps_more ps then is_expect (ps_st ps) else ps_st ps = ST_DONE) /\
                              exists p e b, ps_win ps = Some (p, e) /\ p < e /\ u8 M p b /\ In b [9; 10; 13; 32]))
         (fun ps ps' code R' => code = 0 /\ PMS.consumed ps ps' /\ ps_more ps' = ps_more ps /\ ws_ok ps' /\
                                (ps_st ps' = ps_st ps \/ (ps_st ps' = ST_CR /\ PMS.win_exhausted ps')) /\ ps_level ps' = ps_level ps).
Definition begin_member_specw : Prop :=
  ptransw FBeginMember inp_win PC_BEGIN_MEMBER (PMS.PF_SCR STRTOD_SCR) (ax (fun R M P V E ps => a0 R P /\ a1 R E /\ ps_more ps = true /\ ps_st ps = ST_EXPECT_COMMA_OR_END))
         (fun ps ps' code R' => code = 0 /\ ps_more ps' = true /\ In (ps_st ps') [ST_EXPECT_MEMBER_NAME; ST_EXPECT_VALUE] /\
                                ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps).
Definition after_value_specw : Prop :=
  ptrans_stalew FAfterValue inp_win PC_AFTER_VALUE PMS.AFTERV_SCR (ax (fun R M P V E ps => a0 R P /\ a1 R E /\ ps_more ps = true /\ ps_st ps = ST_NUMBER))
         (fun ps ps' code R' => code = 0 /\ ps_more ps' = true /\ ps_st ps' = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
                                ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps).
(* [comment removed for export] *)
Definition validate_specw : Prop :=
  forall (s len sp r : Z) (txt : list Z),
    cps_pure PC_VALIDATE r sp 96 []
      (fun R M => entry L R M sp r 96 /\ a0 R s /\ a1 R len /\ 0 <= len < 2 ^ 27 /\ L5.defined M s len /\ img_ro M /\
                  4096 <= s /\ s + len <= hl_ceil L /\ L5.bytes_at RSEGS M s txt /\ Z.of_nat (length txt) = len /\ Forall (fun b => 0 <= b <= 255) txt)
      (fun R M R' M' => exists q c, a0 R' q /\ getr R' 11%bv = Z_to_bv 64 c /\ s <= q <= s + len /\ 0 <= c <= 6 /\ c = rm_validate RM txt).

(* [comment removed for export] *)
Definition begin_container_specw (f : fname) (pc kind st' : Z) : Prop :=
  ptransxw f inp_win pc (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING))
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps + 1 /\ ps_st ps' = st' /\ ps_more ps' = true /\ ps_stack ps' = ps_stack ps ++ [kind] /\ ps_win ps' = ps_win ps)
            \/ (code = 5 /\ ps_level ps = 1024)).
Definition begin_object_specw := begin_container_specw FBeginObject PC_BEGIN_OBJECT ST_OBJECT ST_EXPECT_MEMBER_NAME_OR_END.
Definition begin_array_specw := begin_container_specw FBeginArray PC_BEGIN_ARRAY ST_ARRAY ST_EXPECT_VALUE_OR_END.
Definition end_container_specw (f : fname) (pc kind : Z) : Prop :=
  ptransxw f inp_win pc (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING))
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps - 1 /\ ps_more ps' = true /\ (exists rest, ps_stack ps = rest ++ [kind] /\ ps_stack ps' = rest) /\
             ps_st ps' = (if Z.eqb (ps_level ps') 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\ ps_win ps' = ps_win ps)
            \/ In code [20; 21; 22; 23]).
Definition end_object_specw := end_container_specw FEndObject PC_END_OBJECT ST_OBJECT.
Definition end_array_specw := end_container_specw FEndArray PC_END_ARRAY ST_ARRAY.
Definition parse_true_specw : Prop :=
  ptrans_curxw FParseTrue inp_win PC_PARSE_TRUE (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps)))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code /\ PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_false_specw : Prop :=
  ptrans_curxw FParseFalse inp_win PC_PARSE_FALSE (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps)))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code /\ PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_null_specw : Prop :=
  ptransxw FParseNull inp_win PC_PARSE_NULL (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps)))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code).
(* [comment removed for export] *)
Definition end_string_value_specw : Prop :=
  ptrans_stalexlw FEndStringValue inp_aux PC_END_STRING (PMX.ESVX_SCR WD_SCR)                                                   (* [comment removed for export] *)
         (fun LB R M P V E ps x => a0 R P /\ a3 R V /\ getr R 14%bv = Z_to_bv 64 E /\ ps_more ps = true /\ ps_st ps = ST_STRING /\
                                   (exists t, u8 M (P + 220) t /\ 0 <= t <= 1) /\                                           (* [comment removed for export] *)
                                   exists s len, a1 R s /\ a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                                 4096 <= s /\ s + len <= hl_ceil L /\ PMES.in_blocks (ps_blocks ps ++ LB) s len /\        (* [comment removed for export] *)
                                                 L5.bytes_at RSEGS M s x /\ Z.of_nat (length x) = len /\ Forall (fun b => 0 <= b <= 255) x)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_more ps' = true /\ ps_level ps' = ps_level ps /\
             In (ps_st ps') [ST_EXPECT_COLON; ST_EXPECT_COMMA_OR_END; ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).
Definition end_number_specw (f : fname) (pc : Z) : Prop :=
  ptrans_stalexw f inp_buf pc (PMX.ENDNUMX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER /\ num_final (ps_buf ps)))
         (fun ps ps' code R' => (code = 0 /\ ps_more ps' = true /\ ps_st ps' = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
                                 ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps) \/ code = 19).
Definition end_integer_value_specw := end_number_specw FEndInt PC_END_INT.
Definition end_fraction_value_specw := end_number_specw FEndFrac PC_END_FRAC.
Definition parse_string_specw : Prop :=
  ptrans_curxw FParseString inp_win PC_PARSE_STRING (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_STRING))
         (fun ps ps' code R' => PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code <> 0 \/ PMS.consumed ps ps' \/ PMS.win_exhausted ps) /\
                                (code = 0 -> ps_more ps' = true /\ ps_level ps' = ps_level ps)).
Definition parse_number_specw : Prop :=
  ptrans_curxw FParseNumber inp_win PC_PARSE_NUMBER (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER))
         (fun ps ps' code R' => PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code = 0 -> ps_level ps' = ps_level ps /\ ps_more ps' = true /\ (ps_st ps' = ST_NUMBER -> PMS.win_exhausted ps') /\
                                             In (ps_st ps') [ST_NUMBER; ST_ACCEPT; ST_EXPECT_COMMA_OR_END])).
Definition parse_some_specw : Prop :=
  ptransxw FParseSome inp_win PC_PARSE_SOME (PMX.PSOMEX_SCR STRTOD_SCR WD_SCR) (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true))
         (fun ps ps' code R' =>
            (code <> 0 \/ ps_more ps' = false \/ PMS.win_exhausted ps') /\
            (ps_st ps = ST_ACCEPT -> code = 0 /\ ps_more ps' = false /\ ps_done ps' = true) /\
            (PMS.win_exhausted ps -> code = 0 -> ps_more ps' = true -> In (ps_st ps) [ST_NUMBER; ST_CR] /\ ~ In (ps_st ps') [ST_NUMBER; ST_CR]) /\
            (code = 0 -> ws_ok ps')).
(* [comment removed for export] *)
Definition skip_whitespace_specw : Prop :=
  ptransw FSkipWs inp_win PC_SKIP_WS (PMS.SKIPWS_SCR STRTOD_SCR) (ax (fun R M P V E ps => a0 R P /\ ws_ok ps /\ (ps_more ps = true -> PMS.win_exhausted ps)))
         (fun ps ps' code R' => code = 0 /\ PMS.not_retreated ps ps' /\ ps_more ps' = ps_more ps /\ ws_ok ps').
Definition parser_check_done_specw : Prop :=
  ptransw FCheckDone inp_win PC_PCHECK_DONE (PMS.PF_SCR STRTOD_SCR) (ax (fun R M P V E ps => a0 R P /\ a1 R E))
         (fun ps ps' code R' => (code = 0 /\ PMS.win_exhausted ps' /\ ps_more ps' = ps_more ps /\ ps_st ps' = ps_st ps /\ ps_stack ps' = ps_stack ps /\
                                 ps_level ps' = ps_level ps) \/ code = 4).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wroomU (eg : PMES.eghost) (evs : list evk) (al : Z) : Prop := PMES.g_len eg + ind_run (PMES.g_es eg) evs + al <= PMES.CLU.
Definition wroomrU (eg : PMES.eghost) (rr : cres (rm_ctrl RM)) : Prop := wroomU eg (r_evs rr) (r_allow rr).
Lemma wroomU_mono : forall eg evs al al', wroomU eg evs al -> al' <= al -> wroomU eg evs al'.
Proof. unfold wroomU; intros; lia. Qed.
Lemma wroomU_app : forall eg evs1 evs2 al1 al2, wroomU eg (evs1 ++ evs2) (al1 + al2) -> 0 <= ind_run (es_run (PMES.g_es eg) evs1) evs2 -> 0 <= al2 -> wroomU eg evs1 al1.
Proof. unfold wroomU; intros eg evs1 evs2 al1 al2 H H1 H2. rewrite ind_run_app in H. lia. Qed.
Lemma wroomU_shift : forall eg eg1 evs1 evs2 al1 al2 pay,
  wroomU eg (evs1 ++ evs2) (al1 + al2) -> PMES.g_es eg1 = es_run (PMES.g_es eg) evs1 -> PMES.g_len eg1 = PMES.g_len eg + ind_run (PMES.g_es eg) evs1 + pay ->
  0 <= pay <= al1 -> wroomU eg1 evs2 al2.
Proof. unfold wroomU; intros eg eg1 evs1 evs2 al1 al2 pay H Hes Hlen Hp. rewrite ind_run_app in H. rewrite Hes, Hlen. lia. Qed.

Definition ptrans_gbxwU (f : fname) (MIn : rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : ls_state) (ps : pstate) (eg : PMES.eghost) (w x : list Z) (c : rm_ctrl RM),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr
      (fun R M => entry L R M sp r scr /\ Args R M P V E ps x /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ PMX.enc_sync ps eg /\
                  0 <= kx /\ 0 <= bx /\ pcredit_x L cr ps (kx + PMES.kenc L eg) (bx + PMES.benc L eg) /\
                  PMX.objs_x L sp P V E S2 /\
                  win_bytes M ps w /\ MIn c M P ps /\
                  wroomrU eg (rm_step RM f c (inp_of ps w x)))
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ wf_ps ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> PMX.enc_sync ps' eg') /\
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = PMX.W_parx P V E S2 /\
          pcredit_x L cr' ps' (kx + PMES.kenc L eg') (bx + PMES.benc L eg') /\ Rel ps ps' code R' /\
          let rr := rm_step RM f c (inp_of ps w x) in
          code = r_code rr /\
          PMES.g_es eg' = es_run (PMES.g_es eg) (r_evs rr) /\
          (exists pay, 0 <= pay <= r_allow rr /\ PMES.g_len eg' = PMES.g_len eg + ind_run (PMES.g_es eg) (r_evs rr) + pay) /\
          (code = 0 -> rm_match RM (r_ctrl rr) M' P ps' /\ r_used rr = winlen ps - winlen ps' /\ win_bytes M' ps' (w_after rr w))).
Definition ptrans_gxwU f inp := ptrans_gbxwU f (rm_match RM) inp wf_ps buf_bound.
Definition ptransxwU f inp := ptrans_gxwU f inp parser_at (fun _ => parser_at).
Definition ptrans_curxwU f inp := ptrans_gxwU f inp parser_at (fun ps M' P ps' => parser_at M' P (ps_set_win ps' (ps_win ps))).
Definition ptrans_stalexwU f inp (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxwU f (rm_stale RM) inp wf_ps_stale (PMS.buf_bound_stale) (fun M P ps => parser_at M P (ps_set_win ps mw))
               (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.
Definition ptrans_gbxlwU (f : fname) (MIn : rm_ctrl RM -> mem -> Z -> pstate -> Prop) (inp_of : pstate -> list Z -> list Z -> list Z)
           (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : ls_state) (ps : pstate) (eg : PMES.eghost) (w x : list Z) (c : rm_ctrl RM),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo ++ PMES.g_lbv eg) cr
      (fun R M => entry L R M sp r scr /\ Args LBo R M P V E ps x /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  PMES.enc_inv M V S2 eg /\ lits_ok M /\ PMX.enc_sync ps eg /\
                  0 <= kx /\ 0 <= bx /\ pcredit_x L cr ps (kx + PMES.kenc L eg) (bx + PMES.benc L eg) /\
                  PMX.objs_x L sp P V E S2 /\
                  win_bytes M ps w /\ MIn c M P ps /\
                  wroomrU eg (rm_step RM f c (inp_of ps w x)))
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ wf_ps ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          PMES.enc_inv M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> PMX.enc_sync ps' eg') /\
          LB' = ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = PMX.W_parx P V E S2 /\
          pcredit_x L cr' ps' (kx + PMES.kenc L eg') (bx + PMES.benc L eg') /\ Rel ps ps' code R' /\
          let rr := rm_step RM f c (inp_of ps w x) in
          code = r_code rr /\
          PMES.g_es eg' = es_run (PMES.g_es eg) (r_evs rr) /\
          (exists pay, 0 <= pay <= r_allow rr /\ PMES.g_len eg' = PMES.g_len eg + ind_run (PMES.g_es eg) (r_evs rr) + pay) /\
          (code = 0 -> rm_match RM (r_ctrl rr) M' P ps' /\ r_used rr = winlen ps - winlen ps' /\ win_bytes M' ps' (w_after rr w))).
Definition ptrans_stalexlwU f inp (pc scr : Z) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> list Z -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxlwU f (rm_stale RM) inp wf_ps_stale (PMS.buf_bound_stale) (fun M P ps => parser_at M P (ps_set_win ps mw))
                (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.

Definition begin_container_specwU (f : fname) (pc kind st' : Z) : Prop :=
  ptransxwU f inp_win pc (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING))
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps + 1 /\ ps_st ps' = st' /\ ps_more ps' = true /\ ps_stack ps' = ps_stack ps ++ [kind] /\ ps_win ps' = ps_win ps)
            \/ (code = 5 /\ ps_level ps = 1024)).
Definition begin_object_specwU := begin_container_specwU FBeginObject PC_BEGIN_OBJECT ST_OBJECT ST_EXPECT_MEMBER_NAME_OR_END.
Definition begin_array_specwU := begin_container_specwU FBeginArray PC_BEGIN_ARRAY ST_ARRAY ST_EXPECT_VALUE_OR_END.
Definition end_container_specwU (f : fname) (pc kind : Z) : Prop :=
  ptransxwU f inp_win pc (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING))
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps - 1 /\ ps_more ps' = true /\ (exists rest, ps_stack ps = rest ++ [kind] /\ ps_stack ps' = rest) /\
             ps_st ps' = (if Z.eqb (ps_level ps') 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\ ps_win ps' = ps_win ps)
            \/ In code [20; 21; 22; 23]).
Definition end_object_specwU := end_container_specwU FEndObject PC_END_OBJECT ST_OBJECT.
Definition end_array_specwU := end_container_specwU FEndArray PC_END_ARRAY ST_ARRAY.
Definition parse_true_specwU : Prop :=
  ptrans_curxwU FParseTrue inp_win PC_PARSE_TRUE (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps)))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code /\ PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_false_specwU : Prop :=
  ptrans_curxwU FParseFalse inp_win PC_PARSE_FALSE (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps)))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code /\ PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_null_specwU : Prop :=
  ptransxwU FParseNull inp_win PC_PARSE_NULL (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ~ PMS.win_exhausted ps /\ is_expect (ps_st ps)))
         (fun ps ps' code R' => PMS.literal_rel ps ps' code).
Definition end_string_value_specwU : Prop :=
  ptrans_stalexlwU FEndStringValue inp_aux PC_END_STRING (PMX.ESVX_SCR WD_SCR)
         (fun LB R M P V E ps x => a0 R P /\ a3 R V /\ getr R 14%bv = Z_to_bv 64 E /\ ps_more ps = true /\ ps_st ps = ST_STRING /\
                                   (exists t, u8 M (P + 220) t /\ 0 <= t <= 1) /\
                                   exists s len, a1 R s /\ a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                                 4096 <= s /\ s + len <= hl_ceil L /\ PMES.in_blocks (ps_blocks ps ++ LB) s len /\
                                                 L5.bytes_at RSEGS M s x /\ Z.of_nat (length x) = len /\ Forall (fun b => 0 <= b <= 255) x)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_more ps' = true /\ ps_level ps' = ps_level ps /\
             In (ps_st ps') [ST_EXPECT_COLON; ST_EXPECT_COMMA_OR_END; ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).
Definition end_number_specwU (f : fname) (pc : Z) : Prop :=
  ptrans_stalexwU f inp_buf pc (PMX.ENDNUMX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER /\ num_final (ps_buf ps)))
         (fun ps ps' code R' => (code = 0 /\ ps_more ps' = true /\ ps_st ps' = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
                                 ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps) \/ code = 19).
Definition end_integer_value_specwU := end_number_specwU FEndInt PC_END_INT.
Definition end_fraction_value_specwU := end_number_specwU FEndFrac PC_END_FRAC.
Definition parse_string_specwU : Prop :=
  ptrans_curxwU FParseString inp_win PC_PARSE_STRING (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_STRING))
         (fun ps ps' code R' => PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code <> 0 \/ PMS.consumed ps ps' \/ PMS.win_exhausted ps) /\
                                (code = 0 -> ps_more ps' = true /\ ps_level ps' = ps_level ps)).
Definition parse_number_specwU : Prop :=
  ptrans_curxwU FParseNumber inp_win PC_PARSE_NUMBER (PMX.PFX_SCR STRTOD_SCR WD_SCR)
         (ax (fun R M P V E ps => PMS.cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER))
         (fun ps ps' code R' => PMS.not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code = 0 -> ps_level ps' = ps_level ps /\ ps_more ps' = true /\ (ps_st ps' = ST_NUMBER -> PMS.win_exhausted ps') /\
                                             In (ps_st ps') [ST_NUMBER; ST_ACCEPT; ST_EXPECT_COMMA_OR_END])).
Definition parse_some_specwU : Prop :=
  ptransxwU FParseSome inp_win PC_PARSE_SOME (PMX.PSOMEX_SCR STRTOD_SCR WD_SCR) (ax (fun R M P V E ps => PMS.std_args R M P V E ps /\ ps_more ps = true))
         (fun ps ps' code R' =>
            (code <> 0 \/ ps_more ps' = false \/ PMS.win_exhausted ps') /\
            (ps_st ps = ST_ACCEPT -> code = 0 /\ ps_more ps' = false /\ ps_done ps' = true) /\
            (PMS.win_exhausted ps -> code = 0 -> ps_more ps' = true -> In (ps_st ps) [ST_NUMBER; ST_CR] /\ ~ In (ps_st ps') [ST_NUMBER; ST_CR]) /\
            (code = 0 -> ws_ok ps')).

End Specs.
End PMW.
