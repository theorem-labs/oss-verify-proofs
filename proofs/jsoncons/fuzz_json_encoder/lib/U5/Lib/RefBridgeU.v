(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Agreement of the twinned reference reader with the plain one. The twin copy declares fresh records and inductives
   (byte decoder state, control state, step result, action, reader state, event kind, encoder context); each is
   translated field by field or constructor by constructor to its namesake, and every function of the twin commutes
   with the translation. The reader's events, indentation count and allowance then agree, and the output room of the
   twinned library follows from the room bound of the plain model. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PmRef PmLibSpecsW PmEncSpecs PmLibDefs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmRef_u5 PmLibSpecsW_u5 PmEncSpecs_u5 PmLibDefs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
Import ListNotations.
Open Scope Z_scope.

Module RefBridgeU.
Module P := PmRef.PMR.
Module U := PmRef_u5.PMR.
Module PW := PmLibSpecsW.PMW.
Module UW := PmLibSpecsW_u5.PMW.
Module PE := PmEncSpecs.PMES.
Module UE := PmEncSpecs_u5.PMES.
Module PL := PmLibDefs.PML.
Module UL := PmLibDefs_u5.PML.

(* Translations from the twin types to their namesakes. *)
Definition tk (k : UW.evk) : PW.evk :=
  match k with
  | UW.EkBegin a => PW.EkBegin a | UW.EkEnd => PW.EkEnd | UW.EkKey => PW.EkKey
  | UW.EkStr q => PW.EkStr q | UW.EkLit => PW.EkLit | UW.EkNum => PW.EkNum
  end.
Definition tx (c : UE.ectx) : PE.ectx := PE.ECtx (UE.ec_arr c) (UE.ec_count c) (UE.ec_nla c).
Definition te (es : UE.estate) : PE.estate := map tx es.
Definition tu (v : U.u8v) : P.u8v := P.U8 (U.u_err v) (U.u_pend v) (U.u_need v).
Definition tc (c : U.ctrl) : P.ctrl :=
  P.CT (U.c_st c) (U.c_sst c) (U.c_nst c) (U.c_more c) (U.c_done c) (U.c_level c) (U.c_stack c) (U.c_cp c) (U.c_cp2 c)
       (U.c_dlen c) (tu (U.c_u8 c)).
Definition tr (q : U.res) : P.res := P.RES (tc (U.q_c q)) (U.q_w q) (map tk (U.q_evs q)) (U.q_al q) (U.q_code q).
Definition tp (x : U.ctrl * list Z) : P.ctrl * list Z := (tc (fst x), snd x).
Definition ts (s : U.rstate) : P.rstate := P.RS (tc (U.r_c s)) (U.r_w s) (U.r_rest s) (U.r_bof s) (U.r_eof s).
Definition tz (x : U.rstate * Z) : P.rstate * Z := (ts (fst x), snd x).
Definition r4 (t : U.rstate * list UW.evk * Z * Z) : P.rstate * list PW.evk * Z * Z :=
  (ts (fst (fst (fst t))), map tk (snd (fst (fst t))), snd (fst t), snd t).
Definition ta (a : U.act) : P.act :=
  match a with
  | U.AErr c b => P.AErr c b | U.AAccept => P.AAccept | U.ASkip => P.ASkip | U.ASlash => P.ASlash
  | U.ABegin x => P.ABegin x | U.AEnd x => P.AEnd x | U.AString x => P.AString x | U.ANumber => P.ANumber
  | U.ALit x => P.ALit x | U.AComma => P.AComma | U.AGoto s x => P.AGoto s x | U.APop x => P.APop x
  | U.APushCr => P.APushCr | U.ALitDone => P.ALitDone | U.AParseString => P.AParseString
  | U.AParseNumber => P.AParseNumber | U.AStuck => P.AStuck
  end.

(* The indentation count of an event list is the same for both encoder copies. *)
Lemma ind_k_eq : forall es k, UW.ind_k es k = PW.ind_k (te es) (tk k).
Proof.
  intros [|[a n l] r] [x| | |[|]| |]; try destruct a; unfold te; cbn [map];
  cbv beta iota zeta delta [UW.ind_k PW.ind_k UW.eev_of PW.eev_of tk tx UE.ev_ind PE.ev_ind UE.pre_scalar PE.pre_scalar
    UE.comma PE.comma UE.nl PE.nl UE.depth PE.depth UE.quotes PE.quotes UE.set_nla PE.set_nla UE.ec_arr PE.ec_arr
    UE.ec_count PE.ec_count UE.ec_nla PE.ec_nla fst snd];
  cbn [length]; rewrite ?length_map; reflexivity.
Qed.

Lemma step_k_eq : forall es k, te (UW.step_k es k) = PW.step_k (te es) (tk k).
Proof.
  intros [|[a n l] r] [x| | |[|]| |]; try destruct a; try destruct r as [|[a2 n2 l2] r2]; reflexivity.
Qed.

Lemma ind_run_eq : forall ks es, UW.ind_run es ks = PW.ind_run (te es) (map tk ks).
Proof.
  induction ks as [|k r IH]; intros es; cbn [UW.ind_run PW.ind_run map]; [reflexivity|].
  rewrite ind_k_eq, IH, step_k_eq. reflexivity.
Qed.

(* Projections through the translations. *)
Lemma ts_c : forall s, P.r_c (ts s) = tc (U.r_c s). Proof. reflexivity. Qed.
Lemma ts_w : forall s, P.r_w (ts s) = U.r_w s. Proof. reflexivity. Qed.
Lemma ts_rest : forall s, P.r_rest (ts s) = U.r_rest s. Proof. reflexivity. Qed.
Lemma ts_bof : forall s, P.r_bof (ts s) = U.r_bof s. Proof. reflexivity. Qed.
Lemma ts_eof : forall s, P.r_eof (ts s) = U.r_eof s. Proof. reflexivity. Qed.
Lemma tc_more : forall c, P.c_more (tc c) = U.c_more c. Proof. reflexivity. Qed.
Lemma tc_st : forall c, P.c_st (tc c) = U.c_st c. Proof. reflexivity. Qed.
Lemma tc_done : forall c, P.c_done (tc c) = U.c_done c. Proof. reflexivity. Qed.
Lemma tr_c : forall q, P.q_c (tr q) = tc (U.q_c q). Proof. reflexivity. Qed.
Lemma tr_w : forall q, P.q_w (tr q) = U.q_w q. Proof. reflexivity. Qed.
Lemma tr_evs : forall q, P.q_evs (tr q) = map tk (U.q_evs q). Proof. reflexivity. Qed.
Lemma tr_al : forall q, P.q_al (tr q) = U.q_al q. Proof. reflexivity. Qed.
Lemma tr_code : forall q, P.q_code (tr q) = U.q_code q. Proof. reflexivity. Qed.
Lemma tz_fst : forall x, fst (tz x) = ts (fst x). Proof. reflexivity. Qed.
Lemma tz_snd : forall x, snd (tz x) = snd x. Proof. reflexivity. Qed.
Lemma ts_RS : forall c w a b e, ts (U.RS c w a b e) = P.RS (tc c) w a b e. Proof. reflexivity. Qed.
Lemma ret_eq : forall c w, tr (U.ret c w) = P.ret (tc c) w. Proof. reflexivity. Qed.

Ltac push := repeat progress (rewrite ?tz_fst, ?tz_snd, ?ts_c, ?ts_w, ?ts_rest, ?ts_bof, ?ts_eof, ?tr_c, ?tr_w, ?tr_evs,
  ?tr_al, ?tr_code, ?tc_more, ?tc_st, ?tc_done).

(* Case analysis on a test whose scrutinee is itself free of tests. *)
Ltac nop := try fail.
Ltac atomic x := lazymatch x with context [match _ with _ => _ end] => fail | _ => nop end.
Ltac split0 := match goal with
  | |- context [match ?x with _ => _ end] =>
      atomic x;
      lazymatch type of x with
      | bool => destruct x
      | option _ => destruct x
      | list _ => destruct x
      end
  end.
Ltac split1 := split0; cbv beta iota zeta.
Ltac split1p := split0; cbv beta iota zeta delta [fst snd].

(* The pure helpers of the two copies are convertible; the plain ones are used on both sides. *)
Ltac pure :=
  try change U.is_ctl with P.is_ctl;
  try change U.is_ws with P.is_ws;
  try change U.is_digit with P.is_digit;
  try change U.is_nzdigit with P.is_nzdigit;
  try change U.is_exp with P.is_exp;
  try change U.hexval with P.hexval;
  try change U.trailing with P.trailing;
  try change U.is_cont with P.is_cont;
  try change U.legal with P.legal;
  try change U.b256 with P.b256;
  try change U.conv_errc with P.conv_errc;
  try change U.is_high_surr with P.is_high_surr;
  try change U.is_surr with P.is_surr;
  try change U.utf8_of with P.utf8_of;
  try change U.pair_cp with P.pair_cp;
  try change U.al_num with P.al_num;
  try change U.al_str with P.al_str;
  try change U.is_expect_st with P.is_expect_st;
  try change U.loop_fuel with P.loop_fuel;
  try change U.pfx with P.pfx;
  try change U.detect with P.detect;
  try change U.rfuel with P.rfuel.

(* The byte decoder. *)
Lemma u8_feed_eq : forall v b, tu (U.u8_feed v b) = P.u8_feed (tu v) b.
Proof.
  intros [e p n] b. unfold U.u8_feed, P.u8_feed.
  cbv beta iota zeta delta [tu U.u_err U.u_pend U.u_need P.u_err P.u_pend P.u_need]. pure.
  repeat (first [split1 | solve [reflexivity]]).
Qed.

Lemma u8_feeds_eq : forall bs v, tu (U.u8_feeds v bs) = P.u8_feeds (tu v) bs.
Proof.
  induction bs as [|b r IH]; intros v; cbn [U.u8_feeds P.u8_feeds]; [reflexivity|].
  rewrite IH, u8_feed_eq. reflexivity.
Qed.

Lemma u8_finish_eq : forall v, U.u8_finish v = P.u8_finish (tu v).
Proof. intros [e p n]. reflexivity. Qed.

(* Shared normal form: constants, record builders, projections and the control-state translation are unfolded and
   the pure helpers are identified; the larger functions of the reader stay folded. *)
Ltac norm := cbv beta iota zeta delta [
  U.ST_N U.ST_NU U.ST_NUL U.ST_T U.ST_TR U.ST_TRU U.ST_F U.ST_FA U.ST_FAL U.ST_FALS U.SS_TEXT U.SS_ESC U.SS_U1
  U.SS_U2 U.SS_U3 U.SS_U4 U.SS_SP1 U.SS_SP2 U.SS_U5 U.SS_U6 U.SS_U7 U.SS_U8 U.NS_MINUS U.NS_ZERO U.NS_INTEGER
  U.NS_FRAC1 U.NS_FRAC2 U.NS_EXP1 U.NS_EXP2 U.NS_EXP3 U.E_EOF U.E_SOURCE U.E_SYNTAX U.E_EXTRA_CHAR U.E_DEPTH
  U.E_SQUOTE U.E_CHAR_IN_STRING U.E_EXTRA_COMMA U.E_EXPECTED_KEY U.E_EXPECTED_VALUE U.E_INVALID_VALUE
  U.E_EXPECTED_COLON U.E_ILLEGAL_CTL U.E_ILLEGAL_ESC U.E_SURR_PAIR U.E_INVALID_UESC U.E_LEADING_ZERO
  U.E_INVALID_NUMBER U.E_COMMA_OR_RBRACE U.E_COMMA_OR_RBRACKET U.E_UNEXP_RBRACKET U.E_UNEXP_RBRACE
  U.E_ILLEGAL_COMMENT U.E_BAD_CONT U.E_OVERLONG U.E_ILLEGAL_CODEPOINT U.E_ILLEGAL_SURR U.E_UNPAIRED_SURR
  U.E_ILLEGAL_UNICODE U.E_UNEXP_CHAR U.E_STUCK U.E_FUEL U.CHUNK U.AL_LIT U.u8_init U.set_st U.set_sst U.set_nst
  U.set_more U.set_done U.set_level U.set_stack U.set_cp U.set_cp2 U.set_tok U.push U.top U.pop U.tok1 U.tokn
  U.tok_clear U.ctrl0 U.st_after U.ret U.err U.hexstep U.lit_done U.c_st U.c_sst U.c_nst U.c_more U.c_done
  U.c_level U.c_stack U.c_cp U.c_cp2 U.c_dlen U.c_u8 U.q_c U.q_w U.q_evs U.q_al U.q_code U.r_c U.r_w U.r_rest
  U.r_bof U.r_eof P.ST_N P.ST_NU P.ST_NUL P.ST_T P.ST_TR P.ST_TRU P.ST_F P.ST_FA P.ST_FAL P.ST_FALS P.SS_TEXT
  P.SS_ESC P.SS_U1 P.SS_U2 P.SS_U3 P.SS_U4 P.SS_SP1 P.SS_SP2 P.SS_U5 P.SS_U6 P.SS_U7 P.SS_U8 P.NS_MINUS P.NS_ZERO
  P.NS_INTEGER P.NS_FRAC1 P.NS_FRAC2 P.NS_EXP1 P.NS_EXP2 P.NS_EXP3 P.E_EOF P.E_SOURCE P.E_SYNTAX P.E_EXTRA_CHAR
  P.E_DEPTH P.E_SQUOTE P.E_CHAR_IN_STRING P.E_EXTRA_COMMA P.E_EXPECTED_KEY P.E_EXPECTED_VALUE P.E_INVALID_VALUE
  P.E_EXPECTED_COLON P.E_ILLEGAL_CTL P.E_ILLEGAL_ESC P.E_SURR_PAIR P.E_INVALID_UESC P.E_LEADING_ZERO
  P.E_INVALID_NUMBER P.E_COMMA_OR_RBRACE P.E_COMMA_OR_RBRACKET P.E_UNEXP_RBRACKET P.E_UNEXP_RBRACE
  P.E_ILLEGAL_COMMENT P.E_BAD_CONT P.E_OVERLONG P.E_ILLEGAL_CODEPOINT P.E_ILLEGAL_SURR P.E_UNPAIRED_SURR
  P.E_ILLEGAL_UNICODE P.E_UNEXP_CHAR P.E_STUCK P.E_FUEL P.CHUNK P.AL_LIT P.u8_init P.set_st P.set_sst P.set_nst
  P.set_more P.set_done P.set_level P.set_stack P.set_cp P.set_cp2 P.set_tok P.push P.top P.pop P.tok1 P.tokn
  P.tok_clear P.ctrl0 P.st_after P.ret P.err P.hexstep P.lit_done P.c_st P.c_sst P.c_nst P.c_more P.c_done
  P.c_level P.c_stack P.c_cp P.c_cp2 P.c_dlen P.c_u8 P.q_c P.q_w P.q_evs P.q_al P.q_code P.r_c P.r_w P.r_rest
  P.r_bof P.r_eof PL.ST_ROOT PL.ST_START PL.ST_ACCEPT PL.ST_SLASH PL.ST_SLASH_SLASH PL.ST_SLASH_STAR
  PL.ST_SLASH_STAR_STAR PL.ST_EXPECT_COMMA_OR_END PL.ST_OBJECT PL.ST_EXPECT_MEMBER_NAME_OR_END
  PL.ST_EXPECT_MEMBER_NAME PL.ST_EXPECT_COLON PL.ST_EXPECT_VALUE_OR_END PL.ST_EXPECT_VALUE PL.ST_ARRAY PL.ST_STRING
  PL.ST_MEMBER_NAME PL.ST_NUMBER PL.ST_CR PL.ST_DONE UL.ST_ROOT UL.ST_START UL.ST_ACCEPT UL.ST_SLASH
  UL.ST_SLASH_SLASH UL.ST_SLASH_STAR UL.ST_SLASH_STAR_STAR UL.ST_EXPECT_COMMA_OR_END UL.ST_OBJECT
  UL.ST_EXPECT_MEMBER_NAME_OR_END UL.ST_EXPECT_MEMBER_NAME UL.ST_EXPECT_COLON UL.ST_EXPECT_VALUE_OR_END
  UL.ST_EXPECT_VALUE UL.ST_ARRAY UL.ST_STRING UL.ST_MEMBER_NAME UL.ST_NUMBER UL.ST_CR UL.ST_DONE tc ts];
  pure; rewrite ?u8_finish_eq.

Ltac rw := nop.
Ltac leaf t := t; rw; cbv beta iota delta [
  tr tc tp ts tz U.c_st U.c_sst U.c_nst U.c_more U.c_done U.c_level U.c_stack U.c_cp U.c_cp2 U.c_dlen U.c_u8 U.q_c
  U.q_w U.q_evs U.q_al U.q_code U.r_c U.r_w U.r_rest U.r_bof U.r_eof];
  rewrite ?u8_feed_eq, ?u8_feeds_eq; reflexivity.
Ltac go t := repeat (first [split1 | solve [leaf t]]).
Ltac gop t := repeat (first [split1p | solve [leaf t]]).

Lemma bind_eq : forall r k k', (forall c w, tr (k c w) = k' (tc c) w) -> tr (U.bind r k) = P.bind (tr r) k'.
Proof.
  intros [c w evs al code] k k' H. unfold U.bind, P.bind. push.
  cbn [U.q_c U.q_w U.q_evs U.q_al U.q_code].
  destruct (negb (code =? 0)); [reflexivity|].
  rewrite <- H. push. unfold tr. cbn [U.q_c U.q_w U.q_evs U.q_al U.q_code]. rewrite map_app. reflexivity.
Qed.

Lemma after_value_eq : forall c w, tr (U.after_value c w) = P.after_value (tc c) w.
Proof. intros [] w. unfold U.after_value, P.after_value. norm. go ltac:(nop). Qed.

Lemma begin_member_eq : forall c w, tr (U.begin_member c w) = P.begin_member (tc c) w.
Proof. intros [] w. unfold U.begin_member, P.begin_member. norm. go ltac:(nop). Qed.

Lemma end_number_eq : forall c w, tr (U.end_number c w) = P.end_number (tc c) w.
Proof.
  intros c w. unfold U.end_number, P.end_number.
  rewrite (bind_eq _ _ P.after_value) by exact after_value_eq. reflexivity.
Qed.

Lemma begin_container_eq : forall a c w, tr (U.begin_container a c w) = P.begin_container a (tc c) w.
Proof. intros a [] w. unfold U.begin_container, P.begin_container. norm. go ltac:(nop). Qed.

Lemma end_container_eq : forall a c w, tr (U.end_container a c w) = P.end_container a (tc c) w.
Proof. intros a [] w. unfold U.end_container, P.end_container. norm. go ltac:(nop). Qed.

Lemma skip_space_eq_n : forall n w c, (length w <= n)%nat -> tp (U.skip_space c w) = P.skip_space (tc c) w.
Proof.
  induction n as [|n IH]; intros [|b r] [] Hl; try reflexivity; [cbn [length] in Hl; lia|].
  cbn [U.skip_space P.skip_space]. norm. go ltac:(rewrite ?IH by (cbn [length] in Hl |- *; lia)).
Qed.

Lemma skip_space_eq : forall w c, tp (U.skip_space c w) = P.skip_space (tc c) w.
Proof. intros w c. exact (skip_space_eq_n _ w c (le_n _)). Qed.

Lemma skip_space_r_eq : forall c w, tr (U.skip_space_r c w) = P.skip_space_r (tc c) w.
Proof. intros c w. unfold U.skip_space_r, P.skip_space_r. rewrite <- skip_space_eq. reflexivity. Qed.

Lemma parse_lit_eq : forall t s c w, tr (U.parse_lit t s c w) = P.parse_lit t s (tc c) w.
Proof. intros t s [] w. unfold U.parse_lit, P.parse_lit. norm. go ltac:(nop). Qed.

Lemma parse_null_eq : forall c w, tr (U.parse_null c w) = P.parse_null (tc c) w.
Proof. intros c w. unfold U.parse_null, P.parse_null. apply parse_lit_eq. Qed.
Lemma parse_true_eq : forall c w, tr (U.parse_true c w) = P.parse_true (tc c) w.
Proof. intros c w. unfold U.parse_true, P.parse_true. apply parse_lit_eq. Qed.
Lemma parse_false_eq : forall c w, tr (U.parse_false c w) = P.parse_false (tc c) w.
Proof. intros c w. unfold U.parse_false, P.parse_false. apply parse_lit_eq. Qed.

Lemma end_string_eq : forall c w, tr (U.end_string c w) = P.end_string (tc c) w.
Proof. intros [] w. unfold U.end_string, P.end_string. norm. go ltac:(nop). Qed.

Ltac rw ::= rewrite ?end_string_eq, ?end_number_eq.

Lemma parse_string_eq : forall w c, tr (U.parse_string c w) = P.parse_string (tc c) w.
Proof.
  induction w as [|b r IH]; intros []; cbn [U.parse_string P.parse_string]; norm; go ltac:(rewrite ?IH).
Qed.

Lemma parse_number_eq : forall w c, tr (U.parse_number c w) = P.parse_number (tc c) w.
Proof.
  induction w as [|b r IH]; intros []; cbn [U.parse_number P.parse_number]; norm; go ltac:(rewrite ?IH).
Qed.

Ltac rw ::= rewrite ?parse_string_eq, ?parse_number_eq.

Lemma start_string_eq : forall k c r, tr (U.start_string k c r) = P.start_string k (tc c) r.
Proof. intros k [] r. unfold U.start_string, P.start_string. norm. go ltac:(nop). Qed.

Lemma start_number_eq : forall c b r, tr (U.start_number c b r) = P.start_number (tc c) b r.
Proof. intros [] b r. unfold U.start_number, P.start_number. norm. go ltac:(nop). Qed.

(* The action table. *)
Lemma value_act_eq : forall b, match U.value_act b with Some a => Some (ta a) | None => None end = P.value_act b.
Proof. intros b. unfold U.value_act, P.value_act. pure. go ltac:(nop). Qed.

Lemma dispatch_eq : forall st p b, ta (U.dispatch st p b) = P.dispatch st p b.
Proof. intros st p b. unfold U.dispatch, P.dispatch. rewrite <- !value_act_eq. norm. go ltac:(nop). Qed.

Ltac rw ::= rewrite ?skip_space_r_eq, ?begin_container_eq, ?end_container_eq, ?start_string_eq, ?start_number_eq,
  ?parse_null_eq, ?parse_true_eq, ?parse_false_eq, ?parse_string_eq, ?parse_number_eq.

Lemma act_run_eq : forall a c b r, tr (U.act_run a c b r) = P.act_run (ta a) (tc c) b r.
Proof.
  intros a c b r. destruct a; cbv beta iota zeta delta [U.act_run P.act_run ta]; rw; try reflexivity.
  - repeat split1; rw; reflexivity.
  - rewrite (bind_eq _ _ (fun c1 _ => P.ret c1 r)) by (intros; reflexivity).
    rewrite begin_member_eq. reflexivity.
Qed.

Lemma iter_eq : forall c b r, tr (U.iter c b r) = P.iter (tc c) b r.
Proof. intros c b r. unfold U.iter, P.iter. rewrite act_run_eq, dispatch_eq. reflexivity. Qed.

Lemma loop_eq : forall F c w, tr (U.loop F c w) = P.loop F (tc c) w.
Proof.
  induction F as [|F IH]; intros c [|b r]; cbn [U.loop P.loop]; push; try reflexivity;
    destruct (U.c_more c); cbn [negb]; try reflexivity.
  rewrite (bind_eq _ _ (P.loop F)) by exact IH. rewrite iter_eq. reflexivity.
Qed.

Ltac rw ::= rewrite ?end_number_eq, ?loop_eq.

Lemma prologue_eq : forall c, tr (U.prologue c) = P.prologue (tc c).
Proof. intros []. unfold U.prologue, P.prologue. norm. go ltac:(nop). Qed.

Ltac rw ::= rewrite ?prologue_eq, ?loop_eq, ?skip_space_eq.

Lemma parse_some_eq : forall c w, tr (U.parse_some c w) = P.parse_some (tc c) w.
Proof. intros [] w. unfold U.parse_some, P.parse_some. norm. go ltac:(nop). Qed.

Lemma pcheck_done_eq : forall c w, tr (U.pcheck_done c w) = P.pcheck_done (tc c) w.
Proof. intros [] w. unfold U.pcheck_done, P.pcheck_done. norm. go ltac:(nop). Qed.

Lemma skip_whitespace_eq : forall c w, tp (U.skip_whitespace c w) = P.skip_whitespace (tc c) w.
Proof. intros [] w. unfold U.skip_whitespace, P.skip_whitespace. norm. gop ltac:(nop). Qed.

(* The chunked reader. *)
Lemma refill_eq : forall rs, tz (U.refill rs) = P.refill (ts rs).
Proof. intros [[] w rest bof eof]. unfold U.refill, P.refill. norm. go ltac:(nop). Qed.

Lemma sw_eq : forall rs, ts (U.sw rs) = P.sw (ts rs).
Proof. intros rs. unfold U.sw, P.sw. push. rewrite <- skip_whitespace_eq. reflexivity. Qed.

Lemma rloop_eq : forall F rs, P.rloop F (ts rs) = r4 (U.rloop F rs).
Proof.
  induction F as [|F IH]; intros rs; [reflexivity|].
  cbn [P.rloop U.rloop]. rewrite <- refill_eq. push.
  destruct (U.refill rs) as [rs1 e]. cbn [fst snd].
  rewrite <- parse_some_eq. push. rewrite <- !ts_RS, IH.
  unfold PL.ST_START, UL.ST_START, PL.ST_ACCEPT, UL.ST_ACCEPT.
  repeat split1; unfold r4; cbn [fst snd]; rewrite ?map_app; reflexivity.
Qed.

Lemma rtail_eq : forall F rs, tz (U.rtail F rs) = P.rtail F (ts rs).
Proof.
  induction F as [|F IH]; intros rs; [reflexivity|].
  cbn [U.rtail P.rtail]. rewrite <- sw_eq. push. rewrite <- refill_eq. push.
  rewrite <- IH. repeat split1; reflexivity.
Qed.

Lemma rcheck_eq : forall F rs, U.rcheck F rs = P.rcheck F (ts rs).
Proof.
  induction F as [|F IH]; intros rs; [reflexivity|].
  cbn [U.rcheck P.rcheck]. rewrite <- refill_eq. push.
  destruct (U.refill rs) as [rs1 e]. cbn [fst snd].
  destruct (negb (e =? 0)); [reflexivity|].
  destruct (U.r_w rs1) as [|x l]; cbv beta iota.
  - rewrite <- ret_eq. push. rewrite <- !ts_RS. push. rewrite <- IH. reflexivity.
  - rewrite <- pcheck_done_eq. push. rewrite <- !ts_RS. push. rewrite <- IH. reflexivity.
Qed.

Lemma read_check_done_eq : forall F rs, U.read_check_done F rs = P.read_check_done F (ts rs).
Proof.
  intros F rs. unfold U.read_check_done, P.read_check_done. push.
  rewrite <- pcheck_done_eq, <- rcheck_eq. push. reflexivity.
Qed.

(* The reader. *)
Theorem READ_corr : forall p,
  PmRef.PMR.READ p = (map tk (fst (fst (PmRef_u5.PMR.READ p))), snd (fst (PmRef_u5.PMR.READ p)), snd (PmRef_u5.PMR.READ p)).
Proof.
  intros p. cbv beta zeta delta [P.READ U.READ]. pure.
  change (P.RS P.ctrl0 [] p true false) with (ts (U.RS U.ctrl0 [] p true false)).
  rewrite rloop_eq. unfold r4.
  destruct (U.rloop (P.rfuel p) (U.RS U.ctrl0 [] p true false)) as [[[rs evs] al] code]. cbn [fst snd].
  destruct (negb (code =? 0)); [reflexivity|].
  rewrite <- sw_eq, <- rtail_eq.
  destruct (U.rtail (P.rfuel p) (U.sw rs)) as [rs2 z]. cbn [tz fst snd].
  destruct (negb (z =? 0)); [reflexivity|].
  rewrite <- read_check_done_eq. reflexivity.
Qed.

Theorem IND_eq : forall p, PmRef_u5.PMR.IND p = PmRef.PMR.IND p.
Proof.
  intros p. unfold U.IND, P.IND, U.K, P.K. rewrite READ_corr. cbn [fst]. rewrite ind_run_eq. reflexivity.
Qed.

Theorem ALLOW_eq : forall p, PmRef_u5.PMR.ALLOW p = PmRef.PMR.ALLOW p.
Proof. intros p. unfold U.ALLOW, P.ALLOW. rewrite READ_corr. reflexivity. Qed.

(* Output room of the twinned library for one reader output. *)
Theorem wroom_g0 : forall txt : list Z, Z.of_nat (length txt) < 2 ^ 26 -> PmRef.PMR.IND txt < 2 ^ 34 ->
  PmLibSpecsW_u5.PMW.wroomU PmEncSpecs_u5.PMES.g0 (PmRef_u5.PMR.K txt) (PmRef_u5.PMR.ALLOW txt).
Proof.
  intros txt Hn HI. unfold UW.wroomU. cbn [UE.g0 UE.g_len UE.g_es].
  change (UW.ind_run [] (U.K txt)) with (U.IND txt). rewrite IND_eq, ALLOW_eq.
  pose proof (LCU.clok_CLU txt Hn HI). lia.
Qed.

Theorem wroom_g0_phi : forall (PHI : list byte -> Prop) (inp : list byte),
  LCU.phiwU PHI -> PHI inp -> Z.of_nat (length inp) < 2 ^ 26 ->
  PmLibSpecsW_u5.PMW.wroomU PmEncSpecs_u5.PMES.g0 (PmRef_u5.PMR.K (map bv_unsigned inp)) (PmRef_u5.PMR.ALLOW (map bv_unsigned inp)).
Proof.
  intros PHI inp Hphi Hp Hn. apply wroom_g0.
  - rewrite length_map. exact Hn.
  - exact (Hphi inp Hp).
Qed.

End RefBridgeU.
