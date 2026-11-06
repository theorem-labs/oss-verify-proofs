(* fuzz_preset, slice S5b, lane A'Str (was VstrD): THE POST-CALL HALF of parse_value's STRING ARM (image A' 0x85f10,
   rows 143..151): the join at ROW 225, stated over the facts the arm has after parse_string returns and after the
   straight-line stretch of rows 143..151, so that this file builds without the arm's symbolic runs.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Every lemma here is a step of the string arm's join; the callee
   (parse_string) enters only through its post's arms: the kit's published lib/A/PRH_FnReader.v tparse_string_specX (kit
   a working branch 3ac20a5c9e30, blob fb7b12dfa169: the POST-IMPLICATION form - no entry position, each
   arm's live-request Permutation and exact position transfer keyed on the arm's own list prhPs_evs .. okA, the
   refusal arm's OUTCOME exclusion, and fuzz_malloc's refusal ledger verbatim), which the arm lemmas (VrdArmStrOk.v
   vrd_str_a_okP / vrd_str_a_ok) take as their Section hypothesis.
   THE ARM'S RESULT is VrdNum.vrd_pv_post, tparse_value_specX's post body (PRH_FnParse.v blob 94232293d483) read at the
   join. Its three RUN clauses are proved here from parse_string's arms, choosing nothing at entry: (a) the live
   requests moved by rd_hevs tr, (b) THE POSITION TRANSFER at whatever run and position the caller picks (the arm's
   list prhPs_evs y okA IS rd_hevs of the arm's trace under cf_head = PresetReqAt.HEAD, prhPs_evs_model), and (c) THE
   OUTCOME at the ALL-GRANTED list: on the granted arms the arm's list is the granted one (prhPs_evs_arm), the chosen
   failure puts the pick in the window (cnt = fail), and the refusal arm is excluded by parse_string's own clause.
   The per-outcome table (ok, tr, advance): ([], [], 0), ([false], [EFail], 0) for both failure arms,
   ([true], [EAlloc; EFree], 2), ([true], [EAlloc], 1).
   STATES / VIEWS: (ly, S, Hp, W, mem) is the DISPATCH state (VrdPro.vrd_disp_body), memc the CALL memory (after
   rows 135..141 wrote the node's type word [v, v + 4)), (ly2, S2, Hp2, W2, mem2) parse_string's POST state, and memF
   the JOIN memory (after rows 143..151 wrote the node's str field [v + 16, v + 24)). The journal from parse_value's
   entry is at the caller-window stack (STK_parse_value d + e) (spZ regs0 + e), own = [(0, pos)].
   CITED, NOT RE-PROVED: A'Ledger's per-event ledger steps over rd_ledger_move's #102 form (VrdLedgerEv.v at
   a working branch 127f6184b2fe: vle_fail_chosen, vle_fail_refused, vle_alloc_free, vle_alloc), VnumD's
   vrd_pv_post / vrd_epi_a / vrd_zero_val (VrdNum.v), the arm toolkit of VrdArm.v (vrs_ledger_keep, vrs_pst_keep,
   vrs_in_ok_keep, vrs_garr8_keep, vrs_sep_last, vrd_str_model, vrs_gtrace_str), VproC's vrd_saved / vrd_frame /
   vrd_node_frame_disj (VrdPro.v), the kit's prhPs_evs_model / prhPs_evs_arm (PRH_FnReader.v) and the grammar's
   scan_quote / decode_stop (PjGrammar.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdPro.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog VrdNum VrdArm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import VrdLedgerStep VrdLedgerEv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
(* the re-hiding move's SRr' / wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf); the hull meters *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which sets Zify's euclidean-division flag off GLOBALLY; this file's lia goals over `mod`
   and `/` need it on (VrdIStep.v does the same) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section model.
Context {cp : CfParams}.
(* INSTANCE FACT (a Theorem Labs lane's ruling: ONE name, a Section hypothesis in every file whose proofs use it): the allocator's
   head is the model's HEAD (preset alloc.c's 16), so parse_string's list prhPs_evs (requests + cf_head) is the model's
   rd_hevs (requests + HEAD). Discharged at the unit's top by reflexivity at CfParams_preset. *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.

(* ---- the model of the string arm: PjGrammar.jr_value at a quote, one lemma per outcome of parse_string, at any
   strtod model st (the string arm never reaches it): the instance's outcomes, and for the granted outcomes also the
   ALL-GRANTED list [] (PjGrammar.take's default grants), which the OUTCOME clause reads ---- *)

Lemma vrs_model_none : forall st d0 x y ok, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = None ->
  PjGrammar.jr_value st d0 x ok = (None, [], ok).
Proof.
intros st d0 x y ok Hs Hsc. rewrite (vrd_str_model st d0 y x ok Hs).
unfold PjGrammar.jbind, PjGrammar.jr_string. rewrite Hsc. reflexivity.
Qed.

Lemma vrs_model_fail : forall st d0 x y Q, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = Some Q ->
  PjGrammar.jr_value st d0 x [false] = (None, [PjGrammar.EFail (S Q)], []).
Proof.
intros st d0 x y Q Hs Hsc. rewrite (vrd_str_model st d0 y x [false] Hs).
unfold PjGrammar.jbind, PjGrammar.jr_string. rewrite Hsc. reflexivity.
Qed.

Lemma vrs_model_bad : forall st d0 x y Q ok, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = Some Q ->
  PjGrammar.decode y = None -> ok = [] \/ ok = [true] ->
  PjGrammar.jr_value st d0 x ok = (None, [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)], []).
Proof.
intros st d0 x y Q ok Hs Hsc Hd Hok. rewrite (vrd_str_model st d0 y x ok Hs).
destruct Hok as [-> | ->]; unfold PjGrammar.jbind, PjGrammar.jr_string; rewrite Hsc, Hd; reflexivity.
Qed.

Lemma vrs_model_str : forall st d0 x y Q s r ok, PjGrammar.skip x = 34 :: y -> PjGrammar.scan y = Some Q ->
  PjGrammar.decode y = Some (s, r) -> ok = [] \/ ok = [true] ->
  PjGrammar.jr_value st d0 x ok = (Some (JStr s, r), [PjGrammar.EAlloc (S Q)], []).
Proof.
intros st d0 x y Q s r ok Hs Hsc Hd Hok. rewrite (vrd_str_model st d0 y x ok Hs).
destruct Hok as [-> | ->]; unfold PjGrammar.jbind, PjGrammar.jr_string; rewrite Hsc, Hd; reflexivity.
Qed.

(* the trace of jr_value at a quote is jr_string's, at any outcomes *)
Lemma vrs_trace_str : forall st d0 x y ok, PjGrammar.skip x = 34 :: y ->
  snd (fst (PjGrammar.jr_value st d0 x ok)) = snd (fst (PjGrammar.jr_string y ok)).
Proof.
intros st d0 x y ok Hs. rewrite (vrd_str_model st d0 y x ok Hs). unfold PjGrammar.jbind.
destruct (PjGrammar.jr_string y ok) as [[r t] ok1]. destruct r as [[s rr]|].
- cbn [PjGrammar.jret fst snd]. rewrite app_nil_r. reflexivity.
- reflexivity.
Qed.

(* parse_string's granted trace in the three outcomes that do not refuse the allocation *)
Lemma vrs_gt_none : forall y, PjGrammar.scan y = None -> prhPs_gtrace y = [].
Proof. intros y H. unfold prhPs_gtrace, PjGrammar.jr_string. rewrite H. reflexivity. Qed.

Lemma vrs_gt_bad : forall y Q, PjGrammar.scan y = Some Q -> PjGrammar.decode y = None ->
  prhPs_gtrace y = [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)].
Proof.
intros y Q H1 H2. unfold prhPs_gtrace, PjGrammar.jr_string. rewrite H1. unfold PjGrammar.jbind. rewrite H2.
reflexivity.
Qed.

Lemma vrs_gt_str : forall y Q s r, PjGrammar.scan y = Some Q -> PjGrammar.decode y = Some (s, r) ->
  prhPs_gtrace y = [PjGrammar.EAlloc (S Q)].
Proof.
intros y Q s r H1 H2. unfold prhPs_gtrace, PjGrammar.jr_string. rewrite H1. unfold PjGrammar.jbind. rewrite H2.
reflexivity.
Qed.

(* a quote that scans: the granted trace makes ONE harness call, and holds Q + 1 bytes right after it *)
Lemma vrs_gt_scan : forall y Q, PjGrammar.scan y = Some Q ->
  PjGrammar.calls (prhPs_gtrace y) = 1%nat /\ prh_ev_helds (prhPs_gtrace y) = [Z.of_nat (S Q)].
Proof.
intros y Q Hs. destruct (PjGrammar.decode y) as [[s r]|] eqn:Hd.
- rewrite (vrs_gt_str y Q s r Hs Hd). split; reflexivity.
- rewrite (vrs_gt_bad y Q Hs Hd). split; reflexivity.
Qed.

(* parse_value's ALL-GRANTED events at a quote ARE parse_string's all-granted list (the model's HEAD being cf_head) *)
Lemma vrs_gt_evs : forall d0 x y, PjGrammar.skip x = 34 :: y ->
  PresetReqAt.rd_hevs (prhPv_gtrace d0 x) = prhPs_evs y [].
Proof.
intros d0 x y Hs. rewrite (VrdArm.vrs_gtrace_str d0 x y Hs). unfold prhPs_gtrace.
symmetry. exact (prhPs_evs_model y [] HI_head).
Qed.

(* ---- THE LEDGER MOVE of the outcome with no allocator call, over PRH_FnParse.rd_ledger_move's #102 form (the four
   one-event outcomes are A'Ledger's VrdLedgerEv.v steps). Pure ledger arithmetic; no callee is named. ---- *)
Lemma vrs_refused_peak0 : forall ok cnt fail hs, prh_refused_peak ok cnt fail 0 hs = 0.
Proof. reflexivity. Qed.

(* no allocator call (scan = None: parse_string returns NULL at once) *)
Lemma vrs_move_nil : forall Lam peak cnt fail ran most gt,
  0 <= Ledger.lsum Lam <= peak -> 0 <= cnt < 2 ^ 64 ->
  rd_ledger_move Lam peak cnt fail ran most [] gt [] [] Lam peak cnt fail ran.
Proof.
intros Lam peak cnt fail ran most gt Hpk Hc. unfold rd_ledger_move.
cbn [PjGrammar.calls lszR fold_left hpeakR nliveR length map app Z.of_nat].
rewrite vrs_refused_peak0.
split; [unfold prh_oks; split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|].
split; [split; intros H; [lia | reflexivity]|].
split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|]. lia.
Qed.

(* ---- THE RUN CLAUSES of the arm's result, from parse_string's post arms. parse_string's clauses are keyed on the
   CALL state S, which is the entry state S0 up to the fake-frame take (vrd_disp_body: exists f, S = set_fs f S0), so
   a run and position the caller picks at S0 are the call's (PresetRoomPosKeep.room_pos_set_fs), and the live
   requests are the same (YGcfRoom.room_of_cf reads no frame). The text's own spelling, by name: ---- *)
Definition vrs_live (S S2 : astate) (evs : list PresetReqAt.hev) : Prop :=
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) evs).
Definition vrs_pos (S S2 : astate) (evs : list PresetReqAt.hev) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i evs ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length evs)%nat H0 hist' S2.
Definition vrs_excl (S : astate) (evs : list PresetReqAt.hev) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    PRH_Base.prh_run_at sm x os i evs ->
    PRH_Base.prh_cons_from sm x os i (length evs) -> False.

Lemma vrs_room_set_fs : forall (S0 : astate) f, YGcfRoom.room_of_cf (set_fs f S0) = YGcfRoom.room_of_cf S0.
Proof. intros S0 f. destruct S0. reflexivity. Qed.

Lemma vrs_pos_xfer : forall (S0 S S2 : astate) evs, (exists f, S = set_fs f S0) -> vrs_pos S S2 evs -> vrs_pos S0 S2 evs.
Proof.
intros S0 S S2 evs (f & ->) H sm x os i H0 hist Hp Hr.
exact (H sm x os i H0 hist (PresetRoomPosKeep.room_pos_set_fs sm x os i H0 hist S0 f Hp) Hr).
Qed.

Lemma vrs_live_xfer : forall (S0 S S2 : astate) evs, (exists f, S = set_fs f S0) -> vrs_live S S2 evs -> vrs_live S0 S2 evs.
Proof. intros S0 S S2 evs (f & ->) H. unfold vrs_live in *. rewrite vrs_room_set_fs in H. exact H. Qed.

(* (a) and (b): the live requests and THE EXACT ADVANCE by the events the instance made *)
Lemma vrs_runs_made : forall st d0 (S0 S S2 : astate) xx y okA res tr okr,
  (exists f, S = set_fs f S0) -> PjGrammar.skip xx = 34 :: y ->
  PjGrammar.jr_value st d0 xx okA = (res, tr, okr) ->
  vrs_live S S2 (prhPs_evs y okA) -> vrs_pos S S2 (prhPs_evs y okA) ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) (PresetReqAt.rd_hevs tr)) /\
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S2).
Proof.
intros st d0 S0 S S2 xx y okA res tr okr Hfs Hs Hm HL HP.
assert (Etr : tr = snd (fst (PjGrammar.jr_value st d0 xx okA))) by (rewrite Hm; reflexivity).
rewrite Etr, (vrs_trace_str st d0 xx y okA Hs), <- (prhPs_evs_model y okA HI_head).
split; [exact (vrs_live_xfer S0 S S2 _ Hfs HL) | exact (vrs_pos_xfer S0 S S2 _ Hfs HP)].
Qed.

(* (c), THE OUTCOME, on an arm that GRANTED or made no call: the arm's list is the all-granted one *)
Lemma vrs_outcome_granted : forall st d0 (S0 S S2 : astate) xx y okA res tr (cnt fail ran ran' : Z),
  (exists f, S = set_fs f S0) -> PjGrammar.skip xx = 34 :: y ->
  PjGrammar.scan y = None \/ nth 0 okA true = true ->
  vrs_pos S S2 (prhPs_evs y okA) -> ran' = ran -> fst (PjGrammar.jr_value st d0 xx []) = (res, tr) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPv_gtrace d0 xx)) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPv_gtrace d0 xx))) ->
    (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPv_gtrace d0 xx)) <= fail) ->
    ran' = ran /\ fst (PjGrammar.jr_value st d0 xx []) = (res, tr) /\
    exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length (PresetReqAt.rd_hevs (prhPv_gtrace d0 xx)))%nat H0 hist' S2.
Proof.
intros st d0 S0 S S2 xx y okA res tr cnt fail ran ran' Hfs Hs Hok HP Hran Hm sm x os i H0 hist Hp Hr _ _.
split; [exact Hran|]. split; [exact Hm|].
rewrite (vrs_gt_evs d0 xx y Hs) in Hr |- *.
assert (E : prhPs_evs y [] = prhPs_evs y okA).
{ apply prhPs_evs_arm. destruct Hok as [H|H]; [left; exact H | right; rewrite H; reflexivity]. }
rewrite E in Hr |- *.
exact (vrs_pos_xfer S0 S S2 _ Hfs HP sm x os i H0 hist Hp Hr).
Qed.

(* (c) on the CHOSEN FAILURE: cnt = fail puts the pick in the call's window, so the clause's premise fails *)
Lemma vrs_outcome_chosen : forall d0 xx y Q cnt fail (G : Prop),
  PjGrammar.skip xx = 34 :: y -> PjGrammar.scan y = Some Q -> cnt = fail ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPv_gtrace d0 xx)) <= fail) -> G.
Proof.
intros d0 xx y Q cnt fail G Hs Hsc Heq Hw. exfalso.
rewrite (VrdArm.vrs_gtrace_str d0 xx y Hs), (proj1 (vrs_gt_scan y Q Hsc)) in Hw. lia.
Qed.

(* (c) on the allocator's REFUSAL: parse_string's own exclusion at the all-granted list *)
Lemma vrs_outcome_refused : forall d0 (S0 S : astate) xx y (G : Prop),
  (exists f, S = set_fs f S0) -> PjGrammar.skip xx = 34 :: y ->
  vrs_excl S (prhPs_evs y []) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPv_gtrace d0 xx)) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPv_gtrace d0 xx))) -> G.
Proof.
intros d0 S0 S xx y G (f & ->) Hs HX sm x os i H0 hist Hp Hr Hc. exfalso.
rewrite (vrs_gt_evs d0 xx y Hs) in Hr, Hc.
exact (HX sm x os i H0 hist (PresetRoomPosKeep.room_pos_set_fs sm x os i H0 hist S0 f Hp) Hr Hc).
Qed.

End model.

Section join.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PI_prog_A).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Variable d : nat.
(* the instance fact of Section model, same name and statement *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.

(* fpre's fourth conjunct at row 142's `jal parse_string` (PRH_Base.v blob ee2f5cd7ed35 :746, raZ regs <
   YM05.alloc_ceiling): the return pc (ROW 143, listing slot 4825) is below the run's allocation ceiling - PRW_StepKit's
   one copy pa_slot_lt_ceil_b, in a CLOSED goal with the listing instances named (never inside the arm's proof, where
   vm_compute runs away) *)
Lemma vrs_ret_slot_ceil : @pa_val _ _ PI_prog_A A_TEXT + 4 * 4825 < YM05.alloc_ceiling.
Proof.
exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PI_prog_A) (4 * 4825) ltac:(lia)
  ltac:(vm_compute; reflexivity)).
Qed.

(* ---- the node at the join ---- *)

(* a node whose str, kids, keys, n and cap are 0 is a freeable partial tree with no blocks, at any depth *)
Lemma vrs_fd_hdr : forall (m : word -> option byte) (lblk : Z -> Z -> Prop) (n : nat) v ty num,
  pj_hdrR SEGS m v ty num 0 0 0 0 0 -> pj_fdR SEGS m lblk n v [].
Proof.
intros m lblk n v ty num H.
destruct n as [|n]; cbn [pj_fdR]; unfold pj_fshapeR;
  (split; [constructor|]); (split; [intros b x Hb; destruct Hb|]);
  exists ty, num, 0, 0, 0, 0, 0, false, [], [], [], [];
  (split; [exact H|]);
  (split; [left; split; reflexivity|]);
  (split; [left; split; [reflexivity | split; reflexivity]|]);
  (split; [left; split; [reflexivity | split; reflexivity]|]);
  (split; [apply Permutation_refl|]).
- split; reflexivity.
- exact eq_refl.
Qed.

(* the node's header at the join: the type 4 row 140 stored, the str field row 148 stored, and the other fields the
   zeroed node had at the dispatch (the stretches and the call write none of them) *)
Lemma vrs_hdr : forall (Wd Wc W2 : world SEGS) (m mc mF : word -> option byte) v str,
  v mod 8 = 0 -> rd_rw SEGS (rdW W2 mF) v 56 ->
  pj_zeroR SEGS (rdW Wd m) v ->
  (forall a, v <= a < v + 56 -> ~ (v <= a < v + 4) -> ~ (v + 16 <= a < v + 24) ->
     aview SEGS (w_H W2) mF a = aview SEGS (w_H Wd) m a) ->
  val_mem SEGS (rdW Wc mc) v 4 4 ->
  (forall a, v <= a < v + 4 -> aview SEGS (w_H W2) mF a = aview SEGS (w_H Wc) mc a) ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W2 mF) (v + 16) 8 str ->
  pj_hdrR SEGS (rdW W2 mF) v 4 0 str 0 0 0 0.
Proof.
intros Wd Wc W2 m mc mF v str Hv8 Hrw Hz KN Hty KT Hs Hstr.
assert (Z0 : forall o, o = 8 \/ o = 24 \/ o = 32 \/ o = 40 \/ o = 48 -> rd_u64 SEGS (rdW W2 mF) (v + o) 0).
{ intros o Ho. unfold rd_u64. split; [lia|].
  apply (val_mem_kept SEGS (w_H Wd) (w_H W2) m mF).
  - intros k Hk. apply KN; lia.
  - apply (vrd_zero_val SEGS (rdW Wd m) v (v + o) 8 Hz); lia. }
unfold pj_hdrR, pj_rwR, rd_u32.
split; [split; [exact Hv8 | exact Hrw]|].
split; [split; [lia|]; apply (val_mem_kept SEGS (w_H Wc) (w_H W2) mc mF); [intros k Hk; apply KT; lia | exact Hty]|].
split; [apply Z0; lia|].
split; [unfold rd_u64; split; [exact Hs | exact Hstr]|].
split; [apply Z0; lia|]. split; [apply Z0; lia|]. split; [apply Z0; lia|]. apply Z0; lia.
Qed.

(* ---- the ledger's facts BY NAME (a Theorem Labs lane's rule: never destructure a shared record by position; the E sweep
   widens prh_glob). A member's block facts come through S1Ledger.prh_ledger_hblock and the heads' permutation and
   the statics' bounds by unfolding and tauto, so these survive a reordered or widened record. ---- *)
Lemma vrs_hb : forall ly S Hp (W : world SEGS) m Lam peak cnt fail ran most own a k,
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof.
intros ly S Hp W m Lam peak cnt fail ran most own a k HLd Hin.
pose proof (S1Ledger.prh_ledger_hblock B ly S Hp W m Lam peak cnt fail ran a k most own HLd Hin) as H.
unfold prh_hblock in H. tauto.
Qed.
Lemma vrs_heads : forall ly S Hp (W : world SEGS) m Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> Permutation Hp (map (fun ak => fst ak - cf_head) Lam).
Proof. intros ly S Hp W m Lam peak cnt fail ran most own HLd. unfold prh_ledger in HLd. tauto. Qed.
Lemma vrs_bounds : forall ly S Hp (W : world SEGS) m Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> 0 <= Ledger.lsum Lam <= peak /\ 0 <= cnt < 2 ^ 64.
Proof. intros ly S Hp W m Lam peak cnt fail ran most own HLd. unfold prh_ledger, prh_glob in HLd. tauto. Qed.

(* a harness block's head word is a word of memory *)
Lemma vrs_head_range : forall ly S Hp (W : world SEGS) m md Lam peak cnt fail ran most own a kk i,
  ARx ly S Hp W m md -> prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> In (a, kk) Lam -> 0 <= i < 8 ->
  8 <= cf_head -> 0 <= a - cf_head + i < 2 ^ 64.
Proof.
intros ly S Hp W m md Lam peak cnt fail ran most own a kk i HAR HLED Hin Hi Hcf.
destruct (vrs_hb ly S Hp W m Lam peak cnt fail ran most own a kk HLED Hin) as (Hk0 & Hab & _).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W m md _ _ HAR Hab) as (_ & Hb4 & Hbc & _).
pose proof alloc_ceiling_lt. pose proof (@cf_head_nonneg cp).
assert (Hn0 : 0 <= kk + cf_head) by lia. pose proof (req_size_pos _ Hn0). lia.
Qed.


(* ---- parse_string's post arms (lib/A/PRH_FnReader.v tparse_string_specX, blob fb7b12dfa169) with the text after
   the quote read as y, and with the three conjuncts the join does not read dropped (the refused malloc_cf's NULL post,
   errno and the new block's shadow). Each arm keeps its live-request Permutation and its exact position transfer
   (vrs_live / vrs_pos at the arm's own list prhPs_evs y okA), and the refusal arm its OUTCOME exclusion (vrs_excl). *)
Definition vrs_arms (ly : alayout) (S : astate) (Hp : list Z) (ly2 : alayout) (S2 : astate) (Hp2 : list Z)
    (W2 : world SEGS) (mem2 : word -> option byte) (q text len p' dz : Z) (tb : list Z) (Lam : list (Z * Z))
    (peak cnt fail ran most own res : Z) (y : list Z) : Prop :=
  match PjGrammar.scan y with
  | None =>
      res = 0 /\ Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
      prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most own /\
      pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
      vrs_live S S2 (prhPs_evs y []) /\ vrs_pos S S2 (prhPs_evs y [])
  | Some Q =>
      (cnt = fail /\ res = 0 /\ Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
       blocks_bytes S2 = blocks_bytes S /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak (cnt + 1) SIZE_MAXZ ran most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
       vrs_live S S2 (prhPs_evs y [false]) /\ vrs_pos S S2 (prhPs_evs y [false]))
      \/
      (cnt <> fail /\ res = 0 /\ Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
       blocks_bytes S2 = blocks_bytes S /\
       vrs_excl S (prhPs_evs y []) /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat Q + 1))))
         ((cnt + 1) mod 2 ^ 64) fail (if Z.of_nat Q + 1 <=? most then 1 else ran) most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
       vrs_live S S2 (prhPs_evs y [false]) /\ vrs_pos S S2 (prhPs_evs y [false]))
      \/
      (cnt <> fail /\ res = 0 /\ PjGrammar.decode y = None /\
       Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 Lam (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail ran most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
       vrs_live S S2 (prhPs_evs y [true]) /\ vrs_pos S S2 (prhPs_evs y [true]))
      \/
      (cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
       exists s r, PjGrammar.decode y = Some (s, r) /\
       Hp2 = (res - cf_head) :: Hp /\
       ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
       pj_cbytesR SEGS (rdW W2 mem2) res s /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, Z.of_nat Q + 1) :: Lam)
         (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail ran most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len (p' + Z.of_nat Q + 2) dz tb /\
       vrs_live S S2 (prhPs_evs y [true]) /\ vrs_pos S S2 (prhPs_evs y [true]))
  end.

Lemma vrs_arms_weak : forall (ly : alayout) S Hp (W : world SEGS) ly2 S2 Hp2 (W2 : world SEGS) mem2
    q text len p' (dz : Z) tb Lam peak cnt fail ran most own res y,
  match PjGrammar.scan y with
  | None =>
      res = 0 /\ Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
      prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most own /\
      pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
      Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
        (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs y [])) /\
      (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
         PRH_Base.prh_run_at sm x os i (prhPs_evs y []) ->
         exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs y []))%nat H0 hist' S2)
  | Some Q =>
      (cnt = fail /\ res = 0 /\ Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
       blocks_bytes S2 = blocks_bytes S /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak (cnt + 1) SIZE_MAXZ ran most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs y [false])) /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (prhPs_evs y [false]) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs y [false]))%nat H0 hist' S2))
      \/
      (cnt <> fail /\ res = 0 /\ Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
       blocks_bytes S2 = blocks_bytes S /\
       (exists regsc memc mdc Wc cc,
          YG0dcf.malloc_cf_null_post SEGS B ly S Hp W regsc memc mdc (Z.of_nat Q + 1 + cf_head) (PNull, S2) Wc cc) /\
       rd32 (aview SEGS (w_H W2) mem2) (as_errno B) 12 /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (prhPs_evs y []) ->
          PRH_Base.prh_cons_from sm x os i (length (prhPs_evs y [])) -> False) /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 Lam (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat Q + 1))))
         ((cnt + 1) mod 2 ^ 64) fail (if Z.of_nat Q + 1 <=? most then 1 else ran) most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs y [false])) /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (prhPs_evs y [false]) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs y [false]))%nat H0 hist' S2))
      \/
      (cnt <> fail /\ res = 0 /\ PjGrammar.decode y = None /\
       Hp2 = Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 Lam (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail ran most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len p' dz tb /\
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs y [true])) /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (prhPs_evs y [true]) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs y [true]))%nat H0 hist' S2))
      \/
      (cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
       exists s r, PjGrammar.decode y = Some (s, r) /\
       Hp2 = (res - cf_head) :: Hp /\
       ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
       prhReader_vis W2 mem2 res (Z.of_nat Q + 1) /\
       pj_cbytesR SEGS (rdW W2 mem2) res s /\
       prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, Z.of_nat Q + 1) :: Lam)
         (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))) (cnt + 1) fail ran most own /\
       pj_in_okR SEGS (rdW W2 mem2) q text len (p' + Z.of_nat Q + 2) dz tb /\
       Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
         (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPs_evs y [true])) /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
          PRH_Base.prh_run_at sm x os i (prhPs_evs y [true]) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPs_evs y [true]))%nat H0 hist' S2))
  end ->
  vrs_arms ly S Hp ly2 S2 Hp2 W2 mem2 q text len p' dz tb Lam peak cnt fail ran most own res y.
Proof.
intros ly S Hp W ly2 S2 Hp2 W2 mem2 q text len p' dz tb Lam peak cnt fail ran most own res y H.
unfold vrs_arms. destruct (PjGrammar.scan y) as [Q|]; [|exact H].
destruct H as [H | [(A1 & A2 & A3 & A4 & A5 & _ & _ & A8) | [H | (A1 & A2 & A3 & s & r & A4 & A5 & A6 & _ & A8)]]].
- left. exact H.
- right. left. exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 A8))))).
- right. right. left. exact H.
- right. right. right. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  exists s, r. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. exact A8.
Qed.

(* a value stored as 8 bytes reads back as that word (VrdIElem.vrd_rdword_of_val_mem, cgif YCem.v:101-115, restated
   here over this file's SEGS so the join does not load VrdIElem.v) *)
Lemma vrs_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
  intros H mem a v Hv Hr.
  assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
  { intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
  unfold rdword.
  rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
  change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
  change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
  change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
  change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
  f_equal. apply le_bytes8. exact Hr.
Qed.


(* ---- THE ARM'S RESULT at the join: vrd_pv_post, in the five outcomes of parse_string ---- *)
Lemma vrs_rq : forall (ly0 : alayout) S0 e q v text len p tb Lam peak cnt fail ran most own pos y p'
    (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
    (Wc : world SEGS) (mc : word -> option byte)
    ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 memF res,
  8 <= cf_head ->
  (forall a, Exists (in_zr a) prh_pst -> in_img SEGS a) ->
  (d <= PjGrammar.MAXD)%nat ->
  (* the model: the quote at p', after the white space from p *)
  PjGrammar.skip (rest_atR tb text p) = 34 :: y -> rest_atR tb text (p' + 1) = y ->
  text <= p -> p <= p' -> p' < text + len -> Z.of_nat (length tb) = len ->
  (* the dispatch state against the entry state, and the ledger's numbers *)
  frames S = (0, pos) :: frames S0 -> ablocks B ly S = ablocks B ly0 S0 -> (exists f, S = set_fs f S0) ->
  0 <= Ledger.lsum Lam <= peak -> 0 <= cnt -> cnt + 1 < 2 ^ 64 - 1 ->
  (* the node's place at the dispatch state, its harness heads, and the cells apart from it *)
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= v /\ v + 56 <= b + req_size n) \/
   (exists cid pos', In (cid, pos') (frames S) /\ frame_addr ly cid pos' <= v /\
      v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid)) ->
  (forall a kk i, In (a, kk) Lam -> 0 <= i < 8 -> ~ (v <= a - cf_head + i < v + 56)) ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  v mod 8 = 0 -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  (q + 24 <= v \/ v + 56 <= q) -> (text + len <= v \/ v + 56 <= text) -> 0 <= q -> q + 24 <= 2 ^ 64 ->
  (* parse_string's post *)
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (forall cid pos', frame_addr ly2 cid pos' = frame_addr ly cid pos') ->
  frames S2 = frames S ->
  room_live_cf S2 ->
  PresetHullBudget.hull_used S S2 (prhPs_evs y []) ->
  blocks_bytes S2 <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace y) ->
  (* the request bound of the dispatch's room (vrd_disp_body's rd_room at the granted trace, which is parse_string's) *)
  prh_maxreq (prhPs_gtrace y) + cf_head < cf_malloc_max ->
  vrs_arms ly S Hp ly2 S2 Hp2 W2 mem2 q text len p' (Z.of_nat d) tb Lam peak cnt fail ran most own res y ->
  (* the node's bytes at the join *)
  pj_zeroR SEGS (rdW W mem) v ->
  (forall a, v <= a < v + 56 -> ~ (v <= a < v + 4) -> ~ (v + 16 <= a < v + 24) ->
     aview SEGS (w_H W2) memF a = aview SEGS (w_H W) mem a) ->
  val_mem SEGS (rdW Wc mc) v 4 4 ->
  (forall a, v <= a < v + 4 -> aview SEGS (w_H W2) memF a = aview SEGS (w_H Wc) mc a) ->
  val_mem SEGS (rdW W2 memF) (v + 16) 8 (bv_unsigned (w64 res)) ->
  rd_rw SEGS (rdW W2 memF) v 56 ->
  (* the join memory against parse_string's post memory: rows 143..151 write the str field only *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) ->
     aview SEGS (w_H W2) memF a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> memF (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)) ->
  vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos
    (if res =? 0 then -1 else 0) ly2 S2 Hp2 W2 memF.
Proof.
intros ly0 S0 e q v text len p tb Lam peak cnt fail ran most own pos y p'
  ly S Hp W mem Wc mc ly2 S2 Hp2 W2 mem2 md2 memF res
  Hcfw HPSTi HdM Hskip Hsucc Htp Hpp Hp'lt Hlen Hfrs Hab Hsetfs Hpk Hc0 HCNT Hplace HHEAD Hvnimg Hv8 Hv0 Hv64
  Hqv Htv Hq0 Hq64 HAR2 Hfa2 Hfrs3 HRL2 HHU2 HBB2 Hmax HARM Hvzero KN Hty KT HstrF HrwF KR2 KR2r.
pose proof (@cf_head_nonneg cp) as Hcf0.
pose proof alloc_ceiling_lt as Hac.
assert (Hbb0 : blocks_bytes S = blocks_bytes S0) by (destruct Hsetfs as (f & ->); reflexivity).
(* the lengths of the rests *)
assert (Hlr : Z.of_nat (length (rest_atR tb text p)) = text + len - p)
  by (unfold rest_atR; rewrite length_skipn; lia).
assert (Hly : Z.of_nat (length y) = text + len - p' - 1)
  by (rewrite <- Hsucc; unfold rest_atR; rewrite length_skipn; lia).
assert (HdZ : Z.of_nat d <= 32) by (unfold PjGrammar.MAXD in HdM; lia).
(* the cursor and the text survive rows 143..151 *)
assert (HIN : forall p0, pj_in_okR SEGS (rdW W2 mem2) q text len p0 (Z.of_nat d) tb ->
                         pj_in_okR SEGS (rdW W2 memF) q text len p0 (Z.of_nat d) tb).
{ intros p0 Hin0. pose proof Hin0 as (_ & _ & _ & _ & _ & Ht0 & Htl & _).
  apply (VrdArm.vrs_in_ok_keep W2 mem2 memF q text len p0 (Z.of_nat d) tb Hin0).
  - intros a Ha. apply KR2; lia.
  - intros a Ha. apply KR2r; lia.
  - intros a Ha. apply KR2; lia. }
(* the statics survive rows 143..151 *)
assert (HPST : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) memF a = aview SEGS (w_H W2) mem2 a).
{ apply (VrdArm.vrs_pst_keep W2 mem2 memF (v + 16) (v + 24) KR2 HPSTi). intros a Ha. apply Hvnimg. lia. }
(* the header at the join, for a given str value *)
assert (HDR : forall str, 0 <= str < 2 ^ 64 -> bv_unsigned (w64 res) = str ->
                pj_hdrR SEGS (rdW W2 memF) v 4 0 str 0 0 0 0).
{ intros str Hs Hstr. rewrite Hstr in HstrF.
  exact (vrs_hdr W Wc W2 mem mc memF v str Hv8 HrwF Hvzero KN Hty KT Hs HstrF). }
(* the hull use: parse_string's at its all-granted list, which is parse_value's at the quote (vrs_gt_evs); the
   dispatch state's meters are the entry's, set_fs moving the fake frames only *)
assert (HHU0 : PresetHullBudget.hull_used S0 S2 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))).
{ rewrite (vrs_gt_evs HI_head d _ y Hskip). destruct Hsetfs as (f & ->). exact HHU2. }
(* the granted trace is parse_string's *)
pose proof (VrdArm.vrs_gtrace_str d _ y Hskip) as Hgt.
unfold vrd_pv_post. unfold vrs_arms in HARM.
set (st := ReaderRes.jr_strtod).
destruct (PjGrammar.scan y) as [Q|] eqn:Hsc.
2:{ (* scan = None: parse_string returns NULL with no call; ok = [], tr = [], no advance *)
  destruct HARM as (Hres & HHp & Hab2 & HLED2 & HIN2 & HLV & HPS). subst res.
  rewrite (vrs_gt_none y Hsc) in HBB2.
  pose proof (vrs_model_none st d _ y [] Hskip Hsc) as HM.
  destruct (vrs_runs_made HI_head st d S0 S S2 _ y [] None [] [] Hsetfs Hskip HM HLV HPS) as (HLV0 & HPS0).
  exists [], None, [], [], [], Lam, peak, cnt, fail, ran.
  split; [exact HM|].
  split.
  { apply (VrdArm.vrs_ledger_keep B ly2 S2 Hp2 W2 mem2 memF Lam peak cnt fail ran most own HLED2 HPST).
    intros a kk i Hin Hi. pose proof (vrs_head_range _ _ _ _ _ _ _ _ _ _ _ _ _ a kk i HAR2 HLED2 Hin Hi Hcfw).
    apply KR2; [lia|]. intros Hc. apply (HHEAD a kk i Hin Hi). lia. }
  split; [exact HRL2|]. split; [exact HHU0|]. split; [exact HLV0|]. split; [exact HPS0|].
  split; [exact (vrs_outcome_granted HI_head st d S0 S S2 _ y [] None [] cnt fail ran ran Hsetfs Hskip (or_introl Hsc)
                   HPS eq_refl ltac:(rewrite HM; reflexivity))|].
  (* THE OUTCOME OF AN INJECTED READING: no call (the granted trace is empty), so the window is empty *)
  split; [intros sm x os i H0 hist _ _ _ Hw; rewrite Hgt, (vrs_gt_none y Hsc) in Hw;
          cbn [PjGrammar.calls Z.of_nat] in Hw; lia|].
  split; [apply vrs_move_nil; [exact Hpk | exact (proj2 (vrs_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED2))]|].
  split; [intros a k Hin; destruct Hin|].
  split; [rewrite Hab2, Hab; unfold prhReader_ab; cbn [map app]; apply Permutation_refl|].
  split; [rewrite Hfrs3, Hfrs; apply Permutation_refl|].
  split; [cbn [hpeakR]; lia|].
  split; [unfold prh_held in HBB2 |- *; cbn [PjGrammar.held PjGrammar.calls] in HBB2 |- *; lia|].
  split; [reflexivity|].
  split; [reflexivity|].
  (* THE FREE ORDER (the kit's cut, FREEORD-NONE): no block is left (str = 0), so the order list is [] at every depth
     (PRH_PjOrder.pfo_leaf); the model's list is the leaf's of this arm's trace (VrdNum.vrd_frees_leaf), none *)
  split.
  { intros HH nn _. exists []. split.
    - apply (PRH_PjOrder.pfo_leaf SEGS _ _ nn v 4 0 0 []).
      + constructor.
      + intros bb x Hb. destruct Hb.
      + apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + left. split; reflexivity.
    - cbn [map]. rewrite (vrd_frees_leaf d _ _ 34 y Hskip ltac:(lia) ltac:(lia)). fold st. rewrite HM. reflexivity. }
  pose proof (HIN p' HIN2) as HINF.
  split.
  - destruct HINF as (V1 & V2 & V3 & Vrw & _ & _ & _ & Vp & _).
    unfold pj_in_afterR. exists p', (Z.of_nat d). split; [lia|]. split; [lia|]. split; [exact V1|]. split; [exact V2|].
    split; [exact V3 | exact Vrw].
  - apply (vrs_fd_hdr _ _ _ v 4 0). apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HQy : (Q < length y)%nat) by exact (proj1 (PjGrammar.scan_quote y Q Hsc)).
destruct (vrs_gt_scan y Q Hsc) as (Hcalls & Hhelds).
destruct HARM as [A1 | [A2 | [A3 | A4]]].
- (* the chosen failure: ok = [false], tr = [EFail], no advance *)
  destruct A1 as (Hcf & Hres & HHp & Hab2 & Hbb2 & HLED2 & HIN2 & HLV & HPS). subst res.
  pose proof (vrs_model_fail st d _ y Q Hskip Hsc) as HM.
  destruct (vrs_runs_made HI_head st d S0 S S2 _ y [false] None _ [] Hsetfs Hskip HM HLV HPS) as (HLV0 & HPS0).
  exists [false], None, [PjGrammar.EFail (Datatypes.S Q)], [], [], Lam, peak, (cnt + 1), SIZE_MAXZ, ran.
  split; [exact HM|].
  split.
  { apply (VrdArm.vrs_ledger_keep B ly2 S2 Hp2 W2 mem2 memF Lam peak (cnt + 1) SIZE_MAXZ ran most own HLED2 HPST).
    intros a kk i Hin Hi. pose proof (vrs_head_range _ _ _ _ _ _ _ _ _ _ _ _ _ a kk i HAR2 HLED2 Hin Hi Hcfw).
    apply KR2; [lia|]. intros Hc. apply (HHEAD a kk i Hin Hi). lia. }
  split; [exact HRL2|]. split; [exact HHU0|]. split; [exact HLV0|]. split; [exact HPS0|].
  split; [intros sm x os i H0 hist _ _ _ Hw; exact (vrs_outcome_chosen d _ y Q cnt fail _ Hskip Hsc Hcf Hw)|].
  (* THE OUTCOME OF AN INJECTED READING: the one failed outcome is the chosen one (cnt = fail) *)
  split; [intros sm x os i H0 hist _ _ _ _ j _ Hn; destruct j as [|j];
          [cbn [Z.of_nat]; lia | destruct j; cbn in Hn; discriminate Hn]|].
  split; [apply (vle_fail_chosen Lam peak cnt fail ran most _ (Datatypes.S Q)); lia|].
  split; [intros a k Hin; destruct Hin|].
  split; [rewrite Hab2, Hab; unfold prhReader_ab; cbn [map app]; apply Permutation_refl|].
  split; [rewrite Hfrs3, Hfrs; apply Permutation_refl|].
  split; [cbn [hpeakR PjGrammar.held_ev]; lia|].
  split; [unfold prh_held; cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [reflexivity|].
  split; [reflexivity|].
  (* THE FREE ORDER (the kit's cut, FREEORD-NONE): no block is left (str = 0), so the order list is [] at every depth
     (PRH_PjOrder.pfo_leaf); the model's list is the leaf's of this arm's trace (VrdNum.vrd_frees_leaf), none *)
  split.
  { intros HH nn _. exists []. split.
    - apply (PRH_PjOrder.pfo_leaf SEGS _ _ nn v 4 0 0 []).
      + constructor.
      + intros bb x Hb. destruct Hb.
      + apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + left. split; reflexivity.
    - cbn [map]. rewrite (vrd_frees_leaf d _ _ 34 y Hskip ltac:(lia) ltac:(lia)). fold st. rewrite HM. reflexivity. }
  pose proof (HIN p' HIN2) as HINF.
  split.
  + destruct HINF as (V1 & V2 & V3 & Vrw & _ & _ & _ & Vp & _).
    unfold pj_in_afterR. exists p', (Z.of_nat d). split; [lia|]. split; [lia|]. split; [exact V1|]. split; [exact V2|].
    split; [exact V3 | exact Vrw].
  + apply (vrs_fd_hdr _ _ _ v 4 0). apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- (* the allocator's refusal: ok = [false], tr = [EFail], no advance; #102's refusal ledger *)
  destruct A2 as (Hcf & Hres & HHp & Hab2 & Hbb2 & HX & HLED2 & HIN2 & HLV & HPS). subst res.
  rewrite (Z.mod_small (cnt + 1) (2 ^ 64)) in HLED2 by lia.
  pose proof (vrs_model_fail st d _ y Q Hskip Hsc) as HM.
  destruct (vrs_runs_made HI_head st d S0 S S2 _ y [false] None _ [] Hsetfs Hskip HM HLV HPS) as (HLV0 & HPS0).
  exists [false], None, [PjGrammar.EFail (Datatypes.S Q)], [], [], Lam,
    (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat Q + 1)))), (cnt + 1), fail,
    (if Z.of_nat Q + 1 <=? most then 1 else ran).
  split; [exact HM|].
  split.
  { apply (VrdArm.vrs_ledger_keep B ly2 S2 Hp2 W2 mem2 memF Lam _ _ fail _ most own HLED2 HPST).
    intros a kk i Hin Hi. pose proof (vrs_head_range _ _ _ _ _ _ _ _ _ _ _ _ _ a kk i HAR2 HLED2 Hin Hi Hcfw).
    apply KR2; [lia|]. intros Hc. apply (HHEAD a kk i Hin Hi). lia. }
  split; [exact HRL2|]. split; [exact HHU0|]. split; [exact HLV0|]. split; [exact HPS0|].
  split; [intros sm x os i H0 hist Hp0 Hr0 Hc0' _;
          exact (vrs_outcome_refused HI_head d S0 S _ y _ Hsetfs Hskip HX sm x os i H0 hist Hp0 Hr0 Hc0')|].
  (* THE OUTCOME OF AN INJECTED READING: parse_string's one call is in the window only at fail = cnt, which this arm
     excludes *)
  split; [intros sm x os i H0 hist _ _ _ Hw; rewrite Hgt, Hcalls in Hw; cbn [Z.of_nat] in Hw; lia|].
  split; [replace (Z.of_nat Q + 1 <=? most) with (Z.of_nat (Datatypes.S Q) <=? most) by (f_equal; lia);
          apply (vle_fail_refused Lam peak cnt fail ran most _ (Datatypes.S Q) (Z.of_nat Q + 1));
          [lia | lia | exact Hcf | lia | lia | rewrite Hgt, Hhelds; cbn [hd_error]; f_equal; lia]|].
  split; [intros a k Hin; destruct Hin|].
  split; [rewrite Hab2, Hab; unfold prhReader_ab; cbn [map app]; apply Permutation_refl|].
  split; [rewrite Hfrs3, Hfrs; apply Permutation_refl|].
  split; [cbn [hpeakR PjGrammar.held_ev]; lia|].
  split; [unfold prh_held; cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [reflexivity|].
  split; [reflexivity|].
  (* THE FREE ORDER (the kit's cut, FREEORD-NONE): no block is left (str = 0), so the order list is [] at every depth
     (PRH_PjOrder.pfo_leaf); the model's list is the leaf's of this arm's trace (VrdNum.vrd_frees_leaf), none *)
  split.
  { intros HH nn _. exists []. split.
    - apply (PRH_PjOrder.pfo_leaf SEGS _ _ nn v 4 0 0 []).
      + constructor.
      + intros bb x Hb. destruct Hb.
      + apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + left. split; reflexivity.
    - cbn [map]. rewrite (vrd_frees_leaf d _ _ 34 y Hskip ltac:(lia) ltac:(lia)). fold st. rewrite HM. reflexivity. }
  pose proof (HIN p' HIN2) as HINF.
  split.
  + destruct HINF as (V1 & V2 & V3 & Vrw & _ & _ & _ & Vp & _).
    unfold pj_in_afterR. exists p', (Z.of_nat d). split; [lia|]. split; [lia|]. split; [exact V1|]. split; [exact V2|].
    split; [exact V3 | exact Vrw].
  + apply (vrs_fd_hdr _ _ _ v 4 0). apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- (* a bad escape: ok = [true], tr = [EAlloc; EFree], advance 2; the block is taken and given back *)
  destruct A3 as (Hcf & Hres & Hdec & HHp & Hab2 & HLED2 & HIN2 & HLV & HPS). subst res.
  rewrite (vrs_gt_bad y Q Hsc Hdec) in HBB2.
  pose proof (vrs_model_bad st d _ y Q [true] Hskip Hsc Hdec (or_intror eq_refl)) as HM.
  pose proof (vrs_model_bad st d _ y Q [] Hskip Hsc Hdec (or_introl eq_refl)) as HMg.
  destruct (vrs_runs_made HI_head st d S0 S S2 _ y [true] None _ [] Hsetfs Hskip HM HLV HPS) as (HLV0 & HPS0).
  exists [true], None, [PjGrammar.EAlloc (Datatypes.S Q); PjGrammar.EFree (Datatypes.S Q)], [], [], Lam,
    (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))), (cnt + 1), fail, ran.
  split; [exact HM|].
  split.
  { apply (VrdArm.vrs_ledger_keep B ly2 S2 Hp2 W2 mem2 memF Lam _ (cnt + 1) fail ran most own HLED2 HPST).
    intros a kk i Hin Hi. pose proof (vrs_head_range _ _ _ _ _ _ _ _ _ _ _ _ _ a kk i HAR2 HLED2 Hin Hi Hcfw).
    apply KR2; [lia|]. intros Hc. apply (HHEAD a kk i Hin Hi). lia. }
  split; [exact HRL2|]. split; [exact HHU0|]. split; [exact HLV0|]. split; [exact HPS0|].
  split; [exact (vrs_outcome_granted HI_head st d S0 S S2 _ y [true] None _ cnt fail ran ran Hsetfs Hskip
                   (or_intror eq_refl) HPS eq_refl ltac:(rewrite HMg; reflexivity))|].
  (* THE OUTCOME OF AN INJECTED READING: the window is fail = cnt, which this arm excludes *)
  split; [intros sm x os i H0 hist _ _ _ Hw; rewrite Hgt, Hcalls in Hw; cbn [Z.of_nat] in Hw; lia|].
  split; [replace (Z.of_nat Q + 1) with (Z.of_nat (Datatypes.S Q)) by lia;
          apply (vle_alloc_free Lam peak cnt fail ran most _ (Datatypes.S Q)); lia|].
  split; [intros a k Hin; destruct Hin|].
  split; [rewrite Hab2, Hab; unfold prhReader_ab; cbn [map app]; apply Permutation_refl|].
  split; [rewrite Hfrs3, Hfrs; apply Permutation_refl|].
  split; [cbn [hpeakR PjGrammar.held_ev]; lia|].
  split; [rewrite Hbb0 in HBB2; exact HBB2|].
  split; [cbn [Ledger.lsum PjGrammar.held PjGrammar.held_ev]; lia|].
  split; [reflexivity|].
  (* THE FREE ORDER (the kit's cut, FREEORD-NONE): no block is left (str = 0), so the order list is [] at every depth
     (PRH_PjOrder.pfo_leaf); the model's list is the leaf's of this arm's trace (VrdNum.vrd_frees_leaf), none *)
  split.
  { intros HH nn _. exists []. split.
    - apply (PRH_PjOrder.pfo_leaf SEGS _ _ nn v 4 0 0 []).
      + constructor.
      + intros bb x Hb. destruct Hb.
      + apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + left. split; reflexivity.
    - cbn [map]. rewrite (vrd_frees_leaf d _ _ 34 y Hskip ltac:(lia) ltac:(lia)). fold st. rewrite HM. reflexivity. }
  pose proof (HIN p' HIN2) as HINF.
  split.
  + destruct HINF as (V1 & V2 & V3 & Vrw & _ & _ & _ & Vp & _).
    unfold pj_in_afterR. exists p', (Z.of_nat d). split; [lia|]. split; [lia|]. split; [exact V1|]. split; [exact V2|].
    split; [exact V3 | exact Vrw].
  + apply (vrs_fd_hdr _ _ _ v 4 0). apply HDR; [lia|]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- (* the string, in a new harness block: ok = [true], tr = [EAlloc], advance 1 *)
  destruct A4 as (Hcf & Hres4 & Hres16 & s & r & Hdec & HHp & Eab & HCB & HLED2 & HIN2 & HLV & HPS).
  rewrite (vrs_gt_str y Q s r Hsc Hdec) in HBB2, Hmax.
  pose proof (vrs_model_str st d _ y Q s r [true] Hskip Hsc Hdec (or_intror eq_refl)) as HM.
  pose proof (vrs_model_str st d _ y Q s r [] Hskip Hsc Hdec (or_introl eq_refl)) as HMg.
  destruct (vrs_runs_made HI_head st d S0 S S2 _ y [true] _ _ [] Hsetfs Hskip HM HLV HPS) as (HLV0 & HPS0).
  (* the string is shorter than 2 ^ 30: its block's request is below cf_malloc_max, whose sizes fit cf_nob *)
  assert (Hq30 : Z.of_nat Q + 1 < 2 ^ 30).
  { unfold prh_maxreq in Hmax. cbn [map fold_right PjGrammar.esize] in Hmax.
    assert (Hn1 : 0 <= Z.of_nat Q + 1 + cf_head < cf_malloc_max) by lia.
    pose proof (cf_sizes_ok _ Hn1) as Hsz.
    pose proof (YG08cf.sec_map_size_ge _ (proj1 Hn1)) as Hge.
    pose proof cf_nob_ok. lia. }
  destruct (PjGrammar.decode_stop y s r Hdec) as (q0 & Hsc0 & Hr & Hls & _).
  rewrite Hsc in Hsc0. injection Hsc0 as <-.
  assert (Hlenr : Z.of_nat (length r) = Z.of_nat (length y) - Z.of_nat Q - 1)
    by (rewrite Hr, length_skipn; lia).
  (* the new block, appended at the post state *)
  assert (Hinb : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S2))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hinb) as (_ & Hb4 & Hbc & _).
  assert (Hreqn : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
  rewrite Hreqn in Hbc.
  assert (Hfresh : ~ In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S)).
  { intros Hin.
    pose proof ((VrdArm.vrs_sep_last B ARx LAWS) ly2 S2 Hp2 W2 mem2 md2 (ablocks B ly S)
      (res - cf_head, Z.of_nat Q + 1 + cf_head) (res - cf_head) (Z.of_nat Q + 1 + cf_head) HAR2 Eab Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqn in Hd. lia. }
  (* the new block is apart from the node *)
  assert (Happ : forall x, res - cf_head <= x < res + Z.of_nat Q + 1 -> ~ (v <= x < v + 56)).
  { intros x Hx Hxv. destruct Hplace as [(b0 & n0 & Hin0 & Hle0 & Hhi0) | (cid & pos' & Hin0 & Hle0 & Hhi0)].
    - pose proof ((VrdArm.vrs_sep_last B ARx LAWS) ly2 S2 Hp2 W2 mem2 md2 (ablocks B ly S)
        (res - cf_head, Z.of_nat Q + 1 + cf_head) b0 n0 HAR2 Eab Hin0) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqn in Hd. lia.
    - assert (Hin2 : In (cid, pos') (frames S2)) by (rewrite Hfrs3; exact Hin0).
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos' HAR2 Hinb Hin2) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqn, Hfa2 in Hd. lia. }
  assert (Hres0 : (res =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hres0.
  exists [true], (Some (JStr s, r)), [PjGrammar.EAlloc (Datatypes.S Q)], [], [(res, Z.of_nat Q + 1)],
    ((res, Z.of_nat Q + 1) :: Lam), (Z.max peak (Ledger.lsum Lam + (Z.of_nat Q + 1))), (cnt + 1), fail, ran.
  split; [exact HM|].
  split.
  { apply (VrdArm.vrs_ledger_keep B ly2 S2 Hp2 W2 mem2 memF _ _ (cnt + 1) fail ran most own HLED2 HPST).
    intros a kk i Hin Hi. pose proof (vrs_head_range _ _ _ _ _ _ _ _ _ _ _ _ _ a kk i HAR2 HLED2 Hin Hi Hcfw).
    apply KR2; [lia|]. intros Hc. destruct Hin as [Heq | Hin].
    - injection Heq as <- <-. apply (Happ (res - cf_head + i)); lia.
    - apply (HHEAD a kk i Hin Hi). lia. }
  split; [exact HRL2|]. split; [exact HHU0|]. split; [exact HLV0|]. split; [exact HPS0|].
  split; [exact (vrs_outcome_granted HI_head st d S0 S S2 _ y [true] _ _ cnt fail ran ran Hsetfs Hskip
                   (or_intror eq_refl) HPS eq_refl ltac:(rewrite HMg; reflexivity))|].
  (* THE OUTCOME OF AN INJECTED READING: the window is fail = cnt, which this arm excludes *)
  split; [intros sm x os i H0 hist _ _ _ Hw; rewrite Hgt, Hcalls in Hw; cbn [Z.of_nat] in Hw; lia|].
  split; [replace (Z.of_nat Q + 1) with (Z.of_nat (Datatypes.S Q)) by lia;
          apply (vle_alloc Lam peak cnt fail ran most _ res (Datatypes.S Q)); lia|].
  split; [intros a k [Heq | []]; injection Heq as <- <-; rewrite <- Hab; exact Hfresh|].
  split; [rewrite Eab, Hab; unfold prhReader_ab; cbn [map app fst snd]; apply Permutation_sym, Permutation_cons_append|].
  split; [rewrite Hfrs3, Hfrs; apply Permutation_refl|].
  split; [cbn [hpeakR PjGrammar.held_ev]; lia|].
  split; [rewrite Hbb0 in HBB2; exact HBB2|].
  split; [cbn [Ledger.lsum PjGrammar.held PjGrammar.held_ev]; lia|].
  split; [reflexivity|].
  (* THE FREE ORDER (the kit's cut, FREEORD-NONE): the string's one block, the node's str, at every depth; the model's
     list is the leaf's of [EAlloc (S Q)] *)
  split.
  { intros HH nn _. exists [(res, Z.of_nat Q + 1)]. split.
    - apply (PRH_PjOrder.pfo_leaf SEGS _ _ nn v 4 0 res [(res, Z.of_nat Q + 1)]).
      + exact (list_relations.list.NoDup_singleton (res, Z.of_nat Q + 1)).
      + intros b x [<- | []] Hx. unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply (Happ x). lia.
      + apply HDR; [lia | unfold w64; rewrite unsigned_lit_small by lia; reflexivity].
      + right. exists (Z.of_nat Q + 1). split; [unfold prh_lin; left; reflexivity | reflexivity].
    - rewrite (vrd_frees_leaf d _ _ 34 y Hskip ltac:(lia) ltac:(lia)). fold st. rewrite HM.
      cbn [map fst snd PresetReqAt.lf]. f_equal. rewrite HH. lia. }
  split.
  { replace (text + len - Z.of_nat (length r)) with (p' + Z.of_nat Q + 2) by lia. exact (HIN _ HIN2). }
  split.
  { cbn [pj_nodeR tag].
    split; [constructor; [intros Hx; inversion Hx | constructor]|].
    split.
    { intros b x [<- | []] Hx. unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply (Happ x). lia. }
    exists 0, res, 0, 0, 0, 0.
    split; [apply HDR; [lia | unfold w64; rewrite unsigned_lit_small by lia; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists (Z.of_nat Q + 1). split; [|reflexivity].
    unfold pj_cstrR. split; [unfold prh_lin; left; reflexivity|]. split; [lia|]. split; [lia|].
    destruct HCB as (HFs & HG). unfold pj_cbytesR. split; [exact HFs|].
    apply (VrdArm.vrs_garr8_keep W2 mem2 memF res (s ++ [0]) HG).
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    apply KR2; [lia|]. intros Hc. apply (Happ (res + Z.of_nat j)); lia. }
  (* CAP: a string is no container, pj_ncapR holds of it by computation *)
  split; [exact I|].
  cbn [Ledger.lsum]. lia.
Qed.


(* ---- small engine facts the join reads ---- *)

(* rows 149..150 (`snez s5, a0; addi s5, s5, -1`): the return code *)
Lemma vrs_snez : forall res, 0 <= res < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 res)) (Z_to_bv 64 (-1)) =
  w64 (if res =? 0 then -1 else 0).
Proof.
intros res Hr.
assert (E : alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 res) = Z_to_bv 64 (if res =? 0 then 0 else 1)).
{ apply bv_eq. cbn [alu64 alu]. unfold bv_ltu. rewrite !unsigned_lit_small by lia.
  destruct (Z.eqb_spec res 0) as [-> | Hne]; [reflexivity|].
  rewrite (proj2 (Z.ltb_lt 0 res)) by lia. reflexivity. }
rewrite E. unfold w64. destruct (res =? 0); apply bv_eq; vm_compute; reflexivity.
Qed.

(* a value a chunk of a region of an ENGINE state (st_ok, the form a run hands a call) holds: VnumD's
   vrd_val_of_st, which is stated over st_ok_pi, over st_ok; the same three engine lemmas *)
Lemma vrs_val_of_st_ok : forall E ss ms (H : word -> bool) (b : option nat) lo hi wlo whi cs off (n : N) ev v,
  st_ok SEGS E ss (restrict H ms) ->
  In (YP09.mkRegion b lo hi wlo whi cs) (ss_mem ss) -> In (YP09.mkChunk off (CVal n ev)) cs ->
  sv_denot E ev = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E b + off) (N.to_nat n) v.
Proof.
intros E ss ms H b lo hi wlo whi cs off n ev v HS Hr Hc He Hv Hn.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (val_of_chunk_ok SEGS E _ _ off n ev v); [|exact He|exact Hv|exact Hn].
apply (region_ok_chunk SEGS E _ (YP09.mkRegion b lo hi wlo whi cs)); [|exact Hc].
eapply mem_ok_region; [exact HM | exact Hr].
Qed.

(* eight present bytes read as a word *)
Lemma vrs_rdword_present : forall (H : word -> bool) m a,
  (forall k, 0 <= k < 8 -> apresent H m (a + k)) -> exists w, rdword (aview SEGS H m) a = Some w.
Proof.
intros H m a Hp.
assert (Hs : forall k, 0 <= k < 8 -> exists z, aview SEGS H m (a + k) = Some z).
{ intros k Hk. destruct (Hp k Hk) as (Hh & b & Hb). exists (bv_unsigned b).
  unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
destruct (Hs 0 ltac:(lia)) as (z0 & E0). rewrite Z.add_0_r in E0.
destruct (Hs 1 ltac:(lia)) as (z1 & E1). destruct (Hs 2 ltac:(lia)) as (z2 & E2).
destruct (Hs 3 ltac:(lia)) as (z3 & E3). destruct (Hs 4 ltac:(lia)) as (z4 & E4).
destruct (Hs 5 ltac:(lia)) as (z5 & E5). destruct (Hs 6 ltac:(lia)) as (z6 & E6).
destruct (Hs 7 ltac:(lia)) as (z7 & E7).
unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists; reflexivity.
Qed.

(* two views that hold the same value at the same bytes agree there *)
Lemma vrs_aview_of_vals : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a n v,
  val_mem SEGS (mrestrict H1 m1) a n v -> val_mem SEGS (mrestrict H2 m2) a n v ->
  forall k, 0 <= k < Z.of_nat n -> aview SEGS H1 m1 (a + k) = aview SEGS H2 m2 (a + k).
Proof.
intros H1 H2 m1 m2 a n v V1 V2 k Hk. unfold aview.
replace k with (Z.of_nat (Z.to_nat k)) by lia.
rewrite (V1 (Z.to_nat k) ltac:(lia)), (V2 (Z.to_nat k) ltac:(lia)). reflexivity.
Qed.

(* ---- THE CHAINS AT THE CALL of row 142, from VproC's three lemmas (VrdPro.v: vrd_disp_chain, vrd_cur_entry_call,
   vrd_cur_chain_call) and the dispatch state's own facts. STATES: (W0, mem0, regs0) parse_value's entry; (W, mem) the
   dispatch; (W, mc) the call memory (rows 135..141 wrote the node's type word only); regsc the call's registers.
   prh_cur_entry's first conjunct is the Forall over entry chains (PRH_Base.v blob ee2f5cd7ed35); VproD's
   vrd_cur_entry_call carries prh_cur_entry and the cursor set's prh_cw_entry to the call registers from the arm's own
   facts: s0 at the call is parse_value's entry sp (no arm row writes s0), the entry ra is below the ceiling (fpre's
   fourth conjunct), and the entry cursor word p is at least 4096 (pj_in_okR: text <= p, 4096 <= text). At the kit's cut
   7cdbb61b5fa0 parse_string takes prh_cw_ok B CW (PRH_FnReader.v blob f1ae32e3b2cd, in the slot of the deleted
   prh_cur_ok), which is the call state's prh_cw_entry at parse_string's own free word. ---- *)
Lemma vrs_call_chains : forall (CW : list (list Z)) (ly0 ly : alayout) (W0 W : world SEGS)
    (mem0 mem mc : word -> option byte)
    (regs0 regsc : bvmap 5 word) (ch : list (Z * Z * Z)) e q v p p' text len dz tb sp0j STKj,
  pi_s0cur F_parse_string = Some 0 -> pi_s0cur F_parse_items = Some 0 ->
  (exists ch', achain ly0 (aview SEGS (w_H W0) mem0) (spZ regs0) (s0Z regs0) ch' /\ spine ch' = spine ch) ->
  prh_cur_entry W0 mem0 regs0 q -> prh_cw_entry B CW W0 mem0 regs0 q ->
  pj_in_okR SEGS (rdW W0 mem0) q text len p dz tb ->
  pj_in_okR SEGS (rdW W mem) q text len p' dz tb ->
  4096 <= text -> text + len < alloc_ceiling ->
  vrd_saved (rdW W mem) (spZ regs0) regs0 -> 4096 <= raZ regs0 -> raZ regs0 < alloc_ceiling ->
  s0Z regsc = spZ regs0 ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> apresent (w_H W) mem a) ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0j - STKj <= a < sp0j) ->
     aview SEGS (w_H W) mc a = aview SEGS (w_H W0) mem0 a) ->
  sp0j = spZ regs0 + e ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H W) mc a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> mc (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  ly_top ly = ly_top ly0 -> ly_top ly0 <= 2 ^ 64 ->
  alloc_ceiling + 176 <= spZ regs0 -> spZ regs0 mod 16 = 0 ->
  spZ regs0 <= q -> q + 24 <= spZ regs0 + e -> spZ regs0 + e <= ly_top ly0 ->
  v + 56 <= alloc_ceiling -> 0 <= v ->
  spZ regsc + 160 <= spZ regs0 -> 0 <= pi_frame F_parse_string ->
  (exists ch1, achain ly (aview SEGS (w_H W) mc) (spZ regsc) (spZ regs0) ch1 /\ spine ch1 = raZ regs0 :: spine ch) /\
  (exists ch2, achain ly (aview SEGS (w_H W) mc) (spZ regsc - pi_frame F_parse_string) (prh_s0 F_parse_string q) ch2) /\
  prh_cw_ok B CW W mc F_parse_string q /\ prh_cur_low W mc F_parse_string q.
Proof.
intros CW ly0 ly W0 W mem0 mem mc regs0 regsc ch e q v p p' text len dz tb sp0j STKj
  Hps Hpi HCH HCE HCW Hin0 Hin Ht4 Htc Hsv Hra4 HraC Hs0c Hpres Hwin HF1 Hsp0j KR1 KR1r Hly Htop Hsc Hs16 Hq1 Hq2
  Hetop Hvc Hv0 Hrc Hpf.
pose proof alloc_ceiling_lt as Hac.
destruct Hin0 as (P0 & _ & D0 & _ & Hq8 & _ & Htl & Hp0 & _).
pose proof Hin as (P1 & _ & D1 & _ & _ & _ & _ & Hp1 & _).
(* the call view agrees with the entry view at and above the entry sp, off the reader's cells *)
assert (HM : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
               aview SEGS (w_H W) mc a = aview SEGS (w_H W0) mem0 a).
{ intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs0 + e)) as [Hlt | Hge].
  - rewrite (KR1 a ltac:(lia) ltac:(lia)). exact (Hwin a ltac:(lia) Hn).
  - apply HF1; lia. }
(* the two saved words, at the call view *)
destruct Hsv as (V1 & V2 & _).
assert (Hr8 : rdword (aview SEGS (w_H W) mc) (spZ regs0 - 8) = Some (raZ regs0)).
{ apply vrs_rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
  apply (val_mem_kept SEGS (w_H W) (w_H W) mem mc); [|exact V1]. intros k Hk. apply KR1; lia. }
assert (Hr16 : rdword (aview SEGS (w_H W) mc) (spZ regs0 - 16) = Some (s0Z regs0)).
{ apply vrs_rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
  apply (val_mem_kept SEGS (w_H W) (w_H W) mem mc); [|exact V2]. intros k Hk. apply KR1; lia. }
(* the cursor's p words, at the entry view and at the call view *)
assert (Hpw0 : rdword (aview SEGS (w_H W0) mem0) q = Some p)
  by (apply vrs_rdword_of_val_mem; [exact P0 | lia]).
assert (Hpw : rdword (aview SEGS (w_H W) mc) q = Some p').
{ apply vrs_rdword_of_val_mem; [|lia].
  apply (val_mem_kept SEGS (w_H W) (w_H W) mem mc); [|exact P1]. intros k Hk. apply KR1; lia. }
(* the depth bytes, equal in the two views *)
assert (HD : forall a, q + 16 <= a < q + 20 -> aview SEGS (w_H W) mc a = aview SEGS (w_H W0) mem0 a).
{ intros a Ha. rewrite (KR1 a ltac:(lia) ltac:(lia)).
  replace a with (q + 16 + (a - (q + 16))) by lia.
  exact (vrs_aview_of_vals (w_H W) (w_H W0) mem mem0 (q + 16) 4 dz D1 D0 (a - (q + 16)) ltac:(lia)). }
split.
{ eapply vrd_disp_chain; [exact HCH | exact HCE | exact Hpw0 | lia | lia | exact Hpw | lia | lia | exact Hq8
  | exact Hly | exact Htop | lia | lia | lia | lia | exact Hra4 | exact Hr8 | exact Hr16 | exact HM | lia | exact HD]. }
assert (HCEc : prh_cur_entry W mc regsc q /\ prh_cw_entry B CW W mc regsc q).
{ eapply vrd_cur_entry_call;
    [exact Hps | exact Hpi | exact HCE | exact HCW | exact Hs0c | lia | exact HraC | exact Hpw0 | lia
    | lia | lia | exact Hq8 | lia | lia | exact Hr8 | exact Hr16 | exact HM | lia]. }
assert (Hs0 : prh_s0 F_parse_string q = q) by (unfold prh_s0; rewrite Hps; lia).
pose proof (proj2 (proj1 HCEc) F_parse_string (or_introl eq_refl)) as Hlow.
rewrite Hs0 in Hlow.
(* parse_string's own free word: the call state's prh_cw_entry, at a word below the call's sp - 16 *)
assert (Hok' : prh_cw_ok B CW W mc F_parse_string q).
{ unfold prh_cw_ok. rewrite Hs0. intros r w Hr Hw.
  apply (proj2 HCEc F_parse_string r w (or_introl eq_refl) Hr). rewrite Hs0. unfold prh_word_entry.
  rewrite (proj2 (Z.eqb_neq (q - 8) (spZ regsc - 8))) by lia.
  rewrite (proj2 (Z.eqb_neq (q - 8) (spZ regsc - 16))) by lia. exact Hw. }
assert (Hlow' : prh_cur_low W mc F_parse_string q).
{ unfold prh_cur_low. rewrite Hs0. intros w Hw. apply Hlow. unfold prh_word_entry.
  rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regsc - 8))) by lia.
  rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regsc - 16))) by lia. exact Hw. }
(* every 8-aligned word from the saved s0 slot up to the cursor is a word of the call view *)
assert (HW8 : forall a, a mod 8 = 0 -> spZ regs0 - 16 <= a -> a + 8 <= spZ regs0 + e ->
                exists w, rdword (aview SEGS (w_H W) mc) a = Some w).
{ intros a Ha8 Ha1 Ha2.
  destruct (Z.eq_dec a (spZ regs0 - 16)) as [-> | N16]; [eexists; exact Hr16|].
  destruct (Z.eq_dec a (spZ regs0 - 8)) as [-> | N8]; [eexists; exact Hr8|].
  apply vrs_rdword_present. intros k Hk.
  assert (Hak : spZ regs0 <= a + k < spZ regs0 + e) by lia.
  destruct (Hpres (a + k) Hak) as (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite (KR1r (a + k) ltac:(lia) ltac:(lia)). exact Hb. }
destruct (HW8 (q - 16) ltac:(lia) ltac:(lia) ltac:(lia)) as (w16 & H16).
split; [|split; [exact Hok' | exact Hlow']].
rewrite Hs0. eapply vrd_cur_chain_call; [lia | lia | exact Hq8 | lia | exact H16 | exact (Hlow' w16 ltac:(rewrite Hs0; exact H16)) |].
exact (HW8 (q - 8) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* ---- THE JOIN at ROW 225: vrd_epi_aR with the arm's result vrd_pv_post. The kit's cut 7cdbb61b5fa0: parse_string's post
   is budgeted (fpostWbm at wbudget CW 0, PRH_FnReader.v blob f1ae32e3b2cd), so its journal over the call is at a
   budget WS1 and the caller's journal after it at a budget WS within wbudget CW 0, which vrd_epi_aR carries.
   THE RE-HIDING MOVE: parse_string's text concludes SRr' segs RZ_cf with its journal at wle' (it frees its block on a
   bad escape), so both journals here are at wle' and the join is vrd_epi_aR at wle'. ---- *)
Lemma vrs_join : forall ly0 S0 Hp0 W0 regs0 mem0 md0 e q v text len p tb Lam peak cnt fail ran most own pos y p'
    (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem memc : word -> option byte) (md mdc : Model)
    (STKc spc lo : Z) ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 regsF memF mdF kF res (CW WS WS1 : list (list Z)),
  8 <= cf_head ->
  (forall a, Exists (in_zr a) prh_pst -> in_img SEGS a) ->
  (d <= PjGrammar.MAXD)%nat ->
  (* the model *)
  PjGrammar.skip (rest_atR tb text p) = 34 :: y -> rest_atR tb text (p' + 1) = y ->
  text <= p -> p <= p' -> p' < text + len -> Z.of_nat (length tb) = len ->
  (* the dispatch state *)
  ARx ly S Hp W mem md ->
  frames S = (0, pos) :: frames S0 -> ablocks B ly S = ablocks B ly0 S0 -> (exists f, S = set_fs f S0) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> cnt + 1 < 2 ^ 64 - 1 ->
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= v /\ v + 56 <= b + req_size n) \/
   (exists cid pos', In (cid, pos') (frames S) /\ frame_addr ly cid pos' <= v /\
      v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid)) ->
  (forall a kk i, In (a, kk) Lam -> 0 <= i < 8 -> ~ (v <= a - cf_head + i < v + 56)) ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  v mod 8 = 0 -> 4096 <= v -> v + 56 <= alloc_ceiling ->
  (q + 24 <= v \/ v + 56 <= q) -> (text + len <= v \/ v + 56 <= text) ->
  spZ regs0 <= q -> q + 24 <= spZ regs0 + e -> spZ regs0 + e < 2 ^ 64 -> 0 <= e ->
  alloc_ceiling + 176 <= spZ regs0 ->
  pj_zeroR SEGS (rdW W mem) v ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a) ->
  vrd_frame W mem ly pos -> vrd_saved (rdW W mem) (spZ regs0) regs0 ->
  YK0s.ret_ok (getr regs0 1) -> frm_zero (@YK11.fp_csr fx) ->
  prh_maxreq (prhPs_gtrace y) + cf_head < cf_malloc_max ->
  (* rows 135..141 *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  val_mem SEGS (rdW W memc) v 4 4 ->
  (* the call of row 142 *)
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc spc [(q, q + 8)] ly S Hp W memc mdc []
    ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  lo <= spZ regs0 - 104 ->
  (forall a, lo <= a < spZ regs0 + e -> ~ inFP [(q, q + 8)] a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  room_live_cf S2 ->
  PresetHullBudget.hull_used S S2 (prhPs_evs y []) ->
  blocks_bytes S2 <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace y) ->
  vrs_arms ly S Hp ly2 S2 Hp2 W2 mem2 q text len p' (Z.of_nat d) tb Lam peak cnt fail ran most own res y ->
  (forall b n, In (b, n) (ablocks B ly S) -> In (b, n) (ablocks B ly2 S2)) ->
  (* rows 143..151 *)
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_value d + e) (spZ regs0 + e)
    (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly2 S2 Hp2 W2 memF mdF kF WS ->
  YCbqGwild.wbudget CW 0 WS ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) ->
     aview SEGS (w_H W2) memF a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> memF (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)) ->
  val_mem SEGS (rdW W2 memF) (v + 16) 8 (bv_unsigned (w64 res)) ->
  rd_rw SEGS (rdW W2 memF) v 56 ->
  getr regsF 8 = w64 (spZ regs0) -> getr regsF 18 = w64 (frame_addr ly 0 pos) ->
  getr regsF 26 = w64 (frame_addr ly 0 pos) -> getr regsF 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  getr regsF 21 = alu64 ALU_ADD (alu64 ALU_SLTU (Z_to_bv 64 0) (w64 res)) (Z_to_bv 64 (-1)) ->
  getr regsF 3 = getr regs0 3 -> getr regsF 4 = getr regs0 4 ->
  vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos
    (if res =? 0 then -1 else 0)
    (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos (if res =? 0 then -1 else 0))
    W2 (mkCfg (@YK11.mkst fx regsF (w64 (pa_sigma AS_parse_value + PV_EPI)) memF (YK11.seg_rom SEGS)) mdF).
Proof.
intros ly0 S0 Hp0 W0 regs0 mem0 md0 e q v text len p tb Lam peak cnt fail ran most own
  pos y p' ly S Hp W mem memc md mdc STKc spc lo ly2 S2 Hp2 W2 mem2 md2 k1 regsF memF mdF kF res CW WS WS1
  Hcfw HPSTi HdM Hskip Hsucc Htp Hpp Hp'lt Hlen HARd Hfrs Hab Hsetfs HLED HCNT Hplace HHEAD Hvnimg Hv8 Hv4 Hvc
  Hqv Htv Hq1 Hq2 Hse He0 Hsc Hvzero Hvra Hwin Hframe Hsaved Hra HFZ Hmax KR1 HTY HJc Hlo HWIN2 HRL2 HHU2 HBB2
  HARM HCb HJF HWB KR2 KR2r HstrF HrwF HR8 HR18 HR26 HR24 HR21 HR3 HR4.
pose proof alloc_ceiling_lt as Hac. pose proof (@cf_head_nonneg cp) as Hcf0.
pose proof (ajxR_ar HJc) as HAR2. pose proof (ajxR_ly HJc) as Hlyl. pose proof (ajxR_frs HJc) as Hfrs3.
pose proof (ajxR_blk HJc) as HB10. pose proof (ajxR_frm HJc) as HF12.
cbn [app] in Hfrs3.
assert (Hfa2 : forall cid pos', frame_addr ly2 cid pos' = frame_addr ly cid pos').
{ intros cid pos'. unfold frame_addr. destruct Hlyl as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. }
assert (Hfl2 : flag_addr ly2 0 pos = flag_addr ly 0 pos).
{ unfold flag_addr. destruct Hlyl as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. }
assert (Hbb0 : blocks_bytes S = blocks_bytes S0) by (destruct Hsetfs as (f & ->); reflexivity).
destruct (vrs_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hlive & Hcnt64).
(* the node's bytes across the call: parse_string's journal keeps its block (or its fake frame) off [q, q + 8) *)
assert (KCAL : forall a, v <= a < v + 56 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha.
  assert (HnFP : ~ inFP [(q, q + 8)] a)
    by (intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []]; cbn [fst snd] in Hr; lia).
  destruct Hplace as [(b0 & n0 & Hin0 & Hle0 & Hhi0) | (cid & pos' & Hin0 & Hle0 & Hhi0)].
  - replace a with (b0 + (a - b0)) by lia.
    apply (HB10 b0 n0 (a - b0)); [exact Hin0 | exact (HCb b0 n0 Hin0) | lia | replace (b0 + (a - b0)) with a by lia; exact HnFP].
  - apply (HF12 cid pos' a Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP]. }
assert (KT : forall a, v <= a < v + 4 -> aview SEGS (w_H W2) memF a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite (KR2 a ltac:(lia) ltac:(lia)). apply KCAL. lia. }
assert (KN : forall a, v <= a < v + 56 -> ~ (v <= a < v + 4) -> ~ (v + 16 <= a < v + 24) ->
               aview SEGS (w_H W2) memF a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. rewrite (KR2 a ltac:(lia) H2), (KCAL a Ha). exact (KR1 a ltac:(lia) H1). }
(* the return value is a word *)
assert (Hres : 0 <= res < 2 ^ 64).
{ unfold vrs_arms in HARM. destruct (PjGrammar.scan y) as [Q|]; [|destruct HARM as (-> & _); lia].
  destruct HARM as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & H4 & _ & s & r & _ & _ & Eab & _)]]];
    try lia.
  assert (Hinb : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S2))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hinb) as (_ & _ & Hbc & _).
  assert (Hn1 : 0 <= Z.of_nat Q + 1 + cf_head) by lia. pose proof (req_size_pos _ Hn1). lia. }
(* the caller's words at and above the frame keep their dispatch values *)
assert (KV : forall a n val, val_mem SEGS (rdW W mem) a n val -> spZ regs0 - 104 <= a -> a + Z.of_nat n <= spZ regs0 ->
               val_mem SEGS (rdW W2 memF) a n val).
{ intros a n val Hv Ha1 Ha2. apply (val_mem_kept SEGS (w_H W) (w_H W2) mem memF); [|exact Hv].
  intros kk Hk.
  assert (HnF : ~ inFP [(q, q + 8)] (a + kk))
    by (intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []]; cbn [fst snd] in Hr; lia).
  rewrite (KR2 (a + kk) ltac:(lia) ltac:(lia)), (HWIN2 (a + kk) ltac:(lia) HnF).
  exact (KR1 (a + kk) ltac:(lia) ltac:(lia)). }
(* the frame's flag word *)
assert (Hin0 : In (0, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 0 pos HARd Hin0) as (Hf4 & Hfc & _).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md 0 pos HARd Hin0) as (Hf32 & _).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Hfb in Hfc.
assert (Hnf : v + 56 <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= v)
  by (eapply vrd_node_frame_disj; [exact Hframe | lia | exact Hvra]).
exists regsF, memF, mdF, ly2, S2, Hp2, kF.
split; [reflexivity|].
split; [exists WS; split; [exact HJF | exact HWB]|].
split.
{ intros a Ha Hn.
  assert (HnF : ~ inFP [(q, q + 8)] a).
  { intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | []]. apply Hn.
    exists (q, q + 8). split; [left; reflexivity | exact Hr]. }
  rewrite (KR2 a ltac:(lia) ltac:(lia)), (HWIN2 a ltac:(lia) HnF), (KR1 a ltac:(lia) ltac:(lia)).
  exact (Hwin a Ha Hn). }
split; [exact HR8|].
split; [rewrite HR18, Hfa2; reflexivity|].
split; [rewrite HR26, Hfa2; reflexivity|].
split; [rewrite HR24, Hfa2; reflexivity|].
split; [rewrite HR21; exact (vrs_snez res Hres)|].
split; [exact HR3|]. split; [exact HR4|]. split; [exact Hra|].
split.
{ unfold vrd_saved in Hsaved |- *.
  destruct Hsaved as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  repeat split; (eapply KV; [eassumption | lia | lia]). }
split.
{ rewrite Hfa2, Hfl2. destruct Hframe as (_ & _ & HFL & _).
  apply (val_mem_kept SEGS (w_H W) (w_H W2) mem memF); [|exact HFL].
  intros kk Hk.
  assert (HnF : ~ inFP [(q, q + 8)] (frame_addr ly 0 pos + 56 + kk))
    by (intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []]; cbn [fst snd] in Hr; lia).
  rewrite (KR2 (frame_addr ly 0 pos + 56 + kk) ltac:(lia) ltac:(lia)).
  rewrite (HF12 0 pos (frame_addr ly 0 pos + 56 + kk) Hin0
    ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; lia) HnF).
  exact (KR1 (frame_addr ly 0 pos + 56 + kk) ltac:(lia) ltac:(lia)). }
split; [exact HFZ|].
split; [intros rr; reflexivity|].
apply (vrs_rq ly0 S0 e q v text len p tb Lam peak cnt fail ran most own pos y p'
  ly S Hp W mem W memc ly2 S2 Hp2 W2 mem2 md2 memF res Hcfw HPSTi HdM Hskip Hsucc Htp Hpp Hp'lt Hlen
  Hfrs Hab Hsetfs ltac:(lia) ltac:(lia) HCNT Hplace HHEAD Hvnimg Hv8 ltac:(lia) ltac:(lia) Hqv Htv ltac:(lia) ltac:(lia)
  HAR2 Hfa2 Hfrs3 HRL2 HHU2 HBB2 Hmax HARM Hvzero KN HTY KT HstrF HrwF KR2 KR2r).
Qed.

End join.
