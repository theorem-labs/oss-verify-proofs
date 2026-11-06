(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment SM of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B): the call of send_message (jal at 0x8675c, back at 0x86760) through PaFx.v's cl_callS_wideF and srr_after_callF (send_message returns at an FP state fx1 of its own, apost_baseF), in three steps: the call's premises and send_message's from the facts at the call (lt_sm_pre), the caller's facts at the return from send_message's post into the continuation LT_W_stmt at fx1 (lt_sm_post), and the call (lt_call_SM); the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s30.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YP03 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib
  CmdBase CmdRep CmdObj CmdRo CmdGlob PaCall PaNoChain PaFx HarnessArgs HarnessPropsA CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c sup_reply_code_c joined_c
  LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import LLVMFuzzerTestOneInput_defs
  LLVMFuzzerTestOneInput_s01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---- lists ---- *)
Lemma sm_NoDup_app_disj_loc : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 x H Hin Hx; [destruct Hin|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hn Hd]. destruct Hin as [<- | Hin].
- apply Hn, in_or_app. right. exact Hx.
- exact (IH l2 x Hd Hin Hx).
Qed.
Lemma sm_nth_firstn_loc : forall {A} (l : list A) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
intros A l. induction l as [|a l IH]; intros L i d Hi; destruct L as [|L]; try lia; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma sm_nth_skipn_loc : forall {A} (l : list A) o i d, nth i (skipn o l) d = nth (o + i) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l i d; [reflexivity|].
destruct l as [|a l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
(* the bytes [o, o + L) of a byte list shown at p *)
Lemma sm_sub_bytes_loc : forall (rd : reader) (p : Z) (pl : list byte) (o L : nat),
  (o + L <= length pl)%nat ->
  (forall j, (j < length pl)%nat -> rd (p + Z.of_nat j) = Some (bv_unsigned (nth j pl (Z_to_bv 8 0)))) ->
  abytes_atR rd (p + Z.of_nat o) (firstn L (skipn o pl)).
Proof.
intros rd p pl o L Hl Hb i Hi.
rewrite length_firstn, length_skipn in Hi.
rewrite sm_nth_firstn_loc by lia. rewrite sm_nth_skipn_loc.
replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia.
apply Hb. lia.
Qed.
Lemma sm_preserved_reg_loc : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

(* ---- the recorder after one message (send_message's post): the spill is the cleared recorder's, at most 2 calls
   (lib/B/Prog/HarnessPropsA.v run_frame_at, HarnessArgs.v run_args) ---- *)
Lemma sm_run_spill_loc : forall R0 D, r_spill (fst (fst (vr_runA (RecModel.rec_clear R0) D))) = r_spill R0.
Proof.
intros R0 D. unfold vr_runA. change reply_code_a with (rcode_at atoi_a).
rewrite vr_run_out_at.
pose proof (run_frame_at atoi_a R0 (fst (Verbs.receive atoi_a D)) (snd (Verbs.receive atoi_a D))) as F.
destruct (run_out_at atoi_a R0 (fst (Verbs.receive atoi_a D)) (snd (Verbs.receive atoi_a D))) as [[R1 x] q].
exact (proj2 (proj2 F)).
Qed.
Lemma sm_run_calls_loc : forall R0 D, (length (r_calls (fst (fst (vr_runA (RecModel.rec_clear R0) D)))) <= 2)%nat.
Proof.
intros R0 D. pose proof (run_args atoi_a reply_code_a R0 D) as A. unfold vr_runA.
destruct (VerbsRun.run_receive atoi_a reply_code_a (RecModel.rec_clear R0) D) as [[R1 x] q]. exact (proj1 A).
Qed.
(* the code a header selects is one of the table's (SlotSpec.v msg_cd), so declared *)
Lemma sm_msg_cd_declared_loc : forall hdr, declared (SlotSpec.msg_cd hdr) = true.
Proof.
intros hdr. unfold SlotSpec.msg_cd.
assert (Hk : (Z.to_nat ((SlotSpec.hbyte hdr 0 / 2) mod 58) < length rec_codes)%nat).
{ rewrite rec_codes_length. pose proof (Z.mod_pos_bound (SlotSpec.hbyte hdr 0 / 2) 58 ltac:(lia)) as Hm. lia. }
unfold declared. apply existsb_exists. exists (nth (Z.to_nat ((SlotSpec.hbyte hdr 0 / 2) mod 58)) rec_codes 0).
split; [apply nth_In; exact Hk | apply Z.eqb_refl].
Qed.

(* ---- the meter's charges are not negative (ameter_laws) ---- *)
Section x.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Lemma sm_XM_RC_nonneg_loc : forall R, 0 <= XM_REC_CLEAR MT R.
Proof.
intros R. unfold XM_REC_CLEAR. pose proof (ev_args_nonneg R). pose proof (mo_free_nonneg MT MTL).
apply Z.mul_nonneg_nonneg; lia.
Qed.
Lemma sm_XM_SM_nonneg_loc : forall R D, 0 <= XM_SEND_MESSAGE MT R D.
Proof.
intros R D. unfold XM_SEND_MESSAGE, XM_VERBS_RECEIVE, VERBS_RECEIVE_REQ.
pose proof (mo_malloc_nonneg MT MTL 8192 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 8194 ltac:(lia)).
pose proof (mo_free_nonneg MT MTL). pose proof (sm_XM_RC_nonneg_loc R). pose proof (ev_vr_ge0 R D).
assert (0 <= ev_vr (RecModel.rec_clear R) D * (mo_malloc MT 8194 + mo_free MT)) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
(* the budget arithmetic of the call: the events and the meter it spends, out of the rest of the walk's *)
Lemma sm_bud_arith_loc : forall (k acc EVSM REST XSM U XL EL nev0 nev EVMAX : Z),
  0 <= k -> k + (EVSM + REST) <= EL -> 0 <= acc -> acc + (EVSM + REST) * U <= XL ->
  0 <= EVSM -> 0 <= REST -> 0 <= U -> 0 <= XSM -> XSM <= EVSM * U ->
  nev <= nev0 + k -> nev0 + EL <= EVMAX ->
  nev + EVSM <= EVMAX /\ acc + XSM <= XL /\
  0 <= k + EVSM /\ k + EVSM + REST <= EL /\ 0 <= acc + XSM /\ acc + XSM + REST * U <= XL.
Proof.
intros k acc EVSM REST XSM U XL EL nev0 nev EVMAX H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
assert (0 <= REST * U) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End x.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the message of pass r, as LT_SM_stmt names it: the recorder R0 (rec_set_rc of the head's Rh), the bytes D, the
   recorder R1 after the daemon's run (send_message's post), the first byte, the length, the words, the rest *)
#[local] Notation SM_R0 cx r Rh := (lt_R0 (x_pl cx) (x_n cx) r Rh).
#[local] Notation SM_D cx r := (lt_D (x_pl cx) (x_n cx) r).
#[local] Notation SM_R1 cx r Rh :=
  (fst (fst (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r)))).
#[local] Notation SM_SRC cx r := (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r).
#[local] Notation SM_LEN cx r := (lt_len (x_pl cx) (x_n cx) r).
#[local] Notation SM_WS cx r := (lt_ws (x_pl cx) (x_n cx) r).
#[local] Notation SM_REST cx r := (x_rest cx (lt_r' (x_pl cx) (x_n cx) r)).
(* the callee's statement, never restated, in the statement's form at every FP state (LLVMFuzzerTestOneInput_c.v
   HSEND_MESSAGE) *)
Hypothesis HSEND_MESSAGE : forall fx0 : YK11.FPState, @tsend_message_spec fx0 rc SK PI B MT.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the image facts (lib/B/Prog/CmdRecFacts.v): the program's statics are unowned image bytes (CmdRecImg.v
   cmd_prog_unowned), the read-only bytes kept along the journal (_s01.v lt_arodata_kept, lt_ro_kept) *)
Hypothesis IMG : cmd_img_facts SEGS B.

(* the saved registers and the ten words below the struct are kept when the frame's bytes are *)
Lemma sm_saved_kept_loc : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' Hk HS i r Hi.
assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
change (length LT_SAVED) with 13%nat in Hi13.
rewrite (rdword_ext rd rd'); [exact (HS i r Hi)|].
intros j Hj. apply Hk. lia.
Qed.
Lemma sm_slots_kept_loc : forall cx (rd rd' : reader),
  (forall a, x_sp1 cx <= a < x_sp1 cx + 112 -> rd' a = rd a) -> lt_slots cx rd -> lt_slots cx rd'.
Proof.
intros cx rd rd' Hk HS o v Hin.
assert (HF : forallb (fun ov => (0 <=? fst ov) && (fst ov <=? 104)) LT_SLOTS = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HF (o, v) Hin) as Ho. cbn [fst] in Ho.
apply andb_prop in Ho as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
rewrite (rdword_ext rd rd'); [exact (HS o v Hin)|].
intros j Hj. apply Hk. lia.
Qed.

(* send_message's footprint (the recorder's blocks O and the program's statics) lies below alloc_ceiling *)
Lemma sm_FP1_low_loc : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  forall a, inFP (ablocks_fp O ++ cmd_PG) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a Hf. pose proof asan_consts as (C1 & _).
apply inFP_app in Hf as [Hf | Hf].
- destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Ha).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hin)) as (_ & _ & Hc & _). lia.
- destruct Hf as (rr & Hrr & Hlo & Hhi). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hrr. cbn [In] in Hrr.
  destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; lia.
Qed.
(* the events and the meter of the call: send_message's share of the pass's budget, and the budget LT_W_stmt asks
   after it, from send_message's mo_le *)
Lemma sm_bud_loc : forall m cx ly S (W : world SEGS) regs mem md k acc (r : Z) (Rh : rstate),
  lt_base B MT cx -> lt_body B cx ly S W regs mem md k m ->
  lt_bud MT cx S k acc (lt_cost (SM_R0 cx r Rh) (SM_D cx r) (SM_R1 cx r Rh) (SM_WS cx r) +
    ev_from (31 - m) (SM_R1 cx r Rh) (SM_REST cx r)) ->
  st_nev S + EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r) <= EV_MAX /\
  mo_ok MT S (XM_SEND_MESSAGE MT (SM_R0 cx r Rh) (SM_D cx r)) /\
  forall S2, mo_le MT S S2 (XM_SEND_MESSAGE MT (SM_R0 cx r Rh) (SM_D cx r)) ->
  lt_bud MT cx S2 (k + EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r))
    (acc + XM_SEND_MESSAGE MT (SM_R0 cx r Rh) (SM_D cx r))
    ((3 + 3) + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
     EV_CHECK_ROUND_TRIP (SM_R1 cx r Rh) (SM_WS cx r) + ev_from (31 - m) (SM_R1 cx r Rh) (SM_REST cx r)).
Proof.
intros m cx ly S W regs mem md k acc r Rh HBs HBODY HBud.
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _ & Hmo0).
pose proof HBODY as ((HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
assert (HremEq : lt_cost (SM_R0 cx r Rh) (SM_D cx r) (SM_R1 cx r Rh) (SM_WS cx r) +
    ev_from (31 - m) (SM_R1 cx r Rh) (SM_REST cx r) =
  EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r) +
  ((3 + 3) + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
    EV_CHECK_ROUND_TRIP (SM_R1 cx r Rh) (SM_WS cx r) + ev_from (31 - m) (SM_R1 cx r Rh) (SM_REST cx r)))
  by (unfold lt_cost; ring).
rewrite HremEq in HBud.
destruct HBud as (Hb1 & _ & Hb3 & Hb4 & Hb5 & Hb6).
pose proof (EV_SEND_MESSAGE_ge0 (SM_R0 cx r Rh) (SM_D cx r)) as E1.
pose proof (EV_CHECK_ROUND_TRIP_ge0 (SM_R1 cx r Rh) (SM_WS cx r)) as E2.
pose proof (ev_from_nonneg (31 - m) (SM_R1 cx r Rh) (SM_REST cx r)) as E3.
assert (HR0 : 0 <= (3 + 3) + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
    EV_CHECK_ROUND_TRIP (SM_R1 cx r Rh) (SM_WS cx r) + ev_from (31 - m) (SM_R1 cx r Rh) (SM_REST cx r))
  by (unfold EV_CHECK_REPLY, EV_CHECK_ARITY, EV_CHECK_WORDS, EV_JOINED, EV_CHECK_REFUSAL, EV_SUP_REPLY_CODE; lia).
pose proof (LT_U_nonneg MT MTL) as HU.
pose proof (sm_XM_SM_nonneg_loc MT MTL (SM_R0 cx r Rh) (SM_D cx r)) as X1.
pose proof (xm_send_message_le MT MTL (SM_R0 cx r Rh) (SM_D cx r)) as X2.
destruct (sm_bud_arith_loc k acc _ _ _ (LT_U MT) (XM_LTOI MT (x_pl cx)) (EV_LTOI (x_pl cx)) (st_nev (x_S cx)) (st_nev S)
  EV_MAX Hb1 Hb3 Hb5 Hb6 E1 HR0 HU X1 X2 Hnev Hev0) as (HEV & HXM & BA3 & BA4 & BA5 & BA6).
split; [exact HEV|].
split; [exact (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc _ MTL Hmo0 Hb4 X1 HXM)|].
intros S2 HML. unfold lt_bud.
split; [exact BA3|]. split; [exact HR0|]. split; [exact BA4|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hb4 HML)|].
split; [exact BA5 | exact BA6].
Qed.

(* ---- (a) 0x8675c, jal send_message: from the facts at send_message's entry (LT_SM_stmt's premises), the premises
   of the call rule (PaFx.v cl_callS_wideF, the same as PaNoChain.v cl_callS_wide's) with the frame chain at
   sp = entry sp - 256 by achain's empty case (s0 = -1, 0x865f0), and every premise of send_message's statement
   (send_message_c.v tsend_message_spec, in its order) but the rounding mode, with ch = [], src = the message's
   first byte, n = its length, D = its bytes, R = R0, O, rest = the entry's blocks ---- *)
Lemma lt_sm_pre : forall m cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O : list (Z * Z)) (q : Z),
  lt_base B MT cx -> lt_body B cx ly S W regs mem md k m ->
  lt_msg_regs cx regs (rdW W mem) r Rh ->
  getr regs 1 = w64 (BASE + LO_SMRA) ->
  getr regs 10 = w64 (SM_SRC cx r) -> getr regs 11 = w64 (SM_LEN cx r) ->
  lt_rec B cx ly S W mem (SM_R0 cx r Rh) O q [] ->
  lt_bud MT cx S k acc (lt_cost (SM_R0 cx r Rh) (SM_D cx r) (SM_R1 cx r Rh) (SM_WS cx r) +
    ev_from (31 - m) (SM_R1 cx r Rh) (SM_REST cx r)) ->
  (* the call rule's premises *)
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k /\
  spZ regs = x_sp0 cx + -256 /\ 0 <= SEND_MESSAGE_STK /\ SEND_MESSAGE_STK - -256 <= LTOI_STK /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= bv_unsigned (getr regs 1) /\
  achain ly (rdW W mem) (x_sp0 cx + -256) (s0Z regs) [] /\
  (forall a, inFP (ablocks_fp O ++ cmd_PG) a ->
     awr_byte SEGS B LTOI_STK (x_sp0 cx) cmd_PG (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [] a) /\
  (forall (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
     ly2 S2 (W2 : world SEGS) regs2 mem2 md2, K ly2 S2 W2 regs2 mem2 md2 ->
     forall a, inFP (ablocks_fp O ++ cmd_PG) a -> x_sp0 cx - LTOI_STK <= a < x_sp0 cx ->
     ~ (x_sp0 cx + -256 - SEND_MESSAGE_STK <= a < x_sp0 cx + -256) -> rdW W2 mem2 a <> None) /\
  (* send_message's premises *)
  afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md [] /\
  Z.of_nat (length (frames S)) <= 3 /\
  arodata_okP SEGS RLO RHI B (rdW W mem) /\ cmd_ro_ok (rdW W mem) /\ cmd_val_objs /\
  getr regs 10 = w64 (SM_SRC cx r) /\ 0 <= SM_SRC cx r < 2 ^ 64 /\
  getr regs 11 = w64 (SM_LEN cx r) /\ 0 <= SM_LEN cx r <= 8192 /\
  Z.of_nat (length (SM_D cx r)) = SM_LEN cx r /\ abytes_atR (rdW W mem) (SM_SRC cx r) (SM_D cx r) /\
  (SM_LEN cx r <> 0 -> in_blockA (x_bl0 B cx ++ []) (SM_SRC cx r) (SM_LEN cx r)) /\
  Permutation (ablocks B ly S) (O ++ x_bl0 B cx ++ []) /\
  rec_repA B ly S (rdW W mem) (SM_R0 cx r Rh) O /\ (length (r_calls (SM_R0 cx r Rh)) <= 2)%nat /\
  (r_refuse (SM_R0 cx r Rh) <> 0 -> declared (r_code (SM_R0 cx r Rh)) = true) /\
  st_nev S + EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r) <= EV_MAX /\
  blocks_bytes S + LIVE_SEND_MESSAGE <= LIVE_MAX /\
  mo_ok MT S (XM_SEND_MESSAGE MT (SM_R0 cx r Rh) (SM_D cx r)).
Proof.
intros m cx ly S W regs mem md k acc r Rh O q HBs HBODY HMR Hra H10 H11 HR HBud.
pose proof HBs as (HPRE0 & _ & _ & HOBJ & _ & _ & _ & HNL & HGA & HFR0 & _ & _ & Hlive0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal0 & HS00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof HBODY as (HF & Hsl & R8 & R9 & R18 & R25 & R26 & R27 & Hm).
pose proof HF as (HJ & Hsp & Hgp & Htp & Hsv).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HMR as (Hr & R19 & R20 & R21 & R22 & Hstate & Hhost & Hhb).
pose proof HR as (Hrep & Hspill & H2 & Hq & Hq0 & Hperm).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HLS : LTOI_STK = 32768) by reflexivity.
assert (HS1 : 0 <= SEND_MESSAGE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HS2 : SEND_MESSAGE_STK - -256 <= LTOI_STK) by (apply Z.leb_le; vm_compute; reflexivity).
unfold x_sp1, LT_FRAME in Hsp.
assert (Hsp' : spZ regs = x_sp0 cx + -256) by (unfold x_sp0; lia).
(* the payload's block (lt_payload_live), the recorder's blocks and the payload's among the live ones *)
destruct (lt_payload_live B MT cx r HBs Hr) as (Hn26 & Hpin).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn. }
assert (Hpin' : In (x_p cx, x_n cx) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. exact Hpin. }
pose proof (lt_ablocks_NoDup B LAWS ly S W mem md HAR) as HND.
pose proof (Permutation_NoDup Hperm HND) as HND2.
pose proof (sm_FP1_low_loc ly S W mem md O HAR HO) as HFlo.
destruct (al_blocks _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) (x_p cx) (x_n cx) HAR0 Hpin)
  as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
(* the message: hdr_n r header bytes, then lt_len bytes, inside the r bytes left *)
pose proof (lt_len_range (x_pl cx) (x_n cx) r ltac:(lia)) as HL.
assert (Hhd : 0 < SlotSpec.hdr_n r <= r) by (unfold SlotSpec.hdr_n; lia).
assert (HPB : forall j, (j < length (x_pl cx))%nat ->
  rdW W mem (x_p cx + Z.of_nat j) = Some (bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0)))).
{ intros j Hj.
  rewrite (lt_payload_kept B MT cx ly S W mem md [] k HBs HJ (fun _ => Hpin') (Z.of_nat j) ltac:(lia)).
  unfold aview. rewrite (garr8_mbyte SEGS _ _ _ j HGA ltac:(rewrite length_map; exact Hj)).
  assert (Enth : nth j (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 = bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0))).
  { rewrite (nth_indep (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 (bv_unsigned (Z_to_bv 8 0)))
      by (rewrite length_map; exact Hj).
    exact (map_nth (fun b : byte => bv_unsigned b) (x_pl cx) (Z_to_bv 8 0) j). }
  rewrite Enth, Z_to_bv_bv_unsigned. reflexivity. }
assert (HDL : Z.of_nat (length (SM_D cx r)) = SM_LEN cx r).
{ unfold lt_D, lt_rest. rewrite length_firstn, !length_skipn. lia. }
assert (HDB : abytes_atR (rdW W mem) (SM_SRC cx r) (SM_D cx r)).
{ unfold lt_D, lt_rest. rewrite skipn_skipn.
  replace (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r)
    with (x_p cx + Z.of_nat (Z.to_nat (SlotSpec.hdr_n r) + Z.to_nat (x_n cx - r))) by lia.
  apply sm_sub_bytes_loc; [lia | exact HPB]. }
assert (Hsrc : 0 <= SM_SRC cx r < 2 ^ 64) by lia.
assert (Hn8 : 0 <= SM_LEN cx r <= 8192).
{ split; [lia|]. unfold lt_len, SlotSpec.msg_len. apply Z.le_min_r. }
assert (HIB : SM_LEN cx r <> 0 -> in_blockA (x_bl0 B cx ++ []) (SM_SRC cx r) (SM_LEN cx r)).
{ intros _. exists (x_p cx), (x_n cx). split; [apply in_or_app; left; exact Hpin | lia]. }
assert (Hdecl : r_refuse (SM_R0 cx r Rh) <> 0 -> declared (r_code (SM_R0 cx r Rh)) = true).
{ intros _. unfold lt_R0, rec_set_rc. cbn [r_code]. apply sm_msg_cd_declared_loc. }
(* the events, the meter and the live bytes the call may spend *)
destruct (sm_bud_loc m cx ly S W regs mem md k acc r Rh HBs HBODY HBud) as (HEV & HMO & _).
assert (HLIVE : blocks_bytes S + LIVE_SEND_MESSAGE <= LIVE_MAX).
{ pose proof (lt_rec_live B LAWS cx ly S W mem md _ O q [] HAR HR) as HLv. cbn [bsum] in HLv.
  pose proof (Z.le_max_l LIVE_SEND_MESSAGE (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP)) as Hmx.
  unfold LIVE_LTOI in Hlive0. unfold LT_RECB in HLv. lia. }
assert (HFR : Z.of_nat (length (frames S)) <= 3) by (rewrite Hfrs, HFR0; cbn; lia).
pose proof (lt_arodata_kept B MT LAWS HB IMG cx ly S W mem md [] k HBs HJ) as HRO.
pose proof (lt_ro_kept B MT LAWS HB IMG cx ly S W mem md [] k HBs HJ) as HROK.
(* the call's own premises *)
assert (Hraw : YK0s.ret_ok (getr regs 1)).
{ rewrite Hra. unfold w64. apply ret_ok_codeptr_v; [unfold LO_SMRA; lia | reflexivity]. }
assert (Hra4 : 4096 <= bv_unsigned (getr regs 1)).
{ rewrite Hra. unfold w64, LO_SMRA. rewrite unsigned_lit_small; lia. }
assert (Hch : achain ly (rdW W mem) (x_sp0 cx + -256) (s0Z regs) []).
{ assert (E1 : s0Z regs = 2 ^ 64 - 1) by (unfold s0Z; rewrite R8; vm_compute; reflexivity).
  left. split; [right; left; lia | reflexivity]. }
assert (Hgp' : getr regs 3 = w64 (as_gp B)) by (rewrite Hgp; exact Hgp0).
assert (Htp' : getr regs 4 = w64 (as_tp B)) by (rewrite Htp; exact Htp0).
assert (HPRE1 : afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md []).
{ apply (afn_pre_at SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k
    regs SEND_MESSAGE_STK (-256) [] HJ Hsp' eq_refl ltac:(lia) HS1 HS2 Hraw Hra4 Hgp' Htp').
  rewrite Hsp'. exact Hch. }
split; [exact HJ|]. split; [exact Hsp'|]. split; [exact HS1|]. split; [exact HS2|].
split; [exact Hgp'|]. split; [exact Htp'|]. split; [exact Hraw|]. split; [exact Hra4|]. split; [exact Hch|].
split.
{ intros a Hf. apply inFP_app in Hf as [Hf | Hf].
  - right; right; left. destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Ha).
    exists p, n. split; [exact (HO _ Hin)|]. split; [|exact Ha].
    intros Hx. exact (sm_NoDup_app_disj_loc O (x_bl0 B cx ++ []) (p, n) HND2 Hin (in_or_app _ _ _ (or_introl Hx))).
  - right; right; right; right; left. split; [exact Hf|]. exact (rca_prog B HB IMG a Hf). }
split.
{ intros K ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFlo a Ha) as Hlo.
  rewrite HLS in Hw, Hslo0. unfold x_sp0 in Hw. lia. }
split; [exact HPRE1|]. split; [exact HFR|]. split; [exact HRO|]. split; [exact HROK|]. split; [exact HOBJ|].
split; [exact H10|]. split; [exact Hsrc|]. split; [exact H11|]. split; [exact Hn8|].
split; [exact HDL|]. split; [exact HDB|]. split; [exact HIB|]. split; [exact Hperm|].
split; [exact Hrep|]. split; [exact H2|]. split; [exact Hdecl|].
split; [exact HEV|]. split; [exact HLIVE | exact HMO].
Qed.

(* ---- (b) 0x86760, back from send_message: the return as the call rule leaves it (the journal from the entry,
   composed; send_message's own journal from sp = entry sp - 256 with footprint O ++ cmd_PG; the callee-saved
   registers; send_message's post Q with R = R0, rest = the entry's blocks), at the FP state fx1 the call returns
   with rounding mode 0 there (PaFx.v fxrel_frm0), into the continuation LT_W_stmt at fx1: the caller's frame,
   the ten words, s0, s1, s2, s9, s10, s11, the message's registers and the host word are kept, the recorder is
   send_message's, the budget is the rest of the pass's ---- *)
Lemma lt_sm_post : forall m (fx1 : YK11.FPState) cx ly S W regs mem md k acc (r : Z) (Rh : rstate)
  (O : list (Z * Z)) (q : Z) ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
  lt_base B MT cx -> lt_body B cx ly S W regs mem md k m ->
  lt_msg_regs cx regs (rdW W mem) r Rh ->
  lt_rec B cx ly S W mem (SM_R0 cx r Rh) O q [] ->
  lt_bud MT cx S k acc (lt_cost (SM_R0 cx r Rh) (SM_D cx r) (SM_R1 cx r Rh) (SM_WS cx r) +
    ev_from (31 - m) (SM_R1 cx r Rh) (SM_REST cx r)) ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly2 S2 W2 mem2 md2
    (k + EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r)) ->
  ajournal SEGS B SEND_MESSAGE_STK (x_sp0 cx + -256) (ablocks_fp O ++ cmd_PG) ly S W mem md [] ly2 S2 W2 mem2 md2
    (EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r)) ->
  aregs_preserved regs regs2 ->
  (let '(R', _, quit) := vr_runA (RecModel.rec_clear (SM_R0 cx r Rh)) (SM_D cx r) in
   exists O',
   rec_repA B ly2 S2 (rdW W2 mem2) R' O' /\
   aval_mem (rdW W2 mem2) A_G_QUITTING 4 (if quit then 1 else 0) /\
   Permutation (ablocks B ly2 S2) (O' ++ x_bl0 B cx ++ []) /\
   blocks_bytes S2 <= blocks_bytes S + LIVE_SEND_MESSAGE /\
   mo_le MT S S2 (XM_SEND_MESSAGE MT (SM_R0 cx r Rh) (SM_D cx r))) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0 ->
  LT_W_stmt (fx := fx1) B MT m ->
  SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + LO_SMRA)) mem2 (seg_rom SEGS)) md2)
    (lt_post (fx := fx1) B MT cx).
Proof.
intros m fx1 cx ly S W regs mem md k acc r Rh O q ly2 S2 W2 regs2 mem2 md2 HBs HBODY HMR HR HBud HJ2 HJc HP HK
  Hfrm1 HW.
pose proof HBs as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal0 & HS00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof HBODY as (HF & Hsl & R8 & R9 & R18 & R25 & R26 & R27 & Hm).
pose proof HF as (HJ & Hsp & Hgp & Htp & Hsv).
pose proof HJ as (HAR & _).
pose proof HMR as (Hr & R19 & R20 & R21 & R22 & Hstate & Hhost & Hhb).
pose proof HR as (Hrep & Hspill & H2 & Hq & Hq0 & Hperm).
pose proof asan_consts as (C1 & _).
assert (HLS : LTOI_STK = 32768) by reflexivity.
unfold x_sp1, LT_FRAME in Hsp.
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn. }
pose proof (sm_FP1_low_loc ly S W mem md O HAR HO) as HFlo.
destruct (sm_bud_loc m cx ly S W regs mem md k acc r Rh HBs HBODY HBud) as (_ & _ & HBUD2).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JF1 & _).
(* the caller's frame [sp, entry sp) is kept: it is above the callee's window and outside its footprint *)
assert (KEEP : forall a, spZ (x_regs cx) - 256 <= a < spZ (x_regs cx) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. rewrite HLS in Hslo0. apply JF1; [lia | unfold x_sp0; lia |].
  intros Hf. pose proof (HFlo a Hf). lia. }
assert (PR : forall (rr : bv 5) z, acallee_saved z -> Z_to_bv 5 z = rr -> getr regs2 rr = getr regs rr).
{ intros rr z Hz <-. exact (HP z Hz). }
assert (Q2 : getr regs2 2 = getr regs 2) by (apply (PR _ 2); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q3 : getr regs2 3 = getr regs 3) by (apply (PR _ 3); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q4 : getr regs2 4 = getr regs 4) by (apply (PR _ 4); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q8 : getr regs2 8 = getr regs 8) by (apply (PR _ 8); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q9 : getr regs2 9 = getr regs 9) by (apply (PR _ 9); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q18 : getr regs2 18 = getr regs 18) by (apply (PR _ 18); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q19 : getr regs2 19 = getr regs 19) by (apply (PR _ 19); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q20 : getr regs2 20 = getr regs 20) by (apply (PR _ 20); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q21 : getr regs2 21 = getr regs 21) by (apply (PR _ 21); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q22 : getr regs2 22 = getr regs 22) by (apply (PR _ 22); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q25 : getr regs2 25 = getr regs 25) by (apply (PR _ 25); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q26 : getr regs2 26 = getr regs 26) by (apply (PR _ 26); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (Q27 : getr regs2 27 = getr regs 27) by (apply (PR _ 27); [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
assert (HF2 : lt_frame B cx ly2 S2 W2 regs2 mem2 md2 (k + EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r))).
{ split; [exact HJ2|].
  split; [unfold spZ; rewrite Q2; unfold x_sp1, LT_FRAME; exact Hsp|].
  split; [rewrite Q3; exact Hgp|]. split; [rewrite Q4; exact Htp|].
  apply (sm_saved_kept_loc cx (rdW W mem) (rdW W2 mem2)); [|exact Hsv].
  intros a Ha. unfold x_sp0 in Ha. apply KEEP. lia. }
assert (HBODY2 : lt_body B cx ly2 S2 W2 regs2 mem2 md2 (k + EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r)) m).
{ split; [exact HF2|].
  split; [apply (sm_slots_kept_loc cx (rdW W mem) (rdW W2 mem2)); [|exact Hsl];
    intros a Ha; unfold x_sp1, LT_FRAME in Ha; apply KEEP; lia|].
  split; [rewrite Q8; exact R8|]. split; [rewrite Q9; exact R9|]. split; [rewrite Q18; exact R18|].
  split; [rewrite Q25; exact R25|]. split; [rewrite Q26; exact R26|]. split; [rewrite Q27; exact R27|].
  exact Hm. }
assert (HMR2 : lt_msg_regs cx regs2 (rdW W2 mem2) r Rh).
{ split; [exact Hr|].
  split; [rewrite Q19; exact R19|]. split; [rewrite Q20; exact R20|]. split; [rewrite Q21; exact R21|].
  split; [rewrite Q22; exact R22|]. split; [exact Hstate|]. split; [exact Hhost|].
  rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact Hhb|].
  intros j Hj. apply KEEP. unfold x_sp1, LT_FRAME, LT_HOSTB. lia. }
pose proof (sm_run_spill_loc (SM_R0 cx r Rh) (SM_D cx r)) as Hsp1.
pose proof (sm_run_calls_loc (SM_R0 cx r Rh) (SM_D cx r)) as Hc1.
(* name the run's result by its projections *)
assert (EVR : vr_runA (RecModel.rec_clear (SM_R0 cx r Rh)) (SM_D cx r) =
  (SM_R1 cx r Rh, snd (fst (vr_runA (RecModel.rec_clear (SM_R0 cx r Rh)) (SM_D cx r))),
   snd (vr_runA (RecModel.rec_clear (SM_R0 cx r Rh)) (SM_D cx r)))).
{ destruct (vr_runA (RecModel.rec_clear (SM_R0 cx r Rh)) (SM_D cx r)) as [[a b] c]. reflexivity. }
rewrite EVR in HK. cbv beta iota in HK.
destruct HK as (O' & HR' & HQ' & HP' & _ & HML).
pose proof (HW cx ly2 S2 W2 regs2 mem2 md2 (k + EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r))
  (acc + XM_SEND_MESSAGE MT (SM_R0 cx r Rh) (SM_D cx r)) r Rh O' HBs Hfrm1 HBODY2 HMR2) as HW2.
cbv zeta in HW2. rewrite EVR in HW2. cbv beta iota in HW2.
apply HW2.
- split; [exact HR'|]. split; [rewrite Hsp1; exact Hspill|]. split; [exact Hc1|].
  split; [exact HQ'|].
  split; [destruct (snd (vr_runA (RecModel.rec_clear (SM_R0 cx r Rh)) (SM_D cx r))); lia|].
  exact HP'.
- exact (HBUD2 S2 HML).
Qed.

(* ---- 0x8675c, jal send_message, to 0x86760: (a), the callee's statement at the ambient fx under cl_callS_wideF
   (footprint the recorder's blocks O, made since the entry, and the program's statics cmd_PG), then (b) at the FP
   state fx1 send_message returns, through srr_after_callF: cgif A/ACh2.v:208-227 ---- *)
Lemma lt_call_SM : forall m, LTA_W B MT m -> LT_SM_stmt B MT m.
Proof.
intros m HW cx ly S W regs mem md k acc r Rh O q HBs HFRM HBODY HMR Hra H10 H11 HR. cbv zeta. intros HBud.
destruct (lt_sm_pre m cx ly S W regs mem md k acc r Rh O q HBs HBODY HMR Hra H10 H11 HR HBud)
  as (HJ & Hsp' & HS1 & HS2 & Hgp' & Htp' & Hraw & Hra4 & Hch & HFP & HVIS & _ & HFR & HRO & HROK & HOBJ &
      _ & Hsrc & _ & Hn8 & HDL & HDB & HIB & Hperm & Hrep & H2 & Hdecl & HEV & HLIVE & HMO).
pose proof (fun HPRE1 : afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md [] =>
  HSEND_MESSAGE fx ly S W regs mem md [] (SM_SRC cx r) (SM_LEN cx r) (SM_D cx r) (SM_R0 cx r Rh) O (x_bl0 B cx ++ [])
  HPRE1 HFRM HFR HRO HROK HOBJ H10 Hsrc H11 Hn8 HDL HDB HIB Hperm Hrep H2 Hdecl HEV HLIVE HMO) as HCALL.
lazymatch type of HCALL with _ -> SRr _ _ _ (apost_baseF _ _ _ _ _ _ _ _ _ _ _ ?Kq) => set (K := Kq) in HCALL end.
unfold lt_post.
eapply (srr_after_callF (fx := fx) SEGS).
{ apply (cl_callS_wideF (fx := fx) (L := cmd_listing) (PI := PI) B LAWS W regs mem (Z_to_bv 64 (BASE + AF_send_message))
    LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S md k SEND_MESSAGE_STK
    (ablocks_fp O ++ cmd_PG) (EV_SEND_MESSAGE (SM_R0 cx r Rh) (SM_D cx r))
    (-256) (getr regs 1) [] K HJ Hsp' eq_refl ltac:(lia) HS1 HS2 Hgp' Htp' eq_refl Hraw Hra4 Hch).
  - intros HPRE1. eapply SRr_mono; [exact (HCALL HPRE1) | intros W3 c3 _ H3; exact H3].
  - exact HFP.
  - exact (HVIS K). }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfx (HJ2 & HJc & HP & HK).
unfold K in HK. cbv beta in HK.
rewrite Hra. unfold w64.
exact (lt_sm_post m fx1 cx ly S W regs mem md k acc r Rh O q ly2 S2 W2 regs2 mem2 md2 HBs HBODY HMR HR HBud
  HJ2 HJc HP HK (fxrel_frm0 fx fx1 HFRM Hfx) (HW fx1)).
Qed.

End e.
End f.
End d.
