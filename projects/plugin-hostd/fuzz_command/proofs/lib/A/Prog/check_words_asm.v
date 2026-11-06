(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of answer (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   entry 0x8aa10, 209 instructions, 836 bytes): tanswer_spec of a Theorem Labs lane's lib/B/Prog/answer_c.v (a working branch
   f490061c104), assembled from four segments as the A walk lib/A/Prog/answer.v (a working branch d28426fbb96)
   does: the entry to BODY (answer_e.v), BODY to JOIN and HEAD (answer_br.v, with the snprintf step of answer_snp.v),
   syntax_instantiate's loop from HEAD to JOIN (answer_l.v), and JOIN to the return (answer_t.v); the cut statements
   are answer_s1.v's. B's code differs from A's in the loop (B's registers and its five UBSan trap sites) and in the
   snprintf contract (the shared one, RtPFCmd.asnprintf_sh); the post is apost_baseF: JOIN is used at the FP state the
   snprintf call returns on the refused arm and at the entry's FP state on the loop's exit.
   Report / trap / abort edges, each refuted at its branch (the segment files say where and from what):
   0x8abac (beqz s3, UBSan) in answer_bm.v; 0x8ac08, 0x8ac38, 0x8ac64, 0x8ac80 (UBSan), 0x8ac6c -> 0x8ad50
   (__asan_report_load1), 0x8ac78 -> 0x8ac7c and 0x8ad44 -> 0x8ad48 (__asan_report_store1), 0x8ac34 and 0x8aca0
   (abort) in answer_l.v. The entry's and the tail's branches (0x8aa7c, 0x8aa9c, 0x8acc8) are decided by the record's
   use-after-return cell and the frame address (answer_e.v, answer_t.v).
   Section hypotheses beyond the statement's: the allocator record HB, the meter's laws MTL and frame laws MTFL, the
   side-stack entries' record TLF (PaLibF), and, in the form a Theorem Labs lane states them only at the pinned image (PI := PB_cmd,
   tfibsegs), cmd_palib, cmd_sig_prog_PB, cmd_img_facts_tfib and cmd_frame_flag_law; PRW for the store into
   g_rec.state. AnswerClosed.v discharges all of them but HB, MTL and MTFL at the pinned image. Base: a Theorem Labs lane
   fc8bcbd8b42 (the snprintf contract's band premise `+ 8`, discharged in answer_snp.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/answer.v, with its module paths and module names changed; 110 of its 136 lines of code are new or changed and 56 lines of the source are left out. *)
(* check_words' ASan walk: the assembly of the segments. The two loops (calls c < ncalls <= 16, items a < nargs <= 6)
   are closed by induction on the remaining trip count, from the segment statements of check_words_d.v; the
   theorem tcheck_words_spec then follows from the entry statement. The segment lemmas themselves are proved in
   check_words_s*.v; check_words.v applies this file to them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the statements of the points at EVERY FP state (pass 4: after the snprintf call of the item dispatch and the call of
   check_words_chain the walk goes on at the FP state the call returns) *)
Definition G_J : Prop := forall fx0 : YK11.FPState, ST_J (fx := fx0) B MT.
Definition G_P1 : Prop := forall fx0 : YK11.FPState, ST_P1 (fx := fx0) B MT.
Definition G_LH (c : Z) : Prop := forall fx0 : YK11.FPState, ST_LH (fx := fx0) B MT c.
Definition G_IH (c a : Z) : Prop := forall fx0 : YK11.FPState, ST_IH (fx := fx0) B MT c a.
Definition G_IK (c a : Z) : Prop := forall fx0 : YK11.FPState, ST_IK (fx := fx0) B MT c a.
Definition G_ICMP (c a : Z) : Prop := forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a.
Definition G_ICMP2 (c a : Z) : Prop := forall fx0 : YK11.FPState, ST_ICMP2 (fx := fx0) B MT c a.
Definition G_IL (c a : Z) : Prop := forall fx0 : YK11.FPState, ST_IL (fx := fx0) B MT c a.
Definition G_D (c : Z) : Prop := forall fx0 : YK11.FPState, ST_D (fx := fx0) B MT c.
Definition G_REL : Prop := forall fx0 : YK11.FPState, ST_REL (fx := fx0) B MT.
Definition G_ENTRY : Prop := forall fx0 : YK11.FPState, ST_ENTRY (fx := fx0) B MT.

(* the recorder holds at most 16 calls, each with at most 6 arguments (rec_repA's ag1_calls / acall_at) *)
Lemma cw_ent_rec : forall {fx0 : YK11.FPState} e, cw_ent (fx := fx0) B MT e ->
  rec_repA B (e_ly e) (e_S e) (cw_rd0 e) (e_R e) (e_O e).
Proof.
intros fx0 e H. unfold cw_ent in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _). exact Hrec.
Qed.
Lemma cw_ent_ncalls : forall {fx0 : YK11.FPState} e, cw_ent (fx := fx0) B MT e -> cw_ncalls e <= 16.
Proof.
intros fx0 e H. pose proof (cw_ent_rec e H) as (Q & (_ & _ & _ & (Hl & _) & _) & _). unfold cw_ncalls. lia.
Qed.
Lemma cw_ent_nargs : forall {fx0 : YK11.FPState} e i fn args, cw_ent (fx := fx0) B MT e ->
  nth_error (r_calls (e_R e)) i = Some (fn, args) -> (length args <= 6)%nat.
Proof.
intros fx0 e i fn args H Hi. pose proof (cw_ent_rec e H) as (Q & (_ & _ & _ & (Hl & HlQ & _ & Hcalls & _) & _) & _).
destruct (nth_error (l_calls Q) i) as [P|] eqn:HP.
- destruct (Hcalls i (fn, args) P Hi HP) as ((_ & Ha & _) & _). exact Ha.
- exfalso. apply nth_error_None in HP. assert (Hlt : (i < length (r_calls (e_R e)))%nat)
  by (apply nth_error_Some; rewrite Hi; discriminate). lia.
Qed.

(* the item loop of call c: from the segment statements, every head of the loop *)
Lemma cw_item_loop : forall c,
  (forall c a, G_IK c a -> G_D c -> G_IH c a) ->
  (forall c a, G_IH c (a + 1) -> G_D c -> G_IL c a) ->
  (forall c a, G_ICMP c a -> G_ICMP2 c a -> G_IL c a -> G_IK c a) ->
  (forall c a, G_ICMP2 c a -> G_ICMP c a) ->
  (forall c a, G_IL c a -> G_ICMP2 c a) ->
  G_D c -> forall a, G_IH c a.
Proof.
intros c SI1h SI1l SI2 SI3a SI3b HD.
assert (STEP : forall a, G_IH c (a + 1) -> G_IH c a).
{ intros a HIH. apply (SI1h c a); [|exact HD].
  pose proof (SI1l c a HIH HD) as HIL. pose proof (SI3b c a HIL) as HC2. pose proof (SI3a c a HC2) as HC1.
  exact (SI2 c a HC1 HC2 HIL). }
assert (BIG : forall a, 6 <= a -> G_IH c a).
{ intros a Ha fx0. unfold ST_IH. intros e lyc Sc Wc regsc memc mdc pos sp1 line j Hent HI. exfalso.
  destruct HI as (fn & args & (_ & _ & _ & _ & _ & _ & Hnth & Ha') & _).
  pose proof (cw_ent_nargs e _ fn args Hent Hnth). lia. }
assert (IND : forall m : nat, forall a, 6 - a <= Z.of_nat m -> G_IH c a).
{ induction m as [|m IH]; intros a Ha.
  - apply BIG. lia.
  - destruct (Z_le_gt_dec 6 a) as [H6|H6]; [apply BIG; exact H6|].
    apply STEP. apply IH. lia. }
intros a. destruct (Z_le_gt_dec 6 a) as [H6|H6]; [apply BIG; exact H6|].
apply (IND (Z.to_nat (6 - a))). lia.
Qed.

(* the call loop: every head of it *)
Lemma cw_call_loop :
  (forall c, G_IH c 0 -> G_D c -> G_LH c) ->
  (forall c, G_LH (c + 1) -> G_REL -> G_D c) ->
  (forall c, G_D c -> G_IH c 0) ->
  G_REL -> forall c, G_LH c.
Proof.
intros SC SD SIH HR.
assert (BIG : forall c, 16 <= c -> G_LH c).
{ intros c Hc fx0. unfold ST_LH. intros e lyc Sc Wc regsc memc mdc pos sp1 line Hent HI. exfalso.
  destruct HI as (_ & _ & _ & _ & _ & _ & Hc').
  pose proof (cw_ent_ncalls e Hent). lia. }
assert (IND : forall m : nat, forall c, 16 - c <= Z.of_nat m -> G_LH c).
{ induction m as [|m IH]; intros c Hc.
  - apply BIG. lia.
  - destruct (Z_le_gt_dec 16 c) as [H6|H6]; [apply BIG; exact H6|].
    assert (HD : G_D c) by (apply SD; [apply IH; lia | exact HR]).
    exact (SC c (SIH c HD) HD). }
intros c. destruct (Z_le_gt_dec 16 c) as [H6|H6]; [apply BIG; exact H6|].
apply (IND (Z.to_nat (16 - c))). lia.
Qed.

(* the theorem from the segment statements (at every FP state), at the ambient FP state *)
Theorem cw_assemble :
  (G_J -> G_ENTRY) ->
  (G_P1 -> G_J) ->
  (G_LH 0 -> G_REL -> G_P1) ->
  (forall c, G_IH c 0 -> G_D c -> G_LH c) ->
  (forall c a, G_IK c a -> G_D c -> G_IH c a) ->
  (forall c a, G_IH c (a + 1) -> G_D c -> G_IL c a) ->
  (forall c a, G_ICMP c a -> G_ICMP2 c a -> G_IL c a -> G_IK c a) ->
  (forall c a, G_ICMP2 c a -> G_ICMP c a) ->
  (forall c a, G_IL c a -> G_ICMP2 c a) ->
  (forall c, G_LH (c + 1) -> G_REL -> G_D c) ->
  G_REL ->
  tcheck_words_spec B MT.
Proof.
intros SA SJ SB SC SI1h SI1l SI2 SI3a SI3b SD SR.
assert (HLH : forall c, G_LH c).
{ apply (cw_call_loop SC SD); [|exact SR].
  intros c HD. exact (cw_item_loop c SI1h SI1l SI2 SI3a SI3b HD 0). }
assert (HE : G_ENTRY) by exact (SA (SJ (SB (HLH 0) SR))).
unfold tcheck_words_spec.
intros ly S W regs mem md ch Wd arr wp ws R O HPRE HPRES HFRM HROD H10 HRO HOBJ Hsp Hhi HWd8 Harr Harr64 Hn
  Hlen Hn31 Hblk Harr8 Hwords HJN HREC HWP Hc0 Hc4 Hev Hlive MOK.
exact (HE fx (mkCWE ly S W regs mem md ch Wd arr wp ws R O)
  (conj HPRE (conj HFRM (conj HROD (conj H10 (conj HRO (conj HOBJ (conj Hsp (conj Hhi (conj Harr (conj Harr64
  (conj Hn (conj Hlen (conj Hn31 (conj Hblk (conj Hwords (conj HJN (conj HREC (conj HWP (conj Hc0 (conj Hc4
  (conj Hev (conj Hlive (conj MOK (conj HWd8 (conj Harr8 HPRES)))))))))))))))))))))))))).
Qed.
End e.
End f.
End d.
