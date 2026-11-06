(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_policy_set (plugin-hostd/fuzz_command, B entry
   0x8be08, 28 instructions, a 32-byte real frame, no side-stack frame): the statement of lib/B/Prog/sup_policy_set_c.v
   on a Theorem Labs lane fc8bcbd8b42 (a Theorem Labs lane; the statement text is as at f490061c104) over the B core a working branch
   c022a2f6a88. The B re-walk of lib/A/Prog/sup_policy_set.v with its segments _s1/_s2/_s3
   (a working branch 02d1c730d1b), whose A code inlines record() and calls xstrdup;
   B calls record() and arg_s() instead, so the walk is five straight-line runs (lib/B/Prog/sup_policy_set_aux.v)
   and four program calls: record(12) at 0x8be28, arg_s(slot, format) at 0x8be34, arg_s(slot, place) at 0x8be40,
   rec_shape_of("policy_set", 10) at 0x8be50, and the tail jump into answer at 0x8be74, which runs answer at this
   function's entry sp, so the post is answer's apost_baseF and the journals join with ajournal_sub_wide (PaFx.v's
   callS_wideF). Frame chains at the calls (PASS4-REFIT.md section B): record and both arg_s calls have s0 = place,
   a heap pointer below alloc_ceiling (class D, achain_low); rec_shape_of needs none (afn_pre_na); answer has the
   entry s0, restored by the epilogue (class A, afn_pre's chain kept by spsw_achain_kept).
   The program-static facts are the kit's lib/B/Prog/RecBLemmas.v (recb_prog_unowned_m, recb_pair_dec), used
   qualified; the block-membership facts are lib/B/Prog/CmdRecAns.v's (rca_in_answer, rca_call_blocks,
   rca_rep_blocks). The other representation and footprint lemmas are lib/B/Prog/sup_reset.v's (a working branch c79a9f2daf7,
   the Qed'd sibling of the same recorder shape), under this walk's names.
   REPORT / TRAP EDGES: the B function body has NONE. No `jal __asan_report_*`, no UBSan trap site and no
   conditional branch at all (gen/funcs.tsv 0 reports, gen/traps.B.summary 0 traps; measured again with capstone on
   fuzz_command.asan-ubsan, sha256 658cefbe...). Every report and trap of the recording step is inside record,
   arg_s and answer, and their contracts refute them.

   Section hypotheses beyond the statement's: the per-binary record CmdBSyms (HB), the meter's laws (MTL), the
   program functions' call targets (cmd_sig_prog_PB : CmdObj.v's cmd_sig_prog, under a Theorem Labs lane's lemma name), and the
   per-binary image facts in the form of a Theorem Labs lane's lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib, at this walk's abstract
   segments. The per-binary facts the
   walk uses are a Theorem Labs lane's CmdRecRo.v / CmdRecRest.v lemmas over them, by exact (CMD_RO_IN, cmd_ro_ok_of_aro,
   cmd_ro_prog_apart, cmd_prog_img, cmd_atail_kept, cmd_rodata_kept); a closing file at the pinned image
   (lib/B/Prog/SupPolicySetClosed.v, PI := PB_cmd) discharges cmd_img_facts_tfib and cmd_sig_prog_PB by a Theorem Labs lane's
   lemmas of those names. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c mix_call_c hand_back_c record_c arg_s_c rec_shape_of_c answer_c sup_policy_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts sup_policy_set_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the representation's readers (lib/B/Prog/sup_reset.v:66-155, after lib/A/Prog/sup_reset.v:39-136, the same CmdRep forms) ---------- *)

Lemma spsw_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma spsw_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma spsw_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (spsw_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma spsw_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (spsw_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (spsw_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (spsw_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (spsw_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma spsw_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (spsw_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (spsw_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (spsw_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma spsw_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  areply_at bl' rd' gr y q.
Proof.
  intros bl bl' rd rd' gr y q H KA KP.
  destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
    unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj _ (conj P3 (conj P4 (conj Kin (conj P6 (conj _ P8))))))).
    + apply (spsw_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (spsw_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (spsw_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (spsw_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (spsw_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma spsw_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (spsw_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma spsw_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma spsw_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma spsw_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma spsw_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall a, (gr <= a < gr + REC_SIZE) \/ (sc <= a < sc + SC_SIZE) \/
             (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  arep_at bl' rd' gr sc R Q.
Proof.
  intros bl bl' rd rd' gr sc R Q (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW) KL K.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
             forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
  { intros pn Hpn. split; [exact (KL pn Hpn)|]. intros x Hx. apply K. right. right. exists pn.
    split; [exact Hpn | exact Hx]. }
  assert (KR : forall x, gr <= x < gr + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
  assert (KS : forall x, sc <= x < sc + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; left; exact Hx).
  unfold REC_SIZE, SC_SIZE in KR, KS.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj _ (conj _ (conj _ HW))))))).
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (spsw_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (spsw_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (spsw_in_calls Q i P pn EP Hpn).
    + apply (spsw_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply spsw_in_spill. exact Hpn.
  - apply (spsw_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply rca_in_answer. exact Hpn.
  - apply (spsw_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply spsw_in_reply. exact Hpn.
  - apply (spsw_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

(* every block the representation names is a block of the list it is stated over *)

(* the recorder's answer field holds 0 or the start of one of its blocks *)
Definition spsw_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma spsw_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  aval_mem rd (A_G_REC + OFF_ANSWER) 8 (spsw_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
  intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold spsw_old. split.
  - unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
    [exact (proj1 HA) | exact HA].
  - intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
Qed.

(* the slot record() returns (record_c.v rec_slot): an entry of g_rec's table, or record.spill *)
Lemma spsw_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
  (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL.
Proof.
  intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [left | right; reflexivity].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
Qed.

(* the slot fact answer's pre asks (answer_c.v:128-130) *)
Lemma spsw_answer_slot : forall R fn A,
(exists k, nth_error (r_calls (rec_record R fn A)) k = Some (fn, A) /\
   rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R = A_REC_SPILL /\ (fn, A) = r_spill (rec_record R fn A)).
Proof.
intros R fn A. unfold rec_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L].
- left. exists (length (r_calls R)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

(* the program's statics of the record (lib/B/YF0m.v TFIB_PROG_STATIC): g_rec, record.spill, g_quitting *)
Lemma spsw_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Ha. lia. Qed.

Lemma spsw_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

(* the footprint of the statement (sup_policy_set_c.v:105) *)
Definition spsw_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma spsw_FP_pos : forall O, (forall pn, In pn O -> 0 < fst pn) -> Forall (fun r => 0 < fst r) (spsw_FP O).
Proof.
intros O HO. unfold spsw_FP. constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
unfold ablocks_fp. rewrite Forall_map. apply Forall_forall. intros pn Hpn. cbn. exact (HO pn Hpn).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callees (each at every FP state) and object bridge (sup_policy_set_c.v:72-76) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses of a Theorem Labs lane's RULING-STMT.md section 1: the per-binary allocator record (a Theorem Labs lane's
   lib/B/YF0m.v), the meter's laws, the program functions' call targets (lib/B/Prog/CmdObj.v) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the per-binary image facts (a Theorem Labs lane's lib/B/Prog/CmdRecBase.v cmd_img_facts, a working branch 6830f0bf032): a Theorem Labs lane proves
   them at the pinned image (CmdRecImg.v cmd_img_facts_tfib, at tfibsegs); this walk is over an abstract PAImg, so it
   takes that lemma's statement at its own segments, under the lemma's name, and each per-binary fact the walk uses
   is a Theorem Labs lane's lemma over them, by exact: CmdRecRo.v CMD_RO_IN and cmd_ro_ok_of_aro, CmdRecRest.v cmd_ro_prog_apart,
   cmd_prog_img, cmd_atail_kept and cmd_rodata_kept *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let cmd_atail_kept : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' p n e,
  AR SEGS B ly S W mem md -> AR SEGS B ly' S' W' mem' md' ->
  ((In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= e < p + n) \/
   (in_roP SEGS RLO RHI e /\ ~ Exists (in_zr e) (as_owned_static B))) ->
  atail_vis SEGS W mem e -> atail_vis SEGS W' mem' e :=
  CmdRecRest.cmd_atail_kept (SK := SK) SEGS B LAWS HB IMG.
Let cmd_rodata_kept : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' STK sp0 FP own k,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, inFP FP a -> Exists (in_zr a) TFIB_PROG_STATIC \/
     exists b n, In (b, n) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n) ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem') :=
  CmdRecRest.cmd_rodata_kept (SK := SK) SEGS B LAWS HB IMG.

(* ---------- the allocator's blocks ---------- *)

Lemma spsw_O_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HQ & HOQ) pn Hpn. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HOQ pn) Hpn)). Qed.

Lemma spsw_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

Lemma spsw_blk_noimg : forall ly S (W : world SEGS) mem md b m a, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md b m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha)))))).
Qed.

Lemma spsw_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma spsw_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (RecBLemmas.recb_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (spsw_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (spsw_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (spsw_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* a live block is listed once *)
Lemma spsw_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (L1 ++ L2) -> In pn L1 -> In pn L2 -> False.
Proof.
intros ly S W mem md L1 L2 pn HAR HP H1 H2.
pose proof H1 as H1'.
apply in_split in H1 as (a1 & b1 & ->). apply in_split in H2 as (a2 & b2 & ->).
assert (HP' : Permutation (ablocks B ly S) (pn :: pn :: (a1 ++ b1 ++ a2 ++ b2))).
{ eapply Permutation_trans; [exact HP|].
  rewrite <- app_assoc. cbn [app].
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  replace (a1 ++ b1 ++ a2 ++ pn :: b2) with ((a1 ++ b1 ++ a2) ++ pn :: b2) by (rewrite <- !app_assoc; reflexivity).
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite <- !app_assoc. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md pn pn _ HAR HP') as D.
assert (Hin : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact H1').
destruct pn as [b m].
destruct (spsw_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* ---------- the walk's footprint and what a journal keeps ---------- *)

Lemma spsw_inFP_cases : forall O a, inFP (spsw_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold spsw_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply spsw_grec_in. exact Ha.
- left. apply spsw_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.

Lemma spsw_static_low : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> 0x10000 <= a < 0x606000.
Proof. intros a Ha. exact (pa_img_range a (cmd_prog_img a Ha)). Qed.

Lemma spsw_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (spsw_FP O) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
destruct (spsw_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)].
- pose proof (spsw_static_low a HP). lia.
- destruct (spsw_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (H4 & Hc & _). lia.
Qed.

(* arodata_okP along the walk's journal (cmd_rodata_kept: the footprint is statics and the recorder's blocks) *)
Lemma spsw_aro : forall ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp STK,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp (spsw_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O lyc Sc Wc memc mdc own k sp STK HAR HO HJ HR.
apply (cmd_rodata_kept ly S W mem md lyc Sc Wc memc mdc STK sp (spsw_FP O) own k HAR HJ); [|exact HR].
intros a Ha. destruct (spsw_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)]; [left; exact HP|].
right. exists b, n. split; [apply in_or_app; left; exact (HO _ Hin) | exact Hb].
Qed.

Lemma spsw_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

Lemma spsw_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (RecBLemmas.recb_prog_unowned_m (PI := PI) B HB cmd_prog_img a HP) as (H1 & H2 & H3). exact (spsw_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

Lemma spsw_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

Lemma spsw_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain ly' (rdW W' mem') sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch HJ HF Hc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly ly'); [exact Etop|].
apply (achain_kept ly (rdW W mem) (rdW W' mem') sp0 v ch sp0 Hc); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hf; specialize (HF a Hf); lia].
Qed.

(* the bytes the walk's callees may write: g_rec / record.spill (program statics), and the recorder's own blocks *)
Lemma spsw_awr_static : forall STK sp O bl0 blc fr0 ly own a, Exists (in_zr a) TFIB_PROG_STATIC -> inFP (spsw_FP O) a ->
awr_byte SEGS B STK sp (spsw_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a HP HF.
right; right; right; right; left. split; [exact HF|]. split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

Lemma spsw_awr_grec : forall STK sp O bl0 blc fr0 ly own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp (spsw_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply spsw_awr_static; [exact (spsw_grec_in a Ha)|].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma spsw_awr_spill : forall STK sp O bl0 blc fr0 ly own a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp (spsw_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply spsw_awr_static; [exact (spsw_spill_in a Ha)|].
exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

(* a byte of the slot record() returned *)
Lemma spsw_awr_slot : forall STK sp O bl0 blc fr0 ly own R a, (length (r_calls R) <= 16)%nat ->
rec_slot R <= a < rec_slot R + CALL_SIZE -> awr_byte SEGS B STK sp (spsw_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own R a HL Ha. destruct (spsw_slot_bounds R HL) as [Hs | Hs].
- apply spsw_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply spsw_awr_spill. rewrite Hs in Ha. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma spsw_awr_blk : forall STK sp O bl0 blc fr0 ly own b n a, In (b, n) O -> In (b, n) blc ->
b <= a < b + req_size n -> awr_byte SEGS B STK sp (spsw_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own b n a HO Hc Ha. right; left. split.
- unfold spsw_FP. apply inFP_cons. right. apply inFP_cons. right.
  replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b n (a - b)); [exact HO | lia].
- exists b, n. split; [exact Hc | exact Ha].
Qed.

(* ---------- the string argument ---------- *)

(* the bytes of a string argument decide astr_argA's reader part: its other parts name no reader *)
Lemma spsw_argA_kept : forall ly1 S1 (rd rd' : reader) ro O1 p v, astr_argA B ly1 S1 rd ro O1 p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly1 S1 rd' ro O1 p (Some v).
Proof.
intros ly1 S1 rd rd' ro O1 p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [|split; [exact Hl | exact Hr]].
apply (spsw_str_keep rd); [exact Hs|]. intros x Hx. replace x with (p + (x - p)) by lia. apply K. lia.
Qed.

(* a string argument's bytes lie below alloc_ceiling: a block's, or the image's *)
Lemma spsw_argA_low : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 p v, AR SEGS B ly1 S1 W1 mem1 md1 ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 p (Some v) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= p + i < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 O1 p v HAR H i Hi. cbn [astr_argA] in H. pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
- destruct Hblk as (b & m & Hin & Hb1 & Hb2).
  destruct (spsw_blk_bounds ly1 S1 W1 mem1 md1 b m HAR Hin) as (Hb & Hc & _ & Hmr & _). lia.
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia.
Qed.

(* the pointer itself (caller's s0 at the program calls) lies below alloc_ceiling *)

(* the string argument from the entry to a later state: its block (none of the recorder's) is live there with its
   bytes, or its read-only bytes are the image's at both states; its word tail is kept (cmd_atail_kept) *)
Lemma spsw_arg_kept : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O pw x,
AR SEGS B ly S W mem md -> AR SEGS B lyc Sc Wc memc mdc ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k -> rdW Wc memc a = rdW W mem a) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pw (Some x) ->
atail_vis SEGS W mem (pw + Z.of_nat (length x)) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] pw (Some x) /\
atail_vis SEGS Wc memc (pw + Z.of_nat (length x)).
Proof.
intros ly S W mem md lyc Sc Wc memc mdc O pw x HAR HARc HRO HROc Hblk Hbytes HA HT.
cbn [astr_argA] in HA |- *.
destruct HA as (Hp0 & HS & Hlen & [((b & k & Hbk & Hble & Hhi) & Hap) | (Hro & Hck)]).
- assert (HnO : ~ In (b, k) O).
  { intros Hin. rewrite Forall_forall in Hap. pose proof (Hap (b, k) Hin) as Hd. cbn [fst snd] in Hd.
    unfold iv_apart in Hd. lia. }
  assert (HK : forall a, b <= a < b + k -> rdW Wc memc a = rdW W mem a)
    by (intros a Ha; exact (Hbytes b k a Hbk HnO Ha)).
  split.
  + split; [exact Hp0|]. split.
    * apply (spsw_str_keep (rdW W mem)); [exact HS|]. intros a Ha. apply HK. lia.
    * split; [exact Hlen|]. left. split; [|apply Forall_nil].
      exists b, k. split; [exact (Hblk (b, k) Hbk HnO) | split; [exact Hble | exact Hhi]].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc b k (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | left; split; [exact Hbk | split; [exact (Hblk (b, k) Hbk HnO) | lia]] | exact HT].
- split.
  + split; [exact Hp0|]. split.
    * apply (spsw_str_keep (rdW W mem)); [exact HS|]. intros a Ha.
      destruct (Hro (a - pw) ltac:(lia)) as (Hr & Ho & He). replace a with (pw + (a - pw)) by lia.
      rewrite (HROc _ Hr Ho He), (HRO _ Hr Ho He). reflexivity.
    * split; [exact Hlen|]. right. split; [exact Hro | exact Hck].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc 0 0 (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | right | exact HT].
    destruct (Hro (Z.of_nat (length x)) ltac:(lia)) as (Hr & Ho & _). split; [exact Hr | exact Ho].
Qed.

(* rec_repA at a state whose reader agrees on g_rec, record.spill and the recorder's blocks *)
Lemma spsw_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (spsw_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

(* a block answer frees: the recorder's block whose start is the old answer (answer_c.v:137) *)
Lemma spsw_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.



(* the aux file's runs with its Section variables supplied, and PaFx.v's FP-existential call rule *)
Let W_PRO := sps_pro B cmd_sig_prog_PB.
Let W_MID1 := sps_mid1 B cmd_sig_prog_PB.
Let W_MID2 := sps_mid2 B cmd_sig_prog_PB.
Let W_EPI := sps_epi B cmd_sig_prog_PB.
Let W_RSO := sps_rso B VOBJS cmd_sig_prog_PB MT (TREC_SHAPE_OF fx) HB CMD_RO_IN.
Let W_CALLF := callS_wideF (L := cmd_listing) (PI := PI) B LAWS.

(* a register a run keeps, read at a bitvector index *)
Lemma spsw_keep_get : forall (l : list Z) (regs1 regs0 : bvmap 5 word) (rr : bv 5),
(forall r, In r l -> getr regs1 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) -> In (bv_unsigned rr) l ->
getr regs1 rr = getr regs0 rr.
Proof.
intros l regs1 regs0 rr H Hin. pose proof (H (bv_unsigned rr) Hin) as Hq.
rewrite !Z_to_bv_bv_unsigned in Hq. exact Hq.
Qed.
Lemma spsw_g : forall (regs : bvmap 5 word) (r : Z) (rr : bv 5),
bv_unsigned rr = r -> getr regs rr = getr regs (Z_to_bv 5 r).
Proof. intros regs r rr <-. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma spsw_slot_low : forall R a, (length (r_calls R) <= 16)%nat -> rec_slot R <= a < rec_slot R + CALL_SIZE ->
0x5e32d0 <= a < 0x5e3798.
Proof.
intros R a Hn Ha. destruct (spsw_slot_bounds R Hn) as [Hs | Hs]; [|rewrite Hs in Ha];
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL in *; lia.
Qed.
Ltac spsw_in := vm_compute; repeat (first [left; reflexivity | right]).

(* the shape rec_shape_of returns for this verb fits answer's buffer *)
Lemma spsw_fits : fits sps_shape.
Proof. unfold fits, sps_shape. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* ---------- the walk ---------- *)
Theorem tsup_policy_set_holds : tsup_policy_set_spec B MT.
Proof.
unfold tsup_policy_set_spec.
intros ly S W regs mem md ch pf pp format place R O
  HPRE HFRM HROD HRO H10 Hpf H11 Hpp HFMT HPLC HREP HFR8 HEV HLIVE HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
(* the stack budget: each callee's need and the tail call's, under the statement's *)
assert (HSTK : 32 + RECORD_STK <= SUP_POLICY_SET_STK /\ 32 + ARG_S_STK <= SUP_POLICY_SET_STK /\
  32 + REC_SHAPE_OF_STK <= SUP_POLICY_SET_STK /\ ANSWER_STK <= SUP_POLICY_SET_STK /\ 0 <= RECORD_STK /\
  0 <= ARG_S_STK /\ 0 <= REC_SHAPE_OF_STK /\ 0 <= ANSWER_STK /\ 32 <= SUP_POLICY_SET_STK /\
  SUP_POLICY_SET_STK <= 16608)
  by (vm_compute; repeat split; discriminate).
destruct HSTK as (HSK1 & HSK2 & HSK3 & HSK4 & HSK5 & HSK6 & HSK7 & HSK8 & HSK9 & HSK10).
set (sp0 := spZ regs) in *.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (spsw_O_in ly S _ R O HREP).
assert (HOpos : forall pn, In pn O -> 0 < fst pn).
{ intros [b n] Hpn. destruct (spsw_blk_bounds ly S W mem md b n HAR (HOin _ Hpn)) as (Hb & _). cbn. lia. }
assert (HFPpos : Forall (fun r => 0 < fst r) (spsw_FP O)) by exact (spsw_FP_pos O HOpos).
assert (HFPlow : forall a, inFP (spsw_FP O) a -> 0 <= a < alloc_ceiling)
  by (intros a Ha; exact (spsw_FP_low ly S W mem md O a HAR HOin Ha)).
pose proof HREP as (Q0 & HQ0 & HOQ0).
pose proof HQ0 as (_ & _ & _ & (HC1 & _) & _).
assert (EFP : (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O = spsw_FP O)
  by reflexivity.
rewrite EFP.
(* the meter's and the live bytes' parts are nonnegative *)
assert (XR0 : 0 <= XM_RECORD MT R).
{ unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL). destruct (Nat.ltb _ _); lia. }
assert (XA0 : forall v, 0 <= XM_ARG_S MT v).
{ intros v. unfold XM_ARG_S, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (LN0 : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (LA0 : forall v, 0 <= LIVE_ARG_S v) by (intros v; unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
assert (EV1 : 0 <= EV_ARG_S /\ 0 <= EV_ANSWER /\ EV_REC_SHAPE_OF = 0 /\ 0 <= EV_RECORD R).
{ unfold EV_RECORD, rec_spill_frees. destruct (Nat.ltb (length (r_calls R)) 16);
  (repeat split; first [vm_compute; discriminate | reflexivity | lia]). }
destruct EV1 as (EVA & EVN & EVS & EVR).
set (A := [sarg format; sarg place]).
set (e := (REC_POLICY_SET, A)).
assert (HM : sup_policy_set_m R format place = rec_answer (rec_record R REC_POLICY_SET A) e sps_shape true)
  by reflexivity.
(* the two string arguments: the statement's block form gives astr_argA's heap arm and the word tail *)
destruct HFMT as (xf & Hxf & (qf & kf & Hqf & Hqf1 & Hqf2) & Hfs & Hfln & Hfa).
destruct HPLC as (xp & Hxp & (qp & kp & Hqp & Hqp1 & Hqp2) & Hps & Hpln & Hpa).
destruct (spsw_blk_bounds ly S W mem md qf kf HAR Hqf) as (Hqf4 & Hqfc & Hkf0 & Hkfr & _).
destruct (spsw_blk_bounds ly S W mem md qp kp HAR Hqp) as (Hqp4 & Hqpc & Hkp0 & Hkpr & _).
assert (HFA : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pf (Some xf)).
{ cbn [astr_argA]. split; [lia|]. split; [exact Hfs|]. split; [exact Hfln|].
  left. split; [exists qf, kf; split; [exact Hqf | lia] | exact Hfa]. }
assert (HPA' : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pp (Some xp)).
{ cbn [astr_argA]. split; [lia|]. split; [exact Hps|]. split; [exact Hpln|].
  left. split; [exists qp, kp; split; [exact Hqp | lia] | exact Hpa]. }
assert (HFT : atail_vis SEGS W mem (pf + Z.of_nat (length xf)))
  by exact (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md qf kf (pf + Z.of_nat (length xf)) HAR Hqf ltac:(lia)).
assert (HPT : atail_vis SEGS W mem (pp + Z.of_nat (length xp)))
  by exact (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md qp kp (pp + Z.of_nat (length xp)) HAR Hqp ltac:(lia)).
assert (Hpflow : 0 <= pf < alloc_ceiling) by lia.
assert (Hpplow : 0 <= pp < alloc_ceiling) by lia.
pose proof (ajournal_init SEGS B SUP_POLICY_SET_STK (spsw_FP O) ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at, w64. change (BASE + AF_sup_policy_set) with (BASE + SPS_ENTRY).
(* ---- the prologue (0x8be08 .. jal record 0x8be28) ---- *)
apply (W_PRO ly S W regs mem md ch SUP_POLICY_SET_STK (spsw_FP O) _ HPRE ltac:(unfold SPS_FRAME; lia)).
intros regsA memA mdA HJA QA1 QA2 QA8 QA9 QA10 QAk HFRMA KEEPA HGA.
pose proof (proj1 HJA) as HARA.
assert (KAlo : forall a, 0 <= a < alloc_ceiling -> rdW W memA a = rdW W mem a)
  by (intros a Ha; apply KEEPA; [lia | unfold SPS_FRAME; fold sp0; lia]).
assert (GA2 : spZ regsA = sp0 + -32)
  by (unfold spZ at 1; rewrite QA2; unfold w64, SPS_FRAME; rewrite unsigned_lit_small by (fold sp0; lia); fold sp0; lia).
assert (GA3 : getr regsA 3 = w64 (as_gp B))
  by (rewrite (spsw_keep_get sps_kept_pro regsA regs 3%bv QAk ltac:(spsw_in)); exact Hgp).
assert (GA4 : getr regsA 4 = w64 (as_tp B))
  by (rewrite (spsw_keep_get sps_kept_pro regsA regs 4%bv QAk ltac:(spsw_in)); exact Htp).
assert (GA1r : YK0s.ret_ok (getr regsA 1))
  by (rewrite QA1; apply ret_ok_codeptr_v; [unfold SPS_RET_REC, AF_sup_policy_set; lia | reflexivity]).
assert (GA1a : 4096 <= bv_unsigned (getr regsA 1)).
{ rewrite QA1. pose proof HBASE as (HB0 & HB1 & _).
  rewrite unsigned_lit_small by (unfold SPS_RET_REC, AF_sup_policy_set; lia).
  unfold SPS_RET_REC, AF_sup_policy_set. lia. }
assert (HROA : arodata_okP SEGS RLO RHI B (rdW W memA))
  by exact (spsw_aro ly S W mem md O ly S W memA _ [] 0 sp0 _ HAR HOin HJA HROD).
assert (HREPA : rec_repA B ly S (rdW W memA) R O).
{ apply (spsw_rec_repA_ext ly S (rdW W mem) ly S _ R O HREP HOin).
  intros a [Ha | [Ha | ([b n] & Hpn & Ha)]]; cbn [fst snd] in *.
  - apply KAlo; unfold A_G_REC, REC_SIZE in Ha; lia.
  - apply KAlo; unfold A_REC_SPILL, SC_SIZE in Ha; lia.
  - destruct (spsw_blk_bounds ly S W mem md b n HAR (HOin _ Hpn)) as (Hb & Hc & _ & Hmr & _). apply KAlo; lia. }
(* ---- the call of record(12) (0x8be28) ---- *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsA memA _ SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly S _ 0
    RECORD_STK _ (EV_RECORD R) (-32) (getr regsA 1) [] _ HJA GA2 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
    GA3 GA4 eq_refl GA1r GA1a
    ltac:(apply achain_low; unfold s0Z; rewrite QA8, H11; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1. pose proof (TRECORD fx ly S W regsA memA _ [] REC_POLICY_SET R O HPRE1) as T.
    unfold apost_base in T. apply T.
    + exact HROA.
    + exact QA10.
    + unfold REC_POLICY_SET, REC_FN_COUNT. lia.
    + exact HREPA.
    + unfold EV_SUP_POLICY_SET in HEV. lia.
    + apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_POLICY_SET.
      pose proof (XA0 format). pose proof (XA0 place). pose proof (XN0 (snd (sup_policy_set_m R format place))). lia.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { apply spsw_awr_grec. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (spsw_awr_slot _ _ _ _ _ _ _ _ R a HC1). unfold CALL_SIZE. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
    exact (spsw_awr_blk _ _ _ _ _ _ _ _ b n a Hbn (HOin _ Hbn) Hba).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    assert (Hlo : 0 <= a < alloc_ceiling).
    { apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
      apply inFP_cons in Ha as [Ha | Ha].
      { destruct (spsw_slot_bounds R HC1) as [Hs | Hs];
        [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
        rewrite Hs in Ha. unfold A_REC_SPILL in Ha. lia. }
      destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
      destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
      destruct (spsw_blk_bounds ly S W mem md b n HAR (HOin _ Hbn)) as (Hb & Hc & _). lia. }
    fold sp0 in Hw. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HKr).
destruct HKr as (F & O1 & R10 & HPermF & HFlen & HFO & HREP1 & HO1 & HBB1 & MLE1).
pose proof (proj1 HJ2) as HAR2.
assert (Hsp1lo : alloc_ceiling <= sp0 + -32) by (fold sp0 in Hslo; lia).
(* record's footprint lies below the allocator's ceiling *)
assert (HFPr : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
   (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> 0 <= a < alloc_ceiling).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
  apply inFP_cons in Ha as [Ha | Ha].
  { destruct (spsw_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    rewrite Hs in Ha. unfold A_REC_SPILL in Ha. lia. }
  destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
  destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
  destruct (spsw_blk_bounds ly S W mem md b n HAR (HOin _ Hbn)) as (Hb & Hc & _). lia. }
(* the frame survives record: it lies above record's sp *)
assert (HFRM2 : sps_frame (rdW W2 mem2) sp0 regs).
{ intros j r Hj. pose proof (proj1 (nth_error_Some sps_saved j) ltac:(rewrite Hj; discriminate)) as Hj4.
  cbn [length sps_saved] in Hj4.
  apply (spsw_aval_keep (rdW W memA)); [exact (HFRMA j r Hj)|].
  intros x Hx. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
  apply F1c; [lia | lia | intros Hf; pose proof (HFPr x Hf); lia]. }
(* the blocks of the entry that are none of the recorder's are live after record, with their bytes *)
assert (HlivB : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn HnO. apply (Permutation_in _ HPermF) in Hpn. apply in_app_or in Hpn as [H | H]; [exact H|].
  exfalso. exact (HnO (HFO _ H)). }
assert (HbytB : forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k ->
  rdW W2 mem2 a = rdW W mem a).
{ intros b k a Hbk HnO Ha. pose proof (HlivB _ Hbk HnO) as Hbk2.
  destruct (spsw_blk_bounds ly S W mem md b k HAR Hbk) as (Hb & Hbc & Hk0 & Hkr & _).
  replace a with (b + (a - b)) by lia.
  rewrite (spsw_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (a - b) HJc2 Hbk Hbk2 ltac:(lia)).
  - apply KAlo; lia.
  - intros HFa. apply inFP_cons in HFa as [HFa | HFa].
    { apply (spsw_blk_noimg ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. apply spsw_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in HFa as [HFa | HFa].
    { apply (spsw_blk_noimg ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. destruct (spsw_slot_bounds R HC1) as [Hs | Hs].
      - apply spsw_grec_in. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      - apply spsw_spill_in. rewrite Hs in HFa. unfold A_REC_SPILL, SC_SIZE in *. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exact (inFP_nil _ HFa)|].
    destruct (inFP_ablocks_fp_inv O _ HFa) as (b' & n' & Hbn & Hba).
    destruct (RecBLemmas.recb_pair_dec (b, k) (b', n')) as [Eq | Hne]; [apply HnO; rewrite Eq; exact Hbn|].
    destruct (spsw_blk_bounds ly S W mem md b' n' HAR (HOin _ Hbn)) as (_ & _ & _ & Hnr' & _).
    destruct (spsw_blk_apart ly S W mem md b k b' n' HAR Hbk (HOin _ Hbn) Hne); lia. }
(* arg_s's footprint: two words of the slot *)
assert (HFPs : forall (A0 : list (list byte)) a, (length A0 < 6)%nat ->
  inFP (if Z.of_nat (length A0) <? REC_ARGS_MAX
        then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
              (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A0),
               rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A0) + 8)]
        else []) a -> rec_slot R <= a < rec_slot R + CALL_SIZE).
{ intros A0 a HA0 Ha. destruct (Z.of_nat (length A0) <? REC_ARGS_MAX); [|exfalso; exact (inFP_nil a Ha)].
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *.
  apply inFP_cons in Ha as [Ha | Ha]; [lia|]. apply inFP_cons in Ha as [Ha | Ha]; [lia|].
  exfalso; exact (inFP_nil a Ha). }
(* ---- run B: 0x8be2c .. jal arg_s (0x8be34) ---- *)
rewrite QA1.
apply (W_MID1 W2 regs2 mem2 md2 SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly2 S2 (0 + EV_RECORD R) _ HJ2).
intros regsB memB mdB HJB KB HGB QB1 QB18 QB10 QB11 QBk.
pose proof (proj1 HJB) as HARB.
assert (GB2 : spZ regsB = sp0 + -32).
{ unfold spZ. rewrite (spsw_g regsB 2 2%bv eq_refl), (QBk 2 ltac:(spsw_in)), (HP2 2 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsA 2 2%bv eq_refl). exact GA2. }
assert (GB3 : getr regsB 3 = w64 (as_gp B)).
{ rewrite (spsw_g regsB 3 3%bv eq_refl), (QBk 3 ltac:(spsw_in)), (HP2 3 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsA 3 3%bv eq_refl). exact GA3. }
assert (GB4 : getr regsB 4 = w64 (as_tp B)).
{ rewrite (spsw_g regsB 4 4%bv eq_refl), (QBk 4 ltac:(spsw_in)), (HP2 4 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsA 4 4%bv eq_refl). exact GA4. }
assert (GB8 : getr regsB 8 = w64 pp).
{ rewrite (spsw_g regsB 8 8%bv eq_refl), (QBk 8 ltac:(spsw_in)), (HP2 8 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsA 8 8%bv eq_refl). rewrite QA8. exact H11. }
assert (GB10 : getr regsB 10 = w64 (rec_slot R)) by (rewrite QB10; exact R10).
assert (GB18 : getr regsB 18 = w64 (rec_slot R)) by (rewrite QB18; exact R10).
assert (GB11 : getr regsB 11 = w64 pf).
{ rewrite QB11. rewrite (spsw_g regs2 9 9%bv eq_refl), (HP2 9 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsA 9 9%bv eq_refl). rewrite QA9. exact H10. }
assert (GB1r : YK0s.ret_ok (getr regsB 1))
  by (rewrite QB1; apply ret_ok_codeptr_v; [unfold SPS_RET_A1, AF_sup_policy_set; lia | reflexivity]).
assert (GB1a : 4096 <= bv_unsigned (getr regsB 1)).
{ rewrite QB1. pose proof HBASE as (HB0 & HB1 & _).
  rewrite unsigned_lit_small by (unfold SPS_RET_A1, AF_sup_policy_set; lia).
  unfold SPS_RET_A1, AF_sup_policy_set. lia. }
assert (HROB : arodata_okP SEGS RLO RHI B (rdW W2 memB))
  by exact (spsw_aro ly S W mem md O ly2 S2 W2 memB _ [] _ sp0 _ HAR HOin HJB HROD).
assert (HROkB : cmd_ro_ok (rdW W2 memB)) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARB HROB).
assert (HO1in : forall pn, In pn O1 -> In pn (ablocks B ly2 S2)) by exact (spsw_O_in ly2 S2 _ _ O1 HREP1).
assert (HREPB : rec_repA B ly2 S2 (rdW W2 memB) (rec_record R REC_POLICY_SET []) O1).
{ apply (spsw_rec_repA_ext ly2 S2 (rdW W2 mem2) ly2 S2 _ _ O1 HREP1 HO1in). intros a _. apply KB. }
assert (HbytBB : forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k ->
  rdW W2 memB a = rdW W mem a) by (intros b k a H1 H2 H3; rewrite KB; exact (HbytB b k a H1 H2 H3)).
assert (HFB : astr_argA B ly2 S2 (rdW W2 memB) (in_roP SEGS RLO RHI) [] pf (Some xf) /\
  atail_vis SEGS W2 memB (pf + Z.of_nat (length xf)))
  by exact (spsw_arg_kept ly S W mem md ly2 S2 W2 memB mdB O pf xf HAR HARB HROD HROB HlivB HbytBB HFA HFT).
(* ---- the call of arg_s(slot, format) (0x8be34) ---- *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W2 regsB memB _ SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly2 S2 _ _
    ARG_S_STK _ EV_ARG_S (-32) (getr regsB 1) [] _ HJB GB2 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
    GB3 GB4 eq_refl GB1r GB1a
    ltac:(apply achain_low; unfold s0Z; rewrite GB8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1.
    pose proof (TARG_S fx ly2 S2 W2 regsB memB _ [] (rec_slot R) pf REC_POLICY_SET [] format R O1 HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROB.
    + exact HROkB.
    + exact GB10.
    + exact GB11.
    + reflexivity.
    + exact HREPB.
    + left. rewrite Hxf. exact (proj1 HFB).
    + intros x Hx. rewrite Hxf in Hx. injection Hx as <-. exact (proj2 HFB).
    + pose proof HJB as (_ & _ & _ & _ & _ & _ & HnevB & _).
      unfold EV_SUP_POLICY_SET in *. lia.
    + pose proof (LN0 (snd (sup_policy_set_m R format place))). pose proof (LA0 place).
      unfold LIVE_SUP_POLICY_SET in HLIVE. lia.
    + apply (mok_station MT S S2 (XM_SUP_POLICY_SET MT R format place) (XM_RECORD MT R) _ MTL HMOK MLE1 (XA0 format)).
      unfold XM_SUP_POLICY_SET. pose proof (XA0 place). pose proof (XN0 (snd (sup_policy_set_m R format place))). lia.
  - intros a Ha. exact (spsw_awr_slot _ _ _ _ _ _ _ _ R a HC1 (HFPs [] a ltac:(cbn; lia) Ha)).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    pose proof (spsw_slot_low R a HC1 (HFPs [] a ltac:(cbn; lia) Ha)) as Hs. fold sp0 in Hw. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (HBB3 & MLE3 & [(Hc6 & _) | (_ & p1 & Hp1 & Hperm3 & Hfresh3 & HREP3)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length Z.of_nat] in Hc6. lia. }
cbn [app] in HREP3.
set (n1 := Z.of_nat (length (sarg format)) + 1) in *.
pose proof (proj1 HJ3) as HAR3.
assert (HFRM3 : sps_frame (rdW W3 mem3) sp0 regs).
{ intros j r Hj. pose proof (proj1 (nth_error_Some sps_saved j) ltac:(rewrite Hj; discriminate)) as Hj4.
  cbn [length sps_saved] in Hj4.
  apply (spsw_aval_keep (rdW W2 memB)); [apply (spsw_aval_keep (rdW W2 mem2)); [exact (HFRM2 j r Hj) | intros x _; apply KB]|].
  intros x Hx. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
  apply F1c; [lia | lia |]. intros Hf. pose proof (spsw_slot_low R x HC1 (HFPs [] x ltac:(cbn; lia) Hf)) as Hs. lia. }
assert (H2to3 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm3)); right; exact Hpn).
assert (HlivC : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly3 S3))
  by (intros pn H1 H2; exact (H2to3 _ (HlivB pn H1 H2))).
assert (HbytC : forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k ->
  rdW W3 mem3 a = rdW W mem a).
{ intros b k a Hbk HnO Ha. pose proof (HlivB _ Hbk HnO) as Hbk2.
  destruct (spsw_blk_bounds ly S W mem md b k HAR Hbk) as (Hb & Hbc & Hk0 & Hkr & _).
  replace a with (b + (a - b)) by lia.
  rewrite (spsw_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (a - b) HJc3 Hbk2 (H2to3 _ Hbk2) ltac:(lia)).
  - replace (b + (a - b)) with a by lia. exact (HbytBB b k a Hbk HnO Ha).
  - intros HFa. pose proof (HFPs [] (b + (a - b)) ltac:(cbn; lia) HFa) as Hs.
    apply (spsw_blk_noimg ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
    apply cmd_prog_img. destruct (spsw_slot_bounds R HC1) as [Hs' | Hs'].
    + apply spsw_grec_in. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    + apply spsw_spill_in. rewrite Hs' in Hs. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
(* ---- run C: 0x8be38 .. jal arg_s (0x8be40) ---- *)
rewrite QB1.
apply (W_MID2 W3 regs3 mem3 md3 SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly3 S3 (0 + EV_RECORD R + EV_ARG_S) _ HJ3).
intros regsC memC mdC HJC KC HGC QC1 QC10 QC11 QCk.
pose proof (proj1 HJC) as HARC.
assert (GC2 : spZ regsC = sp0 + -32).
{ unfold spZ. rewrite (spsw_g regsC 2 2%bv eq_refl), (QCk 2 ltac:(spsw_in)), (HP3 2 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsB 2 2%bv eq_refl). exact GB2. }
assert (GC3 : getr regsC 3 = w64 (as_gp B)).
{ rewrite (spsw_g regsC 3 3%bv eq_refl), (QCk 3 ltac:(spsw_in)), (HP3 3 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsB 3 3%bv eq_refl). exact GB3. }
assert (GC4 : getr regsC 4 = w64 (as_tp B)).
{ rewrite (spsw_g regsC 4 4%bv eq_refl), (QCk 4 ltac:(spsw_in)), (HP3 4 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsB 4 4%bv eq_refl). exact GB4. }
assert (GC8 : getr regsC 8 = w64 pp).
{ rewrite (spsw_g regsC 8 8%bv eq_refl), (QCk 8 ltac:(spsw_in)), (HP3 8 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsB 8 8%bv eq_refl). exact GB8. }
assert (GC18 : getr regsC 18 = w64 (rec_slot R)).
{ rewrite (spsw_g regsC 18 18%bv eq_refl), (QCk 18 ltac:(spsw_in)), (HP3 18 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsB 18 18%bv eq_refl). exact GB18. }
assert (GC10 : getr regsC 10 = w64 (rec_slot R)).
{ rewrite QC10. rewrite (spsw_g regs3 18 18%bv eq_refl), (HP3 18 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsB 18 18%bv eq_refl). exact GB18. }
assert (GC11 : getr regsC 11 = w64 pp).
{ rewrite QC11. rewrite (spsw_g regs3 8 8%bv eq_refl), (HP3 8 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsB 8 8%bv eq_refl). exact GB8. }
assert (GC1r : YK0s.ret_ok (getr regsC 1))
  by (rewrite QC1; apply ret_ok_codeptr_v; [unfold SPS_RET_A2, AF_sup_policy_set; lia | reflexivity]).
assert (GC1a : 4096 <= bv_unsigned (getr regsC 1)).
{ rewrite QC1. pose proof HBASE as (HB0 & HB1 & _).
  rewrite unsigned_lit_small by (unfold SPS_RET_A2, AF_sup_policy_set; lia).
  unfold SPS_RET_A2, AF_sup_policy_set. lia. }
assert (HROC : arodata_okP SEGS RLO RHI B (rdW W3 memC))
  by exact (spsw_aro ly S W mem md O ly3 S3 W3 memC _ [] _ sp0 _ HAR HOin HJC HROD).
assert (HROkC : cmd_ro_ok (rdW W3 memC)) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARC HROC).
assert (HO2in : forall pn, In pn ((p1, n1) :: O1) -> In pn (ablocks B ly3 S3)) by exact (spsw_O_in ly3 S3 _ _ _ HREP3).
assert (HREPC : rec_repA B ly3 S3 (rdW W3 memC) (rec_record R REC_POLICY_SET [sarg format]) ((p1, n1) :: O1)).
{ apply (spsw_rec_repA_ext ly3 S3 (rdW W3 mem3) ly3 S3 _ _ _ HREP3 HO2in). intros a _. apply KC. }
assert (HbytCC : forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k ->
  rdW W3 memC a = rdW W mem a) by (intros b k a H1 H2 H3; rewrite KC; exact (HbytC b k a H1 H2 H3)).
assert (HPC : astr_argA B ly3 S3 (rdW W3 memC) (in_roP SEGS RLO RHI) [] pp (Some xp) /\
  atail_vis SEGS W3 memC (pp + Z.of_nat (length xp)))
  by exact (spsw_arg_kept ly S W mem md ly3 S3 W3 memC mdC O pp xp HAR HARC HROD HROC HlivC HbytCC HPA' HPT).
(* ---- the call of arg_s(slot, place) (0x8be40) ---- *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W3 regsC memC _ SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly3 S3 _ _
    ARG_S_STK _ EV_ARG_S (-32) (getr regsC 1) [] _ HJC GC2 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
    GC3 GC4 eq_refl GC1r GC1a
    ltac:(apply achain_low; unfold s0Z; rewrite GC8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1.
    pose proof (TARG_S fx ly3 S3 W3 regsC memC _ [] (rec_slot R) pp REC_POLICY_SET [sarg format] place R
      ((p1, n1) :: O1) HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROC.
    + exact HROkC.
    + exact GC10.
    + exact GC11.
    + reflexivity.
    + exact HREPC.
    + left. rewrite Hxp. exact (proj1 HPC).
    + intros x Hx. rewrite Hxp in Hx. injection Hx as <-. exact (proj2 HPC).
    + pose proof HJC as (_ & _ & _ & _ & _ & _ & HnevC & _).
      unfold EV_SUP_POLICY_SET in *. lia.
    + pose proof (LN0 (snd (sup_policy_set_m R format place))).
      unfold LIVE_SUP_POLICY_SET in HLIVE. lia.
    + apply (mok_station MT S S3 (XM_SUP_POLICY_SET MT R format place) (XM_RECORD MT R + XM_ARG_S MT format) _ MTL HMOK
        (mle_station MT S S2 S3 _ _ MTL MLE1 MLE3) (XA0 place)).
      unfold XM_SUP_POLICY_SET. pose proof (XN0 (snd (sup_policy_set_m R format place))). lia.
  - intros a Ha. exact (spsw_awr_slot _ _ _ _ _ _ _ _ R a HC1 (HFPs [sarg format] a ltac:(cbn; lia) Ha)).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    pose proof (spsw_slot_low R a HC1 (HFPs [sarg format] a ltac:(cbn; lia) Ha)) as Hs. fold sp0 in Hw. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HK4).
destruct HK4 as (HBB4 & MLE4 & [(Hc6 & _) | (_ & p2 & Hp2 & Hperm4 & Hfresh4 & HREP4)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length Z.of_nat] in Hc6. lia. }
cbn [app] in HREP4.
set (n2 := Z.of_nat (length (sarg place)) + 1) in *.
pose proof (proj1 HJ4) as HAR4.
assert (HFRM4 : sps_frame (rdW W4 mem4) sp0 regs).
{ intros j r Hj. pose proof (proj1 (nth_error_Some sps_saved j) ltac:(rewrite Hj; discriminate)) as Hj4.
  cbn [length sps_saved] in Hj4.
  apply (spsw_aval_keep (rdW W3 memC)); [apply (spsw_aval_keep (rdW W3 mem3)); [exact (HFRM3 j r Hj) | intros x _; apply KC]|].
  intros x Hx. pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
  apply F1c; [lia | lia |]. intros Hf. pose proof (spsw_slot_low R x HC1 (HFPs [sarg format] x ltac:(cbn; lia) Hf)) as Hs. lia. }
(* ---- rec_shape_of("policy_set", 10) (run 0x8be44 .. 0x8be50 and the call) ---- *)
rewrite QC1.
assert (GD2 : spZ regs4 = sp0 - SPS_FRAME).
{ unfold spZ. rewrite (spsw_g regs4 2 2%bv eq_refl), (HP4 2 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsC 2 2%bv eq_refl). fold (spZ regsC). rewrite GC2. unfold SPS_FRAME. lia. }
assert (GD3 : getr regs4 3 = w64 (as_gp B)).
{ rewrite (spsw_g regs4 3 3%bv eq_refl), (HP4 3 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsC 3 3%bv eq_refl). exact GC3. }
assert (GD4 : getr regs4 4 = w64 (as_tp B)).
{ rewrite (spsw_g regs4 4 4%bv eq_refl), (HP4 4 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsC 4 4%bv eq_refl). exact GC4. }
assert (HROD4 : arodata_okP SEGS RLO RHI B (rdW W4 mem4))
  by exact (spsw_aro ly S W mem md O ly4 S4 W4 mem4 _ [] _ sp0 _ HAR HOin HJ4 HROD).
assert (HROk4 : cmd_ro_ok (rdW W4 mem4)) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HAR4 HROD4).
apply (W_RSO W4 regs4 mem4 md4 SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly4 S4
  (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S) _ HJ4 GD2 ltac:(unfold SPS_FRAME; lia) GD3 GD4 HROD4 HROk4
  ltac:(pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); unfold EV_SUP_POLICY_SET in *; lia)).
intros ly5 S5 W5 regs5 mem5 md5 memX mdX q HJ5 HJc5 KX Q5k Q5a0 Hq64 HqA Hperm5 Ely5 ES5.
subst ly5 S5.
pose proof (proj1 HJ5) as HAR5.
(* rec_shape_of's footprint is empty and it frees nothing: the frame and every block are kept *)
assert (HFRM5 : sps_frame (rdW W5 mem5) sp0 regs).
{ intros j r Hj. pose proof (proj1 (nth_error_Some sps_saved j) ltac:(rewrite Hj; discriminate)) as Hj4.
  cbn [length sps_saved] in Hj4.
  apply (spsw_aval_keep (rdW W4 memX)); [apply (spsw_aval_keep (rdW W4 mem4)); [exact (HFRM4 j r Hj) | intros x _; apply KX]|].
  intros x Hx. pose proof HJc5 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
  apply F1c; [unfold SPS_FRAME in *; lia | unfold SPS_FRAME in *; lia | intros Hf; exact (inFP_nil x Hf)]. }
(* ---- run E: the epilogue (0x8be54 .. j answer 0x8be74) ---- *)
apply (W_EPI W5 regs5 regs mem5 md5 SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly4 S4
  (0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_REC_SHAPE_OF) _ HJ5).
- unfold spZ. rewrite (spsw_g regs5 2 2%bv eq_refl), (Q5k 2 ltac:(spsw_in)).
  rewrite <- (spsw_g regs4 2 2%bv eq_refl). exact GD2.
- unfold SPS_FRAME. fold sp0 in Hslo. lia.
- lia.
- exact Hal16.
- exact HFRM5.
- intros regsE memE mdE HJE KE HGE QE2 QEsav QE10 QE11 QE12 QEk.
pose proof (proj1 HJE) as HARE.
set (k5 := 0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_REC_SHAPE_OF) in *.
assert (XD1 : getr regsE 1 = getr regs 1)
  by (rewrite (spsw_g regsE 1 1%bv eq_refl), (QEsav 1 ltac:(spsw_in)); rewrite <- (spsw_g regs 1 1%bv eq_refl); reflexivity).
assert (SPD : spZ regsE = sp0)
  by (unfold spZ at 1; rewrite QE2; unfold w64, sp0, spZ; apply unsigned_lit_small;
      pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
assert (XD3 : getr regsE 3 = w64 (as_gp B)).
{ rewrite (spsw_g regsE 3 3%bv eq_refl), (QEk 3 ltac:(spsw_in)), (Q5k 3 ltac:(spsw_in)).
  rewrite <- (spsw_g regs4 3 3%bv eq_refl). exact GD3. }
assert (XD4 : getr regsE 4 = w64 (as_tp B)).
{ rewrite (spsw_g regsE 4 4%bv eq_refl), (QEk 4 ltac:(spsw_in)), (Q5k 4 ltac:(spsw_in)).
  rewrite <- (spsw_g regs4 4 4%bv eq_refl). exact GD4. }
assert (XD8 : s0Z regsE = s0Z regs).
{ unfold s0Z. rewrite (spsw_g regsE 8 8%bv eq_refl), (QEsav 8 ltac:(spsw_in)).
  rewrite <- (spsw_g regs 8 8%bv eq_refl). reflexivity. }
assert (GD10 : getr regsE 10 = w64 (rec_slot R)).
{ rewrite QE10, (spsw_g regs5 18 18%bv eq_refl), (Q5k 18 ltac:(spsw_in)), (HP4 18 ltac:(unfold acallee_saved; lia)).
  rewrite <- (spsw_g regsC 18 18%bv eq_refl). exact GC18. }
assert (GD11 : getr regsE 11 = w64 q) by (rewrite QE11; exact Q5a0).
(* every callee-saved register is the entry's at the jump *)
assert (HPA : aregs_preserved regs regsE).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct (Z.eq_dec r 2) as [-> | H2].
  - rewrite <- (spsw_g regsE 2 2%bv eq_refl), <- (spsw_g regs 2 2%bv eq_refl). rewrite QE2.
    unfold w64, sp0, spZ. apply Z_to_bv_bv_unsigned.
  - destruct (in_dec Z.eq_dec r [8; 9; 18]) as [Hs | Hs].
    + apply QEsav. cbv [sps_saved In]. cbv [In] in Hs. tauto.
    + cbv [In] in Hs.
      assert (Hk : In r sps_kept_epi) by (cbv [sps_kept_epi In]; lia).
      assert (Hm : In r sps_kept_mid) by (cbv [sps_kept_mid In]; lia).
      assert (Hm1 : In r sps_kept_mid1) by (cbv [sps_kept_mid1 In]; lia).
      assert (Hp : In r sps_kept_pro) by (cbv [sps_kept_pro In]; lia).
      rewrite (QEk r Hk), (Q5k r Hm), (HP4 r ltac:(unfold acallee_saved; lia)), (QCk r Hm),
        (HP3 r ltac:(unfold acallee_saved; lia)), (QBk r Hm1), (HP2 r ltac:(unfold acallee_saved; lia)).
      exact (QAk r Hp). }
(* ---- the state at the jump, against the earlier states ---- *)
assert (Hn1 : 1 <= n1) by (subst n1; lia).
assert (Hn2 : 1 <= n2) by (subst n2; lia).
assert (H3to4 : forall pn, In pn (ablocks B ly3 S3) -> In pn (ablocks B ly4 S4))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm4)); right; exact Hpn).
assert (HSsplit : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2) \/ In pn F)
  by (intros pn Hpn; apply in_app_or; exact (Permutation_in _ HPermF Hpn)).
assert (HFnot : forall pn, In pn F -> ~ In pn (ablocks B ly2 S2))
  by (intros pn HFi H2; exact (spsw_dup_false ly S W mem md (ablocks B ly2 S2) F pn HAR HPermF H2 HFi)).
assert (Hfresh1 : ~ In (p1, n1) (ablocks B ly2 S2)).
{ intros H2. rewrite Forall_forall in Hfresh3. pose proof (Hfresh3 (p1, n1) H2) as D. cbn [fst snd] in D.
  unfold iv_apart in D. lia. }
assert (Hfresh2 : ~ In (p2, n2) (ablocks B ly3 S3)).
{ intros H3. rewrite Forall_forall in Hfresh4. pose proof (Hfresh4 (p2, n2) H3) as D. cbn [fst snd] in D.
  unfold iv_apart in D. lia. }
assert (Hp1S : In (p1, n1) (ablocks B ly S) -> In (p1, n1) O).
{ intros HS'. destruct (HSsplit _ HS') as [H2 | HFi]; [exfalso; exact (Hfresh1 H2) | exact (HFO _ HFi)]. }
assert (Hp2S : In (p2, n2) (ablocks B ly S) -> In (p2, n2) O).
{ intros HS'. destruct (HSsplit _ HS') as [H2 | HFi]; [exfalso; exact (Hfresh2 (H2to3 _ H2)) | exact (HFO _ HFi)]. }
set (O3 := (p2, n2) :: (p1, n1) :: O1) in *.
assert (HO3S : forall pn, In pn O3 -> In pn (ablocks B ly S) -> In pn O).
{ intros pn [<- | [<- | H1]] HS'; [exact (Hp2S HS') | exact (Hp1S HS') | exact (proj1 (proj1 (HO1 pn) H1))]. }
assert (HO3in4 : forall pn, In pn O3 -> In pn (ablocks B ly4 S4)) by exact (spsw_O_in ly4 S4 _ _ _ HREP4).
assert (HREPD : rec_repA B ly4 S4 (rdW W5 memE) (rec_record R REC_POLICY_SET A) O3).
{ apply (spsw_rec_repA_ext ly4 S4 (rdW W4 mem4) ly4 S4 _ _ _ HREP4 HO3in4).
  assert (K45 : forall a, 0 <= a < alloc_ceiling -> (Exists (in_zr a) TFIB_PROG_STATIC \/
     exists b m, In (b, m) (ablocks B ly4 S4) /\ b <= a < b + req_size m) ->
     rdW W5 memE a = rdW W4 mem4 a).
  { intros a Ha Hc. rewrite KE.
    destruct Hc as [HPs | (b & m & Hbm & Hba)].
    - rewrite (spsw_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc5 (Forall_nil _) (inFP_nil a) HPs). apply KX.
    - replace a with (b + (a - b)) by lia.
      rewrite (spsw_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (a - b) HJc5 Hbm
        (Permutation_in _ (Permutation_sym Hperm5) Hbm) ltac:(lia) (inFP_nil _)).
      apply KX. }
  intros a [Ha | [Ha | ([b m] & Hpn & Ha)]]; cbn [fst snd] in *.
  - apply K45; [unfold A_G_REC, REC_SIZE in Ha; lia | left; exact (spsw_grec_in a Ha)].
  - apply K45; [unfold A_REC_SPILL, SC_SIZE in Ha; lia | left; exact (spsw_spill_in a Ha)].
  - destruct (spsw_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 (HO3in4 _ Hpn)) as (Hb & Hc & _ & Hmr & _).
    apply K45; [lia | right; exists b, m; split; [exact (HO3in4 _ Hpn) | lia]]. }
pose proof HREPD as (QD & HQD & HOQD).
destruct (spsw_old_at _ _ _ _ HQD) as [HOLD HOLDin'].
set (old := spsw_old QD) in *.
assert (HOLDin : forall pn, In pn (ablocks B ly4 S4) -> fst pn = old -> In pn O3).
{ intros pn Hpn Hf. unfold old, spsw_old in Hf. destruct (l_answer QD) as [an|] eqn:Ean.
  - pose proof (HOLDin' an eq_refl) as Han. apply HOQD in Han.
    rewrite (spsw_same_start ly4 S4 W4 mem4 md4 pn an HAR4 Hpn (HO3in4 _ Han) Hf). exact Han.
  - destruct pn as [b m]. destruct (spsw_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 Hpn) as (Hb & _). cbn [fst] in Hf. lia. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ unfold old, spsw_old. destruct (l_answer QD) as [an|] eqn:Ean; [|lia].
  pose proof (HOLDin' an eq_refl) as Han. apply HOQD in Han. destruct an as [a1 a2].
  destruct (spsw_blk_bounds ly4 S4 W4 mem4 md4 a1 a2 HAR4 (HO3in4 _ Han)) as (Hb0 & Hb1 & _ & _ & Hr1). cbn [fst]. lia. }
assert (HRODE : arodata_okP SEGS RLO RHI B (rdW W5 memE))
  by exact (spsw_aro ly S W mem md O ly4 S4 W5 memE _ [] _ sp0 _ HAR HOin HJE HROD).
assert (MLEJ : mo_le MT S S4 (XM_RECORD MT R + XM_ARG_S MT format + XM_ARG_S MT place))
  by exact (mle_station MT S S3 S4 _ _ MTL (mle_station MT S S2 S3 _ _ MTL MLE1 MLE3) MLE4).
pose proof HJE as (_ & _ & _ & _ & _ & HfrE & HnevE & _).
assert (HachE : achain ly4 (rdW W5 memE) (sp0 + 0) (s0Z regsE) ch).
{ rewrite Z.add_0_r, XD8. apply (spsw_achain_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJE).
  - intros a Ha. exact (proj2 (HFPlow a Ha)).
  - exact Hch. }
(* ---- the tail jump into answer (0x8be74): answer runs at the entry's sp and returns to the entry's ra ---- *)
eapply SRr_mono.
{ eapply (W_CALLF W5 regsE memE (w64 (BASE + AF_answer)) SUP_POLICY_SET_STK sp0 (spsw_FP O) ly S W mem md [] ly4 S4
    mdE k5 ANSWER_STK _ EV_ANSWER 0 (getr regsE 1) ch _ HJE ltac:(rewrite SPD; lia) eq_refl ltac:(lia) ltac:(lia)
    ltac:(lia) XD3 XD4 eq_refl ltac:(rewrite XD1; exact Hra) ltac:(rewrite XD1; exact Hra4) HachE).
  - intros HPREA.
    pose proof (TANSWER fx ly4 S4 W5 regsE memE mdE ch (rec_slot R) q old e sps_shape true
      (rec_record R REC_POLICY_SET A) O3 HPREA HFRM) as T.
    cbv zeta in T. unfold apost_baseF in T. apply T; clear T.
    + rewrite HfrE. cbn [app]. exact HFR8.
    + exact HRODE.
    + exact (cmd_ro_ok_of_aro _ _ _ _ _ HARE HRODE).
    + exact GD10.
    + destruct (spsw_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
      rewrite Hs. unfold A_REC_SPILL. lia.
    + exact GD11.
    + exact Hq64.
    + rewrite QE12. reflexivity.
    + exact HREPD.
    + exact HOLD.
    + exact Hold64.
    + intros _. split; [|exact spsw_fits].
      apply (spsw_argA_kept _ _ (rdW W5 mem5)); [exact (HqA _)|]. intros i Hi. apply KE.
    + intros _ _. exact (spsw_answer_slot R REC_POLICY_SET A).
    + unfold EV_SUP_POLICY_SET, k5 in *. lia.
    + rewrite <- HM. pose proof (LA0 format). pose proof (LA0 place).
      unfold LIVE_SUP_POLICY_SET in HLIVE. lia.
    + apply (mok_station MT S S4 (XM_SUP_POLICY_SET MT R format place) _ _ MTL HMOK MLEJ (XN0 _)).
      unfold XM_SUP_POLICY_SET. rewrite HM. lia.
  - intros a Ha.
    apply inFP_cons in Ha as [Ha | Ha]; [apply spsw_awr_grec; unfold OFF_ANSWER, REC_SIZE in *; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [apply spsw_awr_grec; unfold OFF_STATE, REC_SIZE in *; lia|].
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba).
    apply spsw_in_filter in Hbm as [Hbm _].
    destruct (in_dec RecBLemmas.recb_pair_dec (b, m) O) as [HbO | HbnO].
    + exact (spsw_awr_blk _ _ _ _ _ _ _ _ b m a HbO (HO3in4 _ Hbm) Hba).
    + right; right; left. exists b, m. split; [exact (HO3in4 _ Hbm)|].
      split; [intros HbS; exact (HbnO (HO3S _ Hbm HbS)) | exact Hba].
  - intros ly6' S6' W6' regs6' mem6' md6' _ a Ha Hw _. exfalso.
    assert (Hlo : a < alloc_ceiling).
    { apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_ANSWER in Ha; lia|].
      apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|].
      destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba).
      apply spsw_in_filter in Hbm as [Hbm _].
      destruct (spsw_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 (HO3in4 _ Hbm)) as (Hb & Hc & _). lia. }
    fold sp0 in Hw. lia. }
cbv beta. intros W6 c6 _ (fx6 & ly6 & S6 & regs6 & mem6 & md6 & -> & HFX6 & HCSR6 & HJF & HJans & HPA6 & HQ6).
cbv zeta in HQ6.
destruct HQ6 as (p1' & p2' & O' & Hq10 & Hq2a & Hp12 & Hfr12 & Hbl & HrepF & HO' & Hstr & HBB6 & Hmle).
set (t := snd (rec_answer (rec_record R REC_POLICY_SET A) e sps_shape true)) in *.
set (nT := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJans) as HAR6.
assert (Hnew12 : forall pn, In pn (ablocks B ly S) -> (pn = (p1', nT) \/ pn = (p2', nT)) -> In pn O).
{ intros pn HS' Heq. destruct (HSsplit _ HS') as [H2 | HFi]; [|exact (HFO _ HFi)].
  pose proof (H3to4 _ (H2to3 _ H2)) as H4.
  destruct (Z.eq_dec (fst pn) old) as [Ho | Ho]; [exact (HO3S _ (HOLDin _ H4 Ho) HS')|].
  exfalso. destruct (Hfr12 pn H4 Ho) as [N1 N2]. destruct Heq as [Heq | Heq]; [exact (N1 Heq) | exact (N2 Heq)]. }
unfold apost_baseF. exists fx6, ly6, S6, regs6, mem6, md6.
split; [rewrite XD1; reflexivity|].
split; [exact HFX6|]. split; [exact HCSR6|].
split.
{ apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF).
  unfold EV_SUP_POLICY_SET, k5. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPA HPA6)|].
exists (fst (rec_answer (rec_record R REC_POLICY_SET A) e sps_shape true)), t, p2', O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact Hq10|]. split; [exact Hq2a|]. split; [exact HrepF|].
split.
{ intros pn Hpn. destruct (in_dec RecBLemmas.recb_pair_dec pn (ablocks B ly S)) as [HS' | HnS]; [left | right; exact HnS].
  apply HO' in Hpn as [[H3 _] | ->]; [exact (HO3S pn H3 HS') | exact (Hnew12 _ HS' (or_introl eq_refl))]. }
split; [apply Hbl; right; right; reflexivity|].
split; [intros pn HS' HnO Heq; subst pn; exact (HnO (Hnew12 _ HS' (or_intror eq_refl)))|].
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hf & Hpn).
  pose proof (spsw_O_in ly6 S6 _ _ _ HrepF pn Hpn) as Hpn6.
  pose proof (proj2 (Hbl (p2', nT)) (or_intror (or_intror eq_refl))) as Hq6.
  pose proof (spsw_same_start ly6 S6 W6 mem6 md6 pn (p2', nT) HAR6 Hpn6 Hq6 Hf) as ->.
  apply HO' in Hpn as [[Hpn1 Hfo] | Heq];
  [exact (proj2 (Hfr12 _ (HO3in4 _ Hpn1) Hfo) eq_refl) | injection Heq as Heq; exact (Hp12 (eq_sym Heq))]. }
split; [exact Hstr|].
split.
{ intros pn Hpn HnO.
  assert (H2 : In pn (ablocks B ly2 S2)).
  { destruct (HSsplit _ Hpn) as [H | H]; [exact H | exfalso; exact (HnO (HFO _ H))]. }
  pose proof (H3to4 _ (H2to3 _ H2)) as H4.
  assert (Ho : fst pn <> old) by (intros Hf; exact (HnO (HO3S _ (HOLDin _ H4 Hf) Hpn))).
  assert (H6 : In pn (ablocks B ly6 S6)) by (apply Hbl; left; split; [exact H4 | exact Ho]).
  split; [exact H6|].
  pose proof (proj2 (Hbl (p2', nT)) (or_intror (or_intror eq_refl))) as Hq6.
  destruct pn as [b m]. cbn [fst snd].
  assert (Hne : (b, m) <> (p2', nT)) by exact (proj2 (Hfr12 (b, m) H4 Ho)).
  destruct (spsw_blk_bounds ly6 S6 W6 mem6 md6 b m HAR6 H6) as (_ & _ & Hm0 & Hmr & _).
  destruct (spsw_blk_bounds ly6 S6 W6 mem6 md6 p2' nT HAR6 Hq6) as (_ & _ & Hn0 & Hnr & _).
  unfold iv_apart. destruct (spsw_blk_apart ly6 S6 W6 mem6 md6 b m p2' nT HAR6 H6 Hq6 Hne); lia. }
split.
{ intros pn Hpn. apply Hbl in Hpn as [[H4 Hf] | [-> | ->]].
  - apply (Permutation_in _ Hperm4) in H4. destruct H4 as [<- | H3].
    + right; left. apply HO'. left. split; [left; reflexivity | exact Hf].
    + apply (Permutation_in _ Hperm3) in H3. destruct H3 as [<- | H2].
      * right; left. apply HO'. left. split; [right; left; reflexivity | exact Hf].
      * destruct (in_dec RecBLemmas.recb_pair_dec pn O1) as [H1 | H1n].
        -- right; left. apply HO'. left. split; [right; right; exact H1 | exact Hf].
        -- left. split.
           ++ apply (Permutation_in _ (Permutation_sym HPermF)). apply in_or_app. left. exact H2.
           ++ intros HinO. apply H1n. apply HO1. split; [exact HinO | intros HFi; exact (HFnot _ HFi H2)].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ unfold LIVE_SUP_POLICY_SET. rewrite HM. fold t. lia. }
apply (mle_weaken MT S S6 _ _ MTL (mle_station MT S S4 S6 _ _ MTL MLEJ Hmle)).
unfold XM_SUP_POLICY_SET. rewrite HM. fold t. lia.
Qed.

End e.
End f.
End d.
