(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_reset (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry 0x8bd58, 22 instructions): tsup_reset_spec of a Theorem Labs lane's lib/B/Prog/sup_reset_c.v
   (a working branch fc8bcbd8b42), proved over its callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c,
   each taken at every FP state as the statement states them; the post is apost_baseF, answer's (the tail jump).

   The B re-walk of the A walk lib/A/Prog/sup_reset.v (a working branch 3cc8391594b): A inlines record()
   (two arms, rec_calls_free on the spill arm) and the stores of fn, nargs and args[0] with their 4 inline checks,
   and calls xstrdup; B calls record() and arg_s(), which carry those parts and checks in their own contracts. The
   segments (lib/B/Prog/sup_reset_aux.v has the code):
     run A  0x8bd58 .. 0x8bd70  the 32-byte frame (ra, s0, s1), s0 := which, a0 := 10, jal record
     run B  0x8bd74 .. 0x8bd7c  s1 := the slot, a1 := which, jal arg_s
     run C  0x8bd80 .. 0x8bd8c  a0 := "supervisor_reset" (0x21e00), a1 := 16, jal rec_shape_of
     run D  0x8bd90 .. 0x8bdac  a2 := 1, a1 := the shape, a0 := the slot, ra / s0 / s1 back, sp += 32, j answer
   Each run is PaCallRun's plain symbolic run to the call (paj_run_shc), each call is cl_callS_wide (record, arg_s:
   their footprints are g_rec / record.spill fields and, on record's spill arm, recorder blocks) or cl_callS_na
   (rec_shape_of: no footprint), the frame is carried across each call with jafter_call_keep_pi, and the tail jump
   runs answer at this function's entry sp, whose journal joins the walk's with ajournal_sub_wide.
   Report / trap edges: the function has no branch, no `jal __asan_report_*` and no unimp / ebreak
   (lib/B/Prog/sup_reset_aux.v:15-31, measured with capstone), so there is no edge to refute here; the slot's
   checks and traps are record's and arg_s's, refuted in their contracts.

   Section hypotheses beyond the statement's: the per-binary record CmdBSyms (HB), the meter's laws (MTL), the
   program functions' call targets (SIGP, CmdObj.v's cmd_sig_prog), and the per-binary image facts in the form of
   a Theorem Labs lane's lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib (a working branch fc8bcbd8b42), at this walk's abstract segments.
   The per-binary facts the walk uses are a Theorem Labs lane's CmdRecRo.v / CmdRecRest.v lemmas over them, by exact (CMD_RO_IN,
   cmd_ro_ok_of_aro, cmd_ro_prog_apart, cmd_prog_img, cmd_atail_kept, cmd_rodata_kept); a closing file at the
   pinned image (PI := PB_cmd) discharges cmd_img_facts_tfib by a Theorem Labs lane's lemma of that name. The record and allocator
   lemmas recb_prog_unowned_m, recb_heap_noimg_m, recb_grec_in, recb_spill_in, recb_pair_dec and lay_blocks_in are
   a Theorem Labs lane's lib/B/Prog/RecBLemmas.v; rca_in_answer and rca_sig_record are a Theorem Labs lane's lib/B/Prog/CmdRecAns.v. *)
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
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c mix_call_c hand_back_c record_c arg_s_c rec_shape_of_c answer_c sup_reset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts RecBLemmas CmdRecAns sup_reset_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the representation's readers (lib/A/Prog/sup_reset.v:39-136, the same CmdRep forms) ---------- *)

Lemma srb_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma srb_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma srb_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (srb_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma srb_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (srb_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (srb_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (srb_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (srb_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma srb_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (srb_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (srb_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (srb_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma srb_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
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
    + apply (srb_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (srb_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (srb_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (srb_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (srb_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma srb_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (srb_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma srb_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma srb_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma srb_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma srb_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
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
    + apply (srb_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (srb_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (srb_in_calls Q i P pn EP Hpn).
    + apply (srb_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply srb_in_spill. exact Hpn.
  - apply (srb_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply rca_in_answer. exact Hpn.
  - apply (srb_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply srb_in_reply. exact Hpn.
  - apply (srb_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

(* the recorder's answer field holds 0 or the start of one of its blocks *)
Definition srb_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma srb_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  aval_mem rd (A_G_REC + OFF_ANSWER) 8 (srb_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
  intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold srb_old. split.
  - unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
    [exact (proj1 HA) | exact HA].
  - intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
Qed.

(* the slot record() returns (record_c.v rec_slot): an entry of g_rec's table, or record.spill *)
Lemma srb_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
  (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL.
Proof.
  intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [left | right; reflexivity].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
Qed.

(* the slot fact answer's pre asks (answer_c.v:129-131) *)
Lemma srb_answer_slot : forall R x,
(exists k, nth_error (r_calls (rec_record R SRB_FN [x])) k = Some (SRB_FN, [x]) /\
   rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R = A_REC_SPILL /\ (SRB_FN, [x]) = r_spill (rec_record R SRB_FN [x])).
Proof.
intros R x. unfold rec_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L].
- left. exists (length (r_calls R)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

(* the footprint of the statement (sup_reset_c.v:104) *)
Definition srb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma srb_FP_pos : forall O, (forall pn, In pn O -> 0 < fst pn) -> Forall (fun r => 0 < fst r) (srb_FP O).
Proof.
intros O HO. unfold srb_FP. constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
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
(* the statement's callees (each at every FP state) and object bridge (sup_reset_c.v:74-78) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses of a Theorem Labs lane's RULING-STMT.md section 1: the per-binary allocator record (a Theorem Labs lane's
   lib/B/YF0m.v), the meter's laws, the program functions' call targets (lib/B/Prog/CmdObj.v) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary image facts (a Theorem Labs lane's lib/B/Prog/CmdRecBase.v cmd_img_facts, a working branch fc8bcbd8b42): a Theorem Labs lane proves
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
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.

(* ---------- the allocator's blocks ---------- *)

Lemma srb_O_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HQ & HOQ) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HOQ pn) Hpn)). Qed.

Lemma srb_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

Lemma srb_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma srb_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (recb_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (srb_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (srb_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (srb_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* a live block is listed once *)
Lemma srb_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
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
destruct (srb_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* ---------- the walk's footprint and what a journal keeps ---------- *)

Lemma srb_inFP_cases : forall O a, inFP (srb_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold srb_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. exact (recb_grec_in a Ha).
- left. exact (recb_spill_in a Ha).
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.

Lemma srb_static_low : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> 0x10000 <= a < 0x606000.
Proof. intros a Ha. exact (pa_img_range a (cmd_prog_img a Ha)). Qed.

Lemma srb_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (srb_FP O) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
destruct (srb_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)].
- pose proof (srb_static_low a HP). lia.
- destruct (srb_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (H4 & Hc & _). lia.
Qed.

(* arodata_okP along the walk's journal (cmd_rodata_kept: the footprint is statics and the recorder's blocks) *)
Lemma srb_aro : forall ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp STK,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp (srb_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O lyc Sc Wc memc mdc own k sp STK HAR HO HJ HR.
apply (cmd_rodata_kept ly S W mem md lyc Sc Wc memc mdc STK sp (srb_FP O) own k HAR HJ); [|exact HR].
intros a Ha. destruct (srb_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)]; [left; exact HP|].
right. exists b, n. split; [apply in_or_app; left; exact (HO _ Hin) | exact Hb].
Qed.

Lemma srb_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

Lemma srb_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (recb_prog_unowned_m (PI := PI) B HB cmd_prog_img a HP) as (H1 & H2 & H3).
exact (srb_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

Lemma srb_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

Lemma srb_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
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
Lemma srb_awr_static : forall STK sp O bl0 blc fr0 ly own a, Exists (in_zr a) TFIB_PROG_STATIC -> inFP (srb_FP O) a ->
awr_byte SEGS B STK sp (srb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a HP HF.
right; right; right; right; left. split; [exact HF|]. split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

Lemma srb_awr_grec : forall STK sp O bl0 blc fr0 ly own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp (srb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply srb_awr_static; [exact (recb_grec_in a Ha)|].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma srb_awr_spill : forall STK sp O bl0 blc fr0 ly own a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp (srb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply srb_awr_static; [exact (recb_spill_in a Ha)|].
exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

(* a byte of the slot record() returned *)
Lemma srb_awr_slot : forall STK sp O bl0 blc fr0 ly own R a, (length (r_calls R) <= 16)%nat ->
rec_slot R <= a < rec_slot R + CALL_SIZE -> awr_byte SEGS B STK sp (srb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own R a HL Ha. destruct (srb_slot_bounds R HL) as [Hs | Hs].
- apply srb_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply srb_awr_spill. rewrite Hs in Ha. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma srb_awr_blk : forall STK sp O bl0 blc fr0 ly own b n a, In (b, n) O -> In (b, n) blc ->
b <= a < b + req_size n -> awr_byte SEGS B STK sp (srb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own b n a HO Hc Ha. right; left. split.
- unfold srb_FP. apply inFP_cons. right. apply inFP_cons. right.
  replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b n (a - b)); [exact HO | lia].
- exists b, n. split; [exact Hc | exact Ha].
Qed.

(* ---------- the string argument ---------- *)

(* the bytes of a string argument decide astr_argA's reader part: its other parts name no reader *)
Lemma srb_argA_kept : forall ly1 S1 (rd rd' : reader) ro O1 p v, astr_argA B ly1 S1 rd ro O1 p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly1 S1 rd' ro O1 p (Some v).
Proof.
intros ly1 S1 rd rd' ro O1 p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [|split; [exact Hl | exact Hr]].
apply (srb_str_keep rd); [exact Hs|]. intros x Hx. replace x with (p + (x - p)) by lia. apply K. lia.
Qed.

(* a string argument's bytes lie below alloc_ceiling: a block's, or the image's *)
Lemma srb_argA_low : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 p v, AR SEGS B ly1 S1 W1 mem1 md1 ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 p (Some v) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= p + i < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 O1 p v HAR H i Hi. cbn [astr_argA] in H. pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
- destruct Hblk as (b & m & Hin & Hb1 & Hb2).
  destruct (srb_blk_bounds ly1 S1 W1 mem1 md1 b m HAR Hin) as (Hb & Hc & _ & Hmr & _). lia.
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia.
Qed.

(* the pointer itself (caller's s0 at the program calls) lies below alloc_ceiling *)
Lemma srb_pw_low : forall ly S (W : world SEGS) mem md O pw which, AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pw which -> 0 <= pw < alloc_ceiling.
Proof.
intros ly S W mem md O pw which HAR H. pose proof asan_consts as (C1 & _). destruct which as [x|].
- pose proof (srb_argA_low ly S W mem md O pw x HAR H 0 ltac:(lia)). lia.
- cbn [astr_argA] in H. subst pw. lia.
Qed.

(* the string argument from the entry to a later state: its block (none of the recorder's) is live there with its
   bytes, or its read-only bytes are the image's at both states; its word tail is kept (cmd_atail_kept) *)
Lemma srb_arg_kept : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O pw x,
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
    * apply (srb_str_keep (rdW W mem)); [exact HS|]. intros a Ha. apply HK. lia.
    * split; [exact Hlen|]. left. split; [|apply Forall_nil].
      exists b, k. split; [exact (Hblk (b, k) Hbk HnO) | split; [exact Hble | exact Hhi]].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc b k (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | left; split; [exact Hbk | split; [exact (Hblk (b, k) Hbk HnO) | lia]] | exact HT].
- split.
  + split; [exact Hp0|]. split.
    * apply (srb_str_keep (rdW W mem)); [exact HS|]. intros a Ha.
      destruct (Hro (a - pw) ltac:(lia)) as (Hr & Ho & He). replace a with (pw + (a - pw)) by lia.
      rewrite (HROc _ Hr Ho He), (HRO _ Hr Ho He). reflexivity.
    * split; [exact Hlen|]. right. split; [exact Hro | exact Hck].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc 0 0 (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | right | exact HT].
    destruct (Hro (Z.of_nat (length x)) ltac:(lia)) as (Hr & Ho & _). split; [exact Hr | exact Ho].
Qed.

(* rec_repA at a state whose reader agrees on g_rec, record.spill and the recorder's blocks *)
Lemma srb_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (srb_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

(* a block answer frees: the recorder's block whose start is the old answer (answer_c.v:138) *)
Lemma srb_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* after a symbolic run the model term grows: name it *)
Ltac srb_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.

(* ---------- the walk ---------- *)
Theorem tsup_reset_holds : tsup_reset_spec B MT.
Proof.
unfold tsup_reset_spec.
intros ly S W regs mem md ch pw which R O HPRE HFRM HROD HRO H10 Hpw HARG HTL HREP HFR8 HEV HLIVE HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SUP_RESET_STK = 16592) by (vm_compute; reflexivity).
assert (HRS : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HAS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HSS : REC_SHAPE_OF_STK = 8288) by (vm_compute; reflexivity).
assert (HNS : ANSWER_STK = 16592) by (vm_compute; reflexivity).
rewrite HST in Hslo.
set (sp0 := spZ regs) in *.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (srb_O_in ly S _ R O HREP).
assert (HOpos : forall pn, In pn O -> 0 < fst pn).
{ intros [b n] Hpn. destruct (srb_blk_bounds ly S W mem md b n HAR (HOin _ Hpn)) as (Hb & _). cbn. lia. }
assert (HFPpos : Forall (fun r => 0 < fst r) (srb_FP O)) by exact (srb_FP_pos O HOpos).
assert (HFPlow : forall a, inFP (srb_FP O) a -> 0 <= a < alloc_ceiling)
  by (intros a Ha; exact (srb_FP_low ly S W mem md O a HAR HOin Ha)).
assert (Hpwl : 0 <= pw < alloc_ceiling) by exact (srb_pw_low ly S W mem md O pw which HAR HARG).
pose proof HREP as (Q0 & HQ0 & HOQ0).
pose proof HQ0 as (_ & _ & _ & (HC1 & _) & _).
assert (EFP : (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O = srb_FP O)
  by reflexivity.
rewrite EFP.
(* the meter's parts are nonnegative *)
assert (XR0 : 0 <= XM_RECORD MT R).
{ unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL). destruct (Nat.ltb _ _); lia. }
assert (XA0 : 0 <= XM_ARG_S MT which).
{ unfold XM_ARG_S, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (LN0 : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (LA0 : 0 <= LIVE_ARG_S which) by (unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
(* ---- the entry seed and run A: 0x8bd58 .. jal record (0x8bd70) ---- *)
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (fold sp0; lia).
assert (Hp32 : forall a, spZ regs - SRB_FRAME <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; fold sp0 in Ha |- *; rewrite HST; unfold SRB_FRAME in Ha; lia).
pose proof (srb_seed_entry W regs mem Hsp Hal16 Hp32) as HS.
pose proof (ajournal_init SEGS B SUP_RESET_STK (srb_FP O) ly S W regs mem md ch HPRE) as HJ.
set (E := srb_E regs) in *.
assert (HEI : img_env VAL A_LIM E) by exact (srb_E_img regs).
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regs rr)
  by (intros kk rr Hkk; exact (srb_E_reg regs kk rr Hkk)).
assert (AG0 : env_agree 32 (Ereg regs (srb_extra regs)) E) by exact (srb_E_agree regs).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at, w64. change (BASE + AF_sup_reset) with (BASE + SRB_E).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msA, mat into matA, HF into HFA, HFr into HFrA, HG into HGA.
pmkst HS. srb_md.
prreg HS (1%bv : bv 5) PA1. prreg HS (2%bv : bv 5) PA2. prreg HS (3%bv : bv 5) PA3. prreg HS (4%bv : bv 5) PA4.
prreg HS (8%bv : bv 5) PA8. prreg HS (10%bv : bv 5) PA10.
assert (GA2 : spZ (ms_regs msA) = sp0 + -32)
  by (unfold spZ at 1; rewrite PA2, Usp; apply unsigned_lit_small; lia).
assert (GA3 : getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite PA3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GA4 : getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite PA4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GA8 : getr (ms_regs msA) 8 = w64 pw) by (rewrite PA8, (EE 10%nat 10%bv eq_refl); exact H10).
assert (GA10 : getr (ms_regs msA) 10 = w64 SRB_FN) by (rewrite PA10; reflexivity).
assert (GA1r : YK0s.ret_ok (getr (ms_regs msA) 1))
  by (rewrite PA1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GA1a : 4096 <= bv_unsigned (getr (ms_regs msA) 1))
  by (rewrite PA1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
(* run A wrote only the frame *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W (ms_mem msA) a = rdW W mem a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem msA) (fun a => sp0 - 32 <= a < sp0) HFrA).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ) as HARA.
assert (HROA : arodata_okP SEGS RLO RHI B (rdW W (ms_mem msA)))
  by exact (srb_aro ly S W mem md O ly S W (ms_mem msA) _ [] 0 sp0 _ HAR HOin HJ HROD).
assert (HREPA : rec_repA B ly S (rdW W (ms_mem msA)) R O).
{ apply (srb_rec_repA_ext ly S (rdW W mem) ly S _ R O HREP HOin).
  intros a [Ha | [Ha | ([b n] & Hpn & Ha)]]; cbn [fst snd] in *.
  - apply KA; unfold A_G_REC, REC_SIZE in Ha; lia.
  - apply KA; unfold A_REC_SPILL, SC_SIZE in Ha; lia.
  - destruct (srb_blk_bounds ly S W mem md b n HAR (HOin _ Hpn)) as (Hb & Hc & _ & Hmr & _). apply KA; lia. }
(* ---- the call of record(10) (0x8bd70) ---- *)
rewrite (rca_sig_record (PI := PI) SIGP).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs msA) (ms_mem msA) _ SUP_RESET_STK sp0 (srb_FP O) ly S W mem md [] ly S _ 0
    RECORD_STK _ (EV_RECORD R) (-32) (getr (ms_regs msA) 1) [] _ HJ GA2 eq_refl ltac:(lia)
    ltac:(rewrite HRS; lia) ltac:(rewrite HRS, HST; lia) GA3 GA4 eq_refl GA1r GA1a
    ltac:(apply achain_low; unfold s0Z; rewrite GA8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1. pose proof (TRECORD fx ly S W (ms_regs msA) (ms_mem msA) _ [] SRB_FN R O HPRE1) as T.
    unfold apost_base in T. apply T.
    + exact HROA.
    + exact GA10.
    + unfold SRB_FN, REC_FN_COUNT. lia.
    + exact HREPA.
    + unfold EV_SUP_RESET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in HEV. lia.
    + apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_RESET. pose proof (XN0 (snd (sup_reset_m R which))). lia.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { apply srb_awr_grec. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (srb_awr_slot _ _ _ _ _ _ _ _ R a HC1). unfold CALL_SIZE. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
    exact (srb_awr_blk _ _ _ _ _ _ _ _ b n a Hbn (HOin _ Hbn) Hba).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    assert (Hlo : 0 <= a < alloc_ceiling).
    { apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
      apply inFP_cons in Ha as [Ha | Ha].
      { destruct (srb_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
        rewrite Hs in Ha. unfold A_REC_SPILL in Ha. lia. }
      destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
      destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
      destruct (srb_blk_bounds ly S W mem md b n HAR (HOin _ Hbn)) as (Hb & Hc & _). lia. }
    rewrite HST in Hw. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
destruct HK2 as (F & O1 & R10 & HPermF & HFlen & HFO & HREP1 & HO1 & HBB1 & MLE1).
pose proof (proj1 HJ2) as HAR2.
rewrite PA1.
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc2 | exact HJ2 | exact Usp | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. cbn in Ha.
  assert (Hlo : a < alloc_ceiling).
  { apply inFP_cons in HFa as [HFa | HFa]; [unfold A_G_REC, OFF_NCALLS in HFa; lia|].
    apply inFP_cons in HFa as [HFa | HFa].
    { destruct (srb_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
      rewrite Hs in HFa. unfold A_REC_SPILL in HFa. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a HFa)|].
    destruct (inFP_ablocks_fp_inv O a HFa) as (b & n & Hbn & Hba).
    destruct (srb_blk_bounds ly S W mem md b n HAR (HOin _ Hbn)) as (Hb & Hc & _). lia. }
  lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 35)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (A39 : ew E2 39 = getr regs2 10) by (rewrite HE2; reflexivity).
assert (AG2 : env_agree 32 (Ereg regs (srb_extra regs)) E2)
  by (rewrite HE2; apply (env_agree_havoc_ge 32 35); [lia | exact AG0]).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by lia; exact Usp).
(* ---- run B: 0x8bd74 .. jal arg_s (0x8bd7c) ---- *)
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msB, mat into matB, HF into HFB, HFr into HFrB, HG into HGB.
pmkst HS. srb_md.
prreg HS (1%bv : bv 5) PB1. prreg HS (2%bv : bv 5) PB2. prreg HS (3%bv : bv 5) PB3. prreg HS (4%bv : bv 5) PB4.
prreg HS (8%bv : bv 5) PB8. prreg HS (10%bv : bv 5) PB10. prreg HS (11%bv : bv 5) PB11.
assert (GB2 : spZ (ms_regs msB) = sp0 + -32)
  by (unfold spZ at 1; rewrite PB2, Usp2; apply unsigned_lit_small; lia).
assert (GB3 : getr (ms_regs msB) 3 = w64 (as_gp B))
  by (rewrite PB3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GB4 : getr (ms_regs msB) 4 = w64 (as_tp B))
  by (rewrite PB4, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GB8 : getr (ms_regs msB) 8 = w64 pw)
  by (rewrite PB8, OLD2 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (GB10 : getr (ms_regs msB) 10 = w64 (rec_slot R)) by (rewrite PB10, A39; exact R10).
assert (GB11 : getr (ms_regs msB) 11 = w64 pw)
  by (rewrite PB11, OLD2 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (GB1r : YK0s.ret_ok (getr (ms_regs msB) 1))
  by (rewrite PB1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GB1a : 4096 <= bv_unsigned (getr (ms_regs msB) 1))
  by (rewrite PB1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W2 (ms_mem msB) a = rdW W2 mem2 a).
{ apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) mem2 (ms_mem msB) (fun a => sp0 - 32 <= a < sp0) HFrB).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ2) as HARB.
assert (HROB : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem msB)))
  by exact (srb_aro ly S W mem md O ly2 S2 W2 (ms_mem msB) _ [] _ sp0 _ HAR HOin HJ2 HROD).
assert (HROkB : cmd_ro_ok (rdW W2 (ms_mem msB))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARB HROB).
assert (HO1in : forall pn, In pn O1 -> In pn (ablocks B ly2 S2)) by exact (srb_O_in ly2 S2 _ _ O1 HREP1).
assert (HREPB : rec_repA B ly2 S2 (rdW W2 (ms_mem msB)) (rec_record R SRB_FN []) O1).
{ apply (srb_rec_repA_ext ly2 S2 (rdW W2 mem2) ly2 S2 _ _ O1 HREP1 HO1in).
  intros a [Ha | [Ha | ([b n] & Hpn & Ha)]]; cbn [fst snd] in *.
  - apply KB; unfold A_G_REC, REC_SIZE in Ha; lia.
  - apply KB; unfold A_REC_SPILL, SC_SIZE in Ha; lia.
  - destruct (srb_blk_bounds ly2 S2 W2 mem2 md2 b n HAR2 (HO1in _ Hpn)) as (Hb & Hc & _ & Hmr & _). apply KB; lia. }
(* the blocks of the entry that are none of the recorder's are live after record, with their bytes *)
assert (HlivB : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn HnO. apply (Permutation_in _ HPermF) in Hpn. apply in_app_or in Hpn as [H | H]; [exact H|].
  exfalso. exact (HnO (HFO _ H)). }
assert (HbytB : forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k ->
  rdW W2 (ms_mem msB) a = rdW W mem a).
{ intros b k a Hbk HnO Ha. pose proof (HlivB _ Hbk HnO) as Hbk2.
  destruct (srb_blk_bounds ly S W mem md b k HAR Hbk) as (Hb & Hbc & Hk0 & Hkr & _).
  rewrite (KB a ltac:(lia) ltac:(lia)).
  replace a with (b + (a - b)) by lia.
  rewrite (srb_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (a - b) HJc2 Hbk Hbk2 ltac:(lia)).
  - rewrite KA by lia. reflexivity.
  - intros HFa. apply inFP_cons in HFa as [HFa | HFa].
    { apply (recb_heap_noimg_m (PI := PI) B ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. apply recb_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in HFa as [HFa | HFa].
    { apply (recb_heap_noimg_m (PI := PI) B ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. destruct (srb_slot_bounds R HC1) as [Hs | Hs].
      - apply recb_grec_in. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      - apply recb_spill_in. rewrite Hs in HFa. unfold A_REC_SPILL, SC_SIZE in *. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exact (inFP_nil _ HFa)|].
    destruct (inFP_ablocks_fp_inv O _ HFa) as (b' & n' & Hbn & Hba).
    destruct (recb_pair_dec (b, k) (b', n')) as [Eq | Hne]; [apply HnO; rewrite Eq; exact Hbn|].
    destruct (srb_blk_bounds ly S W mem md b' n' HAR (HOin _ Hbn)) as (_ & _ & _ & Hnr' & _).
    destruct (srb_blk_apart ly S W mem md b k b' n' HAR Hbk (HOin _ Hbn) Hne); lia. }
assert (HARGB : forall x, which = Some x ->
  astr_argA B ly2 S2 (rdW W2 (ms_mem msB)) (in_roP SEGS RLO RHI) [] pw (Some x) /\
  atail_vis SEGS W2 (ms_mem msB) (pw + Z.of_nat (length x))).
{ intros x Hx. rewrite Hx in HARG.
  exact (srb_arg_kept ly S W mem md ly2 S2 W2 (ms_mem msB) _ O pw x HAR HARB HROD HROB HlivB HbytB HARG (HTL x Hx)). }
(* ---- the call of arg_s(slot, which) (0x8bd7c) ---- *)
rewrite (srb_sig_arg_s SIGP).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W2 (ms_regs msB) (ms_mem msB) _ SUP_RESET_STK sp0 (srb_FP O) ly S W mem md [] ly2 S2 _ _
    ARG_S_STK _ EV_ARG_S (-32) (getr (ms_regs msB) 1) [] _ HJ2 GB2 eq_refl ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, HST; lia) GB3 GB4 eq_refl GB1r GB1a
    ltac:(apply achain_low; unfold s0Z; rewrite GB8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1. pose proof (TARG_S fx ly2 S2 W2 (ms_regs msB) (ms_mem msB) _ [] (rec_slot R) pw SRB_FN [] which R O1 HPRE1)
      as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROB.
    + exact HROkB.
    + exact GB10.
    + exact GB11.
    + reflexivity.
    + exact HREPB.
    + left. destruct which as [x|]; [exact (proj1 (HARGB x eq_refl)) | cbn [astr_argA] in HARG |- *; exact HARG].
    + intros x Hx. exact (proj2 (HARGB x Hx)).
    + pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
      unfold EV_SUP_RESET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + pose proof (LN0 (snd (sup_reset_m R which))). unfold LIVE_SUP_RESET in HLIVE. lia.
    + apply (mok_station MT S S2 (XM_SUP_RESET MT R which) (XM_RECORD MT R) _ MTL HMOK MLE1 XA0).
      unfold XM_SUP_RESET. pose proof (XN0 (snd (sup_reset_m R which))). lia.
  - intros a Ha. unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (srb_awr_slot _ _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_NARGS, CALL_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    apply (srb_awr_slot _ _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
    assert (Hlo : a < alloc_ceiling).
    { destruct (srb_slot_bounds R HC1) as [Hs | Hs].
      - apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, CALL_OFF_NARGS in *; lia|].
        apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, CALL_OFF_ARGS in *; lia|].
        exact (False_ind _ (inFP_nil a Ha)).
      - rewrite Hs in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, CALL_OFF_NARGS in *; lia|].
        apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, CALL_OFF_ARGS in *; lia|].
        exact (False_ind _ (inFP_nil a Ha)). }
    rewrite HST in Hw. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (HBB3 & MLE3 & [(Hc6 & _) | (_ & p & Hp & Hperm3 & Hfresh3 & HREP3)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length Z.of_nat] in Hc6. lia. }
cbn [app] in HREP3.
set (y := sarg which) in *.
set (n := Z.of_nat (length y) + 1) in *.
pose proof (proj1 HJ3) as HAR3.
rewrite PB1.
jafter_call_keep_pi HS 51%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc3 | exact HJ3 | exact Usp2 | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. cbn in Ha. unfold REC_ARGS_MAX in HFa. cbn [length Z.of_nat Z.ltb Z.compare] in HFa.
  assert (Hlo : a < alloc_ceiling).
  { destruct (srb_slot_bounds R HC1) as [Hs | Hs].
    - apply inFP_cons in HFa as [HFa | HFa]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, CALL_OFF_NARGS in *; lia|].
      apply inFP_cons in HFa as [HFa | HFa]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, CALL_OFF_ARGS in *; lia|].
      exact (False_ind _ (inFP_nil a HFa)).
    - rewrite Hs in HFa. apply inFP_cons in HFa as [HFa | HFa]; [unfold A_REC_SPILL, CALL_OFF_NARGS in *; lia|].
      apply inFP_cons in HFa as [HFa | HFa]; [unfold A_REC_SPILL, CALL_OFF_ARGS in *; lia|].
      exact (False_ind _ (inFP_nil a HFa)). }
  lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 51 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 51)%nat -> ew E3 n = ew E2 n) by (intros n' Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (AG3 : env_agree 32 (Ereg regs (srb_extra regs)) E3)
  by (rewrite HE3; apply (env_agree_havoc_ge 32 51); [lia | exact AG2]).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by lia; exact Usp2).
(* ---- run C: 0x8bd80 .. jal rec_shape_of (0x8bd8c) ---- *)
paj_run_shc RUNP RUNC HS HJ3.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msC, mat into matC, HF into HFC, HFr into HFrC, HG into HGC.
pmkst HS. srb_md.
prreg HS (1%bv : bv 5) PC1. prreg HS (2%bv : bv 5) PC2. prreg HS (3%bv : bv 5) PC3. prreg HS (4%bv : bv 5) PC4.
prreg HS (10%bv : bv 5) PC10. prreg HS (11%bv : bv 5) PC11.
assert (GC2 : spZ (ms_regs msC) = sp0 + -32)
  by (unfold spZ at 1; rewrite PC2, Usp3; apply unsigned_lit_small; lia).
assert (GC3 : getr (ms_regs msC) 3 = w64 (as_gp B))
  by (rewrite PC3, OLD3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GC4 : getr (ms_regs msC) 4 = w64 (as_tp B))
  by (rewrite PC4, OLD3, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GC10 : getr (ms_regs msC) 10 = w64 SRB_VERB).
{ rewrite PC10. unfold w64. rewrite <- (srb_vobj VOBJS).
  apply img_env_atomP; [exact HEI3 | unfold SRB_VOBJ, A_OBJ, A_TEXT, A_LIM; lia]. }
assert (GC11 : getr (ms_regs msC) 11 = w64 (Z.of_nat (length srb_verb))) by (rewrite PC11; reflexivity).
assert (GC1r : YK0s.ret_ok (getr (ms_regs msC) 1))
  by (rewrite PC1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GC1a : 4096 <= bv_unsigned (getr (ms_regs msC) 1))
  by (rewrite PC1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W3 (ms_mem msC) a = rdW W3 mem3 a).
{ apply (kept_of_frame (segs := SEGS) E3 _ (w_H W3) mem3 (ms_mem msC) (fun a => sp0 - 32 <= a < sp0) HFrC).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ3) as HARC.
assert (HROC : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem msC)))
  by exact (srb_aro ly S W mem md O ly3 S3 W3 (ms_mem msC) _ [] _ sp0 _ HAR HOin HJ3 HROD).
assert (HROkC : cmd_ro_ok (rdW W3 (ms_mem msC))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARC HROC).
(* ---- the call of rec_shape_of("supervisor_reset", 16) (0x8bd8c) ---- *)
rewrite (srb_sig_rso SIGP).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W3 (ms_regs msC) (ms_mem msC) _ SUP_RESET_STK sp0 (srb_FP O) ly S W mem md [] ly3 S3 _ _
    REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32) (getr (ms_regs msC) 1) _ HJ3 GC2 eq_refl ltac:(lia)
    ltac:(rewrite HSS; lia) ltac:(rewrite HSS, HST; lia) GC3 GC4 eq_refl GC1r GC1a).
  - intros HPRE1. pose proof (TREC_SHAPE_OF fx ly3 S3 W3 (ms_regs msC) (ms_mem msC) _ SRB_VERB srb_verb HPRE1 HROC GC10
      ltac:(unfold SRB_VERB; lia) GC11 ltac:(rewrite srb_verb_len; lia) HROkC VOBJS
      (srb_verb_ok B HB ly3 S3 W3 (ms_mem msC) HROkC CMD_RO_IN)) as T.
    unfold apost_base in T. apply T.
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
    unfold EV_SUP_RESET, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 &
  ((q & Hq10 & Hq64 & HqA) & Hperm4 & Ely4 & ES4)).
pose proof (proj1 HJ4) as HAR4.
rewrite PC1.
jafter_call_keep_pi HS 67%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc4 | exact HJ4 | exact Usp3 | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a _ HFa. exact (inFP_nil a HFa). }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 67 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 67)%nat -> ew E4 n = ew E3 n) by (intros n' Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (A71 : ew E4 71 = getr regs4 10) by (rewrite HE4; reflexivity).
assert (AG4 : env_agree 32 (Ereg regs (srb_extra regs)) E4)
  by (rewrite HE4; apply (env_agree_havoc_ge 32 67); [lia | exact AG3]).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by lia; exact Usp3).
(* ---- run D: 0x8bd90 .. j answer (0x8bdac) ---- *)
paj_run_shc RUNP RUNC HS HJ4.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp4 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msD, mat into matD, HF into HFD, HFr into HFrD, HG into HGD.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (mdD := m) in *; clearbody mdD end.
prreg HS (1%bv : bv 5) PD1. prreg HS (2%bv : bv 5) PD2. prreg HS (3%bv : bv 5) PD3. prreg HS (4%bv : bv 5) PD4.
prreg HS (8%bv : bv 5) PD8. prreg HS (10%bv : bv 5) PD10. prreg HS (11%bv : bv 5) PD11. prreg HS (12%bv : bv 5) PD12.
assert (HPA : aregs_preserved regs (ms_regs msD))
  by exact (aregs_preserved_of_st_ok SEGS (w_H W4) E4 _ msD regs (srb_extra regs) HS AG4 ltac:(vm_compute; reflexivity)).
assert (XD1 : getr (ms_regs msD) 1 = getr regs 1)
  by (rewrite PD1, OLD4, OLD3, OLD2 by lia; exact (EE 1%nat 1%bv eq_refl)).
assert (SPD : spZ (ms_regs msD) = sp0)
  by (unfold spZ at 1; rewrite PD2, OLD4, OLD3, OLD2 by lia; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (XD3 : getr (ms_regs msD) 3 = w64 (as_gp B))
  by (rewrite PD3, OLD4, OLD3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (XD4 : getr (ms_regs msD) 4 = w64 (as_tp B))
  by (rewrite PD4, OLD4, OLD3, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (XD8 : s0Z (ms_regs msD) = s0Z regs)
  by (unfold s0Z; rewrite PD8, OLD4, OLD3, OLD2 by lia; rewrite (EE 8%nat 8%bv eq_refl); reflexivity).
assert (GD10 : getr (ms_regs msD) 10 = w64 (rec_slot R)) by (rewrite PD10, OLD4, OLD3 by lia; rewrite A39; exact R10).
assert (GD11 : getr (ms_regs msD) 11 = w64 q) by (rewrite PD11, A71; exact Hq10).
assert (GD12 : getr (ms_regs msD) 12 = Z_to_bv 64 1) by (rewrite PD12; reflexivity).
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W4 (ms_mem msD) a = rdW W4 mem4 a).
{ apply (kept_of_frame (segs := SEGS) E4 _ (w_H W4) mem4 (ms_mem msD) (fun a => sp0 - 32 <= a < sp0) HFrD).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp4 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ4) as HARD.
(* ---- the state at the jump, against the earlier states ---- *)
assert (Hn1 : 1 <= n) by (subst n; lia).
assert (HPIN3 : In (p, n) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Hperm3)); left; reflexivity).
assert (H2to3 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm3)); right; exact Hpn).
assert (H3to4 : forall pn, In pn (ablocks B ly3 S3) -> In pn (ablocks B ly4 S4))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm4)); exact Hpn).
assert (H4to3 : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ Hperm4); exact Hpn).
assert (HSsplit : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2) \/ In pn F)
  by (intros pn Hpn; apply in_app_or; exact (Permutation_in _ HPermF Hpn)).
assert (HFnot : forall pn, In pn F -> ~ In pn (ablocks B ly2 S2))
  by (intros pn HFi H2; exact (srb_dup_false ly S W mem md (ablocks B ly2 S2) F pn HAR HPermF H2 HFi)).
assert (Hfresh_self : ~ In (p, n) (ablocks B ly2 S2)).
{ intros H2. rewrite Forall_forall in Hfresh3. pose proof (Hfresh3 (p, n) H2) as D. cbn [fst snd] in D.
  unfold iv_apart in D. lia. }
assert (HpS : In (p, n) (ablocks B ly S) -> In (p, n) O).
{ intros HS'. destruct (HSsplit _ HS') as [H2 | HFi]; [exfalso; exact (Hfresh_self H2) | exact (HFO _ HFi)]. }
assert (HO3S : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B ly S) -> In pn O).
{ intros pn [<- | H1] HS'; [exact (HpS HS') | exact (proj1 (proj1 (HO1 pn) H1))]. }
assert (HO3in3 : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B ly3 S3))
  by exact (srb_O_in ly3 S3 _ _ _ HREP3).
assert (HO3in4 : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B ly4 S4))
  by (intros pn Hpn; exact (H3to4 _ (HO3in3 _ Hpn))).
assert (HREPD : rec_repA B ly4 S4 (rdW W4 (ms_mem msD)) (rec_record R SRB_FN [y]) ((p, n) :: O1)).
{ apply (srb_rec_repA_ext ly3 S3 (rdW W3 mem3) ly4 S4 _ _ _ HREP3 HO3in4).
  assert (K34 : forall a, 0 <= a < alloc_ceiling -> (Exists (in_zr a) TFIB_PROG_STATIC \/
     exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m) ->
     rdW W4 (ms_mem msD) a = rdW W3 mem3 a).
  { intros a Ha Hc. rewrite KD by lia.
    destruct Hc as [HP | (b & m & Hbm & Hba)].
    - rewrite (srb_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc4 (Forall_nil _) (inFP_nil a) HP). apply KC; lia.
    - replace a with (b + (a - b)) by lia.
      rewrite (srb_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (a - b) HJc4 Hbm (H3to4 _ Hbm) ltac:(lia) (inFP_nil _)).
      apply KC; lia. }
  intros a [Ha | [Ha | ([b m] & Hpn & Ha)]]; cbn [fst snd] in *.
  - apply K34; [unfold A_G_REC, REC_SIZE in Ha; lia | left; exact (recb_grec_in a Ha)].
  - apply K34; [unfold A_REC_SPILL, SC_SIZE in Ha; lia | left; exact (recb_spill_in a Ha)].
  - destruct (srb_blk_bounds ly3 S3 W3 mem3 md3 b m HAR3 (HO3in3 _ Hpn)) as (Hb & Hc & _ & Hmr & _).
    apply K34; [lia | right; exists b, m; split; [exact (HO3in3 _ Hpn) | lia]]. }
pose proof HREPD as (QD & HQD & HOQD).
destruct (srb_old_at _ _ _ _ HQD) as [HOLD HOLDin'].
set (old := srb_old QD) in *.
assert (HOLDin : forall pn, In pn (ablocks B ly4 S4) -> fst pn = old -> In pn ((p, n) :: O1)).
{ intros pn Hpn Hf. unfold old, srb_old in Hf. destruct (l_answer QD) as [an|] eqn:Ean.
  - pose proof (HOLDin' an eq_refl) as Han. apply HOQD in Han.
    rewrite (srb_same_start ly4 S4 W4 mem4 md4 pn an HAR4 Hpn (HO3in4 _ Han) Hf). exact Han.
  - destruct pn as [b m]. destruct (srb_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 Hpn) as (Hb & _). cbn [fst] in Hf. lia. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ unfold old, srb_old. destruct (l_answer QD) as [an|] eqn:Ean; [|lia].
  pose proof (HOLDin' an eq_refl) as Han. apply HOQD in Han. destruct an as [a1 a2].
  destruct (srb_blk_bounds ly4 S4 W4 mem4 md4 a1 a2 HAR4 (HO3in4 _ Han)) as (Hb0 & Hb1 & _ & _ & Hr1). cbn [fst]. lia. }
assert (HROD' : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem msD)))
  by exact (srb_aro ly S W mem md O ly4 S4 W4 (ms_mem msD) _ [] _ sp0 _ HAR HOin HJ4 HROD).
assert (HM : sup_reset_m R which = rec_answer (rec_record R SRB_FN [y]) (SRB_FN, [y]) (shape_of srb_verb) true)
  by exact (srb_m R which).
assert (MLEJ : mo_le MT S S4 (XM_RECORD MT R + XM_ARG_S MT which + 0)).
{ apply (mle_station MT S S3 S4 _ 0 MTL (mle_station MT S S2 S3 _ _ MTL MLE1 MLE3)).
  rewrite ES4. exact (mo_le_refl MT MTL S3). }
pose proof HJ4 as (_ & _ & _ & _ & _ & HfrD & HnevD & _).
(* ---- the tail jump into answer (0x8bdac): answer runs at the entry's sp and returns to the entry's ra ---- *)
rewrite (srb_sig_answer SIGP).
assert (HPREA : afn_pre SEGS B ANSWER_STK ly4 S4 W4 (ms_regs msD) (ms_mem msD) mdD ch).
{ apply (afn_pre_at SEGS B SUP_RESET_STK sp0 (srb_FP O) ly S W mem md [] ly4 S4 W4 (ms_mem msD) mdD _
    (ms_regs msD) ANSWER_STK 0 ch HJ4).
  - rewrite SPD. lia.
  - reflexivity.
  - lia.
  - rewrite HNS. lia.
  - rewrite HNS, HST. lia.
  - rewrite XD1. exact Hra.
  - unfold raZ. rewrite XD1. exact Hra4.
  - exact XD3.
  - exact XD4.
  - rewrite SPD, XD8. apply (srb_achain_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4).
    + intros a Ha. exact (proj2 (HFPlow a Ha)).
    + exact Hch. }
eapply SRr_mono.
{ pose proof (TANSWER fx ly4 S4 W4 (ms_regs msD) (ms_mem msD) mdD ch (rec_slot R) q old (SRB_FN, [y])
    (shape_of srb_verb) true (rec_record R SRB_FN [y]) ((p, n) :: O1) HPREA HFRM) as T.
  cbv zeta in T. apply T; clear T.
  - rewrite HfrD. cbn [app]. exact HFR8.
  - exact HROD'.
  - exact (cmd_ro_ok_of_aro _ _ _ _ _ HARD HROD').
  - exact GD10.
  - destruct (srb_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    rewrite Hs. unfold A_REC_SPILL. lia.
  - exact GD11.
  - exact Hq64.
  - rewrite GD12. reflexivity.
  - exact HREPD.
  - exact HOLD.
  - exact Hold64.
  - intros _. split; [|exact srb_fits].
    apply (srb_argA_kept _ _ (rdW W4 mem4)); [exact (HqA _)|]. intros i Hi.
    pose proof (srb_argA_low ly4 S4 W4 mem4 md4 [] q _ HAR4 (HqA []) i Hi) as Hlo. apply KD; lia.
  - intros _ _. exact (srb_answer_slot R y).
  - unfold EV_SUP_RESET, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
  - rewrite ES4. unfold LIVE_SUP_RESET in HLIVE. rewrite HM in HLIVE. lia.
  - apply (mok_station MT S S4 (XM_SUP_RESET MT R which) _ _ MTL HMOK MLEJ (XN0 _)).
    unfold XM_SUP_RESET. rewrite HM. lia. }
cbv beta. intros W5 c5 _ (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & HFX5 & HCSR5 & HJA & HPA5 & HQ5).
cbv zeta in HQ5.
destruct HQ5 as (p1 & p2 & O' & Hp2 & Hp2a & Hp12 & Hfr12 & Hbl & HrepF & HO' & Hstr & HBB5 & Hmle).
set (t := snd (rec_answer (rec_record R SRB_FN [y]) (SRB_FN, [y]) (shape_of srb_verb) true)) in *.
set (nT := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJA) as HAR5.
assert (Hnew12 : forall pn, In pn (ablocks B ly S) -> (pn = (p1, nT) \/ pn = (p2, nT)) -> In pn O).
{ intros pn HS' Heq. destruct (HSsplit _ HS') as [H2 | HFi]; [|exact (HFO _ HFi)].
  pose proof (H3to4 _ (H2to3 _ H2)) as H4.
  destruct (Z.eq_dec (fst pn) old) as [Ho | Ho]; [exact (HO3S _ (HOLDin _ H4 Ho) HS')|].
  exfalso. destruct (Hfr12 pn H4 Ho) as [N1 N2]. destruct Heq as [Heq | Heq]; [exact (N1 Heq) | exact (N2 Heq)]. }
unfold apost_baseF. exists fx5, ly5, S5, regs5, mem5, md5.
split; [rewrite XD1; reflexivity|].
split; [exact HFX5|]. split; [exact HCSR5|].
split.
{ assert (HJF : ajournal SEGS B SUP_RESET_STK sp0 (srb_FP O) ly S W mem md ([] ++ []) ly5 S5 W5 mem5 md5
    ((0 + EV_RECORD R + EV_ARG_S + EV_REC_SHAPE_OF) + EV_ANSWER)).
  { eapply ajournal_sub_wide.
    all: try first [exact LAWS | exact Hsegs | exact HJ4 | exact HJA].
    all: lazymatch goal with
    | |- forall a, inFP _ a -> awr_byte _ _ _ _ _ _ _ _ _ _ a =>
        intros a Ha;
        apply inFP_cons in Ha as [Ha | Ha]; [apply srb_awr_grec; unfold OFF_ANSWER, REC_SIZE in *; lia|];
        apply inFP_cons in Ha as [Ha | Ha]; [apply srb_awr_grec; unfold OFF_STATE, REC_SIZE in *; lia|];
        destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba);
        apply srb_in_filter in Hbm as [Hbm _];
        destruct (in_dec recb_pair_dec (b, m) O) as [HbO | HbnO];
        [ exact (srb_awr_blk _ _ _ _ _ _ _ _ b m a HbO (HO3in4 _ Hbm) Hba)
        | right; right; left; exists b, m; split; [exact (HO3in4 _ Hbm)|];
          split; [intros HbS; exact (HbnO (HO3S _ Hbm HbS)) | exact Hba] ]
    | |- forall a, inFP _ a -> _ => intros a _ Ha Hn; exfalso; apply Hn; rewrite SPD, HNS; rewrite HST in Ha; exact Ha
    | |- _ => rewrite ?SPD, ?HNS, ?HST; lia
    end. }
  cbn [app] in HJF. apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF).
  unfold EV_SUP_RESET, EV_REC_SHAPE_OF. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPA HPA5)|].
exists (fst (rec_answer (rec_record R SRB_FN [y]) (SRB_FN, [y]) (shape_of srb_verb) true)), t, p2, O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact Hp2|]. split; [exact Hp2a|]. split; [exact HrepF|].
split.
{ intros pn Hpn. destruct (in_dec recb_pair_dec pn (ablocks B ly S)) as [HS' | HnS]; [left | right; exact HnS].
  apply HO' in Hpn as [[H3 _] | ->]; [exact (HO3S pn H3 HS') | exact (Hnew12 _ HS' (or_introl eq_refl))]. }
split; [apply Hbl; right; right; reflexivity|].
split; [intros pn HS' HnO Heq; subst pn; exact (HnO (Hnew12 _ HS' (or_intror eq_refl)))|].
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hf & Hpn).
  pose proof (srb_O_in ly5 S5 _ _ _ HrepF pn Hpn) as Hpn5.
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq5.
  pose proof (srb_same_start ly5 S5 W5 mem5 md5 pn (p2, nT) HAR5 Hpn5 Hq5 Hf) as ->.
  apply HO' in Hpn as [[Hpn1 Hfo] | Heq];
  [exact (proj2 (Hfr12 _ (HO3in4 _ Hpn1) Hfo) eq_refl) | injection Heq as Heq; exact (Hp12 (eq_sym Heq))]. }
split; [exact Hstr|].
split.
{ intros pn Hpn HnO.
  assert (H2 : In pn (ablocks B ly2 S2)).
  { destruct (HSsplit _ Hpn) as [H | H]; [exact H | exfalso; exact (HnO (HFO _ H))]. }
  pose proof (H3to4 _ (H2to3 _ H2)) as H4.
  assert (Ho : fst pn <> old) by (intros Hf; exact (HnO (HO3S _ (HOLDin _ H4 Hf) Hpn))).
  assert (H5 : In pn (ablocks B ly5 S5)) by (apply Hbl; left; split; [exact H4 | exact Ho]).
  split; [exact H5|].
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq5.
  destruct pn as [b m]. cbn [fst snd].
  assert (Hne : (b, m) <> (p2, nT)) by exact (proj2 (Hfr12 (b, m) H4 Ho)).
  destruct (srb_blk_bounds ly5 S5 W5 mem5 md5 b m HAR5 H5) as (_ & _ & Hm0 & Hmr & _).
  destruct (srb_blk_bounds ly5 S5 W5 mem5 md5 p2 nT HAR5 Hq5) as (_ & _ & Hn0 & Hnr & _).
  unfold iv_apart. destruct (srb_blk_apart ly5 S5 W5 mem5 md5 b m p2 nT HAR5 H5 Hq5 Hne); lia. }
split.
{ intros pn Hpn. apply Hbl in Hpn as [[H4 Hf] | [-> | ->]].
  - pose proof (H4to3 _ H4) as H3. apply (Permutation_in _ Hperm3) in H3. destruct H3 as [<- | H2].
    + right; left. apply HO'. left. split; [left; reflexivity | exact Hf].
    + destruct (in_dec recb_pair_dec pn O1) as [H1 | H1n].
      * right; left. apply HO'. left. split; [right; exact H1 | exact Hf].
      * left. split.
        -- apply (Permutation_in _ (Permutation_sym HPermF)). apply in_or_app. left. exact H2.
        -- intros HinO. apply H1n. apply HO1. split; [exact HinO | intros HFi; exact (HFnot _ HFi H2)].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ rewrite ES4 in HBB5. unfold LIVE_SUP_RESET. rewrite HM. fold y t. lia. }
apply (mle_weaken MT S S5 _ _ MTL (mle_station MT S S4 S5 _ _ MTL MLEJ Hmle)).
unfold XM_SUP_RESET. rewrite HM. fold y t. lia.
Qed.

End e.
End f.
End d.

Print Assumptions tsup_reset_holds.
