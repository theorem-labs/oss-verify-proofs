(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_worker_env (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry 0x8c13c, 34 instructions): tsup_worker_env_spec of a Theorem Labs lane's
   lib/B/Prog/sup_worker_env_c.v (a working branch fc8bcbd8b42), proved over its callee contracts record_c, arg_s_c,
   rec_shape_of_c and answer_c, each taken at every FP state as the statement states them; the post is apost_baseF,
   answer's (the tail jump).

   The B re-walk of the A walk lib/A/Prog/sup_worker_env.v (a working branch 65a6716e4ad): A inlines record()
   (two arms, rec_calls_free on the spill arm) and the stores of fn, nargs and args[0..2] with their 8 inline checks,
   and calls xstrdup three times; B calls record() and arg_s(), which carry those parts and checks in their own
   contracts. In the form of the B walk lib/B/Prog/sup_reset.v (a working branch c79a9f2daf7), whose code
   is this one's with one call of arg_s for three. The segments (lib/B/Prog/sup_worker_env_aux.v has the code):
     run A  0x8c13c .. 0x8c164  the 48-byte frame (ra, s0 .. s3), s0 := nice, s1 := cpus, s2 := format, a0 := 16,
                                jal record
     run B  0x8c168 .. 0x8c170  s3 := the slot, a1 := format, jal arg_s
     run C  0x8c174 .. 0x8c17c  a0 := the slot, a1 := cpus, jal arg_s
     run D  0x8c180 .. 0x8c188  a0 := the slot, a1 := nice, jal arg_s
     run E  0x8c18c .. 0x8c198  a0 := "worker_env" (0x21f00), a1 := 10, jal rec_shape_of
     run F  0x8c19c .. 0x8c1c0  a2 := 1, a1 := the shape, a0 := the slot, ra / s0 .. s3 back, sp += 48, j answer
   Each run is PaCallRun's plain symbolic run to the call (paj_run_shc), each call is cl_callS_wide (record, arg_s:
   their footprints are g_rec / record.spill fields and, on record's spill arm, recorder blocks) or cl_callS_na
   (rec_shape_of: no footprint), the frame is carried across each call with jafter_call_keep_pi, and the tail jump
   runs answer at this function's entry sp, whose journal joins the walk's with ajournal_sub_wide.
   Report / trap edges: the function has no branch, no `jal __asan_report_*` and no unimp / ebreak
   (lib/B/Prog/sup_worker_env_aux.v:13-36, measured with capstone), so there is no edge to refute here; the slot's
   checks and traps are record's and arg_s's, refuted in their contracts.
   The Generation-N image-B walk lib/B/Prog/sup_worker_env.v of a working branch 543f2c3645b (same code at the
   same B addresses) was read as a template of the B code only, not ported.

   Section hypotheses beyond the statement's: the per-binary record CmdBSyms (HB), the meter's laws (MTL), the
   program functions' call targets (cmd_sig_prog_PB, CmdObj.v's cmd_sig_prog, under the name of a Theorem Labs lane's lemma that
   proves it at the pinned image), and the per-binary image facts in the form of a Theorem Labs lane's lib/B/Prog/CmdRecImg.v
   cmd_img_facts_tfib, at this walk's abstract segments. The per-binary facts the walk uses are a Theorem Labs lane's
   CmdRecRo.v / CmdRecRest.v / CmdRecImg.v lemmas over them, by exact (CMD_RO_IN, cmd_ro_ok_of_aro,
   cmd_ro_prog_apart, cmd_prog_img, cmd_rodata_kept, cmd_heap_tail_vis); a closing file at the pinned image
   (PI := PB_cmd) discharges cmd_img_facts_tfib and cmd_sig_prog_PB by a Theorem Labs lane's lemmas of those names. *)
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
xmalloc_c rec_calls_free_c mix_call_c hand_back_c record_c arg_s_c rec_shape_of_c answer_c sup_worker_env_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts sup_worker_env_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the representation's readers (lib/B/Prog/sup_reset.v:62-224 of a working branch c79a9f2daf7;
   A: lib/A/Prog/sup_worker_env_m.v:34-145, the same CmdRep forms) ---------- *)

Lemma sweb_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma sweb_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma sweb_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (sweb_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma sweb_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (sweb_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (sweb_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (sweb_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (sweb_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma sweb_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (sweb_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (sweb_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (sweb_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma sweb_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
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
    + apply (sweb_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sweb_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (sweb_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (sweb_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sweb_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma sweb_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (sweb_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma sweb_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma sweb_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma sweb_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma sweb_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
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
    + apply (sweb_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (sweb_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (sweb_in_calls Q i P pn EP Hpn).
    + apply (sweb_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply sweb_in_spill. exact Hpn.
  - apply (sweb_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply CmdRecAns.rca_in_answer. exact Hpn.
  - apply (sweb_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply sweb_in_reply. exact Hpn.
  - apply (sweb_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

(* the recorder's answer field holds 0 or the start of one of its blocks *)
Definition sweb_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma sweb_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  aval_mem rd (A_G_REC + OFF_ANSWER) 8 (sweb_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
  intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold sweb_old. split.
  - unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
    [exact (proj1 HA) | exact HA].
  - intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
Qed.

(* the slot record() returns (record_c.v rec_slot): an entry of g_rec's table, or record.spill *)
Lemma sweb_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
  (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL.
Proof.
  intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [left | right; reflexivity].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
Qed.

(* the slot fact answer's pre asks (answer_c.v:128-130), for the call (FN, A) record() and arg_s made *)
Lemma sweb_answer_slot : forall R (A : list (list byte)),
(exists k, nth_error (r_calls (rec_record R SWEB_FN A)) k = Some (SWEB_FN, A) /\
   rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R = A_REC_SPILL /\ (SWEB_FN, A) = r_spill (rec_record R SWEB_FN A)).
Proof.
intros R A. unfold rec_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L].
- left. exists (length (r_calls R)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

Lemma sweb_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

(* the program's statics of the record (lib/B/YF0m.v TFIB_PROG_STATIC): g_rec, record.spill, g_quitting *)
Lemma sweb_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Ha. lia. Qed.

Lemma sweb_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

(* the footprint of the statement (sup_worker_env_c.v:119) *)
Definition sweb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma sweb_FP_pos : forall O, (forall pn, In pn O -> 0 < fst pn) -> Forall (fun r => 0 < fst r) (sweb_FP O).
Proof.
intros O HO. unfold sweb_FP. constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
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
(* the statement's callees (each at every FP state) and object bridge (sup_worker_env_c.v:75-79) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses of a Theorem Labs lane's RULING-STMT.md section 1: the per-binary allocator record (a Theorem Labs lane's
   lib/B/YF0m.v), the meter's laws, and the program functions' call targets (lib/B/Prog/CmdObj.v cmd_sig_prog),
   under the name of a Theorem Labs lane's lemma that proves it at the pinned image (lib/B/Prog/CmdRecRest.v cmd_sig_prog_PB) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the per-binary image facts (a Theorem Labs lane's lib/B/Prog/CmdRecBase.v cmd_img_facts, a working branch 6830f0bf032): a Theorem Labs lane proves
   them at the pinned image (CmdRecImg.v cmd_img_facts_tfib, at tfibsegs); this walk is over an abstract PAImg, so it
   takes that lemma's statement at its own segments, under the lemma's name, and each per-binary fact the walk uses
   is a Theorem Labs lane's lemma over them, by exact: CmdRecRo.v CMD_RO_IN and cmd_ro_ok_of_aro, CmdRecRest.v cmd_ro_prog_apart,
   cmd_prog_img and cmd_rodata_kept, CmdRecImg.v cmd_heap_tail_vis *)
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

Lemma sweb_O_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HQ & HOQ) pn Hpn. exact (CmdRecAns.rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HOQ pn) Hpn)). Qed.

Lemma sweb_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

Lemma sweb_blk_noimg : forall ly S (W : world SEGS) mem md b m a, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md b m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha)))))).
Qed.

Lemma sweb_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma sweb_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (sweb_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (sweb_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (sweb_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (sweb_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* a live block is listed once *)
Lemma sweb_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
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
destruct (sweb_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* ---------- the walk's footprint and what a journal keeps ---------- *)

Lemma sweb_inFP_cases : forall O a, inFP (sweb_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold sweb_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply sweb_grec_in. exact Ha.
- left. apply sweb_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.

Lemma sweb_static_low : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> 0x10000 <= a < 0x606000.
Proof. intros a Ha. exact (pa_img_range a (cmd_prog_img a Ha)). Qed.

Lemma sweb_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (sweb_FP O) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
destruct (sweb_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)].
- pose proof (sweb_static_low a HP). lia.
- destruct (sweb_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (H4 & Hc & _). lia.
Qed.

(* arodata_okP along the walk's journal (cmd_rodata_kept: the footprint is statics and the recorder's blocks) *)
Lemma sweb_aro : forall ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp STK,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp (sweb_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O lyc Sc Wc memc mdc own k sp STK HAR HO HJ HR.
apply (cmd_rodata_kept ly S W mem md lyc Sc Wc memc mdc STK sp (sweb_FP O) own k HAR HJ); [|exact HR].
intros a Ha. destruct (sweb_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)]; [left; exact HP|].
right. exists b, n. split; [apply in_or_app; left; exact (HO _ Hin) | exact Hb].
Qed.

Lemma sweb_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

Lemma sweb_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (RecBLemmas.recb_prog_unowned_m B HB cmd_prog_img a HP) as (H1 & H2 & H3).
exact (sweb_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

Lemma sweb_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

Lemma sweb_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
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
Lemma sweb_awr_static : forall STK sp O bl0 blc fr0 ly own a, Exists (in_zr a) TFIB_PROG_STATIC -> inFP (sweb_FP O) a ->
awr_byte SEGS B STK sp (sweb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a HP HF.
right; right; right; right; left. split; [exact HF|]. split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

Lemma sweb_awr_grec : forall STK sp O bl0 blc fr0 ly own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp (sweb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply sweb_awr_static; [exact (sweb_grec_in a Ha)|].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma sweb_awr_spill : forall STK sp O bl0 blc fr0 ly own a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp (sweb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply sweb_awr_static; [exact (sweb_spill_in a Ha)|].
exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

(* a byte of the slot record() returned *)
Lemma sweb_awr_slot : forall STK sp O bl0 blc fr0 ly own R a, (length (r_calls R) <= 16)%nat ->
rec_slot R <= a < rec_slot R + CALL_SIZE -> awr_byte SEGS B STK sp (sweb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own R a HL Ha. destruct (sweb_slot_bounds R HL) as [Hs | Hs].
- apply sweb_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply sweb_awr_spill. rewrite Hs in Ha. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma sweb_awr_blk : forall STK sp O bl0 blc fr0 ly own b n a, In (b, n) O -> In (b, n) blc ->
b <= a < b + req_size n -> awr_byte SEGS B STK sp (sweb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own b n a HO Hc Ha. right; left. split.
- unfold sweb_FP. apply inFP_cons. right. apply inFP_cons. right.
  replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b n (a - b)); [exact HO | lia].
- exists b, n. split; [exact Hc | exact Ha].
Qed.

(* ---------- the string argument ---------- *)

(* the bytes of a string argument decide astr_argA's reader part: its other parts name no reader *)
Lemma sweb_argA_kept : forall ly1 S1 (rd rd' : reader) ro O1 p v, astr_argA B ly1 S1 rd ro O1 p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly1 S1 rd' ro O1 p (Some v).
Proof.
intros ly1 S1 rd rd' ro O1 p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [|split; [exact Hl | exact Hr]].
apply (sweb_str_keep rd); [exact Hs|]. intros x Hx. replace x with (p + (x - p)) by lia. apply K. lia.
Qed.

(* a string argument's bytes lie below alloc_ceiling: a block's, or the image's *)
Lemma sweb_argA_low : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 p v, AR SEGS B ly1 S1 W1 mem1 md1 ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 p (Some v) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= p + i < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 O1 p v HAR H i Hi. cbn [astr_argA] in H. pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
- destruct Hblk as (b & m & Hin & Hb1 & Hb2).
  destruct (sweb_blk_bounds ly1 S1 W1 mem1 md1 b m HAR Hin) as (Hb & Hc & _ & Hmr & _). lia.
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia.
Qed.

(* a caller's string lies in a block that is none of the recorder's: apart from each of them (the statement's
   premise, sup_worker_env_c.v:99-110) *)
Lemma sweb_blk_notO : forall (b k p n : Z) (O : list (Z * Z)), b <= p -> p + n <= b + k -> 1 <= n ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O -> ~ In (b, k) O.
Proof.
intros b k p n O H1 H2 Hn HF HO. rewrite Forall_forall in HF. specialize (HF _ HO). cbn [fst snd] in HF.
unfold iv_apart in HF. lia.
Qed.

(* a block apart from every block of a list is none of them *)
Lemma sweb_fresh_notin : forall (X : list (Z * Z)) p n, 1 <= n ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) X -> ~ In (p, n) X.
Proof.
intros X p n Hn HF HX. rewrite Forall_forall in HF. specialize (HF _ HX). cbn [fst snd] in HF.
unfold iv_apart in HF. lia.
Qed.

(* a caller's string at a later state of the walk: its block, none of the recorder's, is live there with the bytes
   it had at the entry, so astr_argA's heap arm holds there (with no block excluded) and its word tail is visible
   (a Theorem Labs lane's cmd_heap_tail_vis, lib/B/Prog/CmdRecImg.v:34) *)
Lemma sweb_str_at : forall ly S (W : world SEGS) mem lyc Sc (Wc : world SEGS) memc mdc O p x b k,
AR SEGS B lyc Sc Wc memc mdc ->
In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= p -> p + (Z.of_nat (length x) + 1) <= b + k ->
astr_atR (rdW W mem) p x -> Z.of_nat (length x) + 1 <= LMAX + 1 ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k -> rdW Wc memc a = rdW W mem a) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] p (Some x) /\
atail_vis SEGS Wc memc (p + Z.of_nat (length x)).
Proof.
intros ly S W mem lyc Sc Wc memc mdc O p x b k HARc Hbk HnO Hbp Hpb HS Hn Hliv Hbyt.
pose proof (Hliv _ Hbk HnO) as Hbkc.
destruct (sweb_blk_bounds lyc Sc Wc memc mdc b k HARc Hbkc) as (Hb & _ & Hk0 & Hkr & _).
split.
- cbn [astr_argA]. split; [lia|]. split.
  + apply (sweb_str_keep (rdW W mem)); [exact HS|]. intros a Ha. apply (Hbyt b k a Hbk HnO). lia.
  + split; [exact Hn|]. left. split; [|apply Forall_nil]. exists b, k. split; [exact Hbkc | lia].
- apply (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB lyc Sc Wc memc mdc b k (p + Z.of_nat (length x)) HARc Hbkc). lia.
Qed.

(* the footprint of arg_s (arg_s_c.v:120-123) for the slot record() returned: c->nargs and c->args[m], fields of
   g_rec's table or of record.spill *)
Lemma sweb_argfp_in : forall R (A : list (list byte)) a, (length (r_calls R) <= 16)%nat -> (length A <= 5)%nat ->
inFP (if Z.of_nat (length A) <? REC_ARGS_MAX
      then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
            (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A),
             rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
      else []) a ->
rec_slot R <= a < rec_slot R + CALL_SIZE.
Proof.
intros R A a HC HA Ha. destruct (Z.of_nat (length A) <? REC_ARGS_MAX); [|exact (False_ind _ (inFP_nil a Ha))].
assert (HA' : 0 <= Z.of_nat (length A) <= 5) by lia.
apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia|].
exact (False_ind _ (inFP_nil a Ha)).
Qed.

Lemma sweb_slot_static : forall R a, (length (r_calls R) <= 16)%nat -> rec_slot R <= a < rec_slot R + CALL_SIZE ->
Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros R a HC Ha. destruct (sweb_slot_bounds R HC) as [Hs | Hs].
- apply sweb_grec_in. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply sweb_spill_in. rewrite Hs in Ha. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the bytes of a block of a state are not the slot's (the slot is the image's, a block's bytes are not) *)
Lemma sweb_slot_noblk : forall ly S (W : world SEGS) mem md R b m a, AR SEGS B ly S W mem md ->
(length (r_calls R) <= 16)%nat -> In (b, m) (ablocks B ly S) -> b <= a < b + req_size m ->
~ (rec_slot R <= a < rec_slot R + CALL_SIZE).
Proof.
intros ly S W mem md R b m a HAR HC Hin Ha Hs.
exact (sweb_blk_noimg ly S W mem md b m a HAR Hin Ha (cmd_prog_img a (sweb_slot_static R a HC Hs))).
Qed.

Lemma sweb_slot_low : forall R a, (length (r_calls R) <= 16)%nat -> rec_slot R <= a < rec_slot R + CALL_SIZE ->
0 <= a < alloc_ceiling.
Proof.
intros R a HC Ha. pose proof asan_consts as (C1 & _). pose proof (sweb_static_low a (sweb_slot_static R a HC Ha)). lia.
Qed.

(* the blocks of the entry that are none of the recorder's, and their bytes, from one state of the walk to the next
   across a call of arg_s (its footprint is the slot's, its blocks only grow) and the run after it (which writes
   only the frame) *)
Lemma sweb_live_step : forall ly S (W : world SEGS) mem md O R (A : list (list byte)) lyb Sb (Wb : world SEGS) memb mdb lyc Sc
  (Wc : world SEGS) memc mdc memd STK1 sp1 own1 k1,
AR SEGS B ly S W mem md -> AR SEGS B lyc Sc Wc memc mdc -> (length (r_calls R) <= 16)%nat -> (length A <= 5)%nat ->
ajournal SEGS B STK1 sp1
  (if Z.of_nat (length A) <? REC_ARGS_MAX
   then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
         (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A),
          rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
   else [])
  lyb Sb Wb memb mdb own1 lyc Sc Wc memc mdc k1 ->
(forall pn, In pn (ablocks B lyb Sb) -> In pn (ablocks B lyc Sc)) ->
(forall a, 0 <= a < alloc_ceiling -> rdW Wc memd a = rdW Wc memc a) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyb Sb)) ->
(forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k -> rdW Wb memb a = rdW W mem a) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k -> rdW Wc memd a = rdW W mem a).
Proof.
intros ly S W mem md O R A lyb Sb Wb memb mdb lyc Sc Wc memc mdc memd STK1 sp1 own1 k1 HAR HARc HC HA HJ Hbc KD Hliv Hbyt.
split; [intros pn Hpn HnO; exact (Hbc _ (Hliv _ Hpn HnO))|].
intros b k a Hbk HnO Ha. pose proof (Hliv _ Hbk HnO) as Hbkb. pose proof (Hbc _ Hbkb) as Hbkc.
destruct (sweb_blk_bounds ly S W mem md b k HAR Hbk) as (Hb & Hbcl & Hk0 & Hkr & _).
rewrite (KD a ltac:(lia)). replace a with (b + (a - b)) by lia.
rewrite (sweb_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (a - b) HJ Hbkb Hbkc ltac:(lia)).
- replace (b + (a - b)) with a by lia. exact (Hbyt b k a Hbk HnO Ha).
- intros HFa. apply (sweb_slot_noblk lyc Sc Wc memc mdc R b k (b + (a - b)) HARc HC Hbkc ltac:(lia)).
  exact (sweb_argfp_in R A _ HC HA HFa).
Qed.


(* rec_repA at a state whose reader agrees on g_rec, record.spill and the recorder's blocks *)
Lemma sweb_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (sweb_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

(* a block answer frees: the recorder's block whose start is the old answer (answer_c.v:137) *)
Lemma sweb_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
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
Ltac sweb_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.


(* the record() footprint of the call (record_c.v): g_rec.ncalls, the slot, and on the spill arm the recorder's
   blocks; every byte below alloc_ceiling *)
Lemma sweb_recfp_low : forall ly S (W : world SEGS) mem md O R a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> (length (r_calls R) <= 16)%nat ->
inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
      (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O R a HAR HOin HC1 Ha. pose proof asan_consts as (C1 & _).
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha].
{ destruct (sweb_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
  rewrite Hs in Ha. unfold A_REC_SPILL in Ha. lia. }
destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
destruct (sweb_blk_bounds ly S W mem md b n HAR (HOin _ Hbn)) as (Hb & Hc & _). lia.
Qed.

(* ---------- the walk ---------- *)
Theorem tsup_worker_env_holds : tsup_worker_env_spec B MT.
Proof.
unfold tsup_worker_env_spec.
intros ly S W regs mem md ch pf pcs pnn format cpus nice R O HPRE HFRM HROD HRO H10 Hpf64 H11 Hpc64 H12 Hpn64
  HSF HSC HSN HREP HFR8 HEV HLIVE HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SUP_WORKER_ENV_STK = 16608) by (vm_compute; reflexivity).
assert (HRS : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HAS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HSS : REC_SHAPE_OF_STK = 8288) by (vm_compute; reflexivity).
assert (HNS : ANSWER_STK = 16592) by (vm_compute; reflexivity).
rewrite HST in Hslo.
set (sp0 := spZ regs) in *.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sweb_O_in ly S _ R O HREP).
assert (HOpos : forall pn, In pn O -> 0 < fst pn).
{ intros [b n] Hbn. destruct (sweb_blk_bounds ly S W mem md b n HAR (HOin _ Hbn)) as (Hb & _). cbn. lia. }
assert (HFPpos : Forall (fun r => 0 < fst r) (sweb_FP O)) by exact (sweb_FP_pos O HOpos).
assert (HFPlow : forall a, inFP (sweb_FP O) a -> 0 <= a < alloc_ceiling)
  by (intros a Ha; exact (sweb_FP_low ly S W mem md O a HAR HOin Ha)).
pose proof HREP as (Q0 & HQ0 & HOQ0).
pose proof HQ0 as (_ & _ & _ & (HC1 & _) & _).
assert (EFP : (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O = sweb_FP O)
  by reflexivity.
rewrite EFP.
(* the three strings: in live blocks that are none of the recorder's (sup_worker_env_c.v:99-110) *)
destruct HSF as (xf & -> & (bf & kf & Hbf & Hbf1 & Hbf2) & Hsf & Hnf & Hapf).
destruct HSC as (xc & -> & (bc & kc & Hbc & Hbc1 & Hbc2) & Hsc & Hnc & Hapc).
destruct HSN as (xn & -> & (bn & kn & HBn & HBn1 & HBn2) & Hsn & Hnn & Hapn).
assert (HfO : ~ In (bf, kf) O) by exact (sweb_blk_notO bf kf pf (Z.of_nat (length xf) + 1) O Hbf1 Hbf2 ltac:(lia) Hapf).
assert (HcO : ~ In (bc, kc) O) by exact (sweb_blk_notO bc kc pcs (Z.of_nat (length xc) + 1) O Hbc1 Hbc2 ltac:(lia) Hapc).
assert (HnnO : ~ In (bn, kn) O) by exact (sweb_blk_notO bn kn pnn (Z.of_nat (length xn) + 1) O HBn1 HBn2 ltac:(lia) Hapn).
(* s0 holds nice at the program calls: a heap pointer, below alloc_ceiling (achain_low) *)
assert (Hpnl : 0 <= pnn < alloc_ceiling).
{ destruct (sweb_blk_bounds ly S W mem md bn kn HAR HBn) as (Hb & Hc & _ & Hkr & _). lia. }
assert (Hfrhi : alloc_ceiling <= sp0 - 48) by lia.
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
pose proof (XA0 (Some xf)) as XAf. pose proof (XA0 (Some xc)) as XAc. pose proof (XA0 (Some xn)) as XAn.
pose proof (LA0 (Some xf)) as LAf. pose proof (LA0 (Some xc)) as LAc. pose proof (LA0 (Some xn)) as LAn.
pose proof (XN0 (snd (sup_worker_env_m R (Some xf) (Some xc) (Some xn)))) as XNm.
pose proof (LN0 (snd (sup_worker_env_m R (Some xf) (Some xc) (Some xn)))) as LNm.
(* ---- the entry seed and run A: 0x8c13c .. jal record (0x8c164) ---- *)
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (fold sp0; lia).
assert (Hp48 : forall a, spZ regs - SWEB_FRAME <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; fold sp0 in Ha |- *; rewrite HST; unfold SWEB_FRAME in Ha; lia).
pose proof (sweb_seed_entry W regs mem Hsp Hal16 Hp48) as HS.
pose proof (ajournal_init SEGS B SUP_WORKER_ENV_STK (sweb_FP O) ly S W regs mem md ch HPRE) as HJ.
set (E := sweb_E regs) in *.
assert (HEI : img_env VAL A_LIM E) by exact (sweb_E_img regs).
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regs rr)
  by (intros kk rr Hkk; exact (sweb_E_reg regs kk rr Hkk)).
assert (AG0 : env_agree 32 (Ereg regs (sweb_extra regs)) E) by exact (sweb_E_agree regs).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at, w64. change (BASE + AF_sup_worker_env) with (BASE + SWEB_E).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msA, mat into matA, HF into HFA, HFr into HFrA, HG into HGA.
pmkst HS. sweb_md.
prreg HS (1%bv : bv 5) PA1. prreg HS (2%bv : bv 5) PA2. prreg HS (3%bv : bv 5) PA3. prreg HS (4%bv : bv 5) PA4.
prreg HS (8%bv : bv 5) PA8. prreg HS (10%bv : bv 5) PA10.
assert (GA2 : spZ (ms_regs msA) = sp0 + -48)
  by (unfold spZ at 1; rewrite PA2, Usp; apply unsigned_lit_small; lia).
assert (GA3 : getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite PA3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GA4 : getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite PA4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GA8 : getr (ms_regs msA) 8 = w64 pnn) by (rewrite PA8, (EE 12%nat 12%bv eq_refl); exact H12).
assert (GA10 : getr (ms_regs msA) 10 = w64 SWEB_FN) by (rewrite PA10; reflexivity).
assert (GA1r : YK0s.ret_ok (getr (ms_regs msA) 1))
  by (rewrite PA1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GA1a : 4096 <= bv_unsigned (getr (ms_regs msA) 1))
  by (rewrite PA1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
(* run A wrote only the frame *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W (ms_mem msA) a = rdW W mem a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem msA) (fun a => sp0 - 48 <= a < sp0) HFrA).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ) as HARA.
assert (HAroA : arodata_okP SEGS RLO RHI B (rdW W (ms_mem msA)))
  by exact (sweb_aro ly S W mem md O ly S W (ms_mem msA) _ [] 0 sp0 _ HAR HOin HJ HROD).
assert (HREPA : rec_repA B ly S (rdW W (ms_mem msA)) R O).
{ apply (sweb_rec_repA_ext ly S (rdW W mem) ly S _ R O HREP HOin).
  intros a [Ha | [Ha | ([b n] & Hbn & Ha)]]; cbn [fst snd] in *.
  - apply KA; unfold A_G_REC, REC_SIZE in Ha; lia.
  - apply KA; unfold A_REC_SPILL, SC_SIZE in Ha; lia.
  - destruct (sweb_blk_bounds ly S W mem md b n HAR (HOin _ Hbn)) as (Hb & Hc & _ & Hmr & _). apply KA; lia. }
(* ---- the call of record(16) (0x8c164) ---- *)
rewrite (CmdRecAns.rca_sig_record cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs msA) (ms_mem msA) _ SUP_WORKER_ENV_STK sp0 (sweb_FP O) ly S W mem md [] ly S _ 0
    RECORD_STK _ (EV_RECORD R) (-48) (getr (ms_regs msA) 1) [] _ HJ GA2 eq_refl ltac:(lia)
    ltac:(rewrite HRS; lia) ltac:(rewrite HRS, HST; lia) GA3 GA4 eq_refl GA1r GA1a
    ltac:(apply achain_low; unfold s0Z; rewrite GA8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1. pose proof (TRECORD fx ly S W (ms_regs msA) (ms_mem msA) _ [] SWEB_FN R O HPRE1) as T.
    unfold apost_base in T. apply T.
    + exact HAroA.
    + exact GA10.
    + unfold SWEB_FN, REC_FN_COUNT. lia.
    + exact HREPA.
    + unfold EV_SUP_WORKER_ENV, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in HEV. lia.
    + apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_WORKER_ENV. lia.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { apply sweb_awr_grec. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (sweb_awr_slot _ _ _ _ _ _ _ _ R a HC1). unfold CALL_SIZE. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
    exact (sweb_awr_blk _ _ _ _ _ _ _ _ b n a Hbn (HOin _ Hbn) Hba).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    pose proof (sweb_recfp_low ly S W mem md O R a HAR HOin HC1 Ha) as Hlo. rewrite HST in Hw. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
destruct HK2 as (F & O1 & R10 & HPermF & HFlen & HFO & HREP1 & HO1 & HBB1 & MLE1).
pose proof (proj1 HJ2) as HAR2.
rewrite PA1.
jafter_call_keep_pi HS 37%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc2 | exact HJ2 | exact Usp | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. cbn in Ha.
  pose proof (sweb_recfp_low ly S W mem md O R a HAR HOin HC1 HFa) as Hlo. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 37 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 37)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (A41 : ew E2 41 = getr regs2 10) by (rewrite HE2; reflexivity).
assert (AG2 : env_agree 32 (Ereg regs (sweb_extra regs)) E2)
  by (rewrite HE2; apply (env_agree_havoc_ge 32 37); [lia | exact AG0]).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by lia; exact Usp).
(* ---- run B: 0x8c168 .. jal arg_s (0x8c170), the format ---- *)
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msB, mat into matB, HF into HFB, HFr into HFrB, HG into HGB.
pmkst HS. sweb_md.
prreg HS (1%bv : bv 5) PB1. prreg HS (2%bv : bv 5) PB2. prreg HS (3%bv : bv 5) PB3. prreg HS (4%bv : bv 5) PB4.
prreg HS (8%bv : bv 5) PB8. prreg HS (10%bv : bv 5) PB10. prreg HS (11%bv : bv 5) PB11.
assert (GB2 : spZ (ms_regs msB) = sp0 + -48)
  by (unfold spZ at 1; rewrite PB2, Usp2; apply unsigned_lit_small; lia).
assert (GB3 : getr (ms_regs msB) 3 = w64 (as_gp B))
  by (rewrite PB3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GB4 : getr (ms_regs msB) 4 = w64 (as_tp B))
  by (rewrite PB4, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GB8 : getr (ms_regs msB) 8 = w64 pnn)
  by (rewrite PB8, OLD2 by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (GB10 : getr (ms_regs msB) 10 = w64 (rec_slot R)) by (rewrite PB10, A41; exact R10).
assert (GB11 : getr (ms_regs msB) 11 = w64 pf)
  by (rewrite PB11, OLD2 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (GB1r : YK0s.ret_ok (getr (ms_regs msB) 1))
  by (rewrite PB1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GB1a : 4096 <= bv_unsigned (getr (ms_regs msB) 1))
  by (rewrite PB1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W2 (ms_mem msB) a = rdW W2 mem2 a).
{ apply (kept_of_frame (segs := SEGS) E2 _ (w_H W2) mem2 (ms_mem msB) (fun a => sp0 - 48 <= a < sp0) HFrB).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ2) as HARB.
assert (HAroB : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem msB)))
  by exact (sweb_aro ly S W mem md O ly2 S2 W2 (ms_mem msB) _ [] _ sp0 _ HAR HOin HJ2 HROD).
assert (HRokB : cmd_ro_ok (rdW W2 (ms_mem msB))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARB HAroB).
assert (HO1in : forall pn, In pn O1 -> In pn (ablocks B ly2 S2)) by exact (sweb_O_in ly2 S2 _ _ O1 HREP1).
assert (HREPB : rec_repA B ly2 S2 (rdW W2 (ms_mem msB)) (rec_record R SWEB_FN []) O1).
{ apply (sweb_rec_repA_ext ly2 S2 (rdW W2 mem2) ly2 S2 _ _ O1 HREP1 HO1in).
  intros a [Ha | [Ha | ([b n] & Hbn & Ha)]]; cbn [fst snd] in *.
  - apply KB; unfold A_G_REC, REC_SIZE in Ha; lia.
  - apply KB; unfold A_REC_SPILL, SC_SIZE in Ha; lia.
  - destruct (sweb_blk_bounds ly2 S2 W2 mem2 md2 b n HAR2 (HO1in _ Hbn)) as (Hb & Hc & _ & Hmr & _). apply KB; lia. }
(* the blocks of the entry that are none of the recorder's are live after record, with their bytes *)
assert (HlivB : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn Hbn HnO. apply (Permutation_in _ HPermF) in Hbn. apply in_app_or in Hbn as [H | H]; [exact H|].
  exfalso. exact (HnO (HFO _ H)). }
assert (HbytB : forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k ->
  rdW W2 (ms_mem msB) a = rdW W mem a).
{ intros b k a Hbk HnO Ha. pose proof (HlivB _ Hbk HnO) as Hbk2.
  destruct (sweb_blk_bounds ly S W mem md b k HAR Hbk) as (Hb & Hbcl & Hk0 & Hkr & _).
  rewrite (KB a ltac:(lia) ltac:(lia)).
  replace a with (b + (a - b)) by lia.
  rewrite (sweb_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (a - b) HJc2 Hbk Hbk2 ltac:(lia)).
  - rewrite KA by lia. reflexivity.
  - intros HFa. apply inFP_cons in HFa as [HFa | HFa].
    { apply (sweb_blk_noimg ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. apply sweb_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in HFa as [HFa | HFa].
    { apply (sweb_blk_noimg ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. apply (sweb_slot_static R _ HC1). unfold CALL_SIZE. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exact (inFP_nil _ HFa)|].
    destruct (inFP_ablocks_fp_inv O _ HFa) as (b' & n' & Hbn & Hba).
    destruct (sweb_pair_dec (b, k) (b', n')) as [Eq | Hne]; [apply HnO; rewrite Eq; exact Hbn|].
    destruct (sweb_blk_bounds ly S W mem md b' n' HAR (HOin _ Hbn)) as (_ & _ & _ & Hnr' & _).
    destruct (sweb_blk_apart ly S W mem md b k b' n' HAR Hbk (HOin _ Hbn) Hne); lia. }
pose proof (sweb_str_at ly S W mem ly2 S2 W2 (ms_mem msB) _ O pf xf bf kf HARB Hbf HfO Hbf1 Hbf2 Hsf Hnf HlivB HbytB)
  as [HAFB HTFB].
(* ---- the call of arg_s(slot, format) (0x8c170) ---- *)
rewrite (sweb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W2 (ms_regs msB) (ms_mem msB) _ SUP_WORKER_ENV_STK sp0 (sweb_FP O) ly S W mem md [] ly2 S2 _ _
    ARG_S_STK _ EV_ARG_S (-48) (getr (ms_regs msB) 1) [] _ HJ2 GB2 eq_refl ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, HST; lia) GB3 GB4 eq_refl GB1r GB1a
    ltac:(apply achain_low; unfold s0Z; rewrite GB8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1.
    pose proof (TARG_S fx ly2 S2 W2 (ms_regs msB) (ms_mem msB) _ [] (rec_slot R) pf SWEB_FN [] (Some xf) R O1 HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HAroB.
    + exact HRokB.
    + exact GB10.
    + exact GB11.
    + reflexivity.
    + exact HREPB.
    + left. exact HAFB.
    + intros x Hx. injection Hx as <-. exact HTFB.
    + pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
      unfold EV_SUP_WORKER_ENV, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_WORKER_ENV in HLIVE. lia.
    + apply (mok_station MT S S2 (XM_SUP_WORKER_ENV MT R (Some xf) (Some xc) (Some xn)) (XM_RECORD MT R) _ MTL HMOK MLE1
        XAf).
      unfold XM_SUP_WORKER_ENV. lia.
  - intros a Ha. apply (sweb_awr_slot _ _ _ _ _ _ _ _ R a HC1). exact (sweb_argfp_in R [] a HC1 ltac:(cbn; lia) Ha).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    pose proof (sweb_slot_low R a HC1 (sweb_argfp_in R [] a HC1 ltac:(cbn; lia) Ha)) as Hlo. rewrite HST in Hw. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (HBB3 & MLE3 & [(Hc6 & _) | (_ & p1 & Hp1 & Hperm3 & Hfresh3 & HREP3)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length] in Hc6. lia. }
cbn [app] in HREP3.
set (yf := sarg (Some xf)) in *.
set (n1 := Z.of_nat (length yf) + 1) in *.
pose proof (proj1 HJ3) as HAR3.
rewrite PB1.
jafter_call_keep_pi HS 53%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc3 | exact HJ3 | exact Usp2 | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. cbn in Ha.
  pose proof (sweb_slot_low R a HC1 (sweb_argfp_in R [] a HC1 ltac:(cbn; lia) HFa)) as Hlo. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 53 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 53)%nat -> ew E3 n = ew E2 n) by (intros n' Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (AG3 : env_agree 32 (Ereg regs (sweb_extra regs)) E3)
  by (rewrite HE3; apply (env_agree_havoc_ge 32 53); [lia | exact AG2]).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by lia; exact Usp2).
(* ---- run C: 0x8c174 .. jal arg_s (0x8c17c), cpus ---- *)
paj_run_shc RUNP RUNC HS HJ3.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msC, mat into matC, HF into HFC, HFr into HFrC, HG into HGC.
pmkst HS. sweb_md.
prreg HS (1%bv : bv 5) PC1. prreg HS (2%bv : bv 5) PC2. prreg HS (3%bv : bv 5) PC3. prreg HS (4%bv : bv 5) PC4.
prreg HS (8%bv : bv 5) PC8. prreg HS (10%bv : bv 5) PC10. prreg HS (11%bv : bv 5) PC11.
assert (GC2 : spZ (ms_regs msC) = sp0 + -48)
  by (unfold spZ at 1; rewrite PC2, Usp3; apply unsigned_lit_small; lia).
assert (GC3 : getr (ms_regs msC) 3 = w64 (as_gp B))
  by (rewrite PC3, OLD3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GC4 : getr (ms_regs msC) 4 = w64 (as_tp B))
  by (rewrite PC4, OLD3, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GC8 : getr (ms_regs msC) 8 = w64 pnn)
  by (rewrite PC8, OLD3, OLD2 by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (GC10 : getr (ms_regs msC) 10 = w64 (rec_slot R)) by (rewrite PC10, OLD3 by lia; rewrite A41; exact R10).
assert (GC11 : getr (ms_regs msC) 11 = w64 pcs)
  by (rewrite PC11, OLD3, OLD2 by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (GC1r : YK0s.ret_ok (getr (ms_regs msC) 1))
  by (rewrite PC1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GC1a : 4096 <= bv_unsigned (getr (ms_regs msC) 1))
  by (rewrite PC1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W3 (ms_mem msC) a = rdW W3 mem3 a).
{ apply (kept_of_frame (segs := SEGS) E3 _ (w_H W3) mem3 (ms_mem msC) (fun a => sp0 - 48 <= a < sp0) HFrC).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ3) as HARC.
assert (HAroC : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem msC)))
  by exact (sweb_aro ly S W mem md O ly3 S3 W3 (ms_mem msC) _ [] _ sp0 _ HAR HOin HJ3 HROD).
assert (HRokC : cmd_ro_ok (rdW W3 (ms_mem msC))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARC HAroC).
assert (HO3in : forall pn, In pn ((p1, n1) :: O1) -> In pn (ablocks B ly3 S3)) by exact (sweb_O_in ly3 S3 _ _ _ HREP3).
assert (HREPC : rec_repA B ly3 S3 (rdW W3 (ms_mem msC)) (rec_record R SWEB_FN [yf]) ((p1, n1) :: O1)).
{ apply (sweb_rec_repA_ext ly3 S3 (rdW W3 mem3) ly3 S3 _ _ _ HREP3 HO3in).
  intros a [Ha | [Ha | ([b n] & Hbn & Ha)]]; cbn [fst snd] in *.
  - apply KC; unfold A_G_REC, REC_SIZE in Ha; lia.
  - apply KC; unfold A_REC_SPILL, SC_SIZE in Ha; lia.
  - destruct (sweb_blk_bounds ly3 S3 W3 mem3 md3 b n HAR3 (HO3in _ Hbn)) as (Hb & Hc & _ & Hmr & _). apply KC; lia. }
destruct (sweb_live_step ly S W mem md O R [] ly2 S2 W2 (ms_mem msB) _ ly3 S3 W3 mem3 md3 (ms_mem msC) _ _ _ _
  HAR HAR3 HC1 ltac:(cbn; lia) HJc3
  (fun pn Hbn => Permutation_in _ (Permutation_sym Hperm3) (or_intror Hbn))
  (fun a Ha => KC a ltac:(lia) ltac:(lia)) HlivB HbytB) as [HlivC HbytC].
pose proof (sweb_str_at ly S W mem ly3 S3 W3 (ms_mem msC) _ O pcs xc bc kc HARC Hbc HcO Hbc1 Hbc2 Hsc Hnc HlivC HbytC)
  as [HACC HTCC].
(* ---- the call of arg_s(slot, cpus) (0x8c17c) ---- *)
rewrite (sweb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W3 (ms_regs msC) (ms_mem msC) _ SUP_WORKER_ENV_STK sp0 (sweb_FP O) ly S W mem md [] ly3 S3 _ _
    ARG_S_STK _ EV_ARG_S (-48) (getr (ms_regs msC) 1) [] _ HJ3 GC2 eq_refl ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, HST; lia) GC3 GC4 eq_refl GC1r GC1a
    ltac:(apply achain_low; unfold s0Z; rewrite GC8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1.
    pose proof (TARG_S fx ly3 S3 W3 (ms_regs msC) (ms_mem msC) _ [] (rec_slot R) pcs SWEB_FN [yf] (Some xc) R
      ((p1, n1) :: O1) HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HAroC.
    + exact HRokC.
    + exact GC10.
    + exact GC11.
    + reflexivity.
    + exact HREPC.
    + left. exact HACC.
    + intros x Hx. injection Hx as <-. exact HTCC.
    + pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
      unfold EV_SUP_WORKER_ENV, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_WORKER_ENV in HLIVE. lia.
    + apply (mok_station MT S S3 (XM_SUP_WORKER_ENV MT R (Some xf) (Some xc) (Some xn))
        (XM_RECORD MT R + XM_ARG_S MT (Some xf)) _ MTL HMOK (mle_station MT S S2 S3 _ _ MTL MLE1 MLE3) XAc).
      unfold XM_SUP_WORKER_ENV. lia.
  - intros a Ha. apply (sweb_awr_slot _ _ _ _ _ _ _ _ R a HC1). exact (sweb_argfp_in R [yf] a HC1 ltac:(cbn; lia) Ha).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    pose proof (sweb_slot_low R a HC1 (sweb_argfp_in R [yf] a HC1 ltac:(cbn; lia) Ha)) as Hlo. rewrite HST in Hw. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HK4).
destruct HK4 as (HBB4 & MLE4 & [(Hc6 & _) | (_ & p2 & Hp2 & Hperm4 & Hfresh4 & HREP4)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length] in Hc6. lia. }
cbn [app] in HREP4.
set (yc := sarg (Some xc)) in *.
set (n2 := Z.of_nat (length yc) + 1) in *.
pose proof (proj1 HJ4) as HAR4.
rewrite PC1.
jafter_call_keep_pi HS 69%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc4 | exact HJ4 | exact Usp3 | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. cbn in Ha.
  pose proof (sweb_slot_low R a HC1 (sweb_argfp_in R [yf] a HC1 ltac:(cbn; lia) HFa)) as Hlo. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 69 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 69)%nat -> ew E4 n = ew E3 n) by (intros n' Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (AG4 : env_agree 32 (Ereg regs (sweb_extra regs)) E4)
  by (rewrite HE4; apply (env_agree_havoc_ge 32 69); [lia | exact AG3]).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by lia; exact Usp3).
(* ---- run D: 0x8c180 .. jal arg_s (0x8c188), nice ---- *)
paj_run_shc RUNP RUNC HS HJ4.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp4 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msD, mat into matD, HF into HFD, HFr into HFrD, HG into HGD.
pmkst HS. sweb_md.
prreg HS (1%bv : bv 5) PD1. prreg HS (2%bv : bv 5) PD2. prreg HS (3%bv : bv 5) PD3. prreg HS (4%bv : bv 5) PD4.
prreg HS (8%bv : bv 5) PD8. prreg HS (10%bv : bv 5) PD10. prreg HS (11%bv : bv 5) PD11.
assert (GD2 : spZ (ms_regs msD) = sp0 + -48)
  by (unfold spZ at 1; rewrite PD2, Usp4; apply unsigned_lit_small; lia).
assert (GD3 : getr (ms_regs msD) 3 = w64 (as_gp B))
  by (rewrite PD3, OLD4, OLD3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GD4 : getr (ms_regs msD) 4 = w64 (as_tp B))
  by (rewrite PD4, OLD4, OLD3, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GD8 : getr (ms_regs msD) 8 = w64 pnn)
  by (rewrite PD8, OLD4, OLD3, OLD2 by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (GD10 : getr (ms_regs msD) 10 = w64 (rec_slot R)) by (rewrite PD10, OLD4, OLD3 by lia; rewrite A41; exact R10).
assert (GD11 : getr (ms_regs msD) 11 = w64 pnn)
  by (rewrite PD11, OLD4, OLD3, OLD2 by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (GD1r : YK0s.ret_ok (getr (ms_regs msD) 1))
  by (rewrite PD1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GD1a : 4096 <= bv_unsigned (getr (ms_regs msD) 1))
  by (rewrite PD1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W4 (ms_mem msD) a = rdW W4 mem4 a).
{ apply (kept_of_frame (segs := SEGS) E4 _ (w_H W4) mem4 (ms_mem msD) (fun a => sp0 - 48 <= a < sp0) HFrD).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp4 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ4) as HARD.
assert (HAroD : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem msD)))
  by exact (sweb_aro ly S W mem md O ly4 S4 W4 (ms_mem msD) _ [] _ sp0 _ HAR HOin HJ4 HROD).
assert (HRokD : cmd_ro_ok (rdW W4 (ms_mem msD))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARD HAroD).
assert (HO4in : forall pn, In pn ((p2, n2) :: (p1, n1) :: O1) -> In pn (ablocks B ly4 S4))
  by exact (sweb_O_in ly4 S4 _ _ _ HREP4).
assert (HREPD : rec_repA B ly4 S4 (rdW W4 (ms_mem msD)) (rec_record R SWEB_FN [yf; yc]) ((p2, n2) :: (p1, n1) :: O1)).
{ apply (sweb_rec_repA_ext ly4 S4 (rdW W4 mem4) ly4 S4 _ _ _ HREP4 HO4in).
  intros a [Ha | [Ha | ([b n] & Hbn & Ha)]]; cbn [fst snd] in *.
  - apply KD; unfold A_G_REC, REC_SIZE in Ha; lia.
  - apply KD; unfold A_REC_SPILL, SC_SIZE in Ha; lia.
  - destruct (sweb_blk_bounds ly4 S4 W4 mem4 md4 b n HAR4 (HO4in _ Hbn)) as (Hb & Hc & _ & Hmr & _). apply KD; lia. }
destruct (sweb_live_step ly S W mem md O R [yf] ly3 S3 W3 (ms_mem msC) _ ly4 S4 W4 mem4 md4 (ms_mem msD) _ _ _ _
  HAR HAR4 HC1 ltac:(cbn; lia) HJc4
  (fun pn Hbn => Permutation_in _ (Permutation_sym Hperm4) (or_intror Hbn))
  (fun a Ha => KD a ltac:(lia) ltac:(lia)) HlivC HbytC) as [HlivD HbytD].
pose proof (sweb_str_at ly S W mem ly4 S4 W4 (ms_mem msD) _ O pnn xn bn kn HARD HBn HnnO HBn1 HBn2 Hsn Hnn HlivD HbytD)
  as [HANDd HTNDd].
(* ---- the call of arg_s(slot, nice) (0x8c188) ---- *)
rewrite (sweb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W4 (ms_regs msD) (ms_mem msD) _ SUP_WORKER_ENV_STK sp0 (sweb_FP O) ly S W mem md [] ly4 S4 _ _
    ARG_S_STK _ EV_ARG_S (-48) (getr (ms_regs msD) 1) [] _ HJ4 GD2 eq_refl ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, HST; lia) GD3 GD4 eq_refl GD1r GD1a
    ltac:(apply achain_low; unfold s0Z; rewrite GD8; unfold w64; rewrite unsigned_lit_small by lia; lia)).
  - intros HPRE1.
    pose proof (TARG_S fx ly4 S4 W4 (ms_regs msD) (ms_mem msD) _ [] (rec_slot R) pnn SWEB_FN [yf; yc] (Some xn) R
      ((p2, n2) :: (p1, n1) :: O1) HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HAroD.
    + exact HRokD.
    + exact GD10.
    + exact GD11.
    + reflexivity.
    + exact HREPD.
    + left. exact HANDd.
    + intros x Hx. injection Hx as <-. exact HTNDd.
    + pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _).
      unfold EV_SUP_WORKER_ENV, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_WORKER_ENV in HLIVE. lia.
    + apply (mok_station MT S S4 (XM_SUP_WORKER_ENV MT R (Some xf) (Some xc) (Some xn))
        (XM_RECORD MT R + XM_ARG_S MT (Some xf) + XM_ARG_S MT (Some xc)) _ MTL HMOK
        (mle_station MT S S3 S4 _ _ MTL (mle_station MT S S2 S3 _ _ MTL MLE1 MLE3) MLE4) XAn).
      unfold XM_SUP_WORKER_ENV. lia.
  - intros a Ha. apply (sweb_awr_slot _ _ _ _ _ _ _ _ R a HC1).
    exact (sweb_argfp_in R [yf; yc] a HC1 ltac:(cbn; lia) Ha).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    pose proof (sweb_slot_low R a HC1 (sweb_argfp_in R [yf; yc] a HC1 ltac:(cbn; lia) Ha)) as Hlo.
    rewrite HST in Hw. lia. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HK5).
destruct HK5 as (HBB5 & MLE5 & [(Hc6 & _) | (_ & p3 & Hp3 & Hperm5 & Hfresh5 & HREP5)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length] in Hc6. lia. }
cbn [app] in HREP5.
set (yn := sarg (Some xn)) in *.
set (n3 := Z.of_nat (length yn) + 1) in *.
pose proof (proj1 HJ5) as HAR5.
rewrite PD1.
jafter_call_keep_pi HS 85%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc5 | exact HJ5 | exact Usp4 | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. cbn in Ha.
  pose proof (sweb_slot_low R a HC1 (sweb_argfp_in R [yf; yc] a HC1 ltac:(cbn; lia) HFa)) as Hlo. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
remember (havoc E4 85 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
assert (OLD5 : forall n, (n < 85)%nat -> ew E5 n = ew E4 n) by (intros n' Hn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hn).
assert (AG5 : env_agree 32 (Ereg regs (sweb_extra regs)) E5)
  by (rewrite HE5; apply (env_agree_havoc_ge 32 85); [lia | exact AG4]).
clear HE5.
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by lia; exact Usp4).
(* ---- run E: 0x8c18c .. jal rec_shape_of (0x8c198) ---- *)
paj_run_shc RUNP RUNC HS HJ5.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp5 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msE, mat into matE, HF into HFE, HFr into HFrE, HG into HGE.
pmkst HS. sweb_md.
prreg HS (1%bv : bv 5) PE1. prreg HS (2%bv : bv 5) PE2. prreg HS (3%bv : bv 5) PE3. prreg HS (4%bv : bv 5) PE4.
prreg HS (10%bv : bv 5) PE10. prreg HS (11%bv : bv 5) PE11.
assert (GE2 : spZ (ms_regs msE) = sp0 + -48)
  by (unfold spZ at 1; rewrite PE2, Usp5; apply unsigned_lit_small; lia).
assert (GE3 : getr (ms_regs msE) 3 = w64 (as_gp B))
  by (rewrite PE3, OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (GE4 : getr (ms_regs msE) 4 = w64 (as_tp B))
  by (rewrite PE4, OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (GE10 : getr (ms_regs msE) 10 = w64 SWEB_VERB).
{ rewrite PE10. unfold w64. rewrite <- (sweb_vobj VOBJS).
  apply img_env_atomP; [exact HEI5 | unfold SWEB_VOBJ, A_OBJ, A_TEXT, A_LIM; lia]. }
assert (GE11 : getr (ms_regs msE) 11 = w64 (Z.of_nat (length sweb_verb))) by (rewrite PE11; reflexivity).
assert (GE1r : YK0s.ret_ok (getr (ms_regs msE) 1))
  by (rewrite PE1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GE1a : 4096 <= bv_unsigned (getr (ms_regs msE) 1))
  by (rewrite PE1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W5 (ms_mem msE) a = rdW W5 mem5 a).
{ apply (kept_of_frame (segs := SEGS) E5 _ (w_H W5) mem5 (ms_mem msE) (fun a => sp0 - 48 <= a < sp0) HFrE).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp5 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ5) as HARE.
assert (HAroE : arodata_okP SEGS RLO RHI B (rdW W5 (ms_mem msE)))
  by exact (sweb_aro ly S W mem md O ly5 S5 W5 (ms_mem msE) _ [] _ sp0 _ HAR HOin HJ5 HROD).
assert (HRokE : cmd_ro_ok (rdW W5 (ms_mem msE))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARE HAroE).
(* ---- the call of rec_shape_of("worker_env", 10) (0x8c198) ---- *)
rewrite (sweb_sig_rso cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W5 (ms_regs msE) (ms_mem msE) _ SUP_WORKER_ENV_STK sp0 (sweb_FP O) ly S W mem md [] ly5 S5 _ _
    REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-48) (getr (ms_regs msE) 1) _ HJ5 GE2 eq_refl ltac:(lia)
    ltac:(rewrite HSS; lia) ltac:(rewrite HSS, HST; lia) GE3 GE4 eq_refl GE1r GE1a).
  - intros HPRE1. pose proof (TREC_SHAPE_OF fx ly5 S5 W5 (ms_regs msE) (ms_mem msE) _ SWEB_VERB sweb_verb HPRE1 HAroE GE10
      ltac:(unfold SWEB_VERB; lia) GE11 ltac:(rewrite sweb_verb_len; lia) HRokE VOBJS
      (sweb_verb_ok B HB ly5 S5 W5 (ms_mem msE) HRokE CMD_RO_IN)) as T.
    unfold apost_base in T. apply T.
    pose proof HJ5 as (_ & _ & _ & _ & _ & _ & Hnev5 & _).
    unfold EV_SUP_WORKER_ENV, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJc6 & HP6 &
  ((q & Hq10 & Hq64 & HqA) & Hperm6 & Ely6 & ES6)).
pose proof (proj1 HJ6) as HAR6.
rewrite PE1.
jafter_call_keep_pi HS 101%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0]%nat HS6.
match type of HS6 with ?t -> _ => assert (HRK : t); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc6 | exact HJ6 | exact Usp5 | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a _ HFa. exact (inFP_nil a HFa). }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc E5 101 (map (getr regs6) CLOB)) as E6 eqn:HE6 in HS.
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc; [exact HEI5 | cbv; lia]).
assert (OLD6 : forall n, (n < 101)%nat -> ew E6 n = ew E5 n) by (intros n' Hn; rewrite HE6; apply YN3v.ew_havoc_old; exact Hn).
assert (A105 : ew E6 105 = getr regs6 10) by (rewrite HE6; reflexivity).
assert (AG6 : env_agree 32 (Ereg regs (sweb_extra regs)) E6)
  by (rewrite HE6; apply (env_agree_havoc_ge 32 101); [lia | exact AG5]).
clear HE6.
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by lia; exact Usp5).
(* ---- run F: 0x8c19c .. j answer (0x8c1c0) ---- *)
paj_run_shc RUNP RUNC HS HJ6.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp6 | cbn; rewrite HST; lia | cbn; lia | apply awr_ok_nil]. }
rename ms into msF, mat into matF, HF into HFF, HFr into HFrF, HG into HGF.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (mdF := m) in *; clearbody mdF end.
prreg HS (1%bv : bv 5) PF1. prreg HS (2%bv : bv 5) PF2. prreg HS (3%bv : bv 5) PF3. prreg HS (4%bv : bv 5) PF4.
prreg HS (8%bv : bv 5) PF8. prreg HS (10%bv : bv 5) PF10. prreg HS (11%bv : bv 5) PF11. prreg HS (12%bv : bv 5) PF12.
assert (HPA : aregs_preserved regs (ms_regs msF))
  by exact (aregs_preserved_of_st_ok SEGS (w_H W6) E6 _ msF regs (sweb_extra regs) HS AG6 ltac:(vm_compute; reflexivity)).
assert (XF1 : getr (ms_regs msF) 1 = getr regs 1)
  by (rewrite PF1, OLD6, OLD5, OLD4, OLD3, OLD2 by lia; exact (EE 1%nat 1%bv eq_refl)).
assert (SPF : spZ (ms_regs msF) = sp0)
  by (unfold spZ at 1; rewrite PF2, OLD6, OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (XF3 : getr (ms_regs msF) 3 = w64 (as_gp B))
  by (rewrite PF3, OLD6, OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (XF4 : getr (ms_regs msF) 4 = w64 (as_tp B))
  by (rewrite PF4, OLD6, OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (XF8 : s0Z (ms_regs msF) = s0Z regs)
  by (unfold s0Z; rewrite PF8, OLD6, OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 8%nat 8%bv eq_refl); reflexivity).
assert (GF10 : getr (ms_regs msF) 10 = w64 (rec_slot R))
  by (rewrite PF10, OLD6, OLD5, OLD4, OLD3 by lia; rewrite A41; exact R10).
assert (GF11 : getr (ms_regs msF) 11 = w64 q) by (rewrite PF11, A105; exact Hq10).
assert (GF12 : getr (ms_regs msF) 12 = Z_to_bv 64 1) by (rewrite PF12; reflexivity).
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W6 (ms_mem msF) a = rdW W6 mem6 a).
{ apply (kept_of_frame (segs := SEGS) E6 _ (w_H W6) mem6 (ms_mem msF) (fun a => sp0 - 48 <= a < sp0) HFrF).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp6 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ6) as HARF.
(* ---- the state at the jump, against the earlier states ---- *)
assert (Hn1 : 1 <= n1) by (subst n1; lia).
assert (Hn2 : 1 <= n2) by (subst n2; lia).
assert (Hn3 : 1 <= n3) by (subst n3; lia).
assert (H2to3 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros pn Hbn; apply (Permutation_in _ (Permutation_sym Hperm3)); right; exact Hbn).
assert (H3to4 : forall pn, In pn (ablocks B ly3 S3) -> In pn (ablocks B ly4 S4))
  by (intros pn Hbn; apply (Permutation_in _ (Permutation_sym Hperm4)); right; exact Hbn).
assert (H4to5 : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly5 S5))
  by (intros pn Hbn; apply (Permutation_in _ (Permutation_sym Hperm5)); right; exact Hbn).
assert (H5to6 : forall pn, In pn (ablocks B ly5 S5) -> In pn (ablocks B ly6 S6))
  by (intros pn Hbn; apply (Permutation_in _ (Permutation_sym Hperm6)); exact Hbn).
assert (H6to5 : forall pn, In pn (ablocks B ly6 S6) -> In pn (ablocks B ly5 S5))
  by (intros pn Hbn; apply (Permutation_in _ Hperm6); exact Hbn).
assert (H2to6 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly6 S6))
  by (intros pn Hbn; exact (H5to6 _ (H4to5 _ (H3to4 _ (H2to3 _ Hbn))))).
assert (H5cases : forall pn, In pn (ablocks B ly5 S5) ->
  pn = (p3, n3) \/ pn = (p2, n2) \/ pn = (p1, n1) \/ In pn (ablocks B ly2 S2)).
{ intros pn H5. apply (Permutation_in _ Hperm5) in H5. destruct H5 as [<- | H4]; [left; reflexivity|].
  apply (Permutation_in _ Hperm4) in H4. destruct H4 as [<- | H3]; [right; left; reflexivity|].
  apply (Permutation_in _ Hperm3) in H3. destruct H3 as [<- | H2]; [right; right; left; reflexivity|].
  right; right; right; exact H2. }
assert (HSsplit : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2) \/ In pn F)
  by (intros pn Hbn; apply in_app_or; exact (Permutation_in _ HPermF Hbn)).
assert (HFnot : forall pn, In pn F -> ~ In pn (ablocks B ly2 S2))
  by (intros pn HFi H2; exact (sweb_dup_false ly S W mem md (ablocks B ly2 S2) F pn HAR HPermF H2 HFi)).
assert (Hf1 : ~ In (p1, n1) (ablocks B ly2 S2)) by exact (sweb_fresh_notin _ p1 n1 Hn1 Hfresh3).
assert (Hf2 : ~ In (p2, n2) (ablocks B ly2 S2))
  by (intros H2; exact (sweb_fresh_notin _ p2 n2 Hn2 Hfresh4 (H2to3 _ H2))).
assert (Hf3 : ~ In (p3, n3) (ablocks B ly2 S2))
  by (intros H2; exact (sweb_fresh_notin _ p3 n3 Hn3 Hfresh5 (H3to4 _ (H2to3 _ H2)))).
set (O3 := (p3, n3) :: (p2, n2) :: (p1, n1) :: O1) in *.
assert (HO3S : forall pn, In pn O3 -> In pn (ablocks B ly S) -> In pn O).
{ intros pn Hbn HS'. destruct Hbn as [<- | [<- | [<- | H1]]]; [| | | exact (proj1 (proj1 (HO1 pn) H1))];
  (destruct (HSsplit _ HS') as [H2 | HFi]; [exfalso | exact (HFO _ HFi)]);
  [exact (Hf3 H2) | exact (Hf2 H2) | exact (Hf1 H2)]. }
assert (HO3in5 : forall pn, In pn O3 -> In pn (ablocks B ly5 S5)) by exact (sweb_O_in ly5 S5 _ _ _ HREP5).
assert (HO3in6 : forall pn, In pn O3 -> In pn (ablocks B ly6 S6)) by (intros pn Hbn; exact (H5to6 _ (HO3in5 _ Hbn))).
assert (HREPF : rec_repA B ly6 S6 (rdW W6 (ms_mem msF)) (rec_record R SWEB_FN [yf; yc; yn]) O3).
{ apply (sweb_rec_repA_ext ly5 S5 (rdW W5 mem5) ly6 S6 _ _ _ HREP5 HO3in6).
  assert (K56 : forall a, 0 <= a < alloc_ceiling -> (Exists (in_zr a) TFIB_PROG_STATIC \/
     exists b m, In (b, m) (ablocks B ly5 S5) /\ b <= a < b + req_size m) ->
     rdW W6 (ms_mem msF) a = rdW W5 mem5 a).
  { intros a Ha Hc. rewrite KF by lia.
    destruct Hc as [HP | (b & m & Hbm & Hba)].
    - rewrite (sweb_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc6 (Forall_nil _) (inFP_nil a) HP). apply KE; lia.
    - replace a with (b + (a - b)) by lia.
      rewrite (sweb_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (a - b) HJc6 Hbm (H5to6 _ Hbm) ltac:(lia) (inFP_nil _)).
      apply KE; lia. }
  intros a [Ha | [Ha | ([b m] & Hbn & Ha)]]; cbn [fst snd] in *.
  - apply K56; [unfold A_G_REC, REC_SIZE in Ha; lia | left; exact (sweb_grec_in a Ha)].
  - apply K56; [unfold A_REC_SPILL, SC_SIZE in Ha; lia | left; exact (sweb_spill_in a Ha)].
  - destruct (sweb_blk_bounds ly5 S5 W5 mem5 md5 b m HAR5 (HO3in5 _ Hbn)) as (Hb & Hc & _ & Hmr & _).
    apply K56; [lia | right; exists b, m; split; [exact (HO3in5 _ Hbn) | lia]]. }
pose proof HREPF as (QF & HQF & HOQF).
destruct (sweb_old_at _ _ _ _ HQF) as [HOLD HOLDin'].
set (old := sweb_old QF) in *.
assert (HOLDin : forall pn, In pn (ablocks B ly6 S6) -> fst pn = old -> In pn O3).
{ intros pn Hbn Hf. unfold old, sweb_old in Hf. destruct (l_answer QF) as [an|] eqn:Ean.
  - pose proof (HOLDin' an eq_refl) as Han. apply HOQF in Han.
    rewrite (sweb_same_start ly6 S6 W6 mem6 md6 pn an HAR6 Hbn (HO3in6 _ Han) Hf). exact Han.
  - destruct pn as [b m]. destruct (sweb_blk_bounds ly6 S6 W6 mem6 md6 b m HAR6 Hbn) as (Hb & _). cbn [fst] in Hf. lia. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ unfold old, sweb_old. destruct (l_answer QF) as [an|] eqn:Ean; [|lia].
  pose proof (HOLDin' an eq_refl) as Han. apply HOQF in Han. destruct an as [a1 a2].
  destruct (sweb_blk_bounds ly6 S6 W6 mem6 md6 a1 a2 HAR6 (HO3in6 _ Han)) as (Hb0 & Hb1 & _ & _ & Hr1). cbn [fst]. lia. }
assert (HAroF : arodata_okP SEGS RLO RHI B (rdW W6 (ms_mem msF)))
  by exact (sweb_aro ly S W mem md O ly6 S6 W6 (ms_mem msF) _ [] _ sp0 _ HAR HOin HJ6 HROD).
assert (HM : sup_worker_env_m R (Some xf) (Some xc) (Some xn) =
  rec_answer (rec_record R SWEB_FN [yf; yc; yn]) (SWEB_FN, [yf; yc; yn]) (shape_of sweb_verb) true)
  by exact (sweb_m R (Some xf) (Some xc) (Some xn)).
assert (MLEJ : mo_le MT S S6 (XM_RECORD MT R + XM_ARG_S MT (Some xf) + XM_ARG_S MT (Some xc) + XM_ARG_S MT (Some xn) + 0)).
{ apply (mle_station MT S S5 S6 _ 0 MTL
    (mle_station MT S S4 S5 _ _ MTL (mle_station MT S S3 S4 _ _ MTL (mle_station MT S S2 S3 _ _ MTL MLE1 MLE3) MLE4) MLE5)).
  rewrite ES6. exact (mo_le_refl MT MTL S5). }
pose proof HJ6 as (_ & _ & _ & _ & _ & HfrF & HnevF & _).
(* ---- the tail jump into answer (0x8c1c0): answer runs at the entry's sp and returns to the entry's ra ---- *)
rewrite (sweb_sig_answer cmd_sig_prog_PB).
assert (HPREA : afn_pre SEGS B ANSWER_STK ly6 S6 W6 (ms_regs msF) (ms_mem msF) mdF ch).
{ apply (afn_pre_at SEGS B SUP_WORKER_ENV_STK sp0 (sweb_FP O) ly S W mem md [] ly6 S6 W6 (ms_mem msF) mdF _
    (ms_regs msF) ANSWER_STK 0 ch HJ6).
  - rewrite SPF. lia.
  - reflexivity.
  - lia.
  - rewrite HNS. lia.
  - rewrite HNS, HST. lia.
  - rewrite XF1. exact Hra.
  - unfold raZ. rewrite XF1. exact Hra4.
  - exact XF3.
  - exact XF4.
  - rewrite SPF, XF8. apply (sweb_achain_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6).
    + intros a Ha. exact (proj2 (HFPlow a Ha)).
    + exact Hch. }
eapply SRr_mono.
{ pose proof (TANSWER fx ly6 S6 W6 (ms_regs msF) (ms_mem msF) mdF ch (rec_slot R) q old (SWEB_FN, [yf; yc; yn])
    (shape_of sweb_verb) true (rec_record R SWEB_FN [yf; yc; yn]) O3 HPREA HFRM) as T.
  cbv zeta in T. apply T; clear T.
  - rewrite HfrF. cbn [app]. exact HFR8.
  - exact HAroF.
  - exact (cmd_ro_ok_of_aro _ _ _ _ _ HARF HAroF).
  - exact GF10.
  - destruct (sweb_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    rewrite Hs. unfold A_REC_SPILL. lia.
  - exact GF11.
  - exact Hq64.
  - rewrite GF12. reflexivity.
  - exact HREPF.
  - exact HOLD.
  - exact Hold64.
  - intros _. split; [|exact sweb_fits].
    apply (sweb_argA_kept _ _ (rdW W6 mem6)); [exact (HqA _)|]. intros i Hi.
    pose proof (sweb_argA_low ly6 S6 W6 mem6 md6 [] q _ HAR6 (HqA []) i Hi) as Hlo. apply KF; lia.
  - intros _ _. exact (sweb_answer_slot R [yf; yc; yn]).
  - unfold EV_SUP_WORKER_ENV, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
  - rewrite ES6. unfold LIVE_SUP_WORKER_ENV in HLIVE. rewrite HM in HLIVE. lia.
  - apply (mok_station MT S S6 (XM_SUP_WORKER_ENV MT R (Some xf) (Some xc) (Some xn)) _ _ MTL HMOK MLEJ (XN0 _)).
    unfold XM_SUP_WORKER_ENV. rewrite HM. lia. }
cbv beta. intros W7 c7 _ (fx7 & ly7 & S7 & regs7 & mem7 & md7 & -> & HFX7 & HCSR7 & HJA & HPA7 & HQ7).
cbv zeta in HQ7.
destruct HQ7 as (q1 & q2 & O' & Hq2 & Hq2a & Hq12 & Hfr12 & Hbl & HrepF & HO' & Hstr & HBB7 & Hmle).
set (t := snd (rec_answer (rec_record R SWEB_FN [yf; yc; yn]) (SWEB_FN, [yf; yc; yn]) (shape_of sweb_verb) true)) in *.
set (nT := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJA) as HAR7.
assert (Hnew12 : forall pn, In pn (ablocks B ly S) -> (pn = (q1, nT) \/ pn = (q2, nT)) -> In pn O).
{ intros pn HS' Heq. destruct (HSsplit _ HS') as [H2 | HFi]; [|exact (HFO _ HFi)].
  pose proof (H2to6 _ H2) as H6.
  destruct (Z.eq_dec (fst pn) old) as [Ho | Ho]; [exact (HO3S _ (HOLDin _ H6 Ho) HS')|].
  exfalso. destruct (Hfr12 pn H6 Ho) as [N1 N2]. destruct Heq as [Heq | Heq]; [exact (N1 Heq) | exact (N2 Heq)]. }
unfold apost_baseF. exists fx7, ly7, S7, regs7, mem7, md7.
split; [rewrite XF1; reflexivity|].
split; [exact HFX7|]. split; [exact HCSR7|].
split.
{ assert (HJF : ajournal SEGS B SUP_WORKER_ENV_STK sp0 (sweb_FP O) ly S W mem md ([] ++ []) ly7 S7 W7 mem7 md7
    ((0 + EV_RECORD R + EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_REC_SHAPE_OF) + EV_ANSWER)).
  { eapply ajournal_sub_wide.
    all: try first [exact LAWS | exact Hsegs | exact HJ6 | exact HJA].
    all: lazymatch goal with
    | |- forall a, inFP _ a -> awr_byte _ _ _ _ _ _ _ _ _ _ a =>
        intros a Ha;
        apply inFP_cons in Ha as [Ha | Ha]; [apply sweb_awr_grec; unfold OFF_ANSWER, REC_SIZE in *; lia|];
        apply inFP_cons in Ha as [Ha | Ha]; [apply sweb_awr_grec; unfold OFF_STATE, REC_SIZE in *; lia|];
        destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba);
        apply sweb_in_filter in Hbm as [Hbm _];
        destruct (in_dec sweb_pair_dec (b, m) O) as [HbO | HbnO];
        [ exact (sweb_awr_blk _ _ _ _ _ _ _ _ b m a HbO (HO3in6 _ Hbm) Hba)
        | right; right; left; exists b, m; split; [exact (HO3in6 _ Hbm)|];
          split; [intros HbS; exact (HbnO (HO3S _ Hbm HbS)) | exact Hba] ]
    | |- forall a, inFP _ a -> _ =>
        intros a Ha Hs _; exfalso; rewrite HST in Hs;
        apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_ANSWER in Ha; lia|];
        apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|];
        destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba);
        apply sweb_in_filter in Hbm as [Hbm _];
        destruct (sweb_blk_bounds ly6 S6 W6 mem6 md6 b m HAR6 (HO3in6 _ Hbm)) as (Hb & Hc & _); lia
    | |- _ => rewrite ?SPF, ?HNS, ?HST; lia
    end. }
  cbn [app] in HJF. apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF).
  unfold EV_SUP_WORKER_ENV, EV_REC_SHAPE_OF. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPA HPA7)|].
exists (fst (rec_answer (rec_record R SWEB_FN [yf; yc; yn]) (SWEB_FN, [yf; yc; yn]) (shape_of sweb_verb) true)), t, q2, O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact Hq2|]. split; [exact Hq2a|]. split; [exact HrepF|].
split.
{ intros pn Hbn. destruct (in_dec sweb_pair_dec pn (ablocks B ly S)) as [HS' | HnS]; [left | right; exact HnS].
  apply HO' in Hbn as [[H3 _] | ->]; [exact (HO3S pn H3 HS') | exact (Hnew12 _ HS' (or_introl eq_refl))]. }
split; [apply Hbl; right; right; reflexivity|].
split; [intros pn HS' HnO Heq; subst pn; exact (HnO (Hnew12 _ HS' (or_intror eq_refl)))|].
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hf & Hbn).
  pose proof (sweb_O_in ly7 S7 _ _ _ HrepF pn Hbn) as Hbn7.
  pose proof (proj2 (Hbl (q2, nT)) (or_intror (or_intror eq_refl))) as Hq7.
  pose proof (sweb_same_start ly7 S7 W7 mem7 md7 pn (q2, nT) HAR7 Hbn7 Hq7 Hf) as ->.
  apply HO' in Hbn as [[Hbn1' Hfo] | Heq];
  [exact (proj2 (Hfr12 _ (HO3in6 _ Hbn1') Hfo) eq_refl) | injection Heq as Heq; exact (Hq12 (eq_sym Heq))]. }
split; [exact Hstr|].
split.
{ intros pn Hbn HnO.
  assert (H2 : In pn (ablocks B ly2 S2)).
  { destruct (HSsplit _ Hbn) as [H | H]; [exact H | exfalso; exact (HnO (HFO _ H))]. }
  pose proof (H2to6 _ H2) as H6.
  assert (Ho : fst pn <> old) by (intros Hf; exact (HnO (HO3S _ (HOLDin _ H6 Hf) Hbn))).
  assert (H7 : In pn (ablocks B ly7 S7)) by (apply Hbl; left; split; [exact H6 | exact Ho]).
  split; [exact H7|].
  pose proof (proj2 (Hbl (q2, nT)) (or_intror (or_intror eq_refl))) as Hq7.
  destruct pn as [b m]. cbn [fst snd].
  assert (Hne : (b, m) <> (q2, nT)) by exact (proj2 (Hfr12 (b, m) H6 Ho)).
  destruct (sweb_blk_bounds ly7 S7 W7 mem7 md7 b m HAR7 H7) as (_ & _ & Hm0 & Hmr & _).
  destruct (sweb_blk_bounds ly7 S7 W7 mem7 md7 q2 nT HAR7 Hq7) as (_ & _ & Hn0 & Hnr & _).
  unfold iv_apart. destruct (sweb_blk_apart ly7 S7 W7 mem7 md7 b m q2 nT HAR7 H7 Hq7 Hne); lia. }
split.
{ intros pn Hbn. apply Hbl in Hbn as [[H6 Hf] | [-> | ->]].
  - destruct (H5cases _ (H6to5 _ H6)) as [-> | [-> | [-> | H2]]].
    + right; left. apply HO'. left. split; [left; reflexivity | exact Hf].
    + right; left. apply HO'. left. split; [right; left; reflexivity | exact Hf].
    + right; left. apply HO'. left. split; [right; right; left; reflexivity | exact Hf].
    + destruct (in_dec sweb_pair_dec pn O1) as [H1 | H1n].
      * right; left. apply HO'. left. split; [right; right; right; exact H1 | exact Hf].
      * left. split.
        -- apply (Permutation_in _ (Permutation_sym HPermF)). apply in_or_app. left. exact H2.
        -- intros HinO. apply H1n. apply HO1. split; [exact HinO | intros HFi; exact (HFnot _ HFi H2)].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ rewrite ES6 in HBB7. unfold LIVE_SUP_WORKER_ENV. rewrite HM. fold t. lia. }
apply (mle_weaken MT S S7 _ _ MTL (mle_station MT S S6 S7 _ _ MTL MLEJ Hmle)).
unfold XM_SUP_WORKER_ENV. rewrite HM. fold t. lia.
Qed.

End e.
End f.
End d.

Print Assumptions tsup_worker_env_holds.
