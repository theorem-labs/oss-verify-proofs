(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helper layer of the ASan+UBSan walk of sup_reset (lib/B/Prog/sup_reset.v,
   a working branch c79a9f2daf7, :62-640, the srb_* lemmas before tsup_reset_holds), carried over under
   sivk_* names for the walk of sup_instance_verb (lib/B/Prog/sup_instance_verb.v), over the same statements (at
   a working branch 713692f1e0c) and core (a working branch c022a2f6a88). The two contracts have the same footprint
   (sup_reset_c.v:105, sup_instance_verb_c.v:142: g_rec, record.spill and the recorder's blocks), the same recorder
   representation (CmdRep.v's rec_repA) and the same string-argument form (CmdRep.v's astr_argA), so each lemma keeps
   sup_reset's statement; only the names change. One lemma hard-coded sup_reset's own call: srb_answer_slot is stated
   for record(10) with one argument (sup_reset_aux.v's SRB_FN, [x]); sivk_answer_slot takes the function id and the
   argument list. srb_pw_low and the tactic srb_md, from the same part of sup_reset.v, are carried as sivk_pw_low and
   sivk_md.
   Section hypotheses: the per-binary record CmdBSyms (HB) and the per-binary image facts in the form of a Theorem Labs lane's
   lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib, at this file's abstract segments; the record facts the lemmas use are
   a Theorem Labs lane's CmdRecRest.v lemmas over them, by exact (cmd_prog_img, cmd_ro_prog_apart, cmd_atail_kept,
   cmd_rodata_kept). No meter, no callee contract. At End d a lemma takes B, then HB and cmd_img_facts_tfib if its
   proof uses them, as explicit arguments; rc, SK and PI are implicit (RunCeil is a class, SK and PI come from the
   types), so a walk applies e.g. `sivk_FP_low B HB cmd_img_facts_tfib ly S W mem md O a HAR HOin Ha`. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c CmdRecFacts CmdRecAns.
(* CmdRecAns / CmdSnText (a Theorem Labs lane) change zify's division setting; this file's lia calls were written with it on
   (a Theorem Labs lane 14:17Z, SETTINGS TRAP) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the representation's readers (sup_reset.v:62-158, the same CmdRep forms) ---------- *)

Lemma sivk_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma sivk_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma sivk_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (sivk_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma sivk_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (sivk_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (sivk_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (sivk_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (sivk_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma sivk_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (sivk_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (sivk_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (sivk_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma sivk_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
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
    + apply (sivk_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sivk_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (sivk_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (sivk_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sivk_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma sivk_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (sivk_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma sivk_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma sivk_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

(* sivk_in_answer is the kit's CmdRecAns.rca_in_answer (b-helper-kit-map.md, 'Further copies') *)

Lemma sivk_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma sivk_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
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
    + apply (sivk_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (sivk_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (sivk_in_calls Q i P pn EP Hpn).
    + apply (sivk_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply sivk_in_spill. exact Hpn.
  - apply (sivk_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply rca_in_answer. exact Hpn.
  - apply (sivk_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply sivk_in_reply. exact Hpn.
  - apply (sivk_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

(* every block the representation names is a block of the list it is stated over: the kit's CmdRecAns.rca_call_blocks
   and CmdRecAns.rca_rep_blocks (b-helper-kit-map.md, 'Further copies') *)

(* the recorder's answer field holds 0 or the start of one of its blocks *)
Definition sivk_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma sivk_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  aval_mem rd (A_G_REC + OFF_ANSWER) 8 (sivk_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
  intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold sivk_old. split.
  - unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
    [exact (proj1 HA) | exact HA].
  - intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
Qed.

(* the slot record() returns (record_c.v rec_slot): an entry of g_rec's table, or record.spill *)
Lemma sivk_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
  (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL.
Proof.
  intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [left | right; reflexivity].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
Qed.

(* the slot fact answer's pre asks (answer_c.v:128-130), for the call record(fn) with the arguments A: sup_reset's
   srb_answer_slot is this lemma at its own call, fn = 10 (sup_reset_aux.v SRB_FN) and A = [x]; sup_instance_verb
   takes it at fn = REC_INSTANCE_VERB and A = [canon line; dec ledger] (lib/Prog/RecModel.v:135-136) *)
Lemma sivk_answer_slot : forall (fn : Z) R (A : list (list byte)),
(exists k, nth_error (r_calls (rec_record R fn A)) k = Some (fn, A) /\
   rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R = A_REC_SPILL /\ (fn, A) = r_spill (rec_record R fn A)).
Proof.
intros fn R A. unfold rec_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L].
- left. exists (length (r_calls R)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

Lemma sivk_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

(* the program's statics of the record (lib/B/YF0m.v TFIB_PROG_STATIC): g_rec, record.spill, g_quitting *)
Lemma sivk_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Ha. lia. Qed.

Lemma sivk_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

(* the footprint of the statement (sup_instance_verb_c.v:142, the same as sup_reset_c.v:105) *)
Definition sivk_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma sivk_FP_pos : forall O, (forall pn, In pn O -> 0 < fst pn) -> Forall (fun r => 0 < fst r) (sivk_FP O).
Proof.
intros O HO. unfold sivk_FP. constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
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
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), under its canonical name *)
Hypothesis HB : CmdBSyms B.
(* the per-binary image facts (a Theorem Labs lane's lib/B/Prog/CmdRecBase.v cmd_img_facts): a Theorem Labs lane proves them at the pinned image
   (CmdRecImg.v cmd_img_facts_tfib, at tfibsegs); this file is over an abstract PAImg, so it takes that lemma's
   statement at its own segments, under the lemma's name, and each per-binary fact a lemma below uses is a Theorem Labs lane's
   lemma over them, by exact: CmdRecRest.v cmd_prog_img, cmd_ro_prog_apart, cmd_atail_kept and cmd_rodata_kept *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
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

Lemma sivk_O_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HQ & HOQ) pn Hpn. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HOQ pn) Hpn)). Qed.

Lemma sivk_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

Lemma sivk_blk_noimg : forall ly S (W : world SEGS) mem md b m a, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md b m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha)))))).
Qed.

Lemma sivk_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma sivk_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (sivk_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (sivk_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (sivk_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (sivk_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* a live block is listed once *)
Lemma sivk_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
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
destruct (sivk_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* ---------- the walk's footprint and what a journal keeps ---------- *)

Lemma sivk_inFP_cases : forall O a, inFP (sivk_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold sivk_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply sivk_grec_in. exact Ha.
- left. apply sivk_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.

Lemma sivk_static_low : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> 0x10000 <= a < 0x606000.
Proof. intros a Ha. exact (pa_img_range a (cmd_prog_img a Ha)). Qed.

Lemma sivk_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (sivk_FP O) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
destruct (sivk_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)].
- pose proof (sivk_static_low a HP). lia.
- destruct (sivk_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (H4 & Hc & _). lia.
Qed.

(* arodata_okP along the walk's journal (cmd_rodata_kept: the footprint is statics and the recorder's blocks) *)
Lemma sivk_aro : forall ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp STK,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp (sivk_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O lyc Sc Wc memc mdc own k sp STK HAR HO HJ HR.
apply (cmd_rodata_kept ly S W mem md lyc Sc Wc memc mdc STK sp (sivk_FP O) own k HAR HJ); [|exact HR].
intros a Ha. destruct (sivk_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)]; [left; exact HP|].
right. exists b, n. split; [apply in_or_app; left; exact (HO _ Hin) | exact Hb].
Qed.

(* a journal keeps the image bytes outside its footprint that are neither owned statics nor the errno cell *)
Lemma sivk_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

(* the program's statics are image bytes, unowned, and not the errno cell *)
Lemma sivk_prog_unowned : forall a, Exists (in_zr a) TFIB_PROG_STATIC ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a HP. split; [exact (cmd_prog_img a HP)|].
assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (ts_prog B HB); exact HP).
destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _). split; assumption.
Qed.

(* a journal keeps the program's statics outside its footprint *)
Lemma sivk_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (sivk_prog_unowned a HP) as (H1 & H2 & H3). exact (sivk_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

(* a journal keeps the bytes outside its footprint of a block live at both of its ends *)
Lemma sivk_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

(* the stack words from a callee's sp up to ly_top stay present along the walk *)
Lemma sivk_astack : forall ly S (W : world SEGS) mem md O own lyc Sc (Wc : world SEGS) memc mdc k sp0 sp STK,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (sivk_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
astack_pres ly (w_H W) mem sp0 -> sp0 - STK <= sp -> astack_pres lyc (w_H Wc) memc sp.
Proof.
intros ly S W mem md O own lyc Sc Wc memc mdc k sp0 sp STK HAR HO HJ HP Hsp.
apply (astack_pres_mono lyc (w_H Wc) memc (sp0 - STK) sp Hsp).
eapply astack_pres_journal.
all: try first [exact LAWS | exact pa_segs_low | exact HJ | exact HP].
intros a Ha Hr. exfalso. pose proof (sivk_FP_low ly S W mem md O a HAR HO Ha) as Hlo.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _).
lia.
Qed.

(* the frame chain from sp0 is kept by a journal whose footprint lies below alloc_ceiling *)
Lemma sivk_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
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
Lemma sivk_awr_static : forall STK sp O bl0 blc fr0 ly own a, Exists (in_zr a) TFIB_PROG_STATIC -> inFP (sivk_FP O) a ->
awr_byte SEGS B STK sp (sivk_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a HP HF.
right; right; right; right; left. split; [exact HF|]. split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

Lemma sivk_awr_grec : forall STK sp O bl0 blc fr0 ly own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp (sivk_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply sivk_awr_static; [exact (sivk_grec_in a Ha)|].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma sivk_awr_spill : forall STK sp O bl0 blc fr0 ly own a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp (sivk_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply sivk_awr_static; [exact (sivk_spill_in a Ha)|].
exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

(* a byte of the slot record() returned *)
Lemma sivk_awr_slot : forall STK sp O bl0 blc fr0 ly own R a, (length (r_calls R) <= 16)%nat ->
rec_slot R <= a < rec_slot R + CALL_SIZE -> awr_byte SEGS B STK sp (sivk_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own R a HL Ha. destruct (sivk_slot_bounds R HL) as [Hs | Hs].
- apply sivk_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply sivk_awr_spill. rewrite Hs in Ha. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* a byte of one of the recorder's blocks that is live at the current state *)
Lemma sivk_awr_blk : forall STK sp O bl0 blc fr0 ly own b n a, In (b, n) O -> In (b, n) blc ->
b <= a < b + req_size n -> awr_byte SEGS B STK sp (sivk_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own b n a HO Hc Ha. right; left. split.
- unfold sivk_FP. apply inFP_cons. right. apply inFP_cons. right.
  replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b n (a - b)); [exact HO | lia].
- exists b, n. split; [exact Hc | exact Ha].
Qed.

(* ---------- the string argument ---------- *)

(* the bytes of a string argument decide astr_argA's reader part: its other parts name no reader *)
Lemma sivk_argA_kept : forall ly1 S1 (rd rd' : reader) ro O1 p v, astr_argA B ly1 S1 rd ro O1 p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly1 S1 rd' ro O1 p (Some v).
Proof.
intros ly1 S1 rd rd' ro O1 p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [|split; [exact Hl | exact Hr]].
apply (sivk_str_keep rd); [exact Hs|]. intros x Hx. replace x with (p + (x - p)) by lia. apply K. lia.
Qed.

(* a string argument's bytes lie below alloc_ceiling: a block's, or the image's *)
Lemma sivk_argA_low : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 p v, AR SEGS B ly1 S1 W1 mem1 md1 ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 p (Some v) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= p + i < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 O1 p v HAR H i Hi. cbn [astr_argA] in H. pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
- destruct Hblk as (b & m & Hin & Hb1 & Hb2).
  destruct (sivk_blk_bounds ly1 S1 W1 mem1 md1 b m HAR Hin) as (Hb & Hc & _ & Hmr & _). lia.
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia.
Qed.

(* the pointer of an optional string argument lies below alloc_ceiling *)
Lemma sivk_pw_low : forall ly S (W : world SEGS) mem md O pw which, AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pw which -> 0 <= pw < alloc_ceiling.
Proof.
intros ly S W mem md O pw which HAR H. pose proof asan_consts as (C1 & _). destruct which as [x|].
- pose proof (sivk_argA_low ly S W mem md O pw x HAR H 0 ltac:(lia)). lia.
- cbn [astr_argA] in H. subst pw. lia.
Qed.

(* the string argument from the entry to a later state: its block (none of the recorder's) is live there with its
   bytes, or its read-only bytes are the image's at both states; its word tail is kept (cmd_atail_kept) *)
Lemma sivk_arg_kept : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O pw x,
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
    * apply (sivk_str_keep (rdW W mem)); [exact HS|]. intros a Ha. apply HK. lia.
    * split; [exact Hlen|]. left. split; [|apply Forall_nil].
      exists b, k. split; [exact (Hblk (b, k) Hbk HnO) | split; [exact Hble | exact Hhi]].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc b k (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | left; split; [exact Hbk | split; [exact (Hblk (b, k) Hbk HnO) | lia]] | exact HT].
- split.
  + split; [exact Hp0|]. split.
    * apply (sivk_str_keep (rdW W mem)); [exact HS|]. intros a Ha.
      destruct (Hro (a - pw) ltac:(lia)) as (Hr & Ho & He). replace a with (pw + (a - pw)) by lia.
      rewrite (HROc _ Hr Ho He), (HRO _ Hr Ho He). reflexivity.
    * split; [exact Hlen|]. right. split; [exact Hro | exact Hck].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc 0 0 (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | right | exact HT].
    destruct (Hro (Z.of_nat (length x)) ltac:(lia)) as (Hr & Ho & _). split; [exact Hr | exact Ho].
Qed.

(* rec_repA at a state whose reader agrees on g_rec, record.spill and the recorder's blocks *)
Lemma sivk_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (sivk_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

(* a block answer frees: the recorder's block whose start is the old answer (answer_c.v:137) *)
Lemma sivk_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

End e.
End f.
End d.

(* after a symbolic run the model term grows: name it *)
Ltac sivk_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.
