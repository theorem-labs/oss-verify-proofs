(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from an earlier version of lib/A/Prog/send_message_l.v (ported there from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v, ACke.v at c8557374ad2e) for fuzz_command's program walk: the call rule for a callee whose footprint holds the program's statics (g_rec, record.spill), built on PaNoChain.v's cl_callS_wide, with its statement (send_message_k.v's cl_callS_pg_stmt) stated in the lemma and over any PAImg listing; and the transport lemmas the callers of such a callee need (readers that agree on the bytes read, a journal's footprint widened, the recorder's representation kept). send_message's own lemmas (sm_achain, ev_vr_nonneg, rec_spill_frees_nonneg) are left in its walk. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdPa PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* reads through a reader that agrees on the bytes read *)
Lemma aval_mem_kept_r : forall (rd rd' : reader) a n v,
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite HK by lia. exact (H k Hk). Qed.
Lemma abytes_atR_kept_r : forall (rd rd' : reader) a (l : list byte),
(forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma astr_atR_kept_r : forall (rd rd' : reader) a (s : list byte),
(forall x, a <= x < a + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd a s -> astr_atR rd' a s.
Proof.
intros rd rd' a s HK [H1 H2]. split; [|exact H2]. apply (abytes_atR_kept_r rd rd' a); [|exact H1].
intros x Hx. apply HK. pose proof (length_app s [Z_to_bv 8 0]) as L. cbn [length] in L. rewrite L in Hx. lia.
Qed.
(* a recorded call through a reader that agrees on the call's slot and its argument blocks, over a block list that
   holds those blocks *)
Lemma acall_at_kept : forall (bl bl' : list (Z * Z)) (rd rd' : reader) a c P,
(forall pn, In pn P -> In pn bl') ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn x, In pn P -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
acall_at bl rd a c P -> acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P HB HKa HKb (H1 & H2 & H3 & H4 & H5 & H6 & H7).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept_r rd); [intros x Hx; apply HKa; unfold CALL_OFF_FN, CALL_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact H4]|].
split; [apply (aval_mem_kept_r rd); [intros x Hx; apply HKa; unfold CALL_OFF_NARGS, CALL_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact H5]|].
split; [exact H6|].
intros k s pn Hs Hp. destruct (H7 k s pn Hs Hp) as (A1 & A2 & A3 & A4 & A5).
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
assert (HinP : In pn P) by (eapply nth_error_In; exact Hp).
split; [apply (aval_mem_kept_r rd); [intros x Hx; apply HKa; unfold CALL_OFF_ARGS, CALL_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact A1]|].
split; [exact A2|]. split; [exact (HB pn HinP)|]. split; [exact A4|].
apply (astr_atR_kept_r rd); [intros x Hx; apply (HKb pn x HinP); lia | exact A5].
Qed.

Section r.
Variable B : asyms.
(* the recorder's representation holds after any step that keeps g_rec, record.spill and the recorder's blocks *)
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O,
rec_repA B ly S rd R O -> (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/ inFP (ablocks_fp O) a ->
 rd' a = rd a) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) HB HK.
exists Q. split; [|exact HO].
assert (HBQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hp; apply HB, HO, Hp).
assert (HKg : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) by (intros a Ha; apply HK; left; exact Ha).
assert (HKs : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a)
by (intros a Ha; apply HK; right; left; exact Ha).
assert (HKb : forall pn a, In pn (lay_blocks Q) -> fst pn <= a < fst pn + snd pn -> rd' a = rd a).
{ intros [p m] a Hp Ha. apply HK. right; right. apply HO in Hp. exists (p, p + req_size m). split.
  - unfold ablocks_fp. exact (in_map (fun b => (fst b, fst b + req_size (snd b))) O (p, m) Hp).
  - cbn [fst snd] in *. unfold req_size. destruct (Z.eqb_spec m 0); lia. }
destruct HA as (Hg8 & Hs8 & Hap & HC & HAn & HRe & HSc & HOwn).
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|].
  split; [apply (aval_mem_kept_r rd); [intros x Hx; apply HKg; unfold OFF_NCALLS, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact C3]|].
  split.
  { intros i c P Hc HP. destruct (C4 i c P Hc HP) as (D1 & D2). split; [|exact D2].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    assert (HPin : forall pn, In pn P -> In pn (lay_blocks Q)).
    { intros pn Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
      split; [eapply nth_error_In; exact HP | exact Hpn]. }
    apply (acall_at_kept (ablocks B ly S) _ rd); [intros pn Hpn; apply HBQ, HPin, Hpn | | | exact D1].
    - intros x Hx. apply HKg. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    - intros pn x Hpn Hx. exact (HKb pn x (HPin pn Hpn) Hx). }
  split; [|exact C6].
  assert (HPin : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q))
  by (intros pn Hpn; unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hpn).
  apply (acall_at_kept (ablocks B ly S) _ rd); [intros pn Hpn; apply HBQ, HPin, Hpn | | | exact C5].
  - intros x Hx. apply HKs. unfold CALL_SIZE, SC_SIZE in *. lia.
  - intros pn x Hpn Hx. exact (HKb pn x (HPin pn Hpn) Hx). }
split.
{ unfold aanswer_at in *.
  assert (HPin : forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
  { intros pn Hq. unfold lay_blocks. rewrite Hq. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    cbn. left. reflexivity. }
  destruct (r_answer R) as [x|], (l_answer Q) as [pn|]; try contradiction.
  - destruct HAn as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (HPin pn eq_refl) as Hpn.
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_ANSWER, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A1]|].
    split; [exact A2|]. split; [exact (HBQ pn Hpn)|]. split; [exact A4|].
    split; [apply (astr_atR_kept_r rd); [intros y Hy; apply (HKb pn y Hpn); lia | exact A5] | exact A6].
  - apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_ANSWER, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact HAn]. }
split.
{ unfold areply_at in *.
  assert (HPin : forall pn, l_reply Q = Some pn -> In pn (lay_blocks Q)).
  { intros pn Hq. unfold lay_blocks. rewrite Hq. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
    cbn. left. reflexivity. }
  destruct (r_reply R) as [x|], (l_reply Q) as [pn|]; try contradiction.
  - destruct HRe as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (HPin pn eq_refl) as Hpn.
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A1]|].
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY_SIZE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A2]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HBQ pn Hpn)|]. split; [exact A6|].
    split; [apply (abytes_atR_kept_r rd); [intros y Hy; apply (HKb pn y Hpn); lia | exact A7] | exact A8].
  - destruct HRe as (A1 & A2).
    split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A1]|].
    apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REPLY_SIZE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact A2]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & S6).
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_REFUSE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S1]|].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_CODE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S2]|].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_NREPLIES, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S3]|].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_STATE, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S4]|].
split; [apply (aval_mem_kept_r rd); [intros y Hy; apply HKg; unfold OFF_HOST, REC_SIZE in *; cbn [Z.of_nat Pos.of_succ_nat] in Hy; lia | exact S5]|].
exact S6.
Qed.
End r.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
(* a journal with a smaller footprint is one with a larger footprint *)
Lemma ajournal_fp_widen : forall STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> inFP FP' a) -> ~ YI16.sink_open_fp FP' ->
ajournal segs B STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT) HI Hc.
assert (HS : YI16.sink_open_fp FP -> YI16.sink_open_fp FP') by (intros Ho; exfalso; apply Hc; exact (HI 0 Ho)).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [exact HS | exact Hio]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [intros a Ha Hs Hn; apply F1; [exact Ha | exact Hs | intros Hf; exact (Hn (HI a Hf))]|].
split; [intros p n i H1 H2 Hi Hn; apply (F2 p n i); [exact H1 | exact H2 | exact Hi | intros Hf; exact (Hn (HI _ Hf))]|].
split; [intros a Hi Ho He [Hsp Hnf]; apply F3; [exact Hi | exact Ho | exact He |];
split; [intros Hop; apply Hsp; exact (HS Hop) | intros Hf; exact (Hnf (HI a Hf))]|].
split; [intros cid pos a Hin Hr Hn; apply (F4 cid pos a); [exact Hin | exact Hr | intros Hf; exact (Hn (HI a Hf))]|].
split; [intros p n i H1 H2 Hi; apply HI; exact (Hgone p n i H1 H2 Hi)|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
End e.
Section j.
Context {L : ptable csym} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
Section l.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* the call rule for a callee that writes a program static (rec_clear and verbs_receive write g_rec): cgif's cl_callS
   (PaCall.v) with the footprint premise widened to the program's statics, from the kit's cl_callS_wide (PaNoChain.v):
   every byte of the callee's footprint is a block byte or a static of the image, so it lies below alloc_ceiling and
   outside the caller's stack window, which astk_ok puts at or above alloc_ceiling *)
Lemma cl_callS_pg : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ ((exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
(Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
pose proof HSTK as (_ & _ & Hlo & Hlo2 & _).
pose proof (@pa_segs_low _ L PI) as Hlow. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (LOWFP : forall a, inFP FP1 a -> a < alloc_ceiling).
{ intros a Ha. destruct (HF a Ha) as [[_ [(b & m & Hb & Hab) | (_ & Himg)]] | (b & m & Hb & _ & Hab)].
  - pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & _). lia.
  - pose proof (Hlow a Himg). lia.
  - pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & _). lia. }
assert (HWR : forall a, inFP FP1 a -> awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a).
{ intros a Ha. destruct (HF a Ha) as [[Hfp [Hbl | Hpg]] | Htmp].
  - right; left. split; [exact Hfp | exact Hbl].
  - right; right; right; right. left. split; [exact Hfp | exact Hpg].
  - right; right; left. exact Htmp. }
assert (VIS : forall ly2 S2 W2 regs2 mem2 md2, K ly2 S2 W2 regs2 mem2 md2 ->
  forall a, inFP FP1 a -> sp0 - STK <= a < sp0 -> ~ (sp0 + o - STK1 <= a < sp0 + o) -> aview SEGS (w_H W2) mem2 a <> None).
{ intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (LOWFP a Ha). lia. }
exact (cl_callS_wide B LAWS W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HWR VIS).
Qed.
End l.
End j.
End d.
