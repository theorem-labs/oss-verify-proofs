(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder and journal facts of pins_set's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan; tpins_set_spec of lib/B/Prog/pins_set_c.v, statement from a Theorem Labs lane 917ca7ac6b1).
   - the representation's kept lemmas and the store of g_rec.state: lib/A/Prog/pins_set_s2.v of
     a working branch 3cc8391594b (ps_*_kept, arep_kept, arep_set_state), with the module paths of image B;
   - the program-static and block lemmas of the B walk lib/B/Prog/socket_send.v (a working branch
     a470f91dbfb, module SSRecB);
   - the walk's own facts: the footprint, the strings at any later state of the walk, the block bookkeeping
     through record() and arg_s(), the read-only facts and the stack at a call. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_code_c pins_set_c CmdRecBase CmdRecImg CmdRecRo CmdRecRest pins_set_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* --- the representation's kept lemmas (A walk pins_set_s2.v) ------------------------------------------------ *)
Lemma psr_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.

Lemma psr_aval_mem_in : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk. apply (psr_aval_mem_kept rd); [exact H|]. intros k Hk'. apply Hk. lia. Qed.

Lemma psr_abytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi). Qed.

Lemma psr_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall x, a <= x < a + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (psr_abytes_kept rd); [exact H1|].
intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hk. lia.
Qed.

Lemma psr_acall_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn x, In pn P -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *.
split; [apply (psr_aval_mem_in rd); [exact H4 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [apply (psr_aval_mem_in rd); [exact H5 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
assert (HIn : In pn P) by exact (nth_error_In _ _ Hpn).
split; [apply (psr_aval_mem_in rd); [exact G1 | intros x Hx; apply Ha; cbn in Hx; lia]|].
split; [exact G2|]. split; [exact (Hbl pn HIn)|]. split; [exact G4|].
apply (psr_astr_kept rd); [exact G5 | intros x Hx; apply (Hp pn x HIn); lia].
Qed.

Lemma psr_lay_calls_in : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn Hi Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ Hi) | exact Hpn].
Qed.
Lemma psr_lay_spill_in : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma psr_lay_rep_in : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
rewrite H. left. reflexivity.
Qed.

Lemma psr_answer_kept : forall bl bl' (rd rd' : reader) gr t q, aanswer_at bl rd gr t q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
(forall pn x, q = Some pn -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H Hbl Ha Hp. unfold aanswer_at in *.
destruct t as [x|], q as [pn|]; try contradiction.
- destruct H as (V & Hnz & Hin & Hlen & Hstr & Hlx).
  split; [apply (psr_aval_mem_in rd); [exact V | intros y Hy; apply Ha; cbn in Hy; lia]|].
  split; [exact Hnz|]. split; [exact (Hbl pn eq_refl)|]. split; [exact Hlen|]. split; [|exact Hlx].
  apply (psr_astr_kept rd); [exact Hstr | intros y Hy; apply (Hp pn y eq_refl); lia].
- apply (psr_aval_mem_in rd); [exact H | intros y Hy; apply Ha; cbn in Hy; lia].
Qed.

Lemma psr_reply_kept : forall bl bl' (rd rd' : reader) gr y q, areply_at bl rd gr y q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
(forall pn x, q = Some pn -> fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H Hbl Ha Hp. unfold areply_at in *. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
destruct y as [x|], q as [pn|]; try contradiction.
- destruct H as (V & Vs & Hnz & Hne & Hin & Hlen & Hb & Hlx).
  split; [apply (psr_aval_mem_in rd); [exact V | intros z Hz; apply Ha; cbn in Hz; lia]|].
  split; [apply (psr_aval_mem_in rd); [exact Vs | intros z Hz; apply Ha; cbn in Hz; lia]|].
  split; [exact Hnz|]. split; [exact Hne|]. split; [exact (Hbl pn eq_refl)|]. split; [exact Hlen|]. split; [|exact Hlx].
  apply (psr_abytes_kept rd); [exact Hb | intros z Hz; apply (Hp pn z eq_refl); lia].
- destruct H as [V Vs].
  split; (apply (psr_aval_mem_in rd); [first [exact V | exact Vs] | intros z Hz; apply Ha; cbn in Hz; lia]).
Qed.

Lemma psr_scalars_kept : forall (rd rd' : reader) gr R, ag1_scalars rd gr R ->
(forall x, (gr <= x < gr + 8 \/ gr + OFF_NREPLIES <= x < gr + OFF_NREPLIES + 4 \/ gr + OFF_STATE <= x < gr + OFF_STATE + 16) ->
  rd' x = rd x) ->
ag1_scalars rd' gr R.
Proof.
intros rd rd' gr R (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh) Ha.
unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
repeat split; try lia;
  (apply (psr_aval_mem_in rd); [eassumption | intros z Hz; apply Ha; cbn in Hz; lia]).
Qed.

Definition psr_in_lblk (l : list (Z * Z)) (x : Z) : Prop := exists pn, In pn l /\ fst pn <= x < fst pn + snd pn.

(* the bytes the representation reads *)
Definition psr_rep_bytes (gr sc : Z) (Q : rlay) (x : Z) : Prop :=
(gr <= x < gr + REC_SIZE) \/ (sc <= x < sc + SC_SIZE) \/ psr_in_lblk (lay_blocks Q) x.

Lemma psr_arep_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall x, psr_rep_bytes A_G_REC A_REC_SPILL Q x -> rd' x = rd x) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN) Hk Hbl.
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply Hk; left; exact Hx).
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply Hk; right; left; exact Hx).
assert (KB : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x)
  by (intros pn x Hpn Hx; apply Hk; right; right; exists pn; split; [exact Hpn | exact Hx]).
unfold REC_SIZE, SC_SIZE in KG, KS.
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf).
  split; [exact Hlen|]. split; [exact HlenQ|].
  split; [apply (psr_aval_mem_in rd); [exact Hnc | intros x Hx; apply KG; unfold OFF_NCALLS in Hx; cbn in Hx; lia]|].
  split.
  { intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    apply (psr_acall_kept bl bl' rd rd' _ c P Hca).
    - intros pn Hpn. apply Hbl. exact (psr_lay_calls_in Q i P pn HP Hpn).
    - intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE in *. lia.
    - intros pn x Hpn Hx. exact (KB pn x (psr_lay_calls_in Q i P pn HP Hpn) Hx). }
  split; [|exact Hspf].
  apply (psr_acall_kept bl bl' rd rd' _ _ _ Hspill).
  - intros pn Hpn. apply Hbl. exact (psr_lay_spill_in Q pn Hpn).
  - intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
  - intros pn x Hpn Hx. exact (KB pn x (psr_lay_spill_in Q pn Hpn) Hx). }
split.
{ apply (psr_answer_kept bl bl' rd rd' _ _ _ HA).
  - intros pn Hq. apply Hbl. exact (psb_lay_ans_in Q pn Hq).
  - intros x Hx. apply KG. unfold OFF_ANSWER in Hx. lia.
  - intros pn x Hq Hx. exact (KB pn x (psb_lay_ans_in Q pn Hq) Hx). }
split.
{ apply (psr_reply_kept bl bl' rd rd' _ _ _ HR).
  - intros pn Hq. apply Hbl. exact (psr_lay_rep_in Q pn Hq).
  - intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE in Hx. lia.
  - intros pn x Hq Hx. exact (KB pn x (psr_lay_rep_in Q pn Hq) Hx). }
split; [|exact HOWN].
apply (psr_scalars_kept rd); [exact HSC|]. intros x Hx. apply KG. unfold OFF_NREPLIES, OFF_STATE in Hx. lia.
Qed.

(* mix_call's digest stored to g_rec.state (RecModel.v:29-30 set_state, :41 rec_mix) *)
Lemma psr_arep_set_state : forall bl (rd rd' : reader) R Q h,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall x, psr_rep_bytes A_G_REC A_REC_SPILL Q x -> ~ (A_G_REC + OFF_STATE <= x < A_G_REC + OFF_STATE + 8) -> rd' x = rd x) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_state R h) Q.
Proof.
intros bl rd rd' R Q h HA0 Hk Hst Hh.
pose proof HA0 as (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN).
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_STATE <= x < A_G_REC + OFF_STATE + 8) -> rd' x = rd x)
  by (intros x Hx Hn; apply Hk; [left; exact Hx | exact Hn]).
assert (KB : forall pn x, In pn (lay_blocks Q) -> fst pn <= x < fst pn + snd pn -> rd' x = rd x).
{ intros pn x Hpn Hx. apply Hk; [right; right; exists pn; split; [exact Hpn | exact Hx]|].
  pose proof (proj2 HOWN pn Hpn) as [D _]. unfold iv_apart, REC_SIZE, OFF_STATE in *. lia. }
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x).
{ intros x Hx. apply Hk; [right; left; exact Hx | unfold A_REC_SPILL, A_G_REC, SC_SIZE, OFF_STATE in *; lia]. }
unfold REC_SIZE, OFF_STATE in KG.
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
destruct HC as (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf).
split.
{ change (ag1_calls bl rd' A_G_REC A_REC_SPILL (set_state R h) Q) with (ag1_calls bl rd' A_G_REC A_REC_SPILL R Q).
  split; [exact Hlen|]. split; [exact HlenQ|].
  split; [apply (psr_aval_mem_in rd); [exact Hnc | intros x Hx; apply KG; unfold OFF_NCALLS in *; cbn in Hx; lia]|].
  split.
  { intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    apply (psr_acall_kept bl bl rd rd' _ c P Hca).
    - exact (psb_acall_in bl rd _ c P Hca).
    - intros x Hx. apply KG; unfold OFF_CALLS, CALL_SIZE in *; lia.
    - intros pn x Hpn Hx. exact (KB pn x (psr_lay_calls_in Q i P pn HP Hpn) Hx). }
  split; [|exact Hspf].
  apply (psr_acall_kept bl bl rd rd' _ _ _ Hspill); [exact (psb_acall_in bl rd _ _ _ Hspill) | |].
  - intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
  - intros pn x Hpn Hx. exact (KB pn x (psr_lay_spill_in Q pn Hpn) Hx). }
split.
{ cbn [r_answer set_state].
  apply (psr_answer_kept bl bl rd rd' _ _ _ HA).
  - intros pn Hq. destruct (r_answer R), (l_answer Q); cbn in HA; try contradiction; try discriminate.
    injection Hq as <-. exact (proj1 (proj2 (proj2 HA))).
  - intros x Hx. apply KG; unfold OFF_ANSWER in Hx; lia.
  - intros pn x Hq Hx. exact (KB pn x (psb_lay_ans_in Q pn Hq) Hx). }
split.
{ cbn [r_reply set_state].
  apply (psr_reply_kept bl bl rd rd' _ _ _ HR).
  - intros pn Hq. destruct (r_reply R), (l_reply Q); cbn in HR; try contradiction; try discriminate.
    injection Hq as <-. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
  - intros x Hx. apply KG; unfold OFF_REPLY, OFF_REPLY_SIZE in Hx; lia.
  - intros pn x Hq Hx. exact (KB pn x (psr_lay_rep_in Q pn Hq) Hx). }
split; [|exact HOWN].
destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh).
unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_state].
unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_HOST in *.
split; [apply (psr_aval_mem_in rd); [exact Vr | intros x Hx; apply KG; cbn in Hx; lia]|].
split; [apply (psr_aval_mem_in rd); [exact Vc | intros x Hx; apply KG; cbn in Hx; lia]|].
split; [apply (psr_aval_mem_in rd); [exact Vn | intros x Hx; apply KG; cbn in Hx; lia]|].
split; [exact Hst|].
split; [apply (psr_aval_mem_in rd); [exact Vh | intros x Hx; apply KG; cbn in Hx; lia]|].
repeat split; lia.
Qed.

(* --- program statics and blocks: the kit's lib/B/Prog/RecBLemmas.v (recb_PG, recb_pair_dec, recb_grec_in,
   recb_spill_in, list_nodup_app_disj, and Section w's recb_x_m at the hypotheses each uses: recb_prog_awr_m for a
   footprint byte of any program static, recb_call_keeps_m for a callee with an empty footprint) --------------- *)

(* --- the walk's facts, at the statement's premises ------------------------------------------------------------ *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v) and the per-binary image facts (a Theorem Labs lane's
   lib/B/Prog/CmdRecBase.v cmd_img_facts): a Theorem Labs lane proves them at the pinned image (CmdRecImg.v cmd_img_facts_tfib, at
   tfibsegs); this walk is over an abstract PAImg, so it takes that lemma's statement at its own segments, under the
   lemma's name, and each per-binary fact it uses is a Theorem Labs lane's lemma over them, by exact *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let ROB : ro_below_ofl SEGS CMD_RLO CMD_RHI := CmdRecRo.ROB (SK := SK) SEGS B LAWS HB IMG.
Let RELRO_IMG : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a := CmdRecRo.RELRO_IMG (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS CMD_RLO CMD_RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (u f l : list byte) (verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HSV : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict.
Hypothesis HREP : rec_repA B ly S (rdW W mem) R O.

(* the statement's footprint and post-condition (pins_set_c.v:124-139) *)
Definition psb_FP : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Definition psb_post : world SEGS -> config -> Prop :=
apost_baseF SEGS B PINS_SET_STK psb_FP regs ly S W mem md (EV_PINS_SET R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (r : Z) (O' : list (Z * Z)),
 pins_set_m R (Some u) (Some f) (Some l) verdict = (R', r) /\
 getr regs' 10 = w64 r /\ -2 ^ 31 <= r < 2 ^ 31 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_PINS_SET R (Some u) (Some f) (Some l) verdict /\
 mo_le MT S S' (XM_PINS_SET MT R (Some u) (Some f) (Some l) verdict)).

(* the walk's outer journal: from pins_set's entry, over its footprint *)
Definition psb_J (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
ajournal SEGS B PINS_SET_STK (spZ regs) psb_FP ly S W mem md [] lyc Sc Wc memc mdc k.

(* the blocks at a state of the walk against the entry's, and the recorder's blocks O2 there *)
Definition psb_book (lyc : alayout) (Sc : astate) (O2 : list (Z * Z)) : Prop :=
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O2) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall pn, In pn O2 -> In pn O \/ ~ In pn (ablocks B ly S)).

Lemma psb_sp0 : spZ regs mod 16 = 0 /\ alloc_ceiling + PINS_SET_STK <= spZ regs <= 2 ^ 47 /\
spZ regs <= ly_top ly /\ 0 <= PINS_SET_STK.
Proof.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.

Lemma psb_O_live : forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros pn Hpn. exact (proj2 (psb_O_facts B ly S _ R O HREP pn Hpn)). Qed.

(* every footprint byte lies below the allocator's ceiling: g_rec and record.spill are image bytes, O's blocks are
   live blocks *)
Lemma psb_FP_low : forall a, inFP psb_FP a -> 0 <= a < alloc_ceiling.
Proof.
pose proof HPRE as (HAR & _). pose proof asan_consts as (C1 & _).
intros a Ha. unfold psb_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, SC_SIZE in *; lia|].
apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (psb_O_live (p, n) Hpn)) as (_ & H4096 & Hce & _). lia.
Qed.

(* no read-only byte is in the footprint (cmd_ro_prog_apart: read-only bytes are image bytes, no program static) *)
Lemma psb_FP_ro : forall a, in_roP SEGS RLO RHI a -> ~ inFP psb_FP a.
Proof.
pose proof HPRE as (HAR & _).
intros a Hro Ha. destruct (cmd_ro_prog_apart a Hro) as (Himg & Hpg).
unfold psb_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [apply Hpg; apply recb_grec_in; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [apply Hpg; apply recb_spill_in; lia|].
apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa).
exact (recb_heap_noimg_m B ly S W mem md p n a HAR (psb_O_live (p, n) Hpn) Hpa Himg).
Qed.

(* a heap byte of a live block that is not one of the recorder's blocks O is not in the footprint *)
Lemma psb_FP_blk : forall q m a, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> q <= a < q + req_size m ->
~ inFP psb_FP a.
Proof.
pose proof HPRE as (HAR & _).
intros q m a Hqm HqO Ha Hf.
assert (Hni : ~ in_img SEGS a) by exact (recb_heap_noimg_m B ly S W mem md q m a HAR Hqm Ha).
unfold psb_FP in Hf. apply inFP_cons in Hf as [Hf | Hf]; [exact (Hni (cmd_prog_img a (recb_grec_in a Hf)))|].
apply inFP_cons in Hf as [Hf | Hf]; [exact (Hni (cmd_prog_img a (recb_spill_in a Hf)))|].
apply inFP_ablocks_fp_inv in Hf as (p & n & Hpn & Hpa).
assert (Hne : (q, m) <> (p, n)) by (intros E; rewrite E in HqO; exact (HqO Hpn)).
pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR Hqm (psb_O_live (p, n) Hpn) Hne) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the read-only facts at any state of the walk: arodata_okP through the journal, cmd_ro_ok from it *)
Lemma psb_ro_at : forall lyc Sc Wc memc mdc k, psb_J lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) /\ cmd_ro_ok (rdW Wc memc).
Proof.
intros lyc Sc Wc memc mdc k HJ.
assert (H1 : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ psb_FP_ro HROD).
split; [exact H1 | exact (cmd_ro_ok_of_aro lyc Sc Wc memc mdc (proj1 HJ) H1)].
Qed.

(* a string handed over at the entry (astr_argA, either arm) is a string arg_s may take at any later state of the
   walk (no block excluded), with its word tail readable *)
Lemma psb_arg_later : forall lyc Sc Wc memc mdc k O2 p x, psb_J lyc Sc Wc memc mdc k -> psb_book lyc Sc O2 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] p (Some x) /\
atail_vis SEGS Wc memc (p + Z.of_nat (length x)).
Proof.
intros lyc Sc Wc memc mdc k O2 p x HJ (_ & MID2 & _) HA.
pose proof HPRE as (HAR & _). pose proof (proj1 HJ) as HARc.
destruct (psb_ro_at lyc Sc Wc memc mdc k HJ) as [HRODc HROc].
cbn [astr_argA] in HA |- *. destruct HA as (Hp0 & Hstr & Hn & [[Hblk Hap] | [Hro (Hab & Hhb & Hend)]]).
- destruct Hblk as (q & m & Hqm & Hq1 & Hq2).
  assert (HqO : ~ In (q, m) O).
  { intros H. rewrite Forall_forall in Hap. specialize (Hap _ H). unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
  pose proof (MID2 (q, m) Hqm HqO) as Hqm'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & H4096 & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  assert (KB : forall y, p <= y < p + Z.of_nat (length x) + 1 -> rdW Wc memc y = rdW W mem y).
  { intros y Hy. replace y with (q + (y - q)) by lia.
    apply (F2 q m (y - q) Hqm Hqm' ltac:(lia)).
    apply (psb_FP_blk q m (q + (y - q)) Hqm HqO). lia. }
  split.
  + split; [exact Hp0|]. split; [exact (psr_astr_kept (rdW W mem) _ p x Hstr KB)|]. split; [exact Hn|].
    left. split; [exists q, m; split; [exact Hqm' | lia] | constructor].
  + exact (cmd_heap_tail_vis lyc Sc Wc memc mdc q m (p + Z.of_nat (length x)) HARc Hqm' ltac:(lia)).
- assert (KB : forall y, p <= y < p + Z.of_nat (length x) + 1 -> rdW Wc memc y = rdW W mem y).
  { intros y Hy. destruct (Hro (y - p) ltac:(lia)) as (Hr & Ho & He). replace y with (p + (y - p)) by lia.
    rewrite (HRODc _ Hr Ho He), (HROD _ Hr Ho He). reflexivity. }
  split.
  + split; [exact Hp0|]. split; [exact (psr_astr_kept (rdW W mem) _ p x Hstr KB)|]. split; [exact Hn|].
    right. split; [exact Hro|]. exact (conj Hab (conj Hhb Hend)).
  + intros a Ha. exact (proj2 HROc _ Hend a Ha).
Qed.

(* the string the fourth arg_s takes (0x8c990 .. 0x8c9a4): the verdict, or "-" for a NULL verdict *)
Lemma psb_v4_later : forall lyc Sc Wc memc mdc k O2, psb_J lyc Sc Wc memc mdc k -> psb_book lyc Sc O2 ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] (psb_vptr pv) (Some (darg verdict psb_dash)) /\
atail_vis SEGS Wc memc (psb_vptr pv + Z.of_nat (length (darg verdict psb_dash))).
Proof.
intros lyc Sc Wc memc mdc k O2 HJ HBK.
destruct (psb_ro_at lyc Sc Wc memc mdc k HJ) as [_ HROc].
destruct verdict as [x|] eqn:Ev; cbn [darg].
- assert (Hpv : psb_vptr pv = pv).
  { unfold psb_vptr. destruct (Z.eqb_spec pv 0) as [E|E]; [|reflexivity].
    exfalso. cbn [astr_argA] in HSV. exact (proj1 HSV E). }
  rewrite Hpv. exact (psb_arg_later lyc Sc Wc memc mdc k O2 pv x HJ HBK HSV).
- cbn [astr_argA] in HSV. rewrite HSV. change (psb_vptr 0) with 0x21d80.
  split; [exact (psb_dash_arg B HB lyc Sc Wc memc [] HROc CMD_RO_IN) | exact (psb_dash_tail Wc memc HROc)].
Qed.

(* the recorder's representation needs only the bytes below the allocator's ceiling *)
Lemma psb_rep_low : forall lyc Sc (Wc : world SEGS) memc mdc (rd rd' : reader) R2 O2,
AR SEGS B lyc Sc Wc memc mdc -> rec_repA B lyc Sc rd R2 O2 ->
(forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) -> rec_repA B lyc Sc rd' R2 O2.
Proof.
intros lyc Sc Wc memc mdc rd rd' R2 O2 HARc (Q & HA & HO) Hk. pose proof asan_consts as (C1 & _).
exists Q. split; [|exact HO].
apply (psr_arep_kept _ _ rd rd' R2 Q HA); [|intros pn Hpn; exact (psb_lay_blocks_in _ _ _ _ _ _ HA pn Hpn)].
intros x [Hx | [Hx | ([p n] & Hpn & Hx)]]; apply Hk; [unfold A_G_REC, REC_SIZE in *; lia | unfold A_REC_SPILL, SC_SIZE in *; lia|].
cbn [fst snd] in Hx. pose proof (psb_lay_blocks_in _ _ _ _ _ _ HA (p, n) Hpn) as Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. lia.
Qed.

(* the store of mix_call's digest into g_rec.state (0x8c9d4): every other byte the representation reads is kept *)
Lemma psb_rep_set_low : forall lyc Sc (Wc : world SEGS) memc mdc (rd rd' : reader) R2 O2 h,
AR SEGS B lyc Sc Wc memc mdc -> rec_repA B lyc Sc rd R2 O2 ->
(forall a, 0 <= a < alloc_ceiling -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
rec_repA B lyc Sc rd' (set_state R2 h) O2.
Proof.
intros lyc Sc Wc memc mdc rd rd' R2 O2 h HARc (Q & HA & HO) Hk Hst Hh. pose proof asan_consts as (C1 & _).
exists Q. split; [|exact HO].
apply (psr_arep_set_state _ rd rd' R2 Q h HA); [|exact Hst | exact Hh].
intros x [Hx | [Hx | ([p n] & Hpn & Hx)]] Hns; apply Hk;
  [unfold A_G_REC, REC_SIZE in *; lia | exact Hns | unfold A_REC_SPILL, SC_SIZE in *; lia | exact Hns | | exact Hns].
cbn [fst snd] in Hx. pose proof (psb_lay_blocks_in _ _ _ _ _ _ HA (p, n) Hpn) as Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. lia.
Qed.

(* the representation across a callee whose footprint is empty (mix_call): it keeps every program static and every
   byte of a block live before and after it *)
Lemma psb_rep_call_kept : forall lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 STK1 sp1 R2 O2,
AR SEGS B lyc Sc Wc memc mdc ->
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2)) ->
rec_repA B lyc Sc (rdW Wc memc) R2 O2 -> rec_repA B ly2 S2 (rdW W2 mem2) R2 O2.
Proof.
intros lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 STK1 sp1 R2 O2 HARc HJ Hbl (Q & HA & HO).
exists Q. split; [|exact HO].
apply (psr_arep_kept (ablocks B lyc Sc) _ (rdW Wc memc) (rdW W2 mem2) R2 Q HA);
  [|intros pn Hpn; exact (Hbl pn (psb_lay_blocks_in _ _ _ _ _ _ HA pn Hpn))].
intros x [Hx | [Hx | ([p n] & Hpn & Hx)]].
- exact (recb_call_keeps_m B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ (or_introl (recb_grec_in x Hx))).
- exact (recb_call_keeps_m B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ (or_introl (recb_spill_in x Hx))).
- cbn [fst snd] in Hx. pose proof (psb_lay_blocks_in _ _ _ _ _ _ HA (p, n) Hpn) as Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  assert (Hrng : p <= x < p + req_size n) by lia.
  apply (recb_call_keeps_m B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ).
  right. exists p, n. split; [exact Hin|]. split; [exact (Hbl (p, n) Hin) | exact Hrng].
Qed.

(* --- the block bookkeeping ---------------------------------------------------------------------------------- *)
Lemma psb_book_init : psb_book ly S O.
Proof.
split; [|split].
- intros pn Hpn. destruct (in_dec recb_pair_dec pn O) as [H | H]; [right; exact H | left; split; assumption].
- intros pn Hpn _. exact Hpn.
- intros pn Hpn. left. exact Hpn.
Qed.

(* record(): the spill's old argument blocks F, which the recorder owns, are freed *)
Lemma psb_book_record : forall lyc Sc (Wc : world SEGS) memc mdc O1 ly2 S2 F O1',
AR SEGS B lyc Sc Wc memc mdc -> psb_book lyc Sc O1 ->
Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ F) -> (forall pn, In pn F -> In pn O1) ->
(forall pn, In pn O1' <-> In pn O1 /\ ~ In pn F) -> psb_book ly2 S2 O1'.
Proof.
intros lyc Sc Wc memc mdc O1 ly2 S2 F O1' HARc (M1 & M2 & M3) HP HF HO.
pose proof (Permutation_NoDup HP (recb_ablocks_nodup_m B lyc Sc Wc memc mdc HARc)) as ND.
split; [|split].
- intros pn Hpn.
  assert (Hc : In pn (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hpn).
  destruct (M1 pn Hc) as [H | H]; [left; exact H | right].
  apply HO. split; [exact H|]. intros HpF. exact (list_nodup_app_disj _ _ pn ND Hpn HpF).
- intros pn Hpn HnO. pose proof (M2 pn Hpn HnO) as Hc. apply (Permutation_in _ HP) in Hc.
  apply in_app_or in Hc as [Hc | Hc]; [exact Hc|]. exfalso.
  destruct (M3 pn (HF pn Hc)) as [H | H]; [exact (HnO H) | exact (H Hpn)].
- intros pn Hpn. exact (M3 pn (proj1 (proj1 (HO pn) Hpn))).
Qed.

(* arg_s(): a fresh block, apart from every live block, joins the recorder's blocks *)
Lemma psb_book_arg : forall lyc Sc O1 ly2 S2 p n,
psb_book lyc Sc O1 -> 0 < n ->
Permutation (ablocks B ly2 S2) ((p, n) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B lyc Sc) ->
psb_book ly2 S2 ((p, n) :: O1).
Proof.
intros lyc Sc O1 ly2 S2 p n (M1 & M2 & M3) Hn HP Hap.
split; [|split].
- intros pn Hpn. apply (Permutation_in _ HP) in Hpn. destruct Hpn as [<- | Hpn]; [right; left; reflexivity|].
  destruct (M1 pn Hpn) as [H | H]; [left; exact H | right; right; exact H].
- intros pn Hpn HnO. apply (Permutation_in _ (Permutation_sym HP)). right. exact (M2 pn Hpn HnO).
- intros pn [<- | Hpn]; [|exact (M3 pn Hpn)].
  destruct (in_dec recb_pair_dec (p, n) (ablocks B ly S)) as [HS | HS]; [|right; exact HS].
  destruct (in_dec recb_pair_dec (p, n) O) as [HO | HO]; [left; exact HO|].
  exfalso. pose proof (M2 _ HS HO) as Hc. rewrite Forall_forall in Hap. specialize (Hap _ Hc).
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
Qed.

End entry.
End e.
End f.
End d.
