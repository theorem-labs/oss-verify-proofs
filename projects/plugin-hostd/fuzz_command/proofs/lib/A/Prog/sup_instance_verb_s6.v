(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the state between the calls of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command)
   and the facts it carries across a callee, after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_mid and the kept-block
   lemmas obj_at_kept, blk_kept_call); the segment from the return of the strcspn wrapper (0x8b498) to rec_shape_of's
   call, after A/ACh1.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
(* the plain proof's lemmas on the line's first word (lib/Prog/sup_instance_verb.v:210-276); its module shares the
   base name of the walk, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_instance_verb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PSIV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.sup_instance_verb.
Module PSpn6 := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strspn_c.
Module PCspn6 := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.

(* the line's first word: past its leading spaces and tabs, up to the next one (recorder.c:386-387) *)
Definition siv_spn (line : list byte) : nat := PSpn6.spn_len PSIV.siv_set line.
Definition siv_cspn (line : list byte) : nat := PCspn6.cspn_len PSIV.siv_set (skipn (siv_spn line) line).
Lemma siv_verb_first_word : forall line,
firstn (siv_cspn line) (skipn (siv_spn line) line) = first_word line.
Proof. intros line. exact (PSIV.siv_first_word line). Qed.
Lemma siv_spn_le : forall line, (siv_spn line <= length line)%nat.
Proof. intros line. exact (PSIV.siv_spn_le line). Qed.
Lemma siv_cspn_le : forall line, (siv_cspn line <= length (skipn (siv_spn line) line))%nat.
Proof. intros line. exact (PSIV.siv_cspn_le _). Qed.

(* the bytes of a slice of a C string *)
Lemma siv_slice_bytes : forall rd p (s : list byte) j k, astr_atR rd p s -> (j + k <= length s)%nat ->
abytes_atR rd (p + Z.of_nat j) (firstn k (skipn j s)).
Proof.
intros rd p s j k [H1 _] Hjk i Hi. rewrite length_firstn, length_skipn in Hi.
replace (p + Z.of_nat j + Z.of_nat i) with (p + Z.of_nat (j + i)) by lia.
rewrite (H1 (j + i)%nat) by (rewrite length_app; cbn [length]; lia). f_equal. f_equal.
rewrite nth_firstn. replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn. rewrite app_nth1 by lia. reflexivity.
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

Lemma siv_frame_kept : forall (H H' : word -> bool) (m m' : word -> option byte) sp0 regs,
siv_frame_ok (mrestrict H m) sp0 regs ->
(forall a, sp0 - 48 <= a < sp0 -> aview SEGS H' m' a = aview SEGS H m a) ->
siv_frame_ok (mrestrict H' m') sp0 regs.
Proof.
intros H H' m m' sp0 regs HF Hk j r Hj.
assert (Hj5 : (j < 5)%nat) by (apply (proj1 (nth_error_Some siv_saved j)); rewrite Hj; discriminate).
apply (recb_val_mem_frame_m H H' m m'); [exact (HF j r Hj)|]. intros k Hk0. apply Hk. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the state between two calls: the journal from the entry, the frame, the kept registers, the recorder with the
   call recorded and the arguments A added (its blocks lay_blocks Q1), the block facts I1 .. I3, and the events,
   meter and live bytes spent so far *)
Definition siv_mid ly S W (regs : bvmap 5 word) mem md (line : list byte) (ledger : Z) (R : rstate) (O : list (Z * Z))
  lyc Sc (Wc : world SEGS) memc mdc (regs1 : bvmap 5 word) (kk : Z) (Q1 : rlay) (A : list (list byte))
  (kb msp lsp : Z) : Prop :=
ajournal SEGS B SUP_INSTANCE_VERB_STK (spZ regs) (siv_FP O) ly S W mem md [] lyc Sc Wc memc mdc kk /\
0 <= kk <= kb /\
siv_frame_ok (mrestrict (w_H Wc) memc) (spZ regs) regs /\
siv_regs_ok B regs regs1 (siv_slot R) /\
arep_at (ablocks B lyc Sc) (rdW Wc memc) A_G_REC A_REC_SPILL (rec_record R REC_INSTANCE_VERB A) Q1 /\
(forall pn, In pn (lay_blocks Q1) -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Q1)) /\
mo_le MT S Sc msp /\
blocks_bytes Sc <= blocks_bytes S + lsp.

Lemma siv_prog_unowned : CmdBSyms B -> forall a, Exists (in_zr a) recb_PG ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HB a HP. assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (recb_ts_prog_m B HB); exact HP).
destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _). split; assumption.
Qed.

Lemma siv_FP_closed : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
~ YI16.sink_open_fp (siv_FP O).
Proof.
intros ly S W mem md rd R O HAR HR. unfold siv_FP.
apply sink_closed_cons; [unfold A_G_REC; cbn; lia|]. apply sink_closed_cons; [unfold A_REC_SPILL; cbn; lia|].
apply sink_closed_ablocks_fp. apply Forall_forall. intros [b m] Hb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (rec_repA_in B ly S rd R O HR _ Hb)) as (_ & H4096 & _). cbn. lia.
Qed.

(* the line, read again later: its bytes, its block (none of the recorder's, so still live), its tail word *)
Lemma siv_line_kept : CmdBSyms B -> (forall a, Exists (in_zr a) recb_PG -> in_img SEGS a) ->
(forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e) ->
forall ly S (W : world SEGS) mem md R O pl line lyc Sc (Wc : world SEGS) memc mdc STK sp0 kk,
AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O ->
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) ->
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pl line ->
ajournal SEGS B STK sp0 (siv_FP O) ly S W mem md [] lyc Sc Wc memc mdc kk ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
astr_atR (rdW Wc memc) pl line /\
(exists p k, In (p, k) (ablocks B lyc Sc) /\ p <= pl /\ pl + Z.of_nat (length line) + 1 <= p + k) /\
atail_vis SEGS Wc memc (pl + Z.of_nat (length line)).
Proof.
intros HB PIMG HTV ly S W mem md R O pl line lyc Sc Wc memc mdc STK sp0 kk HAR HR HBLK HAPO HSTR HJ I2.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
destruct (siv_line_block B ly S W mem md pl _ O HAR HBLK ltac:(lia) HAPO) as (p & k & Hpk & HnO & Hp1 & Hp2 & Hp4096 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hpk) as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
pose proof (I2 _ Hpk HnO) as Hpkc.
assert (KEEP : forall i, 0 <= i < Z.of_nat (length line) + 1 -> rdW Wc memc (pl + i) = rdW W mem (pl + i)).
{ intros i Hi. replace (pl + i) with (p + (pl + i - p)) by lia.
  apply (F2 p k); [exact Hpk | exact Hpkc | lia |].
  intros (r & Hr & Hra). replace (p + (pl + i - p)) with (pl + i) in Hra by lia.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra.
  - apply (recb_heap_noimg_m B ly S W mem md p k (pl + i) HAR Hpk ltac:(lia)). apply PIMG. apply recb_grec_in. exact Hra.
  - apply (recb_heap_noimg_m B ly S W mem md p k (pl + i) HAR Hpk ltac:(lia)). apply PIMG. apply recb_spill_in. exact Hra.
  - destruct (inFP_ablocks_fp_inv O (pl + i) (ex_intro _ r (conj Hr Hra))) as (b & m & Hbm & Hba).
    pose proof (rec_repA_in B ly S _ R O HR _ Hbm) as Hbm'.
    assert (Hne : (b, m) <> (p, k)) by (intros E; rewrite E in Hbm; exact (HnO Hbm)).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p k HAR Hbm' Hpk Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }
split; [exact (rastr_kept _ _ _ _ HSTR KEEP)|].
split; [exists p, k; split; [exact Hpkc | lia]|].
apply (HTV lyc Sc Wc memc mdc p k); [exact HARc | exact Hpkc | lia].
Qed.

(* the recorder's representation over another block list and reader that agree on g_rec, record.spill and the
   recorder's blocks: rec_repA_kept (lib/A/Prog/sup_instance_verb_s3.v) at the layout's level *)
Lemma siv_arep_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) (lay_blocks Q) -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA HblQ Hg Hs Hb.
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; exact (Hb p n i Hpn Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept bl _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept bl _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

End e.
End f.
End d.
