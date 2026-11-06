(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_lv2_worker_set (plugin-hostd/fuzz_command.asan) from the
   return of its first xstrdup to its tail jump into answer, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call
   and the walk back from it) and lib/A/AChc.v (the seed of a segment); rec_repA_in / rec_repA_kept and the field
   transports after an earlier version of lib/A/Prog/answer_code.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdAddr CmdList CmdPa CmdPaLib PaCall PaCallRun PaLibF PaLibG
PaLibH PaSB PaDenot PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c answer_c sup_lv2_worker_set_c RecBTemplate sup_lv2_worker_set_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require RecBLemmas.
Import RecBLemmas(aval_mem_view, list_nodup_app_disj, recb_ablocks_nodup_m).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state a segment of the walk starts from (RecBTemplate.v's atoms): atom 2 is the sp of the frame
   (sp0 - 64), 32 the shadow base, 33 the call count record() read, 34 the slot c, and 35 .. 41 the entry values of
   the registers the frame saves (slw_saved). The frame region holds them in their slots; the slot region is c's
   56 bytes, writable on the nargs field and the first two argument pointers [c + 4, c + 24). *)
Definition slw_extra (regs : bvmap 5 word) (n c : Z) : list word :=
map (Z_to_bv 64) [SB; n; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) slw_saved.
Definition slw_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
  (map (fun j => YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 7)).
(* the slot's nargs field [c + 4, c + 8) and the argument word a segment writes [c + a, c + a + 8) *)
Definition slw_slotr1 (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some RB_C) 4 8 4 8 cs.
Definition slw_slotr2 (a : Z) : YP09.region := YP09.mkRegion (Some RB_C) a (a + 8) a (a + 8) [].
Definition slw_rs (cs : list YP09.chunk) (a : Z) : YP09.smem := [slw_stack; slw_slotr1 cs; slw_slotr2 a].
(* the shadow byte address of c + 4, as the code computes it (srli s5,s2,3; add s5,s5,s4) *)
Definition slw_shx4 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff RB_C 4) (SLit 3)) (SOff RB_SB 0).
Definition slw_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the registers at +0xc0: s0 = c, s2 = c + 4, s4 = the shadow base, s5 = the shadow byte of c + 4 *)
Definition slw_sregs1 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff RB_C 0)) 18 (SOff RB_C 4)) 20 (SOff RB_SB 0)) 21 slw_shx4.
(* at +0x110 also s3 = c + 8 *)
Definition slw_sregs2 : list sv := Eval vm_compute in sr_set slw_sregs1 19 (SOff RB_C 8).
(* at +0x150 only s0 = c matters *)
Definition slw_sregs3 : list sv := Eval vm_compute in sr_set sr_atoms 8 (SOff RB_C 0).
Definition slw_nargs (v : Z) : list YP09.chunk := [YP09.mkChunk 4 (CVal 4 (SLit v))].
Definition ss_slw1 : sstate := mkSS SLW_RET1 slw_sregs1 (slw_rs (slw_nargs 0) 8) None (rbt_facts 0 16).
Definition ss_slw2 : sstate := mkSS SLW_RET2 slw_sregs2 (slw_rs (slw_nargs 1) 16) None (rbt_facts 0 16).
Definition ss_slw3 : sstate := mkSS SLW_RET3 slw_sregs3 [slw_stack] None (rbt_facts 0 16).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the per-binary record, as the walks take it *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* the program's writable statics (RecBTemplate.v:102-106 forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the statement's Section hypotheses (sup_lv2_worker_set_c.v:68-72) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
(* the walk hypotheses (cgif's names) and the walks' shared facts the statement does not carry yet (CmdRecFacts.v
   was not yet in the tree), each under its canonical name *)
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the premise an earlier commit deleted from the statements, which rec_shape_of's read-only arm needs for the verb
   literal (CmdRo.v:434; one name for all walks) *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

Ltac tmpl_args := first [exact LAWS | exact HB | exact TL | exact VOBJS | exact (recb_ts_prog_m B HB) | exact cmd_prog_img
  | exact cmd_prog_writable].

(* --- the recorder's state across writes outside it (an earlier version of lib/A/Prog/answer_code.v, verbatim) --- *)

Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
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
apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
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

(* --- record(): one argument appended to the slot (recorder.c:223-227, arg_s inlined) --------------------- *)

Lemma slw_nth_last : forall {X} (l : list X) x k y, nth_error (l ++ [x]) k = Some y ->
((k < length l)%nat /\ nth_error l k = Some y) \/ (k = length l /\ y = x).
Proof.
intros X l x k y H. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- left. split; [exact Hk|]. rewrite nth_error_app1 in H by exact Hk. exact H.
- right. rewrite nth_error_app2 in H by exact Hk. destruct (k - length l)%nat as [|j] eqn:Ej.
  + cbn in H. injection H as <-. split; [lia | reflexivity].
  + cbn in H. destruct j; discriminate H.
Qed.

Lemma slw_acall_push : forall bl bl' (rd rd' : reader) a fn A P s p n,
acall_at bl rd a (fn, A) P -> (length A < 6)%nat ->
(forall i, 0 <= i < 4 -> rd' (a + i) = rd (a + i)) ->
(forall i, 8 <= i < 8 + 8 * Z.of_nat (length A) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn P -> In pn bl') ->
aval_mem rd' (a + 4) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (a + 8 + 8 * Z.of_nat (length A)) 8 p ->
p <> 0 -> In (p, n) bl' -> Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> astr_atR rd' p s ->
~ In p (map fst P) ->
acall_at bl' rd' a (fn, A ++ [s]) (P ++ [(p, n)]).
Proof.
intros bl bl' rd rd' a fn A P s p n (H1 & H2 & H3 & H4 & H5 & H6 & H7) HA Hfn Hargs Hblk Hbl Hna Harg Hp0 Hpn Hn Hs Hnot.
cbn [fst snd] in *. unfold acall_at. cbn [fst snd]. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, H3; reflexivity|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite Z.add_0_r; apply Hfn; lia]|].
split; [rewrite length_app, Nat2Z.inj_add; exact Hna|].
split.
{ rewrite map_app. cbn [map fst].
  apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_cons_append (map fst P) p)).
  constructor; [exact Hnot | apply NoDup_ListNoDup; exact H6]. }
intros k s' pn Hk Hkp.
apply slw_nth_last in Hk as [(Hk & Hk') | (-> & ->)].
- rewrite nth_error_app1 in Hkp by lia.
  destruct (H7 k s' pn Hk' Hkp) as (G1 & G2 & G3 & G4 & G5).
  split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; replace (a + 8 + 8 * Z.of_nat k + Z.of_nat j) with (a + (8 + 8 * Z.of_nat k + Z.of_nat j)) by lia; apply Hargs; lia]|].
  split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hkp)|]. split; [exact G4|].
  apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hblk; [exact (nth_error_In _ _ Hkp) | lia]].
- rewrite nth_error_app2 in Hkp by lia. rewrite H3, Nat.sub_diag in Hkp. cbn in Hkp. injection Hkp as <-. cbn [fst snd].
  split; [exact Harg|]. split; [exact Hp0|]. split; [exact Hpn|]. split; [exact Hn | exact Hs].
Qed.

Lemma slw_perm_last : forall (L rest : list (Z * Z)) x, Permutation (L ++ x :: rest) (x :: L ++ rest).
Proof. intros L rest x. apply Permutation_sym, Permutation_middle. Qed.

(* the recorder's answer, reply and scalars are kept by writes that leave their words and blocks alone *)
Lemma slw_ans_rep_kept : forall bl bl' (rd rd' : reader) R Q,
aanswer_at bl rd A_G_REC (r_answer R) (l_answer Q) -> areply_at bl rd A_G_REC (r_reply R) (l_reply Q) ->
ag1_scalars rd A_G_REC R ->
(forall a, (A_G_REC <= a < A_G_REC + 16 \/ A_G_REC + OFF_ANSWER <= a < A_G_REC + REC_SIZE) -> rd' a = rd a) ->
(forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl') ->
(forall pn i, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q) /\ areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q) /\
ag1_scalars rd' A_G_REC R.
Proof.
intros bl bl' rd rd' R Q Ha Hr (S1 & S2 & S3 & S4 & S5 & S6) Hg HblQ HbQ.
unfold aanswer_at, areply_at, ag1_scalars in *.
unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *.
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (oblk (Some q) ++ oblk (l_reply Q))) by (left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (oblk (l_answer Q) ++ oblk (Some q))) by (apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

Lemma slw_own_push : forall Q Q' (O' : list (Z * Z)) p n,
Permutation (lay_blocks Q') ((p, n) :: lay_blocks Q) ->
ag1_own A_G_REC A_REC_SPILL Q -> (forall pn, In pn O' <-> In pn (lay_blocks Q)) ->
(forall pn, In pn O' -> fst pn <> p) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
ag1_own A_G_REC A_REC_SPILL Q' /\ (forall pn, In pn (O' ++ [(p, n)]) <-> In pn (lay_blocks Q')).
Proof.
intros Q Q' O' p n HP (Hnd & Hap) HO Hfst Hg Hs. split; [split|].
- apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst (Permutation_sym HP))).
  cbn [map fst]. constructor; [| apply NoDup_ListNoDup; exact Hnd].
  intros Hin. apply in_map_iff in Hin as (pn & Hp & Hin). apply (Hfst pn); [apply HO; exact Hin | exact Hp].
- intros pn Hin. apply (Permutation_in _ HP) in Hin. destruct Hin as [<- | Hin]; [cbn [fst snd]; split; assumption | exact (Hap pn Hin)].
- intros pn. split; intros Hin.
  + apply (Permutation_in _ (Permutation_sym HP)). apply in_app_iff in Hin as [Hin | [<- | []]]; [right; apply HO; exact Hin | left; reflexivity].
  + apply (Permutation_in _ HP) in Hin. apply in_app_iff. destruct Hin as [<- | Hin]; [right; left; reflexivity | left; apply HO; exact Hin].
Qed.

Lemma slw_rep_push : forall ly S rd ly' S' rd' R fn A O' s p n,
rec_repA B ly S rd (rec_record R fn A) O' ->
(length (r_calls R) <= 16)%nat -> (length A < 6)%nat -> Z.of_nat (length s) <= LMAX ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (slw_slot R + 4 <= a < slw_slot R + 8) ->
   ~ (slw_slot R + 8 + 8 * Z.of_nat (length A) <= a < slw_slot R + 16 + 8 * Z.of_nat (length A)) -> rd' a = rd a) ->
aval_mem rd' (slw_slot R + 4) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (slw_slot R + 8 + 8 * Z.of_nat (length A)) 8 p ->
(forall q m i, In (q, m) O' -> 0 <= i < m -> rd' (q + i) = rd (q + i)) ->
(forall pn, In pn O' -> In pn (ablocks B ly' S')) ->
In (p, n) (ablocks B ly' S') -> p <> 0 ->
Z.of_nat (length s) + 1 <= n <= LMAX + 2 -> astr_atR rd' p s ->
(forall pn, In pn O' -> fst pn <> p) ->
iv_apart p n A_G_REC REC_SIZE -> iv_apart p n A_REC_SPILL SC_SIZE ->
rec_repA B ly' S' rd' (rec_record R fn (A ++ [s])) (O' ++ [(p, n)]).
Proof.
intros ly S rd ly' S' rd' R fn A O' s p n (Q & HA & HO) Hlen HA6 Hsl Hkeep Hna Harg Hblk Hbl Hpn Hp0 Hn Hstr Hfst Hg Hsp.
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn'; apply Hbl, HO, Hpn').
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros [q m] i Hq Hi; apply (Hblk q m i (proj2 (HO (q, m)) Hq) Hi)).
unfold lay_blocks in HblQ, HbQ.
assert (HA8 : 16 + 8 * Z.of_nat (length A) <= 56) by lia.
unfold rec_record in HA |- *. unfold slw_slot in Hkeep, Hna, Harg.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
- (* the slot is the next entry of g_rec's call table *)
  set (c := A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) in *.
  assert (Hc : A_G_REC + 16 <= c /\ c + 56 <= A_G_REC + 912)
    by (subst c; unfold A_G_REC, OFF_CALLS, CALL_SIZE; lia).
  destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
  cbn [set_calls r_calls r_spill r_answer r_reply] in C1, C2, C3, C4, C5, C6, Ha, Hr, HS |- *.
  assert (Hne : l_calls Q <> []) by (intros E; rewrite E in C2; rewrite length_app in C2; cbn in C2; lia).
  destruct (exists_last Hne) as (Lc & P & EQ).
  assert (HLc : length Lc = length (r_calls R)) by (rewrite EQ, !length_app in C2; cbn in C2; lia).
  assert (HPold : acall_at (ablocks B ly S) rd c (fn, A) P /\ Forall (fun s0 => Z.of_nat (length s0) <= LMAX) A).
  { apply (C4 (length (r_calls R)) (fn, A) P).
    - rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
    - rewrite EQ, nth_error_app2, HLc, Nat.sub_diag by lia. reflexivity. }
  destruct HPold as [HPa HPf].
  exists (RLay (Lc ++ [P ++ [(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  assert (HPerm : Permutation (lay_blocks (RLay (Lc ++ [P ++ [(p, n)]]) (l_spill Q) (l_answer Q) (l_reply Q)))
    ((p, n) :: lay_blocks Q)).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite EQ, !concat_app. cbn [concat]. rewrite !app_nil_r.
    rewrite <- !app_assoc. cbn [app]. rewrite !(app_assoc (concat Lc) P). apply slw_perm_last. }
  destruct (slw_own_push Q _ O' p n HPerm Hown HO Hfst Hg Hsp) as [Hown' HO'].
  split; [|exact HO'].
  unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  assert (Hgk : forall a, A_G_REC <= a < A_G_REC + 960 -> ~ (c <= a < c + 56) -> rd' a = rd a)
    by (intros a Ha1 Ha2; apply Hkeep; [left; unfold REC_SIZE; exact Ha1 | lia | lia]).
  assert (Hgk2 : forall a, A_G_REC <= a < A_G_REC + 960 -> ~ (c + 4 <= a < c + 8) ->
    ~ (c + 8 + 8 * Z.of_nat (length A) <= a < c + 16 + 8 * Z.of_nat (length A)) -> rd' a = rd a)
    by (intros a Ha1 Ha2 Ha3; apply Hkeep; [left; unfold REC_SIZE; exact Ha1 | exact Ha2 | exact Ha3]).
  assert (Hsk : forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a)
    by (intros a Ha1; apply Hkeep; [right; unfold SC_SIZE; exact Ha1 | unfold A_REC_SPILL, A_G_REC in *; lia | unfold A_REC_SPILL, A_G_REC in *; lia]).
  split.
  { unfold ag1_calls. cbn [l_calls l_spill r_calls r_spill set_calls].
    split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite !length_app; cbn [length]; lia|].
    split.
    { rewrite length_app. rewrite length_app in C3. cbn [length] in C3 |- *.
      apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hgk; unfold OFF_NCALLS, A_G_REC in *; lia]. }
    split.
    - intros i c' P' Hi Hip.
      apply slw_nth_last in Hi as [(Hi & Hi') | (-> & ->)];
      apply slw_nth_last in Hip as [(Hip & Hip') | (Ei & ->)]; try lia.
      + destruct (C4 i c' P' ltac:(rewrite nth_error_app1 by lia; exact Hi') ltac:(rewrite EQ, nth_error_app1 by lia; exact Hip'))
          as [HC HF].
        split; [|exact HF].
        pose proof HC as (_ & HL6 & _).
        apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
        * intros pn Hpn'. apply HblQ. apply in_app_iff. left. rewrite EQ. apply in_concat. exists P'.
          split; [apply in_or_app; left; exact (nth_error_In _ _ Hip') | exact Hpn'].
        * intros j Hj. unfold CALL_OFF_ARGS in Hj. rewrite <- !Z.add_assoc. apply Hgk;
            unfold OFF_CALLS, CALL_SIZE, A_G_REC in *; nia.
        * intros pn j Hpn' Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. rewrite EQ. apply in_concat. exists P'.
          split; [apply in_or_app; left; exact (nth_error_In _ _ Hip') | exact Hpn'].
      + split; [| apply Forall_app; split; [exact HPf | constructor; [exact Hsl | constructor]]].
        assert (HPin : forall pn, In pn P -> In pn (concat (l_calls Q))).
        { intros pn Hpn'. rewrite EQ. apply in_concat. exists P. split; [apply in_or_app; right; left; reflexivity | exact Hpn']. }
        apply (slw_acall_push (ablocks B ly S) _ rd rd' c fn A P s p n HPa HA6).
        * intros i Hi. apply Hgk2; lia.
        * intros i Hi. apply Hgk2; lia.
        * intros pn i Hpn' Hi. apply HbQ; [apply in_app_iff; left; exact (HPin pn Hpn') | exact Hi].
        * intros pn Hpn'. apply HblQ. apply in_app_iff. left. exact (HPin pn Hpn').
        * exact Hna.
        * exact Harg.
        * exact Hp0.
        * exact Hpn.
        * exact Hn.
        * exact Hstr.
        * intros Hin. apply in_map_iff in Hin as (pn & Hp & Hin). apply (Hfst pn); [|exact Hp].
          apply HO. apply in_app_iff. left. exact (HPin pn Hin).
    - split; [|exact C6].
      apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
      + intros pn Hpn'. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn'.
      + intros j Hj. apply Hsk. pose proof C5 as (_ & HL6 & _). unfold CALL_OFF_ARGS in Hj. lia.
      + intros pn j Hpn' Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn'. }
  destruct (slw_ans_rep_kept (ablocks B ly S) (ablocks B ly' S') rd rd' _ Q Ha Hr HS) as (Ha' & Hr' & HS');
  [ intros a Ha1; apply Hgk; unfold OFF_ANSWER, REC_SIZE in *; lia
  | intros pn Hpn'; apply HblQ; apply in_app_iff; right; apply in_app_iff; right; exact Hpn'
  | intros pn i Hpn' Hi; apply HbQ; [apply in_app_iff; right; apply in_app_iff; right; exact Hpn' | exact Hi]
  | ].
  cbn [l_answer l_reply]. split; [exact Ha'|]. split; [exact Hr'|]. split; [exact HS' | exact Hown'].
- (* the table is full: the slot is record.spill *)
  assert (Hl16 : length (r_calls R) = 16%nat) by lia.
  destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
  cbn [set_spill r_calls r_spill r_answer r_reply] in C1, C2, C3, C4, C5, C6, Ha, Hr, HS |- *.
  exists (RLay (l_calls Q) (l_spill Q ++ [(p, n)]) (l_answer Q) (l_reply Q)).
  assert (HPerm : Permutation (lay_blocks (RLay (l_calls Q) (l_spill Q ++ [(p, n)]) (l_answer Q) (l_reply Q)))
    ((p, n) :: lay_blocks Q)).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    rewrite <- !app_assoc. cbn [app]. rewrite !(app_assoc (concat (l_calls Q)) (l_spill Q)). apply slw_perm_last. }
  destruct (slw_own_push Q _ O' p n HPerm Hown HO Hfst Hg Hsp) as [Hown' HO'].
  split; [|exact HO'].
  unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  assert (Hgk : forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a)
    by (intros a Ha1; apply Hkeep; [left; unfold REC_SIZE; exact Ha1 | unfold A_REC_SPILL, A_G_REC in *; lia | unfold A_REC_SPILL, A_G_REC in *; lia]).
  split.
  { unfold ag1_calls. cbn [l_calls l_spill r_calls r_spill set_spill].
    split; [exact C1|]. split; [exact C2|].
    split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hgk; unfold OFF_NCALLS, A_G_REC in *; lia]|].
    split.
    - intros i c' P' Hi Hip. destruct (C4 i c' P' Hi Hip) as [HC HF]. split; [|exact HF].
      pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hi; discriminate)) as Hi2.
      pose proof HC as (_ & HL6 & _).
      apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
      + intros pn Hpn'. apply HblQ. apply in_app_iff. left. apply in_concat. exists P'. split; [exact (nth_error_In _ _ Hip) | exact Hpn'].
      + intros j Hj. rewrite <- !Z.add_assoc. apply Hgk. unfold CALL_OFF_ARGS, OFF_CALLS, CALL_SIZE, A_G_REC in *. nia.
      + intros pn j Hpn' Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P'. split; [exact (nth_error_In _ _ Hip) | exact Hpn'].
    - split; [| apply Forall_app; split; [exact C6 | constructor; [exact Hsl | constructor]]].
      assert (Hsk2 : forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> ~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) ->
        ~ (A_REC_SPILL + 8 + 8 * Z.of_nat (length A) <= a < A_REC_SPILL + 16 + 8 * Z.of_nat (length A)) -> rd' a = rd a)
        by (intros a Ha1 Ha2 Ha3; apply Hkeep; [right; unfold SC_SIZE; exact Ha1 | exact Ha2 | exact Ha3]).
      apply (slw_acall_push (ablocks B ly S) _ rd rd' A_REC_SPILL fn A (l_spill Q) s p n C5 HA6).
      + intros i Hi. apply Hsk2; lia.
      + intros i Hi. apply Hsk2; lia.
      + intros pn i Hpn' Hi. apply HbQ; [apply in_app_iff; right; apply in_app_iff; left; exact Hpn' | exact Hi].
      + intros pn Hpn'. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn'.
      + exact Hna.
      + exact Harg.
      + exact Hp0.
      + exact Hpn.
      + exact Hn.
      + exact Hstr.
      + intros Hin. apply in_map_iff in Hin as (pn & Hp & Hin). apply (Hfst pn); [|exact Hp].
        apply HO. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
  destruct (slw_ans_rep_kept (ablocks B ly S) (ablocks B ly' S') rd rd' _ Q Ha Hr HS) as (Ha' & Hr' & HS');
  [ intros a Ha1; apply Hgk; unfold OFF_ANSWER, REC_SIZE in *; lia
  | intros pn Hpn'; apply HblQ; apply in_app_iff; right; apply in_app_iff; right; exact Hpn'
  | intros pn i Hpn' Hi; apply HbQ; [apply in_app_iff; right; apply in_app_iff; right; exact Hpn' | exact Hi]
  | ].
  cbn [l_answer l_reply]. split; [exact Ha'|]. split; [exact Hr'|]. split; [exact HS' | exact Hown'].
Qed.

(* --- the seed of a segment ------------------------------------------------------------------------------- *)

Lemma slw_seed : forall pc sregs cs aw ly S (W : world SEGS) mem md (regs regs1 : bvmap 5 word) sp n c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= sp -> sp + 64 <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> rbt_slot_ok c ->
bv_unsigned (getr regs1 2) = sp ->
slw_frame (rdW W mem) (sp + 64) regs ->
regs_ok (Eimg (Ereg regs1 (slw_extra regs n c))) sregs regs1 ->
Forall (YP09.chunk_ok SEGS (Eimg (Ereg regs1 (slw_extra regs n c))) (mrestrict (w_H W) mem) c) cs ->
YP09.regions_wf (slw_rs cs aw) = true -> 8 <= aw <= 48 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (slw_extra regs n c))) (mkSS pc sregs (slw_rs cs aw) None (rbt_facts 0 16))
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbt_SH (Eimg (Ereg regs1 (slw_extra regs n c))) (mrestrict (w_H W) mem).
Proof.
intros pc sregs cs aw ly S W mem md regs regs1 sp n c HAR Hsp Hsp2 Hsp16 Hn Hc Hsp1 HFR HREG HCS HWF Haw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
set (E := Eimg (Ereg regs1 (slw_extra regs n c))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (slw_extra regs n c) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = Z_to_bv 64 sp).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl).
  rewrite <- Hsp1. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (ESB : ew E RB_SB = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (EN : ew E RB_N = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (EC : ew E RB_C = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
assert (HENV : rbt_env_ok E sp n c) by (split; [exact HEI | split; [exact E2 | split; [exact ESB | split; [exact EN | exact EC]]]]).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (U2 : base_val E (Some 2%nat) = sp) by (apply VB; [exact E2 | lia]).
assert (UC : base_val E (Some RB_C) = c) by (apply VB; [exact EC | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia]).
split.
2: { apply (rbt_sh_ok B) with (ly := ly) (S := S) (md := md) (sp := sp) (n := n) (c := c);
     first [exact HAR | exact HENV | exact Hc | tmpl_args]. }
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HREG.
- exact HWF.
- unfold slw_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold slw_stack, YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    lazymatch goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end.
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?m 0))) =>
      let j := eval compute in (m - 35)%nat in
      let k := eval compute in (m - 32)%nat in
      let r := eval compute in (nth j slw_saved 0) in
      apply (chunk_ok_val SEGS E _ sp off 8 (SOff m 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
      [ cbn [sv_denot]; rewrite Z.add_0_r;
        change m with (32 + k)%nat; rewrite EX by lia; cbn [nth slw_extra map app slw_saved];
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HR
      | cbn; lia
      | apply (RecBLemmas.val_mem_view SEGS (w_H W) mem);
        replace (sp + off) with (sp + 64 - 8 - 8 * Z.of_nat j) by (cbn; lia);
        exact (HFR j r eq_refl) ]
    end.
  + unfold slw_slotr1, YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UC. split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
    split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
    split; [|exact HCS].
    intros o Ho. apply (cmd_prog_writable ly S W mem md (c + o) HAR).
    destruct Hc as [(H1 & H2 & H3) | ->].
    * apply recb_grec_in. unfold CALL_SIZE, A_G_REC, OFF_CALLS, REC_SIZE in *. lia.
    * apply recb_spill_in. unfold SC_SIZE, A_REC_SPILL. lia.
  + unfold slw_slotr2, YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UC. split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
    split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia|].
    split; [|constructor].
    intros o Ho. apply (cmd_prog_writable ly S W mem md (c + o) HAR).
    destruct Hc as [(H1 & H2 & H3) | ->].
    * apply recb_grec_in. unfold CALL_SIZE, A_G_REC, OFF_CALLS, REC_SIZE in *. lia.
    * apply recb_spill_in. unfold SC_SIZE, A_REC_SPILL. lia.
- apply pairwise_disjoint_of_extents. unfold slw_rs, slw_stack, slw_slotr1, slw_slotr2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, UC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold CALL_SIZE, A_G_REC, A_REC_SPILL, OFF_CALLS in *. repeat split; lia.
- apply rbt_facts_ok with (sp := sp) (n := n) (c := c) (lo := 0) (hi := 16);
  first [exact HENV | exact Hsp16 | exact Hn | exact Hc | tmpl_args | lia].
Qed.

(* --- facts every segment uses ------------------------------------------------------------------------- *)

Lemma slw_rep_len : forall ly S rd R O, rec_repA B ly S rd R O -> (length (r_calls R) <= 16)%nat.
Proof. intros ly S rd R O (Q & (_ & _ & _ & (H & _) & _) & _). exact H. Qed.

Lemma slw_slot_ok : forall R, (length (r_calls R) <= 16)%nat -> rbt_slot_ok (slw_slot R).
Proof.
intros R H. unfold slw_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl]; [left | right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia|].
apply Z.mod_divide; [lia|]. exists (771818 + 7 * Z.of_nat (length (r_calls R))). lia.
Qed.

Lemma slw_inFP_prog : forall O a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
inFP (slw_FP O) a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros O a [Ha | Ha].
- assert (HP : Exists (in_zr a) recb_PG) by (apply recb_grec_in; exact Ha).
  split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]|].
  split; [rewrite (recb_ts_prog_m B HB); exact HP | exact (cmd_prog_img a HP)].
- assert (HP : Exists (in_zr a) recb_PG) by (apply recb_spill_in; exact Ha).
  split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
  split; [rewrite (recb_ts_prog_m B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

Lemma slw_slot_in : forall c i, rbt_slot_ok c -> 0 <= i < CALL_SIZE ->
A_G_REC <= c + i < A_G_REC + REC_SIZE \/ A_REC_SPILL <= c + i < A_REC_SPILL + SC_SIZE.
Proof.
intros c i [(H1 & H2 & _) | ->] Hi; [left | right]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma slw_awr_ok : forall E cs aw STK sp0 O bl0 blc fr0 ly own c,
bv_unsigned (ew E RB_C) = c -> rbt_slot_ok c -> 8 <= aw -> aw + 8 <= CALL_SIZE ->
awr_ok SEGS B E (slw_rs cs aw) STK sp0 (slw_FP O) bl0 blc fr0 ly own.
Proof.
intros E cs aw STK sp0 O bl0 blc fr0 ly own c Hc Hok Haw1 Haw2. unfold slw_rs.
apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact Hc | | ].
{ intros a Ha. cbn [slw_slotr1 YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; right; left. apply slw_inFP_prog.
  replace a with (c + (a - c)) by lia. apply slw_slot_in; [exact Hok | unfold CALL_SIZE; lia]. }
eapply awr_ok_cons_gen; [reflexivity | exact Hc | | apply awr_ok_nil].
intros a Ha. cbn [slw_slotr2 YP09.r_wlo YP09.r_whi] in Ha.
right; right; right; right; left. apply slw_inFP_prog.
replace a with (c + (a - c)) by lia. apply slw_slot_in; [exact Hok | unfold CALL_SIZE in *; lia].
Qed.

(* the seed of the last segment: the frame only *)
Lemma slw_seed0 : forall pc sregs ly S (W : world SEGS) mem md (regs regs1 : bvmap 5 word) sp n c,
AR SEGS B ly S W mem md ->
2 ^ 46 <= sp -> sp + 64 <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> rbt_slot_ok c ->
bv_unsigned (getr regs1 2) = sp ->
slw_frame (rdW W mem) (sp + 64) regs ->
regs_ok (Eimg (Ereg regs1 (slw_extra regs n c))) sregs regs1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (slw_extra regs n c))) (mkSS pc sregs [slw_stack] None (rbt_facts 0 16))
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbt_SH (Eimg (Ereg regs1 (slw_extra regs n c))) (mrestrict (w_H W) mem).
Proof.
intros pc sregs ly S W mem md regs regs1 sp n c HAR Hsp Hsp2 Hsp16 Hn Hc Hsp1 HFR HREG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
set (E := Eimg (Ereg regs1 (slw_extra regs n c))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (slw_extra regs n c) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = Z_to_bv 64 sp).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl).
  rewrite <- Hsp1. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (ESB : ew E RB_SB = Z_to_bv 64 SB) by exact (EX 0%nat ltac:(lia)).
assert (EN : ew E RB_N = Z_to_bv 64 n) by exact (EX 1%nat ltac:(lia)).
assert (EC : ew E RB_C = Z_to_bv 64 c) by exact (EX 2%nat ltac:(lia)).
assert (HENV : rbt_env_ok E sp n c) by (split; [exact HEI | split; [exact E2 | split; [exact ESB | split; [exact EN | exact EC]]]]).
assert (U2 : base_val E (Some 2%nat) = sp) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
split.
2: { apply (rbt_sh_ok B) with (ly := ly) (S := S) (md := md) (sp := sp) (n := n) (c := c);
     first [exact HAR | exact HENV | exact Hc | tmpl_args]. }
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HREG.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold slw_stack, YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  lazymatch goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end.
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?m 0))) =>
    let j := eval compute in (m - 35)%nat in
    let k := eval compute in (m - 32)%nat in
    let r := eval compute in (nth j slw_saved 0) in
    apply (chunk_ok_val SEGS E _ sp off 8 (SOff m 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
    [ cbn [sv_denot]; rewrite Z.add_0_r;
      change m with (32 + k)%nat; rewrite EX by lia; cbn [nth slw_extra map app slw_saved];
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HR
    | cbn; lia
    | apply (RecBLemmas.val_mem_view SEGS (w_H W) mem);
      replace (sp + off) with (sp + 64 - 8 - 8 * Z.of_nat j) by (cbn; lia);
      exact (HFR j r eq_refl) ]
  end.
- cbn. repeat split.
- apply rbt_facts_ok with (sp := sp) (n := n) (c := c) (lo := 0) (hi := 16);
  first [exact HENV | exact Hsp16 | exact Hn | exact Hc | tmpl_args | lia].
Qed.

(* the call targets of the callees, against the listing's base (CmdObj.v's cmd_sig_prog) *)
Lemma slw_sig : forall s, In s cmd_prog_syms -> SIG s = BASE + cmd_af s.
Proof. intros s Hs. exact (SIGP s Hs). Qed.
Ltac slw_in_syms := cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]).
Lemma slw_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite slw_sig by slw_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma slw_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite slw_sig by slw_in_syms. f_equal; try (vm_compute; reflexivity). Qed.
Lemma slw_sig_rec_shape_of : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite slw_sig by slw_in_syms. f_equal; try (vm_compute; reflexivity). Qed.

(* the read-only bytes lie outside the statement's footprint, so arodata_okP survives every journal of the walk *)
Lemma slw_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (slw_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro (r & Hr & Ha). destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply HnPG. apply recb_grec_in. exact Ha.
- apply HnPG. apply recb_spill_in. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HO (p, n) Hin) Ha Himg).
Qed.

Lemma slw_aro_at : forall ly S (W : world SEGS) mem md O STK sp0 own ly' S' W' mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (slw_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros ly S W mem md O STK sp0 own ly' S' W' mem' md' k HAR HO HJ HR.
exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B STK sp0 (slw_FP O) ly S W mem md own ly' S' W' mem' md' k HJ
  (slw_ro_off ly S W mem md O HAR HO) HR).
Qed.

Lemma slw_in_filter : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn : Z * Z => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|y l IH]; intros Hx; [exact Hx|].
revert Hx. cbn. case_decide as Hd; intros Hx; [destruct Hx as [-> | Hx]; [left; reflexivity | right; exact (IH Hx)] | right; exact (IH Hx)].
Qed.

(* every byte of the statement's footprint lies below the stack *)
Lemma slw_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (slw_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO (r & Hr & Ha). pose proof asan_consts as (C1 & _).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, REC_SIZE in Ha. lia.
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hin)) as (_ & _ & Hpc & _). lia.
Qed.

Lemma slw_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' P. induction P; unfold bsum in *; cbn [fold_right] in *; lia. Qed.

Lemma slw_bsum_nonneg : forall ly S (W : world SEGS) mem md L, AR SEGS B ly S W mem md ->
(forall pn, In pn L -> In pn (ablocks B ly S)) -> 0 <= bsum L.
Proof.
intros ly S W mem md L HAR HL. induction L as [|[p n] L IH]; [unfold bsum; cbn; lia|].
rewrite bsum_cons. cbn [snd]. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HL (p, n) (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (IH (fun pn H => HL pn (or_intror H))). lia.
Qed.

Definition slw_pair_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma slw_ra_kept : forall (rd rd' : reader) a n, range_addressable rd SHADOW_OFF a n -> (forall x, rd' x = rd x) ->
range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n H K x Hx. destruct (H x Hx) as (s & Hs & Hok). exists s. rewrite K. split; assumption. Qed.

Lemma slw_kept_all : forall H (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' K a.
assert (Hz : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
pose proof (K (a mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as Ka. unfold aview, mbyte in *. rewrite Hz. exact Ka.
Qed.

(* the answer the recorder holds: 0, or the start of one of its blocks *)
Lemma slw_old_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists m, In (old, m) O).
Proof.
intros ly S rd R O (Q & (_ & _ & _ & _ & Ha & _) & HO). unfold aanswer_at in Ha. unfold lay_blocks in HO.
destruct (r_answer R) as [x|], (l_answer Q) as [[q m]|] eqn:EA; try contradiction.
- exists q. split; [exact (proj1 Ha)|]. right. exists m. apply HO.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- exists 0. split; [exact Ha | left; reflexivity].
Qed.

(* two distinct live blocks are apart; a live block's start determines it *)
Lemma slw_blk_apart : forall ly S (W : world SEGS) mem md b m p n,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
iv_apart b m p n /\ b <> p.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2]. pose proof (req_size_pos n ltac:(lia)) as [Rn1 Rn2].
unfold iv_apart. split; lia.
Qed.

Lemma slw_blk_pos : forall ly S (W : world SEGS) mem md p n,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 4096 <= p /\ 0 <= n.
Proof.
intros ly S W mem md p n HAR H. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR H) as (_ & H4 & _ & _ & _ & _ & Hn).
split; lia.
Qed.

Lemma slw_nodup : forall ly S (W : world SEGS) mem md L1 L2 x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) -> In x L1 -> In x L2 -> False.
Proof.
intros ly S W mem md L1 L2 x HAR HP H1 H2.
exact (list_nodup_app_disj L1 L2 x (Permutation_NoDup HP (recb_ablocks_nodup_m B ly S W mem md HAR)) H1 H2).
Qed.

(* the callee-saved registers of a state, register by register *)
Lemma slw_aregs : forall (regs regsA : bvmap 5 word),
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr regsA (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> aregs_preserved regs regsA.
Proof.
intros regs regsA H r Hr. apply H. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [cbn; tauto ..|].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc]; [cbn; tauto|]). subst. cbn; tauto.
Qed.

(* --- the segment from +0x150 (after rec_shape_of) to the end ------------------------------------------- *)

Definition slw_shape : list byte := daemon_shape "lv2_worker_set".

Lemma slw_astr_argA_rd : forall ly S (rd rd' : reader) ro O p v, astr_argA B ly S rd ro O p v ->
(forall a, rd' a = rd a) -> astr_argA B ly S rd' ro O p v.
Proof.
intros ly S rd rd' ro O p [x|] H K; [|exact H]. cbn [astr_argA] in *. destruct H as (H0 & Hs & Hn & Hr).
split; [exact H0|]. split; [apply (rastr_kept rd); [exact Hs | intros; apply K]|]. split; [exact Hn | exact Hr].
Qed.

(* MID3, the state at +0x150 (0x8bfd0), just after rec_shape_of returned the reply shape qs: the slot holds the
   call with both arguments, the recorder owns their copies p1, p2 *)
Definition slw_mid3 ly S (W : world SEGS) (regs : bvmap 5 word) mem md (uri worker : option (list byte))
(R : rstate) (O : list (Z * Z)) ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word) mem3 md3 (k p1 p2 qs : Z)
(Df Lk O1 : list (Z * Z)) : Prop :=
let sp0 := spZ regs in
let c := slw_slot R in
ajournal SEGS B SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md [] ly3 S3 W3 mem3 md3 k /\
0 <= k <= rec_spill_frees R + EV_XSTRDUP + EV_XSTRDUP /\
slw_frame (rdW W3 mem3) sp0 regs /\
getr regs3 2 = w64 (sp0 - 64) /\ getr regs3 3 = getr regs 3 /\ getr regs3 4 = getr regs 4 /\
getr regs3 8 = w64 c /\ getr regs3 10 = w64 qs /\
(forall r, 22 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker])
  (O1 ++ [(p1, slw_n uri); (p2, slw_n worker)]) /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Df) /\ (forall pn, In pn Df -> In pn O) /\
((length (r_calls R) < 16)%nat -> Df = []) /\
Permutation (ablocks B ly S) (Df ++ Lk) /\
Permutation (ablocks B ly3 S3) ((p2, slw_n worker) :: (p1, slw_n uri) :: Lk) /\
~ In (p1, slw_n uri) Lk /\ ~ In (p2, slw_n worker) ((p1, slw_n uri) :: Lk) /\
4096 <= p1 /\ 4096 <= p2 /\
0 <= qs < 2 ^ 64 /\
(forall O', astr_argA B ly3 S3 (rdW W3 mem3) (in_roP SEGS RLO RHI) O' qs (Some slw_shape)) /\
mo_le MT S S3 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg uri) + XM_XSTRDUP MT (sarg worker)).

Ltac slw_regs_tac EEo :=
  apply regs_ok_by_cases; let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbv [all_regs In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get ?l ?rr) =>
        let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v end;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      first [ symmetry; apply EEo; reflexivity | rewrite getr_zero; reflexivity | idtac ]
    | ]); try (destruct Hr; fail).

Lemma slw_D3 : forall ly S W regs mem md ch pu pw uri worker R O ly3 S3 W3 regs3 mem3 md3 k p1 p2 qs Df Lk O1,
slw_pre B MT ly S W regs mem md ch pu pw uri worker R O ->
slw_mid3 ly S W regs mem md uri worker R O ly3 S3 W3 regs3 mem3 md3 k p1 p2 qs Df Lk O1 ->
SRr SEGS W3 (cfg_at SEGS (BASE + SLW_RET3) regs3 mem3 md3) (slw_post B MT ly S W regs mem md R uri worker O).
Proof.
intros ly S W regs mem md ch pu pw uri worker R O ly3 S3 W3 regs3 mem3 md3 k p1 p2 qs Df Lk O1 HPRE MID.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPRE as (HFN & HFM0 & HROD & HRO & H10 & Hpub & H11 & Hpwb & HSU & HSW & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct MID as (HJ & Hk & HFRM & R2 & R3 & R4 & R8 & R10 & Rhi & HREP3 & HO1 & HDf & HDf0 & HPS & HP3 & Hn1 & Hn2 &
  Hp1 & Hp2 & Hqsb & Hqs & MLE3).
pose proof (proj1 HJ) as HAR3.
set (sp0 := spZ regs) in *. set (c := slw_slot R) in *.
assert (Hlen : (length (r_calls R) <= 16)%nat) by exact (slw_rep_len _ _ _ _ _ HREP).
assert (Hc : rbt_slot_ok c) by exact (slw_slot_ok R Hlen).
assert (HSTK : SUP_LV2_WORKER_SET_STK = 16592) by (vm_compute; reflexivity).
destruct (slw_seed0 SLW_RET3 slw_sregs3 ly3 S3 W3 mem3 md3 regs regs3 (sp0 - 64) (Z.of_nat (length (r_calls R))) c HAR3)
  as [HS SHOK].
{ lia. } { lia. } { Z.div_mod_to_equations. lia. } { lia. } { exact Hc. }
{ rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
{ replace (sp0 - 64 + 64) with sp0 by lia. exact HFRM. }
{ set (E := Eimg (Ereg regs3 (slw_extra regs (Z.of_nat (length (r_calls R))) c))).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs3 rr).
  { intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  slw_regs_tac EEo.
  rewrite R8. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). change 34%nat with (32 + 2)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
set (n0 := Z.of_nat (length (r_calls R))) in *.
set (E := Eimg (Ereg regs3 (slw_extra regs n0 c))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs3 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (slw_extra regs n0 c) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (HAE : env_agree 32 (Ereg regs3 (slw_extra regs n0 c)) E).
{ split; [intros m Hm; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK slw_Bspan.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
(* the registers at answer's entry *)
assert (EXV : forall j r, (j < 7)%nat -> nth_error slw_saved j = Some r -> ew E (35 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj Hr. replace (35 + j)%nat with (32 + (3 + j))%nat by lia. rewrite EX by lia.
  destruct j as [|[|[|[|[|[|[|j]]]]]]]; cbn in Hr; try lia; injection Hr as <-; reflexivity. }
assert (EC : ew E 34 = Z_to_bv 64 c) by (change 34%nat with (32 + 2)%nat; rewrite EX by lia; reflexivity).
assert (Usp3 : bv_unsigned (ew E 2) = sp0 - 64).
{ rewrite (EEo 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
set (regsA := ms_regs ms) in *. set (memA := ms_mem ms) in *.
assert (QA1 : getr regsA 1 = getr regs 1) by (rewrite Q1; exact (EXV 0%nat 1 ltac:(lia) eq_refl)).
assert (QA2 : getr regsA 2 = getr regs 2).
{ rewrite Q2, Usp3. replace (sp0 - 64 + 64) with sp0 by lia. subst sp0. unfold spZ. apply Z_to_bv_bv_unsigned. }
assert (QA3 : getr regsA 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (QA4 : getr regsA 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4; exact Htp).
assert (QA10 : getr regsA 10 = w64 c) by (rewrite Q10; exact EC).
assert (QA11 : getr regsA 11 = w64 qs) by (rewrite Q11, (EEo 10%nat 10%bv eq_refl); exact R10).
assert (QA12 : getr regsA 12 = w64 1) by exact Q12.
assert (HspA : spZ regsA = sp0 + 0) by (unfold spZ; rewrite QA2; fold (spZ regs); lia).
assert (HPRA : aregs_preserved regs regsA).
{ apply slw_aregs. intros r Hr. cbv [In] in Hr.
  destruct Hr as [<- | [<- | [<- | Hr]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact QA2.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite QA3, Hgp. reflexivity.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite QA4, Htp. reflexivity.
  - repeat (destruct Hr as [<- | Hr];
      [ rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ _ _ HS); cbn [ms_regs];
        lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
          let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
        cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        first [ exact (EXV 1%nat 8 ltac:(lia) eq_refl) | exact (EXV 2%nat 9 ltac:(lia) eq_refl)
              | exact (EXV 3%nat 18 ltac:(lia) eq_refl) | exact (EXV 4%nat 19 ltac:(lia) eq_refl)
              | exact (EXV 5%nat 20 ltac:(lia) eq_refl) | exact (EXV 6%nat 21 ltac:(lia) eq_refl)
              | lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?m) =>
                  rewrite (EEo n (Z_to_bv 5 m) eq_refl); apply Rhi; lia end ]
      | ]).
    destruct Hr. }
(* the memory at answer's entry is the memory after rec_shape_of: the epilogue only reads *)
lazymatch goal with Hfr : frame_of E _ (mrestrict _ mem3) (mrestrict _ memA) |- _ =>
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) Hfr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin))
    as KEEP0 end.
assert (KEEP : forall a, aview SEGS (w_H W3) memA a = aview SEGS (w_H W3) mem3 a).
{ apply slw_kept_all. intros a Ha. exact (KEEP0 a Ha (fun H => H)). }
(* the facts answer asks of its entry state *)
pose proof (proj1 HJ) as HARA.
pose proof HJ as (_ & HLYA & _ & _ & _ & HFRA & HNEVA & _).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (rec_repA_in ly S _ R O HREP).
assert (HROA : arodata_okP SEGS RLO RHI B (rdW W3 memA)) by exact (slw_aro_at ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOin HJ HROD).
set (RA := rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker]) in *.
set (OA := O1 ++ [(p1, slw_n uri); (p2, slw_n worker)]) in *.
assert (HREPA : rec_repA B ly3 S3 (rdW W3 memA) RA OA).
{ apply (rec_repA_kept ly3 S3 (rdW W3 mem3) ly3 S3 _ RA OA HREP3); [exact (rec_repA_in _ _ _ _ _ HREP3) | | |];
  intros; apply KEEP. }
destruct (slw_old_answer _ _ _ _ _ HREPA) as (old & Hold & Hold').
assert (HOA : forall pn, In pn OA -> In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn Hpn. apply in_app_iff in Hpn as [Hpn | [<- | [<- | []]]].
  - left. exact (proj1 (proj1 (HO1 pn) Hpn)).
  - destruct (in_dec slw_pair_dec (p1, slw_n uri) (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
    apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [exact (HDf _ Hin) | contradiction].
  - destruct (in_dec slw_pair_dec (p2, slw_n worker) (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
    apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [exact (HDf _ Hin) | exfalso; apply Hn2; right; exact Hin]. }
assert (HFR8A : Z.of_nat (length (frames S3)) <= 8) by (rewrite HFRA; exact HFR8).
assert (HROKA : cmd_ro_ok (rdW W3 memA)) by exact (cmd_ro_ok_of_aro ly3 S3 W3 memA _ HARA HROA).
assert (Hchg : true = negb (bv_unsigned (getr regsA 12) =? 0)) by (rewrite QA12; reflexivity).
set (e := (REC_LV2_WORKER_SET, [sarg uri; sarg worker])).
assert (HM : sup_lv2_worker_set_m R uri worker = rec_answer RA e slw_shape true) by reflexivity.
assert (Hshape : r_refuse RA = 0 -> astr_argA B ly3 S3 (rdW W3 memA) (in_roP SEGS RLO RHI) OA qs (Some slw_shape) /\
  fits slw_shape).
{ intros _. split.
  - apply (slw_astr_argA_rd ly3 S3 (rdW W3 mem3)); [exact (Hqs OA) | intros; apply KEEP].
  - unfold fits, slw_shape. apply Z.leb_le. vm_compute. reflexivity. }
assert (Hslot : r_refuse RA = 0 -> true = true ->
  (exists k0, nth_error (r_calls RA) k0 = Some e /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k0) \/
  (c = A_REC_SPILL /\ e = r_spill RA)).
{ intros _ _. change c with (slw_slot R). change RA with (rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker]).
  unfold rec_record, slw_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
  - left. exists (length (r_calls R)). split; [|reflexivity].
    cbn [set_calls r_calls]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  - right. split; reflexivity. }
assert (HEVA : st_nev S3 + EV_ANSWER <= EV_MAX) by (unfold EV_SUP_LV2_WORKER_SET in HEV; lia).
assert (HBB : blocks_bytes S3 <= blocks_bytes S + slw_n uri + slw_n worker).
{ rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly S).
  rewrite (slw_bsum_perm _ _ HP3), (slw_bsum_perm _ _ HPS), bsum_app. cbn [bsum fold_right fst snd].
  pose proof (slw_bsum_nonneg ly S W mem md Df HAR
    ltac:(intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPS)); apply in_or_app; left; exact Hpn)).
  unfold bsum. cbn [fold_right snd]. unfold bsum in H. lia. }
assert (HLIVEA : blocks_bytes S3 + LIVE_ANSWER (snd (rec_answer RA e slw_shape true)) <= LIVE_MAX).
{ unfold LIVE_SUP_LV2_WORKER_SET in HLIVE. rewrite HM in HLIVE. unfold LIVE_XSTRDUP, slw_n in *. lia. }
assert (HMOKA : mo_ok MT S3 (XM_ANSWER MT (snd (rec_answer RA e slw_shape true)))).
{ apply (mo_ok_step MT MTL S S3 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg uri) + XM_XSTRDUP MT (sarg worker)));
  [| exact MLE3].
  unfold XM_SUP_LV2_WORKER_SET in HMOK. rewrite HM in HMOK. exact HMOK. }
assert (HAS : ANSWER_STK = 16592) by (vm_compute; reflexivity).
assert (Hcb64 : 0 <= c < 2 ^ 64).
{ destruct (rbt_slot_bounds c (slw_slot_ok R (slw_rep_len _ _ _ _ _ HREP))) as [Hcb _].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb. lia. }
assert (Holdb : 0 <= old < 2 ^ 64).
{ destruct Hold' as [-> | (m & Hm)]; [lia|].
  pose proof (rec_repA_in _ _ _ _ _ HREPA _ Hm) as Hm3.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 memA _ old m HARA Hm3) as (_ & H4 & Hpc & _ & _ & _ & Hm0).
  pose proof (req_size_pos m ltac:(lia)) as [Rq1 Rq2]. lia. }
assert (Hach : achain ly3 (rdW W3 memA) (sp0 + 0) (s0Z regsA) ch).
{ assert (Hs0 : s0Z regsA = s0Z regs).
  { unfold s0Z. pose proof (HPRA 8 ltac:(unfold acallee_saved; lia)) as H8.
    replace (Z_to_bv 5 8) with (8%bv : bv 5) in H8 by (apply bv_eq; reflexivity). rewrite H8. reflexivity. }
  rewrite Hs0, Z.add_0_r.
  pose proof HLYA as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  apply (achain_ly_top ly ly3 _ sp0 (s0Z regs) ch Etop).
  apply (achain_kept ly (rdW W mem) _ sp0 (s0Z regs) ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply F1; [lia | lia |]. intros HinF. pose proof (slw_FP_low ly S W mem md O a HAR HOin HinF). lia. }
assert (Hsig : Z_to_bv 64 (SIG CS_answer) = w64 (BASE + AF_answer)) by (rewrite slw_sig_answer; reflexivity).
rewrite Hsig.
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W3 regsA memA (w64 (BASE + AF_answer)) SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md []
    ly3 S3 _ k ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) OA))
    EV_ANSWER 0 (getr regsA 1) ch _ HJ HspA eq_refl ltac:(lia) ltac:(lia) ltac:(lia) QA3 QA4 eq_refl
    ltac:(rewrite QA1; exact Hra) ltac:(rewrite QA1; exact Hra4) Hach).
  - intros HPREA.
    exact (TANSWER fx ly3 S3 W3 regsA memA _ ch c qs old e slw_shape true RA OA HPREA HFM0 HFR8A HROA HROKA QA10 Hcb64
      QA11 Hqsb Hchg HREPA Hold Holdb Hshape Hslot HEVA HLIVEA HMOKA).
  - intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]].
    + right; right; right; right; left. apply slw_inFP_prog. left. cbn [fst snd] in Ha.
      unfold OFF_ANSWER, A_G_REC, REC_SIZE in *. lia.
    + right; right; right; right; left. apply slw_inFP_prog. left. cbn [fst snd] in Ha.
      unfold OFF_STATE, A_G_REC, REC_SIZE in *. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
      apply slw_in_filter in Hin.
      assert (Hin3 : In (p, n) (ablocks B ly3 S3)) by exact (rec_repA_in _ _ _ _ _ HREPA _ Hin).
      destruct (HOA (p, n) Hin) as [HinO | Hnew].
      * right; left. split.
        -- exists (p, p + req_size n). split; [right; right; unfold ablocks_fp; apply in_map_iff; exists (p, n); split; [reflexivity | exact HinO] | cbn; lia].
        -- exists p, n. split; [exact Hin3 | lia].
      * right; right; left. exists p, n. split; [exact Hin3|]. split; [exact Hnew | lia].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    destruct Ha as (r & Hr & Ha). pose proof asan_consts as (CC1 & _).
    destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + unfold OFF_ANSWER, A_G_REC in Ha. lia.
    + unfold OFF_STATE, A_G_REC in Ha. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
      apply slw_in_filter in Hin.
      destruct (al_blocks _ _ LAWS ly3 S3 W3 memA _ p n HARA (rec_repA_in _ _ _ _ _ HREPA _ Hin)) as (_ & _ & Hpc & _).
      lia. }
cbv beta. intros W4 c4 Hwle4 (fx1 & ly4 & S4 & regs4 & mem4 & md4 & Hfx & -> & HJ4 & HJa & HP4 & HK4).
(* the post: answer's, composed with what record() and the two copies did *)
pose proof (proj1 HJ4) as HAR4.
rewrite QA1. unfold slw_post.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly4 S4);
  [ exact Hfx
  | eapply (ajournal_mono_k SEGS B); [exact HJ4 | unfold EV_SUP_LV2_WORKER_SET; lia]
  | exact (aregs_preserved_trans _ _ _ HPRA HP4) |].
destruct HK4 as (p1' & q & O' & HK4). cbv zeta in HK4.
destruct HK4 as (HA10 & H4096 & Hne & HG1 & Hbl & Hrep' & HO' & Hstr & Hbb4 & Hmle).
set (t := snd (rec_answer RA e slw_shape true)) in *.
set (nt := Z.of_nat (length t) + 1) in *.
assert (HL3 : forall pn, In pn Lk -> In pn (ablocks B ly3 S3))
  by (intros pn HpnL; apply (Permutation_in _ (Permutation_sym HP3)); right; right; exact HpnL).
assert (HoldO : forall pn, In pn Lk -> ~ In pn O -> fst pn <> old).
{ intros pn HpnL HpnO Heq. destruct Hold' as [-> | (m & Hm)].
  - destruct pn as [pp pm]. pose proof (slw_blk_pos _ _ _ _ _ _ _ HARA (HL3 _ HpnL)). cbn in Heq. lia.
  - assert (Hm3 : In (old, m) (ablocks B ly3 S3)) by exact (rec_repA_in _ _ _ _ _ HREPA _ Hm).
    destruct (slw_pair_dec pn (old, m)) as [-> | Hne2].
    + destruct (HOA _ Hm) as [HinO | Hnin]; [exact (HpnO HinO)|].
      apply Hnin. apply (Permutation_in _ (Permutation_sym HPS)). apply in_or_app. right. exact HpnL.
    + destruct pn as [pp pm]. cbn in Heq. subst pp.
      exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HARA (HL3 _ HpnL) Hm3 Hne2) eq_refl). }
assert (HoldN : forall pn, ~ In pn Lk -> In pn O \/ ~ In pn (ablocks B ly S)).
{ intros pn HpnL. destruct (in_dec slw_pair_dec pn (ablocks B ly S)) as [Hin|Hin]; [left|right; exact Hin].
  apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [exact (HDf _ Hin) | contradiction]. }
(* a block answer made that is one of Lk can only be the old answer's, which the recorder owned *)
assert (HfreshL : forall x, x = p1' \/ x = q -> In (x, nt) Lk -> In (x, nt) OA).
{ intros x Hx HxL. pose proof (HL3 _ HxL) as Hx3.
  destruct (Z.eq_dec x old) as [Hxo | Hxo].
  2: { exfalso. destruct (HG1 (x, nt) Hx3 Hxo) as [Ha Hb]. destruct Hx as [-> | ->]; [exact (Ha eq_refl) | exact (Hb eq_refl)]. }
  subst x. destruct Hold' as [Ho0 | (m & Hm)].
  - exfalso. pose proof (slw_blk_pos _ _ _ _ _ _ _ HARA Hx3). lia.
  - assert (Hm3 : In (old, m) (ablocks B ly3 S3)) by exact (rec_repA_in _ _ _ _ _ HREPA _ Hm).
    destruct (slw_pair_dec (old, nt) (old, m)) as [-> | Hne2]; [exact Hm|].
    exfalso. exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HARA Hx3 Hm3 Hne2) eq_refl). }
assert (Hq4 : In (q, nt) (ablocks B ly4 S4)) by (apply Hbl; right; right; reflexivity).
unfold slw_Q.
exists (fst (rec_answer RA e slw_shape true)), t, q, O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact HA10|]. split; [exact H4096|]. split; [exact Hrep'|].
split.
{ intros pn Hpn. apply HO' in Hpn as [[HpnA _] | ->]; [exact (HOA pn HpnA)|].
  destruct (in_dec slw_pair_dec (p1', nt) Lk) as [HL | HL]; [exact (HOA _ (HfreshL p1' (or_introl eq_refl) HL)) | exact (HoldN _ HL)]. }
split; [exact Hq4|].
split.
{ intros pn Hpn HpnO ->.
  assert (HpnL : In (q, nt) Lk).
  { apply (Permutation_in _ HPS), in_app_iff in Hpn as [Hpn|Hpn]; [exact (False_ind _ (HpnO (HDf _ Hpn))) | exact Hpn]. }
  destruct (HOA _ (HfreshL q (or_intror eq_refl) HpnL)) as [HinO | Hnin]; [exact (HpnO HinO) | exact (Hnin Hpn)]. }
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hpq & Hpn). apply HO' in Hpn as [[HpnA Hpold] | ->].
  - assert (Hp3 : In pn (ablocks B ly3 S3)) by exact (rec_repA_in _ _ _ _ _ HREPA _ HpnA).
    assert (Hp4 : In pn (ablocks B ly4 S4)) by (apply Hbl; left; split; [exact Hp3 | exact Hpold]).
    destruct (slw_pair_dec pn (q, nt)) as [-> | Hne2]; [exact (proj2 (HG1 _ Hp3 Hpold) eq_refl)|].
    destruct pn as [pp pm]. cbn in Hpq. subst pp.
    exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HAR4 Hp4 Hq4 Hne2) eq_refl).
  - cbn in Hpq. exact (Hne Hpq). }
split; [exact Hstr|].
split.
{ intros pn Hpn HpnO.
  assert (HpnL : In pn Lk).
  { apply (Permutation_in _ HPS), in_app_iff in Hpn as [Hpn|Hpn]; [exact (False_ind _ (HpnO (HDf _ Hpn))) | exact Hpn]. }
  pose proof (HoldO pn HpnL HpnO) as Hpold.
  assert (Hp4 : In pn (ablocks B ly4 S4)) by (apply Hbl; left; split; [exact (HL3 _ HpnL) | exact Hpold]).
  split; [exact Hp4|].
  destruct (slw_pair_dec pn (q, nt)) as [-> | Hne2]; [exact (False_ind _ (proj2 (HG1 _ (HL3 _ HpnL) Hpold) eq_refl))|].
  destruct pn as [pp pm]. exact (proj1 (slw_blk_apart _ _ _ _ _ _ _ _ _ HAR4 Hp4 Hq4 Hne2)). }
split.
{ intros pn Hpn. apply Hbl in Hpn as [[Hp3 Hpold] | [-> | ->]].
  - apply (Permutation_in _ HP3) in Hp3. destruct Hp3 as [<- | [<- | HpnL]].
    + right; left. apply HO'. left. split; [apply in_or_app; right; right; left; reflexivity | exact Hpold].
    + right; left. apply HO'. left. split; [apply in_or_app; right; left; reflexivity | exact Hpold].
    + destruct (in_dec slw_pair_dec pn O) as [HinO | HnO].
      * right; left. apply HO'. left. split; [|exact Hpold]. apply in_or_app. left. apply HO1. split; [exact HinO|].
        intros HDfp. exact (slw_nodup ly S W mem md Df Lk pn HAR HPS HDfp HpnL).
      * left. split; [apply (Permutation_in _ (Permutation_sym HPS)); apply in_or_app; right; exact HpnL | exact HnO].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ unfold LIVE_SUP_LV2_WORKER_SET. rewrite HM. fold t. unfold LIVE_XSTRDUP, slw_n in *. lia. }
pose proof (mo_le_trans MT MTL _ _ _ _ _ MLE3 Hmle) as HML.
unfold XM_SUP_LV2_WORKER_SET. rewrite HM. exact HML.
Qed.

(* --- the segment from +0x110 (after the second xstrdup) to +0x150 ------------------------------------- *)

(* what a callee with an empty footprint keeps: the program's statics, the caller's frame above its sp, the
   bytes of every block that stays live *)
Lemma slw_callee_keeps : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc memc a) /\
(forall a, sp1 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
(forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW Wc memc (p + i)).
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & _).
split; [|split].
- intros a HP. rewrite <- (recb_ts_prog_m B HB) in HP.
  destruct (prog_static_sep B a (ts_ok B HB) HP) as (Ho & He & _).
  apply F3; [apply cmd_prog_img; rewrite <- (recb_ts_prog_m B HB); exact HP | exact Ho | exact He |].
  apply fp_spares_closed; [exact sink_closed_nil | intros (r & [] & _)].
- intros a Ha. apply F1; [lia | lia | intros (r & [] & _)].
- intros p n i H1 H2 Hi. exact (F2 p n i H1 H2 Hi (fun HF => match HF with ex_intro _ r (conj Hr _) => Hr end)).
Qed.

(* a live block lies apart from the program's statics *)
Lemma slw_heap_prog_apart : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> iv_apart p n A_G_REC REC_SIZE /\ iv_apart p n A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
assert (Himg : forall a, p <= a < p + req_size n -> ~ in_img SEGS a) by (intros a Ha; exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin Ha)).
unfold iv_apart. split.
- destruct (Z_le_gt_dec (p + n) A_G_REC) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (A_G_REC + REC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (Himg (Z.max p A_G_REC)); [lia|]. apply cmd_prog_img. apply recb_grec_in. unfold REC_SIZE in *. lia.
- destruct (Z_le_gt_dec (p + n) A_REC_SPILL) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (A_REC_SPILL + SC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (Himg (Z.max p A_REC_SPILL)); [lia|]. apply cmd_prog_img. apply recb_spill_in. unfold SC_SIZE in *. lia.
Qed.

Lemma slw_sarg_len : forall ly S rd ro O p v, astr_argA B ly S rd ro O p v -> Z.of_nat (length (sarg v)) <= LMAX.
Proof.
intros ly S rd ro O p [x|] H; cbn [sarg]; [|unfold LMAX; cbn; lia].
destruct H as (_ & _ & Hn & _). unfold LMAX in *. lia.
Qed.

(* the slot's nargs field holds the arguments recorded so far *)
Lemma slw_slot_nargs : forall ly S rd R fn A O', rec_repA B ly S rd (rec_record R fn A) O' ->
(length (r_calls R) <= 16)%nat -> aval_mem rd (slw_slot R + 4) 4 (Z.of_nat (length A)).
Proof.
intros ly S rd R fn A O' (Q & HA & _) Hlen. unfold rec_record, slw_slot in *.
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl]; cbn [set_calls set_spill r_calls r_spill] in *.
- assert (Hne : l_calls Q <> []) by (intros E; rewrite E in C2; rewrite length_app in C2; cbn in C2; lia).
  destruct (exists_last Hne) as (Lc & P & EQ).
  assert (HLc : length Lc = length (r_calls R)) by (rewrite EQ, !length_app in C2; cbn in C2; lia).
  destruct (C4 (length (r_calls R)) (fn, A) P) as [(_ & _ & _ & _ & H5 & _) _].
  + rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  + rewrite EQ, nth_error_app2, HLc, Nat.sub_diag by lia. reflexivity.
  + unfold CALL_OFF_NARGS in H5. exact H5.
- destruct C5 as (_ & _ & _ & _ & H5 & _). unfold CALL_OFF_NARGS in H5. exact H5.
Qed.

(* MID2, the state at +0x110 (0x8bf90), just after the second xstrdup returned the copy p2 of the second argument;
   the slot holds FN and the first argument *)
Definition slw_mid2 ly S (W : world SEGS) (regs : bvmap 5 word) mem md (uri worker : option (list byte))
(R : rstate) (O : list (Z * Z)) lyc Sc (Wc : world SEGS) (regs2 : bvmap 5 word) memc mdc (k p1 p2 : Z)
(Df Lk O1 : list (Z * Z)) : Prop :=
let sp0 := spZ regs in
let c := slw_slot R in
ajournal SEGS B SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= rec_spill_frees R + EV_XSTRDUP + EV_XSTRDUP /\
slw_frame (rdW Wc memc) sp0 regs /\
getr regs2 2 = w64 (sp0 - 64) /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
getr regs2 8 = w64 c /\ getr regs2 18 = w64 (c + 4) /\ getr regs2 19 = w64 (c + 8) /\
getr regs2 20 = w64 SHADOW_OFF /\ getr regs2 21 = w64 (SHADOW_OFF + (c + 4) / 8) /\ getr regs2 10 = w64 p2 /\
(forall r, 22 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_LV2_WORKER_SET [sarg uri]) (O1 ++ [(p1, slw_n uri)]) /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Df) /\ (forall pn, In pn Df -> In pn O) /\
((length (r_calls R) < 16)%nat -> Df = []) /\
Permutation (ablocks B ly S) (Df ++ Lk) /\
Permutation (ablocks B lyc Sc) ((p2, slw_n worker) :: (p1, slw_n uri) :: Lk) /\
~ In (p1, slw_n uri) Lk /\ ~ In (p2, slw_n worker) ((p1, slw_n uri) :: Lk) /\
4096 <= p1 /\ 4096 <= p2 /\ astr_atR (rdW Wc memc) p2 (sarg worker) /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg uri) + XM_XSTRDUP MT (sarg worker)).

Lemma slw_abytes_prefix : forall rd a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. specialize (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by lia. exact H.
Qed.

Definition slw_verb : list byte := bstr "lv2_worker_set".

Lemma slw_harg_len : forall ly S rd O p v, slw_harg B ly S rd O p v -> Z.of_nat (length (sarg v)) <= LMAX.
Proof. intros ly S rd O p v (x & -> & _ & _ & Hn & _). cbn [sarg]. unfold LMAX in *. lia. Qed.

(* a byte range none of a concrete list of ranges holds *)
Lemma slw_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz).
rewrite forallb_forall in Hb. specialize (Hb r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma slw_verb_lit : RO_lit_21ea0 = slw_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

(* the conjunct of a long conjunction that is the goal *)
Ltac slw_proj H :=
  lazymatch type of H with
  | _ /\ _ => first [exact (proj1 H) | let H2 := constr:(proj2 H) in slw_proj H2]
  | _ => exact H
  end.

Lemma slw_D2 : forall ly S W regs mem md ch pu pw uri worker R O lyc Sc Wc regs2 memc mdc k p1 p2 Df Lk O1,
slw_pre B MT ly S W regs mem md ch pu pw uri worker R O ->
slw_mid2 ly S W regs mem md uri worker R O lyc Sc Wc regs2 memc mdc k p1 p2 Df Lk O1 ->
SRr SEGS Wc (cfg_at SEGS (BASE + SLW_RET2) regs2 memc mdc) (slw_post B MT ly S W regs mem md R uri worker O).
Proof.
intros ly S W regs mem md ch pu pw uri worker R O lyc Sc Wc regs2 memc mdc k p1 p2 Df Lk O1 HPRE MID.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as HPRE0.
destruct HPRE as (HFN & HFM0 & HROD & HRO & H10 & Hpub & H11 & Hpwb & HSU & HSW & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as MID0.
destruct MID as (HJ & Hk & HFRM & R2 & R3 & R4 & R8 & R18 & R19 & R20 & R21 & R10 & Rhi & HREP2 & HO1 & HDf & HDf0 &
  HPS & HP2 & Hn1 & Hn2 & Hp1 & Hp2 & Hstr2 & MLE2).
pose proof (proj1 HJ) as HAR2.
set (sp0 := spZ regs) in *. set (c := slw_slot R) in *.
assert (Hlen : (length (r_calls R) <= 16)%nat) by exact (slw_rep_len _ _ _ _ _ HREP).
assert (Hc : rbt_slot_ok c) by exact (slw_slot_ok R Hlen).
destruct (rbt_slot_bounds c Hc) as [Hcb Hc8].
assert (HSTK : SUP_LV2_WORKER_SET_STK = 16592) by (vm_compute; reflexivity).
set (n0 := Z.of_nat (length (r_calls R))) in *.
set (E := Eimg (Ereg regs2 (slw_extra regs n0 c))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (slw_extra regs n0 c) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EC : ew E 34 = Z_to_bv 64 c) by (change 34%nat with (32 + 2)%nat; rewrite EX by lia; reflexivity).
assert (ESB : ew E 32 = Z_to_bv 64 SB) by (change 32%nat with (32 + 0)%nat; rewrite EX by lia; reflexivity).
assert (Hc0 : 0 <= c < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia).
destruct (slw_seed SLW_RET2 slw_sregs2 (slw_nargs 1) 16 lyc Sc Wc memc mdc regs regs2 (sp0 - 64) n0 c HAR2)
  as [HS SHOK].
{ lia. } { lia. } { Z.div_mod_to_equations. lia. } { subst n0; lia. } { exact Hc. }
{ rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
{ replace (sp0 - 64 + 64) with sp0 by lia. exact HFRM. }
{ fold E. apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get ?l ?rr) =>
        let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v end;
      first [ (cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; symmetry; apply EEo; reflexivity)
            | (cbn [sv_denot]; rewrite getr_zero; reflexivity)
            | idtac ]
    | ]); try (destruct Hr; fail).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EC. exact R8.
  - cbn [sv_denot]. rewrite EC, unsigned_lit_small by lia. exact R18.
  - cbn [sv_denot]. rewrite EC, unsigned_lit_small by lia. exact R19.
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ESB. exact R20.
  - unfold slw_shx4. rewrite (denot_shx E 34 32 4 c SB EC ESB) by (unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    exact R21. }
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ c 4 4 (SLit 1) 1); [reflexivity | lia | lia |].
  apply (RecBLemmas.val_mem_view SEGS). exact (slw_slot_nargs _ _ _ _ _ _ _ HREP2 Hlen). }
{ vm_compute. reflexivity. }
{ lia. }
fold E in HS, SHOK.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK slw_Bspan.
{ apply (slw_awr_ok E (slw_nargs 1) 16 _ sp0 O _ _ _ _ _ c); [unfold RB_C; rewrite EC; apply unsigned_lit_small; lia | exact Hc | lia | unfold CALL_SIZE; lia]. }
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdv0 |} _ => set (mdX := mdv0) in *; clearbody mdX end.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
set (regsX := ms_regs ms) in *. set (memX := ms_mem ms) in *.
assert (UC : bv_unsigned (ew E 34) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (Hsp64 : 0 <= sp0 - 64 < 2 ^ 64) by lia.
(* p2's block, and the bounds of the live blocks *)
assert (Hp2in : In (p2, slw_n worker) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
assert (Hbnd : forall p n, In (p, n) (ablocks B lyc Sc) -> 4096 <= p /\ p + n < 2 ^ 47 /\ 0 <= n).
{ intros p n Hpn. destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR2 Hpn) as (_ & H4 & Hpc & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [Rq1 Rq2]. lia. }
destruct (Hbnd p2 (slw_n worker) Hp2in) as (Hp2a & Hp2b & Hp2c).
(* the two stores: nargs = 2 at c + 4, the copy p2 at c + 16 *)
pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as HRg1. cbn [ms_mem restrict] in HRg1.
pose proof (st_ok_region_nth E _ _ 2 _ HS eq_refl) as HRg2. cbn [ms_mem restrict] in HRg2.
pose proof (field_of_region_any E _ 34 c _ _ _ _ _ 4 4 (SLit 2) HRg1 UC ltac:(cbn; tauto) ltac:(cbn; lia)) as V4.
pose proof (field_of_region_any E _ 34 c _ _ _ _ _ 16 8 (SOff 10 0) HRg2 UC ltac:(cbn; tauto) ltac:(cbn; lia)) as V16.
assert (D4 : bv_unsigned (sv_denot E (SLit 2)) mod 2 ^ (8 * Z.of_N 4) = Z.of_nat (length [sarg uri]) + 1)
  by (cbn [sv_denot length]; rewrite unsigned_lit_small by lia; reflexivity).
assert (D16 : bv_unsigned (sv_denot E (SOff 10 0)) mod 2 ^ (8 * Z.of_N 8) = p2).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl), R10. unfold w64.
  rewrite unsigned_lit_small by lia. apply Z.mod_small. cbn. lia. }
rewrite D4 in V4. rewrite D16 in V16.
apply (aval_mem_view SEGS) in V4. apply (aval_mem_view SEGS) in V16.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ memc) (mrestrict _ memX) |- _ =>
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c + 4 <= a < c + 8 \/ c + 16 <= a < c + 24) Hfr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?UC in Hrr; lia|]);
          destruct Hin))
    as KEEP0 end.
assert (KEEPX : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 4 <= a < c + 8 \/ c + 16 <= a < c + 24) ->
  rdW Wc memX a = rdW Wc memc a) by exact KEEP0.
clear KEEP0.
(* the recorder after the stores: the slot holds both arguments *)
set (RA := rec_record R REC_LV2_WORKER_SET [sarg uri; sarg worker]) in *.
set (OA := O1 ++ [(p1, slw_n uri); (p2, slw_n worker)]) in *.
assert (HO1Lk : forall pn, In pn O1 -> In pn Lk).
{ intros pn Hpn. destruct (proj1 (HO1 pn) Hpn) as [HinO HnDf].
  pose proof (rec_repA_in _ _ _ _ _ HREP pn HinO) as Hin.
  apply (Permutation_in _ HPS), in_app_iff in Hin as [Hin|Hin]; [contradiction | exact Hin]. }
assert (HOAc : forall pn, In pn (O1 ++ [(p1, slw_n uri)]) -> In pn (ablocks B lyc Sc))
  by exact (rec_repA_in _ _ _ _ _ HREP2).
assert (HREPX : rec_repA B lyc Sc (rdW Wc memX) RA OA).
{ subst RA OA. replace (O1 ++ [(p1, slw_n uri); (p2, slw_n worker)]) with ((O1 ++ [(p1, slw_n uri)]) ++ [(p2, slw_n worker)])
    by (rewrite <- app_assoc; reflexivity).
  change [sarg uri; sarg worker] with ([sarg uri] ++ [sarg worker]).
  apply (slw_rep_push lyc Sc (rdW Wc memc) lyc Sc (rdW Wc memX) R REC_LV2_WORKER_SET [sarg uri] (O1 ++ [(p1, slw_n uri)])
    (sarg worker) p2 (slw_n worker) HREP2 Hlen ltac:(cbn; lia) (slw_harg_len _ _ _ _ _ _ HSW)).
  - intros a Ha Hn4 Hn16. apply KEEPX; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia|].
    fold c in Hn4, Hn16. cbn [length] in Hn16. lia.
  - exact V4.
  - cbn [length]. change (slw_slot R) with c. replace (c + 8 + 8 * Z.of_nat 1) with (c + 16) by lia. exact V16.
  - intros q m i Hq Hi. destruct (Hbnd q m (HOAc _ Hq)) as (Hq1 & Hq2 & Hq3).
    destruct (slw_heap_prog_apart lyc Sc Wc memc mdc q m HAR2 (HOAc _ Hq)) as [Ag As].
    apply KEEPX; [lia|]. unfold iv_apart, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *.
    destruct Hc as [(Hc1 & Hc2 & _) | Hc']; unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia.
  - exact HOAc.
  - exact Hp2in.
  - lia.
  - pose proof (slw_harg_len _ _ _ _ _ _ HSW). unfold slw_n. lia.
  - apply (rastr_kept (rdW Wc memc)); [exact Hstr2|]. intros i Hi.
    destruct (slw_heap_prog_apart lyc Sc Wc memc mdc p2 _ HAR2 Hp2in) as [Ag As].
    apply KEEPX; [unfold slw_n in *; lia|]. unfold iv_apart, slw_n, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *.
    destruct Hc as [(Hc1 & Hc2 & _) | Hc']; unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia.
  - intros pn Hpn Heq. apply in_app_iff in Hpn as [Hpn | [<- | []]].
    + assert (HpnL : In pn Lk) by exact (HO1Lk pn Hpn).
      assert (Hpn3 : In pn (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP2)); right; right; exact HpnL).
      destruct (slw_pair_dec pn (p2, slw_n worker)) as [-> | Hne2]; [apply Hn2; right; exact HpnL|].
      destruct pn as [pp pm]. cbn in Heq. subst pp.
      exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HAR2 Hpn3 Hp2in Hne2) eq_refl).
    + assert (Hp13 : In (p1, slw_n uri) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP2)); right; left; reflexivity).
      cbn in Heq. subst p1.
      destruct (slw_pair_dec (p2, slw_n uri) (p2, slw_n worker)) as [Heq2 | Hne2]; [apply Hn2; left; exact Heq2|].
      exact (proj2 (slw_blk_apart _ _ _ _ _ _ _ _ _ HAR2 Hp13 Hp2in Hne2) eq_refl).
  - exact (proj1 (slw_heap_prog_apart lyc Sc Wc memc mdc p2 _ HAR2 Hp2in)).
  - exact (proj2 (slw_heap_prog_apart lyc Sc Wc memc mdc p2 _ HAR2 Hp2in)). }
(* rec_shape_of's entry: the verb literal and its length *)
pose proof (proj1 HJ) as HARX.
pose proof HJ as (_ & HLYX & _ & _ & _ & HFRX & HNEVX & _).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (rec_repA_in ly S _ R O HREP).
assert (HROX : arodata_okP SEGS RLO RHI B (rdW Wc memX)) by exact (slw_aro_at ly S W mem md O _ _ _ _ _ _ _ _ _ HAR HOin HJ HROD).
assert (HROKX : cmd_ro_ok (rdW Wc memX)) by exact (cmd_ro_ok_of_aro lyc Sc Wc memX _ HARX HROX).
assert (HLIT : abytes_atR (rdW Wc memX) 0x21ea0 RO_lit_21ea0).
{ destruct HROKX as [HBY _]. unfold cmd_ro_bytes in HBY. slw_proj HBY. }
assert (HLITro : forall i, 0 <= i < 15 -> in_roP SEGS RLO RHI (0x21ea0 + i)).
{ pose proof CMD_RO_IN as HRI. unfold cmd_ro_in in HRI. slw_proj HRI. }
assert (HBYTES : Z.of_nat (length slw_verb) <= 16 ->
  abytes_atR (rdW Wc memX) 0x21ea0 slw_verb /\
  (in_blockA (ablocks B lyc Sc) 0x21ea0 (Z.of_nat (length slw_verb)) \/
   astr_argA B lyc Sc (rdW Wc memX) (in_roP SEGS RLO RHI) [] 0x21ea0 (Some slw_verb))).
{ intros _. rewrite slw_verb_lit in HLIT. split; [exact (slw_abytes_prefix _ _ _ _ HLIT)|].
  right. cbn [astr_argA]. change (Z.of_nat (length slw_verb)) with 14. split; [lia|]. split.
  { split; [exact HLIT|]. intros Hz. cbn in Hz.
    repeat (destruct Hz as [Hz|Hz]; [apply (f_equal bv_unsigned) in Hz; vm_compute in Hz; discriminate Hz|]). exact Hz. }
  split; [unfold LMAX; lia|]. right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]].
  - intros i Hi. split; [apply HLITro; lia|]. rewrite (ts_owned B HB), (ts_errno B HB). split.
    + apply (slw_unowned_rng 0x21ea0 15); [vm_compute; reflexivity | lia].
    + unfold TFIB_ERRNO. lia.
  - cbv [cmd_ro_ends]. repeat (first [left; reflexivity | right]). }
assert (QX10 : getr regsX 10 = w64 0x21ea0).
{ rewrite Q10. subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
  change 310%nat with (A_OBJ 69%nat). rewrite (VOBJS 69%nat ltac:(vm_compute; lia)). reflexivity. }
assert (QX11 : getr regsX 11 = w64 (Z.of_nat (length slw_verb))) by (rewrite Q11; reflexivity).
assert (HEVX : st_nev Sc + EV_REC_SHAPE_OF <= EV_MAX).
{ assert (0 <= EV_ANSWER) by (unfold EV_ANSWER; vm_compute; congruence).
  unfold EV_REC_SHAPE_OF, EV_SUP_LV2_WORKER_SET in *; lia. }
assert (QX2 : getr regsX 2 = w64 (sp0 - 64)) by (rewrite Q2, (EEo 2%nat 2%bv eq_refl); exact R2).
assert (QX3 : getr regsX 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (QX4 : getr regsX 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4; exact Htp).
assert (QX8 : getr regsX 8 = w64 c) by (rewrite Q8; exact EC).
assert (HspX : spZ regsX = sp0 + -64) by (unfold spZ; rewrite QX2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hach0 : achain lyc (rdW Wc memX) (sp0 + -64) (s0Z regsX) []).
{ apply achain_low. unfold s0Z. rewrite QX8. unfold w64. rewrite unsigned_lit_small by lia.
  pose proof asan_consts as (CC1 & _). unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb. lia. }
assert (Hsig : Z_to_bv 64 (SIG CS_rec_shape_of) = w64 (BASE + AF_rec_shape_of)) by (rewrite slw_sig_rec_shape_of; reflexivity).
rewrite Hsig.
assert (QR1 : getr regsX 1 = w64 (BASE + SLW_RET3)) by (rewrite Q1; reflexivity).
assert (QXhi : forall r, 22 <= r <= 27 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. assert (Hr6 : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
    let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew E ?n = getr regs (Z_to_bv 5 ?m) =>
    rewrite (EEo n (Z_to_bv 5 m) eq_refl); apply Rhi; lia end. }
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS Wc regsX memX (w64 (BASE + AF_rec_shape_of)) SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md []
    lyc Sc mdX k REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-64) (getr regsX 1) _ HJ HspX ltac:(reflexivity) ltac:(lia)
    ltac:(vm_compute; discriminate) ltac:(rewrite HSTK; vm_compute; discriminate) QX3 QX4 eq_refl
    ltac:(rewrite QR1; apply ret_ok_codeptr_v; [unfold SLW_RET3, AF_sup_lv2_worker_set; lia | reflexivity])
    ltac:(rewrite QR1; unfold w64; rewrite unsigned_lit_small by (unfold SLW_RET3, AF_sup_lv2_worker_set; lia);
          unfold SLW_RET3, AF_sup_lv2_worker_set; lia)).
  - intros HPREX.
    exact (TREC_SHAPE_OF fx lyc Sc Wc regsX memX mdX 0x21ea0 slw_verb HPREX HROX QX10 ltac:(lia) QX11 ltac:(vm_compute; split; congruence)
      HROKX VOBJS HBYTES HEVX).
  - intros a (r & [] & _). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & HK4).
destruct HK4 as ((qs & HQ10 & Hqsb & Hqs) & HPerm4 & Ely4 & ES4). subst lyc Sc.
destruct (slw_callee_keeps _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (KP & KF & KB).
replace (mkCfg (mkst regs4 (getr regsX 1) mem4 (seg_rom SEGS)) md4) with (cfg_at SEGS (BASE + SLW_RET3) regs4 mem4 md4)
  by (unfold cfg_at; rewrite QR1; reflexivity).
apply (slw_D3 ly S W regs mem md ch pu pw uri worker R O ly4 S4 W4 regs4 mem4 md4 (k + EV_REC_SHAPE_OF) p1 p2 qs Df Lk O1 HPRE0).
assert (HP4' : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr regsX r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). exact (HP4 _ Hr). }
assert (HinX4 : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly4 S4))
  by (intros pn Hpn; exact Hpn).
unfold slw_mid3. change (spZ regs) with sp0. change (slw_slot R) with c.
split; [exact HJ4|].
split; [unfold EV_REC_SHAPE_OF; lia|].
split.
{ intros j r Hj. pose proof (proj1 (nth_error_Some slw_saved j) ltac:(rewrite Hj; discriminate)) as Hj7.
  cbn [length slw_saved] in Hj7.
  apply (aval_mem_kept (rdW Wc memc)); [exact (HFRM j r Hj)|]. intros kk Hkk.
  rewrite KF by lia. apply KEEPX; [lia|].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb. lia. }
split; [rewrite HP4' by (unfold acallee_saved; left; reflexivity); exact QX2|].
split; [rewrite HP4' by (unfold acallee_saved; right; left; reflexivity); rewrite QX3; symmetry; exact Hgp|].
split; [rewrite HP4' by (unfold acallee_saved; right; right; left; reflexivity); rewrite QX4; symmetry; exact Htp|].
split; [rewrite HP4' by (unfold acallee_saved; right; right; right; left; reflexivity); exact QX8|].
split; [exact HQ10|].
split.
{ intros r Hr. rewrite (HP4 r ltac:(unfold acallee_saved; lia)). exact (QXhi r Hr). }
split.
{ apply (rec_repA_kept ly4 S4 (rdW Wc memX) ly4 S4 (rdW W4 mem4) RA OA HREPX).
  - intros pn Hpn. exact (HinX4 _ (rec_repA_in _ _ _ _ _ HREPX pn Hpn)).
  - intros a Ha. apply KP. apply recb_grec_in. unfold REC_SIZE. exact Ha.
  - intros a Ha. apply KP. apply recb_spill_in. unfold SC_SIZE. exact Ha.
  - intros p n i Hpn Hi. pose proof (rec_repA_in _ _ _ _ _ HREPX _ Hpn) as Hpc.
    destruct (Hbnd p n Hpc) as (_ & _ & Hn0). pose proof (req_size_pos n Hn0) as [_ Rn].
    exact (KB p n i Hpc (HinX4 _ Hpc) ltac:(lia)). }
split; [exact HO1|]. split; [exact HDf|]. split; [exact HDf0|]. split; [exact HPS|].
split; [exact HP2|].
split; [exact Hn1|]. split; [exact Hn2|]. split; [exact Hp1|]. split; [exact Hp2|].
replace slw_shape with (shape_of slw_verb) by (vm_compute; reflexivity).
split; [exact Hqsb|]. split; [exact Hqs|].
exact MLE2.
Qed.

End e.
End f.
End d.
