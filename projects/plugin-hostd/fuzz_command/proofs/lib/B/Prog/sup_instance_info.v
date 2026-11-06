(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_instance_info (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8bb70, 122 instructions), after lib/A/Prog/answer_code.v (a working branch
   2ba4488ce71: a side-stack frame taken by __asan_stack_malloc_N, its header and shadow, the snprintf call and the
   release by the flag store) and lib/A/Prog/sup_instance_info.v (a working branch 0de7ca03d26: the
   recorder's chain through record, arg_s, rec_shape_of and answer and the post), re-derived on B's code, against
   a Theorem Labs lane's statement (a working branch f490061c104). The snprintf step through the shared contract and the change of FP
   state after it follow a working branch 07b554c4785 (lib/B/Prog/answer_code.v:943-1070), the release
   by the flag store answer_code.v's end, the post's block algebra a working branch b5e1a22725a
   (descriptors_panel_get_aux.v dpgb_post_of), the calls after record a working branch c79a9f2daf7. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaArt PaFx RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c hand_back_c mix_call_c record_c arg_s_c rec_shape_of_c answer_c sup_instance_info_c
sup_instance_info_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a register's symbolic value in a symbolic state, without normalising the denotation *)
Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Ltac norm_ssp HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* an address outside every write window of a symbolic memory *)
Ltac nwin_tac rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.

Lemma sii_denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U.
change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma sii_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* a byte the reader shows is in [0, 256) (answer_code.v:49 ac_aview_rng) *)
Lemma sii_aview_rng : forall (sg : list Segment) H mem a v, aview sg H mem a = Some v -> 0 <= v < 256.
Proof.
intros sg H mem a v Hv. unfold aview in Hv. destruct (mbyte sg (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
(* the recorder's answer field holds 0 or the start of one of its blocks (sup_reset.v:227-237) *)
Definition sii_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma sii_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  aval_mem rd (A_G_REC + OFF_ANSWER) 8 (sii_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
  intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold sii_old. split.
  - unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
    [exact (proj1 HA) | exact HA].
  - intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
Qed.

Lemma sii_fits : fits (shape_of sii_verb).
Proof. unfold fits. vm_compute. congruence. Qed.

Lemma sii_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* the read-only ranges the snprintf chain names (RtPFCmd.CMD_SNP_CR): low image addresses (decided on the closed
   list; a working branch 07b554c4785 answer_code.v:56 ac_snp_rng; bound 0x606000 since a Theorem Labs lane's FR_cmd
   mirror 0934cb146c3, whose CMD_SNP_CR is the two non-writable load segments, as CmdSnText's snt_cr_in) *)
Lemma sii_snp_rng : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ fst r + snd r <= 0x606000 /\ 0 <= snd r.
Proof.
intros r Hr.
assert (H : forallb (fun r : Z * Z => (0x10000 <=? fst r) && (fst r + snd r <=? 0x606000) && (0 <=? snd r))
  RtPFCmd.CMD_SNP_CR = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2, H3. lia.
Qed.
(* a low object (in the image hull) is apart from the snprintf chain's outputs: the scratch window below sp and the
   destination, which lies off the image hull (answer_code.v:78 ac_lo_disj) *)
Lemma sii_lo_disj : forall a n K sp d w, 0 <= n -> 0x10000 <= a -> a + n <= 0x606000 -> a + n <= sp - K -> 0 <= K ->
(d + w <= 0x10000 \/ 0x606000 <= d) -> Forall (zdisjoint (a, n)) (snp_out K sp d w).
Proof.
intros a n K sp d w Hn Ha Han Hsp HK Hd. unfold snp_out.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; lia.
Qed.
(* the format "%d" as the shared contract reads it: the bytes of CmdRo's literal 0x21f40 *)
Lemma sii_fmt_rd : forall rd, abytes_atR rd 0x21f40 RO_lit_21f40 ->
forall i, 0 <= i <= 2 -> rd (0x21f40 + i) = Some (nth (Z.to_nat i) (PAI.AI_FMT ++ [0]) 0).
Proof.
intros rd H i Hi.
assert (E : exists k, (k < 3)%nat /\ i = Z.of_nat k) by (exists (Z.to_nat i); split; lia).
destruct E as (k & Hk & ->). rewrite Nat2Z.id. rewrite (H k ltac:(unfold RO_lit_21f40; cbn [length map]; lia)).
do 3 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* the write windows of the six regions the walk carries from the frame setup on (the frame's shadow, its flag
   word, its header, two pieces of the own stack frame, the realigned stack word), class 0's sizes
   (answer_code.v:690 awr6) *)
Ltac sii_awr6 fpos sp1 regs FS Vs Vf V2 V34 EFA :=
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1041%nat); [reflexivity | exact Vs |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |];
apply (awr_ok_cons_ro _ _); [cbn; lia|];
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1028%nat); [reflexivity | exact Vf |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 0) with 64; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |];
apply (awr_ok_nil _ _).

Section d. Context {rc : YM05.RunCeil}.
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
(* the statement's Section hypotheses (sup_instance_info_c.v:83-90), word for word *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
@asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses of RULING-STMT.md section 1 (cgif's names) *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
(* a Theorem Labs lane states it only at PI := PB_cmd (CmdRecRest.v cmd_sig_prog_PB), so it is a Section
   hypothesis under that lemma's name *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the per-binary record facts: a Theorem Labs lane's B CmdRecFacts groups (a working branch 707acd856cb, lib/B/Prog/CmdRec*.v)
   prove them for any segs / B from LAWS, HB and this one record, so the walk carries only it *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
(* the side-stack frame's flag law: a Theorem Labs lane states it at tfibsegs (CmdRecRest.v cmd_frame_flag_law), so it is a
   Section hypothesis under that lemma's name *)
Hypothesis cmd_frame_flag_law : forall B0, frame_flag_lawP SEGS B0.

Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
(* every per-binary record fact is a Theorem Labs lane's lemma over LAWS, HB and IMG (lib/B/Prog/CmdRec*.v) *)
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a ->
  in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.
Let RELRO_IMG : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecRo.RELRO_IMG (SK := SK) SEGS B LAWS HB IMG.
Let ROB : ro_below_ofl SEGS RLO RHI := CmdRecRo.ROB (SK := SK) SEGS B LAWS HB IMG.
Let ML : model_laws (as_universe B) := CmdRecRest.cmd_model_laws B HB.
Let sii_SMP : stack_malloc_progressP B := CmdRecRest.cmd_stack_malloc_progress B.
Let sii_ts_prog : as_prog_static B = TFIB_PROG_STATIC := recb_ts_prog_m B HB.
Let sii_FFL : frame_flag_lawP SEGS B := cmd_frame_flag_law B.
(* every byte of g_rec / record.spill / g_quitting is an image byte no runtime entry owns *)
Let sii_prog_unowned : forall a, Exists (in_zr a) TFIB_PROG_STATIC ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) :=
  recb_prog_unowned_m B HB cmd_prog_img.

Lemma sii_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_exists. exists (0x5e32c0, 960). split; [left; reflexivity|].
unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
Qed.

Lemma sii_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_exists. exists (0x5e3760, 56). split; [right; left; reflexivity|].
unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
Qed.

(* ---- what a callee's journal keeps (sup_reset.v:434-469, c79a9f2daf7) ---- *)
Lemma sii_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

Lemma sii_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (sii_prog_unowned a HP) as (H1 & H2 & H3).
exact (sii_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

Lemma sii_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

(* the bytes of a string argument decide astr_argA's reader part (sup_reset.v:543) *)
Lemma sii_argA_kept : forall ly1 S1 (rd rd' : reader) ro O1 p v, astr_argA B ly1 S1 rd ro O1 p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly1 S1 rd' ro O1 p (Some v).
Proof.
intros ly1 S1 rd rd' ro O1 p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [|split; [exact Hl | exact Hr]].
apply (sii_astr_kept rd); [exact Hs|]. intros x Hx. replace x with (p + (x - p)) by lia. apply K. lia.
Qed.

(* ---- the blocks of the walk's points and the statement's post (descriptors_panel_get_aux.v:943-1088,
   a working branch b5e1a22725a, for sup_instance_info's model) ---- *)
Lemma siq_req_ge : forall x, 0 <= x -> 1 <= req_size x /\ x <= req_size x.
Proof. exact req_size_pos. Qed.

Lemma siq_same_start : forall ly S (W : world SEGS) mem md p m n, AR SEGS B ly S W mem md ->
In (p, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> m = n.
Proof.
intros ly S W mem md p m n HAR H1 H2.
destruct (Z.eq_dec m n) as [E | E]; [exact E|]. exfalso.
pose proof (al_blocks _ _ LAWS ly S W mem md p m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
assert (Hne : (p, m) <> (p, n)) by congruence.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p m p n HAR H1 H2 Hne) as Hd.
pose proof (siq_req_ge m ltac:(lia)) as Rm. pose proof (siq_req_ge n ltac:(lia)) as Rn.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma siq_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) -> iv_apart b m p n.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (al_blocks _ _ LAWS ly S W mem md b m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as Hd.
pose proof (siq_req_ge m ltac:(lia)) as Rm. pose proof (siq_req_ge n ltac:(lia)) as Rn.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold iv_apart. lia.
Qed.

(* how the blocks after record() relate to the entry's *)
Definition siq_blk ly S (O : list (Z * Z)) lyc Sc (O1 : list (Z * Z)) : Prop :=
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O) /\
(forall pn, In pn O1 -> In pn O) /\
(forall pn, In pn O -> ~ In pn O1 -> ~ In pn (ablocks B lyc Sc)) /\
(exists fr, Permutation (ablocks B ly S) (ablocks B lyc Sc ++ fr)).

Lemma siq_blk_of_record : forall ly S (W : world SEGS) mem md O lyc Sc F O1, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) -> siq_blk ly S O lyc Sc O1.
Proof.
intros ly S W mem md O lyc Sc F O1 HAR HP HF HO1.
pose proof (Permutation_NoDup HP (recb_ablocks_nodup_m B ly S W mem md HAR)) as Hnd.
split.
{ intros pn H. apply (Permutation_in pn (Permutation_sym HP)). apply in_or_app. left. exact H. }
split.
{ intros pn H1 H2. apply (Permutation_in pn HP) in H1. apply in_app_or in H1 as [H | H]; [exfalso; exact (H2 H)|].
  exact (HF pn H). }
split.
{ intros pn H. exact (proj1 (proj1 (HO1 pn) H)). }
split.
{ intros pn HO HnO1 Hc. destruct (in_dec sii_pair_dec pn F) as [HinF | HnF].
  - exact (sii_nodup_disj _ _ pn Hnd Hc HinF).
  - apply HnO1. apply (proj2 (HO1 pn)). split; [exact HO | exact HnF]. }
exists F. exact HP.
Qed.

Lemma siq_post_of : forall ly S R id O lyc Sc O1 ly2 S2 ly3 S3 (W3 : world SEGS) mem3 md3 ly4 S4 (W4 : world SEGS)
  (regs4 : bvmap 5 word) mem4 md4
  (x : list byte) (p p1 p2 old : Z) (O2 O' : list (Z * Z)) (R' : rstate) (t : list byte),
siq_blk ly S O lyc Sc O1 ->
Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length x) + 1) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) ->
Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
AR SEGS B ly3 S3 W3 mem3 md3 -> AR SEGS B ly4 S4 W4 mem4 md4 ->
(forall pn, In pn O2 <-> In pn O1 \/ pn = (p, Z.of_nat (length x) + 1)) ->
(forall pn, In pn O2 -> In pn (ablocks B ly3 S3)) ->
(old = 0 \/ exists m, In (old, m) O2) ->
4096 <= p2 < 2 ^ 64 -> p1 <> p2 ->
(forall pn, In pn (ablocks B ly3 S3) -> fst pn <> old ->
   pn <> (p1, Z.of_nat (length t) + 1) /\ pn <> (p2, Z.of_nat (length t) + 1)) ->
(forall pn, In pn (ablocks B ly4 S4) <-> (In pn (ablocks B ly3 S3) /\ fst pn <> old) \/
   pn = (p1, Z.of_nat (length t) + 1) \/ pn = (p2, Z.of_nat (length t) + 1)) ->
rec_repA B ly4 S4 (rdW W4 mem4) R' O' ->
(forall pn, In pn O' <-> (In pn O2 /\ fst pn <> old) \/ pn = (p1, Z.of_nat (length t) + 1)) ->
astr_atR (rdW W4 mem4) p2 t -> getr regs4 10 = w64 p2 ->
sup_instance_info_m R id = (R', t) ->
blocks_bytes S4 <= blocks_bytes S + LIVE_SUP_INSTANCE_INFO R id ->
mo_le MT S S4 (XM_SUP_INSTANCE_INFO MT R id) ->
exists (R'0 : rstate) (t0 : list byte) (q : Z) (O'0 : list (Z * Z)),
 sup_instance_info_m R id = (R'0, t0) /\
 getr regs4 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly4 S4 (rdW W4 mem4) R'0 O'0 /\
 (forall pn, In pn O'0 -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t0) + 1) (ablocks B ly4 S4) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t0) + 1)) /\ ~ In q (map fst O'0) /\
 astr_atR (rdW W4 mem4) q t0 /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly4 S4) /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t0) + 1)) /\
 (forall pn, In pn (ablocks B ly4 S4) ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O'0 \/ pn = (q, Z.of_nat (length t0) + 1)) /\
 blocks_bytes S4 <= blocks_bytes S + LIVE_SUP_INSTANCE_INFO R id /\
 mo_le MT S S4 (XM_SUP_INSTANCE_INFO MT R id).
Proof.
intros ly S R id O lyc Sc O1 ly2 S2 ly3 S3 W3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 x p p1 p2 old O2 O' R' t
  Hblk Hp2 HF Hp3 HAR3 HAR4 HO2 HO2in Hold Hq Hp12 Hn12 H4 Hrep HO' Hstr Hreg Hm Hbb Hmo.
destruct Hblk as (B1 & B2 & B3 & B4 & _).
assert (Hc3 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly3 S3)).
{ intros pn H. apply (Permutation_in pn (Permutation_sym Hp3)). apply (Permutation_in pn (Permutation_sym Hp2)).
  right. exact H. }
assert (H3c : forall pn, In pn (ablocks B ly3 S3) -> pn = (p, Z.of_nat (length x) + 1) \/ In pn (ablocks B lyc Sc)).
{ intros pn H. apply (Permutation_in pn Hp3) in H. apply (Permutation_in pn Hp2) in H.
  destruct H as [<- | H]; [left; reflexivity | right; exact H]. }
assert (Hpc : ~ In (p, Z.of_nat (length x) + 1) (ablocks B lyc Sc)).
{ intro H. rewrite Forall_forall in HF. specialize (HF _ H). cbn [fst snd] in HF. unfold iv_apart in HF. lia. }
assert (HO'4 : forall pn, In pn O' -> In pn (ablocks B ly4 S4))
  by exact (sii_rec_repA_in B ly4 S4 (rdW W4 mem4) R' O' Hrep).
assert (Hq4 : In (p2, Z.of_nat (length t) + 1) (ablocks B ly4 S4))
  by (apply (proj2 (H4 _)); right; right; reflexivity).
assert (Hnold : forall b m, In (b, m) (ablocks B ly3 S3) -> ~ In (b, m) O2 -> b <> old).
{ intros b m H3 HnO2 E. subst b. destruct Hold as [E | (m' & Hm')].
  - pose proof (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 old m HAR3 H3) as (_ & H4096 & _). lia.
  - pose proof (siq_same_start ly3 S3 W3 mem3 md3 old m m' HAR3 H3 (HO2in _ Hm')) as E. subst m'.
    exact (HnO2 Hm'). }
assert (HkeptO2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly3 S3) /\ ~ In pn O2).
{ intros pn H1 H2.
  destruct (in_dec sii_pair_dec pn (ablocks B lyc Sc)) as [Hc | Hc]; [|exfalso; exact (H2 (B2 _ H1 Hc))].
  split; [exact (Hc3 _ Hc)|]. intros H. apply (proj1 (HO2 pn)) in H. destruct H as [H | ->].
  - exact (H2 (B3 _ H)).
  - exact (Hpc Hc). }
exists R', t, p2, O'.
split; [exact Hm|]. split; [exact Hreg|]. split; [exact Hq|]. split; [exact Hrep|].
split.
{ intros pn H. apply (proj1 (HO' pn)) in H. destruct H as [(H & _) | ->].
  - apply (proj1 (HO2 pn)) in H. destruct H as [H | ->].
    + left. exact (B3 pn H).
    + destruct (in_dec sii_pair_dec (p, Z.of_nat (length x) + 1) (ablocks B ly S)) as [H1 | H1]; [left | right; exact H1].
      exact (B2 _ H1 Hpc).
  - destruct (in_dec sii_pair_dec (p1, Z.of_nat (length t) + 1) (ablocks B ly S)) as [H1 | H1]; [left | right; exact H1].
    destruct (in_dec sii_pair_dec (p1, Z.of_nat (length t) + 1) O) as [HO | HO]; [exact HO|].
    exfalso. destruct (HkeptO2 _ H1 HO) as [H3 HnO2].
    exact (proj1 (Hn12 _ H3 (Hnold _ _ H3 HnO2)) eq_refl). }
split; [exact Hq4|].
split.
{ intros pn H1 H2 E. destruct (HkeptO2 pn H1 H2) as [H3 HnO2]. destruct pn as [b m].
  exact (proj2 (Hn12 _ H3 (Hnold _ _ H3 HnO2)) E). }
split.
{ intros Hin. apply in_map_iff in Hin as ([b m] & Eb & Hbm). cbn [fst] in Eb. subst b.
  assert (Em : m = Z.of_nat (length t) + 1) by exact (siq_same_start ly4 S4 W4 mem4 md4 p2 m _ HAR4 (HO'4 _ Hbm) Hq4).
  subst m. apply (proj1 (HO' _)) in Hbm. destruct Hbm as [(Hb & Hbo) | Hb].
  - exact (proj2 (Hn12 _ (HO2in _ Hb) Hbo) eq_refl).
  - apply Hp12. congruence. }
split; [exact Hstr|].
split.
{ intros [b m] H1 H2. destruct (HkeptO2 _ H1 H2) as [H3 HnO2].
  pose proof (Hnold _ _ H3 HnO2) as Hb.
  assert (H4b : In (b, m) (ablocks B ly4 S4)) by (apply (proj2 (H4 _)); left; split; [exact H3 | exact Hb]).
  split; [exact H4b|].
  apply (siq_apart ly4 S4 W4 mem4 md4 b m p2 _ HAR4 H4b Hq4).
  exact (proj2 (Hn12 _ H3 Hb)). }
split.
{ intros pn H. apply (proj1 (H4 pn)) in H. destruct H as [(H & Hold') | [-> | ->]].
  - destruct (H3c pn H) as [-> | Hc].
    + right; left. apply (proj2 (HO' _)). left. split; [apply (proj2 (HO2 _)); right; reflexivity | exact Hold'].
    + destruct (in_dec sii_pair_dec pn O) as [HO | HO].
      * right; left. apply (proj2 (HO' _)). left. split; [|exact Hold'].
        apply (proj2 (HO2 _)). left. destruct (in_dec sii_pair_dec pn O1) as [HO1 | HO1]; [exact HO1|].
        exfalso. exact (B4 pn HO HO1 Hc).
      * left. split; [exact (B1 pn Hc) | exact HO].
  - right; left. apply (proj2 (HO' _)). right. reflexivity.
  - right; right. reflexivity. }
split; [exact Hbb | exact Hmo].
Qed.

(* the read-only bytes keep the image's values along the walk: none is in the statement's footprint *)
Lemma sii_rodata_at : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k R O,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
  ly S W mem md own ly' S' W' mem' md' k ->
rec_repA B ly S (rdW W mem) R O ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k R O HAR HJ HREP HR.
apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B STK sp0 _
  ly S W mem md own ly' S' W' mem' md' k HJ);
[|exact HR].
intros a Hro HF. destruct (cmd_ro_prog_apart a Hro) as [Himg Hnpg].
apply inFP_cons in HF as [Ha | HF].
{ apply Hnpg. apply sii_grec_in. unfold REC_SIZE in *. lia. }
apply inFP_cons in HF as [Ha | HF].
{ apply Hnpg. apply sii_spill_in. unfold SC_SIZE in *. lia. }
destruct (inFP_ablocks_fp_inv O a HF) as (p & n & Hpn & Hr).
pose proof (sii_rec_repA_in B ly S _ R O HREP (p, n) Hpn) as Hin.
destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [_ Hni].
{ left. exists p, n. split; [exact Hin | exact Hr]. }
exact (Hni Himg).
Qed.

(* ---- the symbolic entry state -------------------------------------------------------------------------- *)
Lemma sii_entry : forall (fx0 : YK11.FPState) W ly S regs mem md ch,
afn_pre SEGS B SUP_INSTANCE_INFO_STK ly S W regs mem md ch ->
@st_ok_pi SEGS VAL fx0 (Eimg (Ereg regs (sii_extra (as_uar_cell B) (32 * ((spZ regs - 96) / 32))))) sii_ss0
(restrict (w_H W) (@mkst fx0 regs (Z_to_bv 64 (BASE + AF_sup_instance_info)) mem (seg_rom SEGS))).
Proof.
intros fx0 W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SUP_INSTANCE_INFO_STK = 16704) by (vm_compute; reflexivity).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1.
pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
rewrite restrict_mkst_fx.
set (sp1 := 32 * ((spZ regs - 96) / 32)).
destruct (sii_sp1_facts (spZ regs) ltac:(lia) Hal16) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
set (E := Eimg (Ereg regs (sii_extra (as_uar_cell B) sp1))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (U34 : base_val E (Some 34%nat) = sp1) by (apply VB; [exact E34 | lia]).
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact E242 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold sii_ss0, sii_regions0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FS. lia.
  + rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FS. lia.
  + rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FS. lia.
  + rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [rewrite sii_denot_off0; exact E253 | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [rewrite sii_denot_off0; exact E32 | unfold SB; lia | lia |].
    rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
    [rewrite sii_denot_off0; exact E33 | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U34, U0, U1, U12, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct Hsp1 as [Hs1 | Hs1]; repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [sii_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E34, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  rewrite Hal16, Hsp1a. unfold SB. repeat split; lia.
Qed.

(* the walk at any entry FP state fx: the snprintf call returns at some fx1 and answer at some fx2; the code after
   each runs at the FP state it returned *)
Theorem tsup_instance_info_holds_any : forall fx : YK11.FPState, @tsup_instance_info_spec fx rc SK PI B MT.
Proof.
intros fx. unfold tsup_instance_info_spec.
intros ly S W regs mem md ch id R O HPRE HFRM HROD HRO H10 Hid HREP Hfr7 Hev Hlive MOK.
pose (RUNP := @SRr_run_pi_AJ fx rc SK cmd_listing PL_cmd PI B LAWS).
pose (RUNC := @SRr_run_pi_AJ_call fx rc SK cmd_listing PL_cmd PI B LAWS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
set (FP := (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
pose proof (sii_entry fx W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_INSTANCE_INFO_STK FP ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SUP_INSTANCE_INFO_STK = 16704) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
set (sp1 := 32 * ((spZ regs - 96) / 32)) in HS.
destruct (sii_sp1_facts (spZ regs) ltac:(lia) Hal16) as (Hsp1 & Hsp1a & Hsp1b).
fold sp1 in Hsp1, Hsp1a, Hsp1b.
assert (Hsp1r : spZ regs - 112 <= sp1 <= spZ regs - 96) by (destruct Hsp1 as [-> | ->]; lia). clear Hsp1.
remember (Eimg (Ereg regs (sii_extra (as_uar_cell B) sp1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_sup_instance_info)) with (Z_to_bv 64 (BASE + AF_sup_instance_info)).
(* run 1: the prologue, the realignment, the shadow base and the use-after-return flag (1, the record's constant
   cell), then the call of __asan_stack_malloc_0 *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold sii_ss0, sii_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0);
    [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0);
    [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs);
    [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
  repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
preg HS (2%bv : bv 5) R2. preg HS (9%bv : bv 5) R9. preg HS (1%bv : bv 5) R1.
preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
rewrite (snt_denot_and_m32 E 2 (spZ regs) (-96) Esp ltac:(lia) ltac:(lia) ltac:(lia)) in R2.
replace (32 * ((spZ regs + -96) / 32)) with sp1 in R2 by (unfold sp1; do 3 f_equal; lia).
rewrite sii_denot_add0, (snt_denot_and_m32 E 2 (spZ regs) (-96) Esp ltac:(lia) ltac:(lia) ltac:(lia)) in R9.
replace (32 * ((spZ regs + -96) / 32)) with sp1 in R9 by (unfold sp1; do 3 f_equal; lia).
cbn [sv_denot] in R1. rewrite (img_env_codeptr E HEI 22180) in R1.
rewrite sii_denot_off0, (EE 3%nat 3%bv eq_refl) in R3. rewrite sii_denot_off0, (EE 4%nat 4%bv eq_refl) in R4.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp SEGS E ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl
    ltac:(rewrite sii_denot_off0, E34; cbn [ms_regs restrict]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp SEGS E ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl
    ltac:(rewrite sii_denot_off0, E34; cbn [ms_regs restrict]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
pose proof (palf_sm B TLF 0 ltac:(cbn; tauto)) as SM0.
change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in SM0.
rewrite SM0.
assert (Qsp : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML sii_SMP 0 (ASTACK_MALLOC0 fx) ltac:(lia)
    W (ms_regs ms1) (ms_mem ms1) SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md [] ly S _ 0
    (sp1 - spZ regs) _ HJ);
  [ exact Qsp | exact Hsp1b | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
  | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | pose proof (count_cid_le_length 0 (frames S)); change (fs_frames 0) with 16384; lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin &
  Hnev2 & Hbb2 & Hz & Hflag & HK & HJS & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & _ & HK3 & _ & _ & _).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply sii_region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
  - eapply sii_region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
  - eapply sii_region_kept_hi; [exact U34 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 R9 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HAE1 : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E1)
  by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
destruct (sii_FFL _ _ _ _ _ 0 fpos HAR2 Hfin)
  as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
replace (F + 64 - 8) with (F + 56) in Hflag by lia.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HFin : in_app F 64) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS
    ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HAE2 : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E2)
  by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n)
  by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1040 : ew E2 1040 = Z_to_bv 64 FL)
  by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2028 : ew E2 1028 = Z_to_bv 64 F) by (rewrite HE2, ew_havoc_old by lia; exact E1028).
clear HE2.
assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (V2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (V34 : bv_unsigned (ew E2 34) = sp1) by (rewrite OLD2 by lia; exact U34).
assert (V1028 : bv_unsigned (ew E2 1028) = F) by (rewrite E2028; apply unsigned_lit_small; lia).
assert (V1040 : bv_unsigned (ew E2 1040) = FL) by (rewrite E1040; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HF8b : F / 8 <= 17592185978880) by (apply Z.div_le_upper_bound; lia).
assert (V1041 : bv_unsigned (ew E2 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 1028 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite V1028; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_alias Ev _ msv sii_shx (SOff 1041 0) HS
    (shadow_decl_ok Ev 1028 32 1041 F SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv sii_fr_hdr HS eq_refl
    ltac:(unfold region_ok, sii_fr_hdr;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
    ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sii_fr_hdr;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv sii_fr_flg HS eq_refl
    ltac:(unfold region_ok, sii_fr_flg;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite V1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Ev _ F 56 8 (SOff 1040 0) FL);
      [rewrite sii_denot_off0; exact E1040 | lia | lia |];
      exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
    ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sii_fr_flg, sii_fr_hdr;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv sii_fr_shd HS eq_refl
    ltac:(unfold region_ok, sii_fr_shd;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite V1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS);
      replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres o ltac:(lia))))
    ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sii_fr_shd, sii_fr_flg, sii_fr_hdr;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite V1041, V1028, V2, V34; unfold SB;
      pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
      repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* run 2: the side-stack frame's header and shadow (f1 f1 f1 f1 | f8 f8 | f3 f3), then the call of record(9) *)
paj_run_shc RUNP RUNC HS HJ2.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact V1041 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos;
    split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; rewrite <- SB_SHADOW_OFF;
    change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact V1028 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos;
    split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0);
    [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0);
    [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs);
    [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
(* where the recorder's state and the live blocks lie: none of them in the frame, its shadow, its flag or the
   stack (answer_code's KA block, at class 0's sizes) *)
set (KA := fun a : Z => (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
  (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n)).
assert (KIMG : forall a, KA a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
  (in_img SEGS a /\ 0x10000 <= a < 0x606000 /\ ~ Exists (in_zr a) (as_owned_static B) /\
   ~ (as_errno B <= a < as_errno B + 4))).
{ intros a Ha. destruct Ha as [Ha | [Ha | Ha]]; [right | right | left; exact Ha].
  - destruct (sii_prog_unowned a (sii_grec_in a Ha)) as (Hi & Ho & He).
    split; [exact Hi|]. split; [exact (pa_img_range a Hi) | split; [exact Ho | exact He]].
  - destruct (sii_prog_unowned a (sii_spill_in a Ha)) as (Hi & Ho & He).
    split; [exact Hi|]. split; [exact (pa_img_range a Hi) | split; [exact Ho | exact He]]. }
assert (KLOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\
  ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & Hr & _ & _)].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & _ & _).
    assert (Hpn2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hpn).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hpn2) as (_ & _ & _ & _ & Hpres2 & _).
    pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p n 0 fpos HAR2 Hpn2 Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
    intros ->. exact (proj2 (Hpres2 FL ltac:(lia)) HFLo).
  - split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (HFLimg Hi). }
assert (K01 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & _).
  apply (sii_aview_frame_pt E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
  nwin_tac ltac:(fun H => rewrite ?Usp, ?U34 in H; lia). }
assert (K12 : forall a, KA a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms1) a).
{ pose proof HK as (_ & HK2 & _ & _ & _ & _).
  intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & _ & Ho & He)].
  - replace a with (p + (a - p)) by lia. apply (HK2 p n (a - p) Hpn); [lia | intros []].
  - exact (HK3 a Hi Ho He). }
assert (K23 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _).
  apply (sii_aview_frame_pt E2 _ (w_H W) mem2 (ms_mem ms3) a HFr3); [lia|].
  nwin_tac ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; lia). }
assert (K03 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; rewrite (K23 a Ha), (K12 a Ha), (K01 a Ha); reflexivity).
(* the recorder's state and the budgets at record's entry *)
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sii_rec_repA_in B ly S _ R O HREP).
assert (HREP3 : rec_repA B ly S2 (rdW W (ms_mem ms3)) R O).
{ apply (sii_rec_repA_kept B ly S (rdW W mem) ly S2 (rdW W (ms_mem ms3)) R O HREP).
  - intros pn Hpn. rewrite Eab. exact (HOin pn Hpn).
  - intros a Ha. apply K03. left. exact Ha.
  - intros a Ha. apply K03. right. left. exact Ha.
  - intros p n i Hpn Hi. apply K03. right. right. exists p, n.
    split; [exact (HOin _ Hpn)|]. pose proof (req_size_pos n) as Hq.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOin _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (Hq ltac:(lia)). lia. }
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms3)))
  by exact (sii_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJ2 HREP HROD).
assert (HFPlow : forall a, inFP FP a -> a < alloc_ceiling)
  by exact (sii_FP_low B ly S W mem md _ R O HAR HREP).
pose proof (proj1 HJ2) as HAR3.
(* the registers at record's entry *)
pmkst HS.
preg HS (1%bv : bv 5) Q1. preg HS (2%bv : bv 5) Q2. preg HS (3%bv : bv 5) Q3. preg HS (4%bv : bv 5) Q4.
preg HS (8%bv : bv 5) Q8. preg HS (10%bv : bv 5) Q10.
cbn [sv_denot] in Q1. rewrite (img_env_codeptr E2 HEI2 22332) in Q1.
rewrite sii_denot_off0, OLD2, E34 in Q2 by lia.
rewrite sii_denot_off0, OLD2, (EE 3%nat 3%bv eq_refl) in Q3 by lia.
rewrite sii_denot_off0, OLD2, (EE 4%nat 4%bv eq_refl) in Q4 by lia.
rewrite sii_denot_off0, OLD2, Esp in Q8 by lia.
cbn [sv_denot] in Q10.
assert (GR2 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite Q2, unsigned_lit_small by lia; lia).
assert (GR3 : getr (ms_regs ms3) 3 = w64 (as_gp B)) by (rewrite Q3; exact Hgp).
assert (GR4 : getr (ms_regs ms3) 4 = w64 (as_tp B)) by (rewrite Q4; exact Htp).
assert (GR1r : YK0s.ret_ok (getr (ms_regs ms3) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GR1a : 4096 <= bv_unsigned (getr (ms_regs ms3) 1))
  by (rewrite Q1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (GR8 : s0Z (ms_regs ms3) = spZ regs) by (unfold s0Z; rewrite Q8, unsigned_lit_small by lia; reflexivity).
assert (GR10 : getr (ms_regs ms3) 10 = w64 SII_FN) by (rewrite Q10; reflexivity).
assert (HRS : RECORD_STK = 16560) by (vm_compute; reflexivity).
(* the frame chain for s0 = the entry sp: ra and the caller's s0 saved by the prologue (region 4 of the symbolic
   state: sp0 - 80 .. sp0), on top of afn_pre's chain *)
assert (FW8 : rdword (rdW W (ms_mem ms3)) (spZ regs - 8) = Some (raZ regs)).
{ pose proof (st_ok_region_nth E2 _ _ 4 _ HS eq_refl) as HR1. cbn [ms_mem restrict mkst] in HR1.
  apply (rdword_of_val_mem SEGS); [|unfold raZ; exact (bv_unsigned_in_range 64 (getr regs 1))].
  replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (field_of_region E2 _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR1 V2 _ _ _ _);
  [cbn [In]; tauto | rewrite sii_denot_off0, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ;
    symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; exact (bv_unsigned_in_range 64 (getr regs 1)) | lia]. }
assert (FW16 : rdword (rdW W (ms_mem ms3)) (spZ regs - 16) = Some (s0Z regs)).
{ pose proof (st_ok_region_nth E2 _ _ 4 _ HS eq_refl) as HR1. cbn [ms_mem restrict mkst] in HR1.
  apply (rdword_of_val_mem SEGS); [|unfold s0Z; exact (bv_unsigned_in_range 64 (getr regs 8))].
  replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (field_of_region E2 _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR1 V2 _ _ _ _);
  [cbn [In]; tauto | rewrite sii_denot_off0, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z;
    symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; exact (bv_unsigned_in_range 64 (getr regs 8)) | lia]. }
destruct (sii_chain_at B SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md _ ly S2 W (ms_mem ms3) _ _ (s0Z regs) ch
  (raZ regs) (spZ regs + (sp1 - spZ regs)) HJ2 HFPlow Hch FW8 FW16 Hra4 ltac:(lia)) as (ch1 & Hch1).
assert (Hch1' : achain ly (rdW W (ms_mem ms3)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms3)) ch1)
  by (rewrite GR8; exact Hch1).
pose proof HREP3 as (Q0 & HQ0 & HOQ0).
pose proof HQ0 as (_ & _ & _ & (HC1 & _) & _).
(* the meter's parts are non-negative, the slot's bounds, and the bytes record's footprint may hold *)
assert (XA0 : 0 <= XM_ARG_S MT (Some (dec id)))
  by (unfold XM_ARG_S, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (HSLOT : (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/
  rec_slot R = A_REC_SPILL).
{ unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge]; [left | right; reflexivity].
  assert (Z.of_nat (length (r_calls R)) <= 15) by lia.
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia. }
(* the record's footprint lies among the recorder's bytes KA: g_rec.ncalls, the slot (in g_rec or record.spill),
   and in the spill arm the recorder's blocks *)
assert (HFPR : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> KA a).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
  { left. unfold OFF_NCALLS, REC_SIZE in *. lia. }
  apply inFP_cons in Ha as [Ha | Ha].
  { destruct HSLOT as [Hs | Hs]; [left; unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    right; left. rewrite Hs in Ha. unfold SC_SIZE in *. lia. }
  destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
  destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
  right; right. exists b, n. split; [exact (HOin _ Hbn) | exact Hba]. }
(* ---- the call of record(9) (0x8bc68) ---- *)
rewrite (rca_sig_record (PI := PI) cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms3) (ms_mem ms3) _ SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly S2 _ 0 RECORD_STK _ (EV_RECORD R) (sp1 - spZ regs) (getr (ms_regs ms3) 1) ch1 _ HJ2 GR2 Hsp1b
    ltac:(lia) ltac:(rewrite HRS; lia) ltac:(rewrite HRS, FS; lia) GR3 GR4 eq_refl GR1r GR1a Hch1').
  - intros HPRE1. pose proof (TRECORD fx ly S2 W (ms_regs ms3) (ms_mem ms3) _ ch1 SII_FN R O HPRE1) as T.
    unfold apost_base in T. apply T.
    + exact HROD3.
    + exact GR10.
    + unfold SII_FN, REC_INSTANCE_INFO, REC_FN_COUNT. lia.
    + exact HREP3.
    + rewrite Hnev2. pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev0 & _).
      unfold EV_SUP_INSTANCE_INFO in Hev. unfold EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in Hev. lia.
    + rewrite ES2. apply (mo_ok_set_fs MT MTLF). apply (mo_ok_le MT MTL S _ _ MOK).
      unfold XM_SUP_INSTANCE_INFO. pose proof XA0. pose proof (XN0 (snd (sup_instance_info_m R id))). lia.
  - intros a Ha.
    assert (AWRG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> inFP FP x /\
      Exists (in_zr x) (as_prog_static B) /\ in_img SEGS x).
    { intros x Hx. split; [unfold FP; apply inFP_cons; left; unfold REC_SIZE in *; lia|].
      split; [rewrite sii_ts_prog; exact (sii_grec_in x Hx) | exact (cmd_prog_img x (sii_grec_in x Hx))]. }
    assert (AWRSP : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> inFP FP x /\
      Exists (in_zr x) (as_prog_static B) /\ in_img SEGS x).
    { intros x Hx. split;
        [unfold FP; apply inFP_cons; right; apply inFP_cons; left; unfold SC_SIZE in *; lia|].
      split; [rewrite sii_ts_prog; exact (sii_spill_in x Hx) | exact (cmd_prog_img x (sii_spill_in x Hx))]. }
    apply inFP_cons in Ha as [Ha | Ha].
    { right; right; right; right; left. apply AWRG. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { right; right; right; right; left. destruct HSLOT as [Hs | Hs].
      - apply AWRG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      - apply AWRSP. rewrite Hs in Ha. unfold CALL_SIZE, SC_SIZE in *. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
    right; left. split.
    { unfold FP. apply inFP_cons. right. apply inFP_cons. right.
      replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b n (a - b)); [exact Hbn | lia]. }
    exists b, n. split; [rewrite Eab; exact (HOin _ Hbn) | exact Hba].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    assert (Hlo : a < alloc_ceiling).
    { apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
      apply inFP_cons in Ha as [Ha | Ha].
      { destruct HSLOT as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
        rewrite Hs in Ha. unfold A_REC_SPILL in Ha. lia. }
      destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
      destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR (HOin _ Hbn)) as (_ & _ & Hbc & _). lia. }
    rewrite FS in Hw. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HK4).
destruct HK4 as (Fr & O1 & RS10 & HPermF & HFlen & HFO & HREP4 & HO1 & HBB4 & MLE4).
pose proof (proj1 HJ4) as HAR4.
rewrite Q1.
(* the frame after record: same address in ly4 (al_layout), still the walk's own, present *)
pose proof HJc4 as (_ & Hly4 & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR3 Hly4) as (Eab4 & Efa4 & _).
assert (EFA4 : frame_addr ly4 0 fpos = F) by (rewrite Efa4; reflexivity).
assert (Hfin4 : In (0, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
rewrite EFA4 in HFpres4, HFSpres4.
change (fs_frame_bytes 0) with 64 in HFpres4, HFSpres4. change (64 / 8) with 8 in HFSpres4.
jafter_call_keep_hi HS 1058%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0;1;2;3;4;5]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
(* the six regions in the state's order: the frame's shadow, its flag word, its header, the two pieces of the own
   stack frame, the realigned stack word (an eapply that does not fit its region costs minutes to fail, so no
   `first`) *)
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1041
      (SB + F / 8) _ _ _ _ _ 0 fpos HJc4 V1041 Hfin);
    [ unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (KLOC a (HFPR a HFa)) as (_ & _ & HnS & _); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8)))
        by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres4 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1028 F
      _ _ _ _ _ 0 fpos HJc4 V1028 Hfin);
    [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC a (HFPR a HFa)) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1028 F
      _ _ _ _ _ 0 fpos HJc4 V1028 Hfin);
    [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC a (HFPR a HFa)) as (_ & HnF & _); lia
    | intros a Ha; exact (proj1 (HFpres4 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc4 HJ4 V2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPR a HFa)); lia].
  - eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc4 HJ4 V2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPR a HFa)); lia].
  - eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _
      HJc4 HJ4 V34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPR a HFa)); lia]. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
clear Q1 Q2 Q3 Q4 Q8 Q10.
remember (havoc E2 1058 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HAE3 : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E3)
  by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (OLD3 : forall n, (n < 1058)%nat -> ew E3 n = ew E2 n)
  by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (E1062 : ew E3 1062 = w64 (rec_slot R)).
{ rewrite HE3. change 1062%nat with (1058 + 4)%nat. rewrite (ew_havoc_new E2 1058 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact RS10. }
clear HE3.
assert (X2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact V2).
assert (X34 : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3 by lia; exact V34).
assert (X1028 : bv_unsigned (ew E3 1028) = F) by (rewrite OLD3 by lia; exact V1028).
assert (X1040 : bv_unsigned (ew E3 1040) = FL) by (rewrite OLD3 by lia; exact V1040).
assert (X1041 : bv_unsigned (ew E3 1041) = SB + F / 8) by (rewrite OLD3 by lia; exact V1041).
(* run 3 (0x8bc6c .. 0x8bc88): s5 := the slot, b's shadow 00 00, the format "%d", n = 16, a0 = b, a3 = id *)
paj_run_shc RUNP RUNC HS HJ4.
{ sii_awr6 fpos sp1 regs FS X1041 X1028 X2 X34 EFA4. }
rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
pmkst HS.
preg HS (10%bv : bv 5) R10. preg HS (11%bv : bv 5) R11. preg HS (12%bv : bv 5) R12. preg HS (13%bv : bv 5) R13.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
cbn [sv_denot] in R10, R11, R1. rewrite X1028 in R10. rewrite (img_env_codeptr E3 HEI3 22368) in R1.
rewrite sii_denot_off0, (img_env_atomP E3 292 HEI3 ltac:(unfold A_TEXT, A_LIM; lia)) in R12.
change (VAL 292) with (VAL SII_FOBJ) in R12. rewrite (sii_vobj_fmt VOBJS) in R12.
rewrite sii_denot_off0, OLD3, OLD2, (EE 10%nat 10%bv eq_refl), H10 in R13 by lia.
rewrite sii_denot_off0, OLD3, OLD2, E34 in R2 by lia.
rewrite sii_denot_off0, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite sii_denot_off0, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pose proof (proj1 HJ4) as HAR5.
assert (Qsp5 : spZ (ms_regs ms5) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms5)))
  by exact (sii_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJ4 HREP HROD).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HAR5 HROD5) as HRO5.
(* b's two shadow bytes are 0 after run 3's stores (region 0: the frame's shadow) *)
assert (ZS5 : forall j, 4 <= j < 6 -> rdW W4 (ms_mem ms5) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E3 _ _ 0 _ HS eq_refl) as HR0.
  cbn [ms_mem restrict mkst] in HR0.
  assert (Hj4 : j = 4 \/ j = 5) by lia.
  destruct Hj4 as [-> | ->];
  (apply (aview_of_val_mem1 SEGS); [|lia]);
  (lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
     refine (field_of_region E3 _ 1041 (SB + F / 8) _ _ _ _ _ od 1%N (SLit 0) 0 HR0 X1041 _ _ _ _) end;
   [cbn [In]; tauto | reflexivity | lia | lia]). }
(* the call of the snprintf wrapper (0x8bc8c): snprintf(b = F + 32, 16, "%d", id) at the entry's FP state, through
   the shared contract (asnprintf_realizes = RtPFCmd.asnprintf_sh at FR_cmd, window CMD_SNP_K = 2 * ESTACK); the
   text T = pf_dec id is 1 .. 11 bytes, so all of it and its terminator are written (copied from
   a working branch 07b554c4785 lib/B/Prog/answer_code.v:943-1070) *)
set (T := PF.pf_dec id).
assert (HTL : (1 <= length T <= 11)%nat)
  by (unfold T; rewrite (sii_dec_len id Hid); exact (dec_length id Hid)).
assert (HSL : sn_len (16 - 1) T = Z.of_nat (length T) + 1).
{ unfold sn_len, sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat. rewrite length_app, firstn_all2 by lia.
  cbn [length]. lia. }
assert (HSB : sn_bytes (16 - 1) T = T ++ [0]).
{ unfold sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia. reflexivity. }
assert (HDOFF : F + 32 + (Z.of_nat (length T) + 1) <= 0x10000 \/ 0x606000 <= F + 32) by (clear - HFoff HTL; lia).
assert (HDSP : F + 32 + (Z.of_nat (length T) + 1) <= spZ (ms_regs ms5) - CMD_SNP_K).
{ rewrite Qsp5. unfold CMD_SNP_K. rewrite Hes. rewrite FS in Hslo. clear - HFceil Hceil Hslo Hsp1r HTL. lia. }
assert (HSPK : 0x606000 <= spZ (ms_regs ms5) - CMD_SNP_K).
{ rewrite Qsp5. unfold CMD_SNP_K. rewrite Hes. rewrite FS in Hslo. pose proof alloc_ceiling_value as (Hacr & _).
  clear - Hceil Hslo Hsp1r Hacr. lia. }
destruct (cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG _ _ _ _ _ HAR5) as (_ & (HGW & cval & HGV) & _).
pose proof (ecall_pre_stk_at SEGS B CMD_SNP_K SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md [(0, fpos)]
  ly4 S4 W4 (ms_mem ms5) _ _ (ms_regs ms5) (sp1 - spZ regs) HJ4 Qsp5 Hsp1b ltac:(lia)
  ltac:(unfold CMD_SNP_K; rewrite Hes; lia) ltac:(unfold CMD_SNP_K; rewrite Hes, FS; lia)
  ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
  ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)) as (HECP & HSLO5 & HWIN5).
assert (E13 : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
pose proof (sii_fmt_at_lit _ HRO5) as HLIT5.
destruct (cmd_aread_ok_chk SEGS B LAWS HB _ _ _ _ _ SII_FMT 3 HAR5 sii_fmt_addr_b sii_fmt_hull_b)
  as (HFRA & HFHV).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR5 Hfin4) as (_ & _ & HFpres5 & _).
rewrite EFA4 in HFpres5. change (fs_frame_bytes 0) with 64 in HFpres5.
eapply SRr_bind.
{ eapply (ASNPRINTF fx ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _ (F + 32) 16 SII_FMT []
    (map (argZ (ms_regs ms5)) [3; 4; 5; 6; 7] ++ []) T cval).
  - exact HECP.
  - exact HSLO5.
  - exact HWIN5.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact (CmdRecImg.cmd_consts_view_snp (SK := SK) SEGS B LAWS HB IMG RLO RHI W4 (ms_mem ms5) HROD5).
  - apply Forall_forall. intros r Hr. destruct (sii_snp_rng r Hr) as (A1 & A2 & A3). clear - A1 A2 A3. lia.
  - apply Forall_forall. intros r Hr. destruct (sii_snp_rng r Hr) as (A1 & A2 & A3). destruct r as [r1 r2].
    cbn [fst snd] in A1, A2, A3. rewrite HSL.
    apply sii_lo_disj; [clear - A3; lia | clear - A1; lia | clear - A2; lia | clear - A2 HSPK; lia
    | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF].
  - exact HGW.
  - exact HGV.
  - clear - Hes. lia.
  - clear - Hes. lia.
  - clear - Hes. lia.
  - clear - Hes. lia.
  - rewrite HSL. apply sii_lo_disj; [clear - Hes; lia | clear - Hes; lia | clear - Hes; lia | clear - HSPK; lia
    | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF].
  - rewrite HSL. apply sii_lo_disj; [clear - Hes; lia | clear - Hes; lia | clear - Hes; lia | clear - HSPK; lia
    | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF].
  - split; [reflexivity | intros i Hi; cbn [length] in Hi; exfalso; clear - Hi; lia].
  - cbn [length Z.of_nat]. rewrite Qsp5. clear - Hsp1r Hshi H47. lia.
  - cbn [length Z.of_nat]. rewrite HSL. unfold snp_out.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
    [unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia
    | clear - HDSP Hes; unfold CMD_SNP_K in HDSP; rewrite Hes in HDSP; lia].
  - apply (FR_cmd_intro _ _ _ _ _ PAI.AI_FMT PAI.AI_PS [PF.AInt id]).
    + unfold fmt_at. change (Z.of_nat (length PAI.AI_FMT)) with 2.
      split; [unfold SII_FMT; lia|]. split; [exact (sii_fmt_rd _ HLIT5)|].
      split; [rewrite HSL; apply sii_lo_disj; [lia | unfold SII_FMT; lia | unfold SII_FMT; lia
        | unfold SII_FMT; clear - HSPK; lia | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF]|].
      split; [left; unfold kLowMemEnd, SII_FMT; lia|].
      split; [exact HFRA | exact HFHV].
    + exact PAI.ai_parse.
    + cbn [map RtPFCmd.arg_of app]. cbn [pf_args_asan pf_arg_asan]. refine (conj (conj Hid _) I).
      unfold argZ. rewrite E13, R13. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64).
      rewrite <- (Zmod_div_mod (2 ^ 32) (2 ^ 64) id); [reflexivity | lia | lia | exists (2 ^ 32); reflexivity].
    + exact (PAI.ai_text id).
    + unfold PAI.AI_PS. cbn. trivial.
    + (* fr_lit_ok (a working branch 40ec8c3d85c, PASS4-REFIT.md E.0.4): "%d" at 0x21f40 in the image, no %s *)
      vm_compute. reflexivity.
  - clear - Hes. lia.
  - clear - HTL. lia.
  - clear - HF4096. lia.
  - rewrite HSL. pose proof alloc_ceiling_lt as Hlt. clear - HFceil HTL Hlt. lia.
  - rewrite HSL. unfold snp_out. cbn [pairwise].
    split; [apply Forall_cons; [|apply Forall_nil]; unfold zdisjoint; cbn [fst snd]; clear - HDSP; lia
    | split; [apply Forall_nil | exact I]].
  - rewrite HSL. intros a Ha. destruct (HFpres5 a ltac:(clear - Ha HTL; lia)) as [Hp Hno].
    split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite Qsp5, Hes. rewrite FS in Hslo.
    clear - Ha HTL HFceil Hceil Hslo Hsp1r. lia.
  - (* the shared contract's slack word (a Theorem Labs lane 55f29e496f6: GXA's range check reads 8 bytes past the
       destination): b = F + 32 holds at most 12 bytes, so 8 more still lie in the 64-byte frame *)
    rewrite HSL. exact (amem_range_sub_app F 64 (F + 32) (Z.of_nat (length T) + 1 + 8) HFapp HFceil
      ltac:(clear - Hes; lia) ltac:(clear - HTL; lia) ltac:(clear - HTL; lia)).
  - rewrite HSL. intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
    pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
    assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS5.
    assert (F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc;
      apply Z_mod_mult).
    split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia
    | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia].
  - rewrite HSL. apply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 (ms_mem ms5) _ 0 fpos (F + 32) _ HAR5 Hfin4);
    [rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia | lia].
  - rewrite HSL. unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. clear - HDOFF. lia.
  - exact HFRM. }
cbv beta. intros W5 c5 _ (-> & fx1 & regs5 & mem5 & md5 & -> & Hfx5 & Hfrm5 & HAR5' & HP5 & Hsame5 & Ha05 & Hbuf5 &
  Hkeep5 & Hpres5).
rewrite HSL in Hkeep5, Hbuf5. rewrite HSB in Hbuf5.
pose proof HJ4 as (_ & _ & _ & _ & _ & HfrJ4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT4).
assert (HJ5 : ajournal SEGS B SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly4 S4 W4 mem5 md5
  (0 + EV_RECORD R)).
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md [(0, fpos)]
    ly4 S4 W4 (ms_mem ms5) _ _ mem5 md5 (fun a => (F + 32 <= a < F + 64) \/ (sp1 - 3 * ESTACK <= a < sp1)) S4
    [(0, fpos)] HJ4).
  - intros a Ha Hn. apply Hkeep5; [exact Ha | intros H; apply Hn; left; clear - H HTL; lia
    | rewrite Qsp5; intros H; apply Hn; right; unfold CMD_SNP_K in H; rewrite Hes in H |- *; clear - H; lia].
  - exact Hpres5.
  - exact Hsame5.
  - intros a [Ha | Ha]; left.
    + right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
      left. unfold in_zr, frame_rng; cbn [fst snd]. rewrite EFA4. change (fs_frame_bytes 0) with 64. lia.
    + left. rewrite FS, Hes in *. lia.
  - exact HAR5'.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact HfrJ4.
  - exact HQT4. }
assert (RA5 : w64 (raZ (ms_regs ms5)) = Z_to_bv 64 (BASE + 22368))
  by (unfold raZ; rewrite R1; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
unfold cfg_at. rewrite RA5.
jafter_call_keep_hi HS 1074%nat regs5 (mrestrict (w_H W4) mem5) HP5 [0;1;2;3;4;5]%nat HS5.
match type of HS5 with ?tq -> _ => assert (HRK : tq); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_aview E3 (w_H W4) (ms_mem ms5) mem5); [exact X1041 | | exact Hpres5].
    intros a Ha; apply Hkeep5; unfold SB in Ha; [lia | lia | rewrite Qsp5; unfold CMD_SNP_K; lia].
  - eapply (region_kept_aview E3 (w_H W4) (ms_mem ms5) mem5); [exact X1028 | | exact Hpres5].
    intros a Ha; apply Hkeep5; [lia | lia | rewrite Qsp5; unfold CMD_SNP_K; lia].
  - eapply (region_kept_aview E3 (w_H W4) (ms_mem ms5) mem5); [exact X1028 | | exact Hpres5].
    intros a Ha; apply Hkeep5; [lia | lia | rewrite Qsp5; unfold CMD_SNP_K; lia].
  - eapply (region_kept_aview E3 (w_H W4) (ms_mem ms5) mem5); [exact X2 | | exact Hpres5].
    intros a Ha; apply Hkeep5; [lia | lia | rewrite Qsp5; unfold CMD_SNP_K; lia].
  - eapply (region_kept_aview E3 (w_H W4) (ms_mem ms5) mem5); [exact X2 | | exact Hpres5].
    intros a Ha; apply Hkeep5; [lia | lia | rewrite Qsp5; unfold CMD_SNP_K; lia].
  - eapply (region_kept_aview E3 (w_H W4) (ms_mem ms5) mem5); [exact X34 | | exact Hpres5].
    intros a Ha; apply Hkeep5; [lia | lia | rewrite Qsp5; unfold CMD_SNP_K; lia]. }
rewrite <- restrict_mkst_fx in HS5. clear HS. rename HS5 into HS.
(* the recorder's bytes from record's return to snprintf's: run 3 writes the frame's shadow only, snprintf the
   destination b and its stack window *)
pose proof alloc_ceiling_lt as Hacl.
assert (K45 : forall a, KA a -> rdW W4 (ms_mem ms5) a = rdW W4 mem4 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _).
  apply (sii_aview_frame_pt E3 _ (w_H W4) mem4 (ms_mem ms5) a HFr5); [lia|].
  nwin_tac ltac:(fun H => rewrite ?X2, ?X34, ?X1028, ?X1041 in H; lia). }
assert (K4m5 : forall a, KA a -> rdW W4 mem5 a = rdW W4 mem4 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & _). rewrite <- (K45 a Ha).
  apply Hkeep5; [lia | lia | rewrite Qsp5; unfold CMD_SNP_K; lia]. }
(* the text snprintf left in b: dec id and its terminator *)
assert (HBUF5 : abytes_at SEGS W4 mem5 (F + 32) (dec id ++ [Z_to_bv 8 0])).
{ rewrite <- (PAI.ai_pf_dec id Hid). fold T. intros i Hi. unfold PF.pf_bytes in Hi |- *.
  rewrite length_app, length_map in Hi. cbn [length] in Hi.
  assert (Hx : aview SEGS (w_H W4) mem5 (F + 32 + Z.of_nat i) = Some (nth i (T ++ [0]) 0)).
  { rewrite (Hbuf5 (Z.of_nat i) ltac:(lia)), Nat2Z.id. reflexivity. }
  rewrite Hx. f_equal.
  change [Z_to_bv 8 0] with (map (Z_to_bv 8) [0]). rewrite <- map_app, map_nth.
  pose proof (sii_aview_rng _ _ _ _ _ Hx) as Rx.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
(* the code after the snprintf call runs at the FP state fx1 the call returned: the symbolic state is read at fx1,
   the goal's post is apost_baseF at fx1 (srr_apost_baseF_lift with the call's two FP clauses), and fx leaves the
   context, so every implicit FP state below is fx1 *)
pose proof (st_ok_pi_restrict_xfx fx fx1 SEGS VAL _ _ _ _ _ _ _ HS) as HS1. clear HS. rename HS1 into HS.
eapply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact (fxrel_of_frm0 fx fx1 Hfx5 Hfrm5)|].
clear RUNP RUNC Hfx5 HFRM. rename Hfrm5 into HFRM1.
repeat match goal with H : context [fx] |- _ => clear H end.
clear fx.
pose (RUNP := @SRr_run_pi_AJ fx1 rc SK cmd_listing PL_cmd PI B LAWS).
pose (RUNC := @SRr_run_pi_AJ_call fx1 rc SK cmd_listing PL_cmd PI B LAWS).
remember (havoc E3 1074 (map (getr regs5) CLOB)) as E4 eqn:HE4 in HS.
assert (HAE4 : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E4)
  by (rewrite HE4; apply env_agree_havoc_ge; [lia | exact HAE3]).
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (OLD4 : forall n, (n < 1074)%nat -> ew E4 n = ew E3 n)
  by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
clear HE4.
assert (Y2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact X2).
assert (Y34 : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact X34).
assert (Y1028 : bv_unsigned (ew E4 1028) = F) by (rewrite OLD4 by lia; exact X1028).
assert (Y1040 : bv_unsigned (ew E4 1040) = FL) by (rewrite OLD4 by lia; exact X1040).
assert (Y1041 : bv_unsigned (ew E4 1041) = SB + F / 8) by (rewrite OLD4 by lia; exact X1041).
(* run 4 (0x8bc90 .. 0x8bc94): a0 = the slot, a1 = b *)
paj_run_shc RUNP RUNC HS HJ5.
{ sii_awr6 fpos sp1 regs FS Y1041 Y1028 Y2 Y34 EFA4. }
rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
pmkst HS.
preg HS (10%bv : bv 5) P10. preg HS (11%bv : bv 5) P11. preg HS (1%bv : bv 5) P1. preg HS (2%bv : bv 5) P2.
preg HS (3%bv : bv 5) P3. preg HS (4%bv : bv 5) P4. preg HS (8%bv : bv 5) P8.
rewrite sii_denot_off0, OLD4, E1062 in P10 by lia.
cbn [sv_denot] in P11, P1. rewrite Y1028 in P11. rewrite (img_env_codeptr E4 HEI4 22380) in P1.
rewrite sii_denot_off0, OLD4, OLD3, OLD2, E34 in P2 by lia.
rewrite sii_denot_off0, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in P3 by lia.
rewrite sii_denot_off0, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in P4 by lia.
rewrite sii_denot_off0, OLD4, OLD3, OLD2, Esp in P8 by lia.
pose proof (proj1 HJ5) as HAR6.
assert (Qsp6 : spZ (ms_regs ms6) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite P2, unsigned_lit_small by lia; lia).
assert (GA3 : getr (ms_regs ms6) 3 = w64 (as_gp B)) by (rewrite P3; exact Hgp).
assert (GA4 : getr (ms_regs ms6) 4 = w64 (as_tp B)) by (rewrite P4; exact Htp).
assert (GA1r : YK0s.ret_ok (getr (ms_regs ms6) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GA1a : 4096 <= bv_unsigned (getr (ms_regs ms6) 1))
  by (rewrite P1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (GA8 : s0Z (ms_regs ms6) = spZ regs) by (unfold s0Z; rewrite P8, unsigned_lit_small by lia; reflexivity).
assert (HROD6 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms6)))
  by exact (sii_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJ5 HREP HROD).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HAR6 HROD6) as HRO6.
assert (HAS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (K56 : forall a, KA a -> rdW W4 (ms_mem ms6) a = rdW W4 mem5 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _).
  apply (sii_aview_frame_pt E4 _ (w_H W4) mem5 (ms_mem ms6) a HFr6); [lia|].
  nwin_tac ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in H; lia). }
assert (K46 : forall a, KA a -> rdW W4 (ms_mem ms6) a = rdW W4 mem4 a)
  by (intros a Ha; rewrite (K56 a Ha); exact (K4m5 a Ha)).
(* the recorder at arg_s's entry: record's post, its bytes kept *)
assert (HO1in : forall pn, In pn O1 -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (HOin pn (proj1 (proj1 (HO1 pn) Hpn)))).
assert (HREP6 : rec_repA B ly4 S4 (rdW W4 (ms_mem ms6)) (rec_record R SII_FN []) O1).
{ apply (sii_rec_repA_kept B ly4 S4 (rdW W4 mem4) ly4 S4 (rdW W4 (ms_mem ms6)) _ O1 HREP4).
  - exact (sii_rec_repA_in B ly4 S4 _ _ O1 HREP4).
  - intros a Ha. apply K46. left. exact Ha.
  - intros a Ha. apply K46. right. left. exact Ha.
  - intros p n i Hpn Hi. apply K46. right. right. exists p, n.
    split; [exact (HO1in _ Hpn)|]. pose proof (req_size_pos n) as Hq.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO1in _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (Hq ltac:(lia)). lia. }
(* b at arg_s's entry: dec id with its terminator, its two shadow bytes 0, in the walk's frame *)
assert (HF8m : F mod 8 = 0)
  by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
pose proof (dec_length id Hid) as HDL.
assert (HSTR6 : astr_atR (rdW W4 (ms_mem ms6)) (F + 32) (dec id)).
{ split; [|exact (dec_no0 id)]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (sii_aview_frame_pt E4 _ (w_H W4) mem5 (ms_mem ms6) (F + 32 + Z.of_nat i) HFr6);
  [exact (HBUF5 i ltac:(rewrite length_app; cbn [length]; lia)) | lia |].
  nwin_tac ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in H; unfold SB in *; lia). }
assert (ZS6 : forall j, 4 <= j < 6 -> rdW W4 (ms_mem ms6) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E4 _ _ 0 _ HS eq_refl) as HR0.
  cbn [ms_mem restrict mkst] in HR0.
  assert (Hj4 : j = 4 \/ j = 5) by lia.
  destruct Hj4 as [-> | ->];
  (apply (aview_of_val_mem1 SEGS); [|lia]);
  (lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
     refine (field_of_region E4 _ 1041 (SB + F / 8) _ _ _ _ _ od 1%N (SLit 0) 0 HR0 Y1041 _ _ _ _) end;
   [cbn [In]; tauto | reflexivity | lia | lia]). }
assert (HRA6 : range_addressable (rdW W4 (ms_mem ms6)) SHADOW_OFF (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
  assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS6.
  split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia
  | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia]. }
assert (HAFO6 : afobj SEGS B ly4 S4 W4 (ms_mem ms6) (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ split; [exists 0, fpos; split; [exact Hfin4|]; rewrite EFA4; split; [lia|]; split; [exact HF8m|];
    split; [lia | change (fs_frame_bytes 0) with 64; lia]|].
  split; [rewrite Zplus_mod, HF8m; reflexivity | exact HRA6]. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR6 Hfin4) as (_ & _ & HFpres6 & _).
rewrite EFA4 in HFpres6. change (fs_frame_bytes 0) with 64 in HFpres6.
assert (HTV6 : atail_vis SEGS W4 (ms_mem ms6) (F + 32 + Z.of_nat (length (dec id)))).
{ intros a Ha HN. pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length (dec id))) 8 ltac:(lia)).
  exact (aview_some_of_apresent SEGS _ _ a (proj1 (HFpres6 a ltac:(lia))) HN). }
(* the frame chain for s0 = the entry sp, read at arg_s's entry *)
assert (FW8b : rdword (rdW W4 (ms_mem ms6)) (spZ regs - 8) = Some (raZ regs)).
{ pose proof (st_ok_region_nth E4 _ _ 4 _ HS eq_refl) as HR1. cbn [ms_mem restrict mkst] in HR1.
  apply (rdword_of_val_mem SEGS); [|unfold raZ; exact (bv_unsigned_in_range 64 (getr regs 1))].
  replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (field_of_region E4 _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR1 Y2 _ _ _ _);
  [cbn [In]; tauto | rewrite sii_denot_off0, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ;
    symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; exact (bv_unsigned_in_range 64 (getr regs 1)) | lia]. }
assert (FW16b : rdword (rdW W4 (ms_mem ms6)) (spZ regs - 16) = Some (s0Z regs)).
{ pose proof (st_ok_region_nth E4 _ _ 4 _ HS eq_refl) as HR1. cbn [ms_mem restrict mkst] in HR1.
  apply (rdword_of_val_mem SEGS); [|unfold s0Z; exact (bv_unsigned_in_range 64 (getr regs 8))].
  replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (field_of_region E4 _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR1 Y2 _ _ _ _);
  [cbn [In]; tauto | rewrite sii_denot_off0, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z;
    symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; exact (bv_unsigned_in_range 64 (getr regs 8)) | lia]. }
destruct (sii_chain_at B SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md _ ly4 S4 W4 (ms_mem ms6) _ _ (s0Z regs) ch
  (raZ regs) (spZ regs + (sp1 - spZ regs)) HJ5 HFPlow Hch FW8b FW16b Hra4 ltac:(lia)) as (ch6 & Hch6).
assert (Hch6' : achain ly4 (rdW W4 (ms_mem ms6)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms6)) ch6)
  by (rewrite GA8; exact Hch6).
(* the meter and the blocks up to here *)
assert (MLE4' : mo_le MT S S4 (XM_RECORD MT R))
  by (apply (mo_le_set_fs_l MT MTLF S S4 fS2); rewrite <- ES2; exact MLE4).
assert (BB2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
assert (LN0 : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
(* the slot lies among the recorder's bytes KA *)
assert (HSLKA : forall a, rec_slot R <= a < rec_slot R + CALL_SIZE -> KA a).
{ intros a Ha. destruct HSLOT as [Hs | Hs]; [left; unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
  right; left. rewrite Hs in Ha. unfold CALL_SIZE, SC_SIZE in *. lia. }
assert (AWRG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> inFP FP x /\
  Exists (in_zr x) (as_prog_static B) /\ in_img SEGS x).
{ intros x Hx. split; [unfold FP; apply inFP_cons; left; unfold REC_SIZE in *; lia|].
  split; [rewrite sii_ts_prog; exact (sii_grec_in x Hx) | exact (cmd_prog_img x (sii_grec_in x Hx))]. }
assert (AWRSP : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> inFP FP x /\
  Exists (in_zr x) (as_prog_static B) /\ in_img SEGS x).
{ intros x Hx. split;
    [unfold FP; apply inFP_cons; right; apply inFP_cons; left; unfold SC_SIZE in *; lia|].
  split; [rewrite sii_ts_prog; exact (sii_spill_in x Hx) | exact (cmd_prog_img x (sii_spill_in x Hx))]. }
(* ---- the call of arg_s(slot, b) (0x8bc98) ---- *)
rewrite (sii_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W4 (ms_regs ms6) (ms_mem ms6) _ SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly4 S4 _ _ ARG_S_STK _ EV_ARG_S (sp1 - spZ regs) (getr (ms_regs ms6) 1) ch6 _ HJ5 Qsp6 Hsp1b
    ltac:(lia) ltac:(rewrite HAS; lia) ltac:(rewrite HAS, FS; lia) GA3 GA4 eq_refl GA1r GA1a Hch6').
  - intros HPRE1. pose proof (TARG_S fx1 ly4 S4 W4 (ms_regs ms6) (ms_mem ms6) _ ch6 (rec_slot R) (F + 32) SII_FN []
      (Some (dec id)) R O1 HPRE1) as T6.
    cbv zeta in T6. unfold apost_base in T6. apply T6.
    + exact HROD6.
    + exact HRO6.
    + exact P10.
    + exact P11.
    + reflexivity.
    + exact HREP6.
    + right. exists (dec id). split; [reflexivity|]. split; [exact HSTR6|].
      split; [unfold LMAX; lia | exact HAFO6].
    + intros x Hx. injection Hx as <-. exact HTV6.
    + pose proof HJ5 as (_ & _ & _ & _ & _ & _ & Hnev5 & _).
      unfold EV_SUP_INSTANCE_INFO, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + pose proof (LN0 (snd (sup_instance_info_m R id))). unfold LIVE_SUP_INSTANCE_INFO in Hlive. lia.
    + apply (mok_station MT S S4 (XM_SUP_INSTANCE_INFO MT R id) (XM_RECORD MT R) _ MTL MOK MLE4' XA0).
      unfold XM_SUP_INSTANCE_INFO. pose proof (XN0 (snd (sup_instance_info_m R id))). lia.
  - intros a Ha. unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
    right; right; right; right; left.
    assert (Hs : rec_slot R <= a < rec_slot R + CALL_SIZE).
    { apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in Ha |- *; lia|].
      apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in Ha |- *; lia | exfalso; exact (inFP_nil a Ha)]. }
    destruct HSLOT as [Hs' | Hs']; [apply AWRG; unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    apply AWRSP. rewrite Hs' in Hs. unfold CALL_SIZE, SC_SIZE in *. lia.
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
    assert (Hs : rec_slot R <= a < rec_slot R + CALL_SIZE).
    { apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in Ha |- *; lia|].
      apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in Ha |- *; lia | exfalso; exact (inFP_nil a Ha)]. }
    destruct (KLOC a (HSLKA a Hs)) as (Hb & _). rewrite FS in Hw. lia. }
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc7 & HP7 & HK7).
destruct HK7 as (HBB7 & MLE7 & [(Hc6 & _) | (_ & p & Hp & Hperm7 & Hfresh7 & HREP7)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length Z.of_nat] in Hc6. lia. }
cbn [app] in HREP7.
set (y := sarg (Some (dec id))) in *.
set (n := Z.of_nat (length y) + 1) in *.
pose proof (proj1 HJ7) as HAR7.
rewrite P1.
(* the frame after arg_s *)
lazymatch type of HJc7 with ajournal _ _ _ _ ?FPa _ _ _ _ _ _ _ _ _ _ _ _ =>
  assert (HFPA : forall a, inFP FPa a -> rec_slot R <= a < rec_slot R + CALL_SIZE) end.
{ intros a HFa. unfold REC_ARGS_MAX in HFa. cbn [length Z.of_nat Z.ltb Z.compare] in HFa.
  apply inFP_cons in HFa as [HFa | HFa]; [unfold CALL_OFF_NARGS, CALL_SIZE in HFa |- *; lia|].
  apply inFP_cons in HFa as [HFa | HFa];
  [unfold CALL_OFF_ARGS, CALL_SIZE in HFa |- *; lia | exfalso; exact (inFP_nil a HFa)]. }
pose proof HJc7 as (_ & Hly7 & _ & _ & _ & Hfrs7 & _). cbn [app] in Hfrs7.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly7 HAR6 Hly7) as (Eab7 & Efa7 & _).
assert (EFA7 : frame_addr ly7 0 fpos = F) by (rewrite Efa7; exact EFA4).
assert (Hfin7 : In (0, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin4).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7).
rewrite EFA7 in HFpres7, HFSpres7.
change (fs_frame_bytes 0) with 64 in HFpres7, HFSpres7. change (64 / 8) with 8 in HFSpres7.
jafter_call_keep_hi HS 1090%nat regs7 (mrestrict (w_H W7) mem7) HP7 [0;1;2;3;4;5]%nat HS7.
match type of HS7 with ?tq -> _ => assert (HRK : tq); [|specialize (HS7 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E4 _ _ _ ly4 S4 W4 (ms_mem ms6) _ ly7 S7 W7 mem7 md7 _ 1041
      (SB + F / 8) _ _ _ _ _ 0 fpos HJc7 Y1041 Hfin4);
    [ unfold shadow_addr; rewrite EFA4, <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA4, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (KLOC a (HSLKA a (HFPA a HFa))) as (_ & _ & HnS & _); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8)))
        by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres7 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E4 _ _ _ ly4 S4 W4 (ms_mem ms6) _ ly7 S7 W7 mem7 md7 _ 1028 F
      _ _ _ _ _ 0 fpos HJc7 Y1028 Hfin4);
    [ rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC a (HSLKA a (HFPA a HFa))) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E4 _ _ _ ly4 S4 W4 (ms_mem ms6) _ ly7 S7 W7 mem7 md7 _ 1028 F
      _ _ _ _ _ 0 fpos HJc7 Y1028 Hfin4);
    [ rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC a (HSLKA a (HFPA a HFa))) as (_ & HnF & _); lia
    | intros a Ha; exact (proj1 (HFpres7 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc7 HJ7 Y2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HSLKA a (HFPA a HFa))); lia].
  - eapply (region_kept_stack_sub SEGS B E4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc7 HJ7 Y2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HSLKA a (HFPA a HFa))); lia].
  - eapply (region_kept_stack_sub SEGS B E4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _
      HJc7 HJ7 Y34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HSLKA a (HFPA a HFa))); lia]. }
rewrite <- restrict_mkst_fx in HS7. clear HS. rename HS7 into HS.
clear P1 P2 P3 P4 P8 P10 P11.
remember (havoc E4 1090 (map (getr regs7) CLOB)) as E5 eqn:HE5 in HS.
assert (HAE5 : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E5)
  by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact HAE4]).
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI4 | unfold A_LIM; lia]).
assert (OLD5 : forall n, (n < 1090)%nat -> ew E5 n = ew E4 n)
  by (intros n0 Hn0; rewrite HE5; apply ew_havoc_old; exact Hn0).
clear HE5.
assert (Z2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Y2).
assert (Z34 : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact Y34).
assert (Z1028 : bv_unsigned (ew E5 1028) = F) by (rewrite OLD5 by lia; exact Y1028).
assert (Z1040 : bv_unsigned (ew E5 1040) = FL) by (rewrite OLD5 by lia; exact Y1040).
assert (Z1041 : bv_unsigned (ew E5 1041) = SB + F / 8) by (rewrite OLD5 by lia; exact Y1041).
(* the recorder's bytes and blocks from arg_s's return on: g_rec, record.spill, and the blocks live at that point
   (the copy p and the entry's blocks that record kept), none of them in the frame, its shadow or its flag *)
set (KA7 := fun a : Z => (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
  (exists p n, In (p, n) (ablocks B ly7 S7) /\ p <= a < p + req_size n)).
assert (KLOC7 : forall a, KA7 a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\
  ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a Ha. destruct Ha as [Ha | [Ha | (p0 & n0 & Hpn & Hpa)]].
  - apply KLOC. left. exact Ha.
  - apply KLOC. right. left. exact Ha.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HAR7 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres7 & _).
    pose proof (sep_block_frame SEGS B LAWS ly7 S7 W7 mem7 md7 p0 n0 0 fpos HAR7 Hpn Hfin7) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA7 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    destruct (sii_FFL _ _ _ _ _ 0 fpos HAR7 Hfin7) as (_ & HFLo7 & _).
    assert (EFL7 : flag_addr ly7 0 fpos = FL).
    { pose proof EFA7 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
    rewrite EFL7 in HFLo7.
    split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
    intros ->. exact (proj2 (Hpres7 FL ltac:(lia)) HFLo7). }
(* run 5 (0x8bc9c .. 0x8bcac): b's shadow f8 f8 again, a0 = the verb "instance_info", a1 = 13 *)
paj_run_shc RUNP RUNC HS HJ7.
{ sii_awr6 fpos sp1 regs FS Z1041 Z1028 Z2 Z34 EFA7. }
rename ms into ms8, mat into mat8, HF into HFl8, HFr into HFr8, HG into HG8.
pmkst HS.
preg HS (10%bv : bv 5) M10. preg HS (11%bv : bv 5) M11. preg HS (1%bv : bv 5) M1. preg HS (2%bv : bv 5) M2.
preg HS (3%bv : bv 5) M3. preg HS (4%bv : bv 5) M4.
rewrite sii_denot_off0, (img_env_atomP E5 309 HEI5 ltac:(unfold A_TEXT, A_LIM; lia)) in M10.
change (VAL 309) with (VAL SII_VOBJ) in M10. rewrite (sii_vobj_verb VOBJS) in M10.
cbn [sv_denot] in M11, M1. rewrite (img_env_codeptr E5 HEI5 22404) in M1.
rewrite sii_denot_off0, OLD5, OLD4, OLD3, OLD2, E34 in M2 by lia.
rewrite sii_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in M3 by lia.
rewrite sii_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in M4 by lia.
pose proof (proj1 HJ7) as HAR8.
assert (Qsp8 : spZ (ms_regs ms8) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite M2, unsigned_lit_small by lia; lia).
assert (GC3 : getr (ms_regs ms8) 3 = w64 (as_gp B)) by (rewrite M3; exact Hgp).
assert (GC4 : getr (ms_regs ms8) 4 = w64 (as_tp B)) by (rewrite M4; exact Htp).
assert (GC1r : YK0s.ret_ok (getr (ms_regs ms8) 1)) by (rewrite M1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GC1a : 4096 <= bv_unsigned (getr (ms_regs ms8) 1))
  by (rewrite M1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (GC11 : getr (ms_regs ms8) 11 = w64 (Z.of_nat (length sii_verb))) by (rewrite M11; reflexivity).
assert (HROD8 : arodata_okP SEGS RLO RHI B (rdW W7 (ms_mem ms8)))
  by exact (sii_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJ7 HREP HROD).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HAR8 HROD8) as HRO8.
assert (HSS : REC_SHAPE_OF_STK = 8288) by (vm_compute; reflexivity).
(* ---- the call of rec_shape_of("instance_info", 13) (0x8bcb0) ---- *)
rewrite (sii_sig_rso cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W7 (ms_regs ms8) (ms_mem ms8) _ SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly7 S7 _ _ REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (sp1 - spZ regs) (getr (ms_regs ms8) 1) _ HJ7 Qsp8 Hsp1b
    ltac:(lia) ltac:(rewrite HSS; lia) ltac:(rewrite HSS, FS; lia) GC3 GC4 eq_refl GC1r GC1a).
  - intros HPRE1. pose proof (TREC_SHAPE_OF fx1 ly7 S7 W7 (ms_regs ms8) (ms_mem ms8) _ SII_VERB sii_verb HPRE1 HROD8
      M10 ltac:(unfold SII_VERB; lia) GC11 ltac:(rewrite sii_verb_len; lia) HRO8 VOBJS
      (fun _ => sii_verb_ok B HB ly7 S7 W7 (ms_mem ms8) _ HAR8 HRO8 CMD_RO_IN)) as T8.
    unfold apost_base in T8. apply T8.
    pose proof HJ7 as (_ & _ & _ & _ & _ & _ & Hnev7 & _).
    unfold EV_SUP_INSTANCE_INFO, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W9 c9 Hwle9 (ly9 & S9 & regs9 & mem9 & md9 & -> & HJ9 & HJc9 & HP9 &
  ((q & Hq10 & Hq64 & HqA) & Hperm9 & Ely9 & ES9)).
subst ly9 S9.
pose proof (proj1 HJ9) as HAR9.
rewrite M1.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR9 Hfin7) as (_ & _ & HFpres9 & HFSpres9).
rewrite EFA7 in HFpres9, HFSpres9.
change (fs_frame_bytes 0) with 64 in HFpres9, HFSpres9. change (64 / 8) with 8 in HFSpres9.
jafter_call_keep_hi HS 1106%nat regs9 (mrestrict (w_H W9) mem9) HP9 [0;1;2;3;4;5]%nat HS9.
match type of HS9 with ?tq -> _ => assert (HRK : tq); [|specialize (HS9 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E5 _ _ _ ly7 S7 W7 (ms_mem ms8) _ ly7 S7 W9 mem9 md9 _ 1041
      (SB + F / 8) _ _ _ _ _ 0 fpos HJc9 Z1041 Hfin7);
    [ unfold shadow_addr; rewrite EFA7, <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA7, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a _ HFa; exact (inFP_nil a HFa)
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8)))
        by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres9 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E5 _ _ _ ly7 S7 W7 (ms_mem ms8) _ ly7 S7 W9 mem9 md9 _ 1028 F
      _ _ _ _ _ 0 fpos HJc9 Z1028 Hfin7);
    [ rewrite EFA7; lia | rewrite EFA7; change (fs_frame_bytes 0) with 64; lia
    | intros a _ HFa; exact (inFP_nil a HFa) | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E5 _ _ _ ly7 S7 W7 (ms_mem ms8) _ ly7 S7 W9 mem9 md9 _ 1028 F
      _ _ _ _ _ 0 fpos HJc9 Z1028 Hfin7);
    [ rewrite EFA7; lia | rewrite EFA7; change (fs_frame_bytes 0) with 64; lia
    | intros a _ HFa; exact (inFP_nil a HFa) | intros a Ha; exact (proj1 (HFpres9 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc9 HJ9 Z2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a _ HFa; exact (inFP_nil a HFa)].
  - eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc9 HJ9 Z2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a _ HFa; exact (inFP_nil a HFa)].
  - eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _
      HJc9 HJ9 Z34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a _ HFa; exact (inFP_nil a HFa)]. }
rewrite <- restrict_mkst_fx in HS9. clear HS. rename HS9 into HS.
clear M1 M2 M3 M4 M10 M11.
remember (havoc E5 1106 (map (getr regs9) CLOB)) as E6 eqn:HE6 in HS.
assert (HAE6 : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E6)
  by (rewrite HE6; apply env_agree_havoc_ge; [lia | exact HAE5]).
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc_hi; [exact HEI5 | unfold A_LIM; lia]).
assert (OLD6 : forall n0, (n0 < 1106)%nat -> ew E6 n0 = ew E5 n0)
  by (intros n0 Hn0; rewrite HE6; apply ew_havoc_old; exact Hn0).
assert (E1110 : ew E6 1110 = w64 q).
{ rewrite HE6. change 1110%nat with (1106 + 4)%nat. rewrite (ew_havoc_new E5 1106 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact Hq10. }
clear HE6.
assert (V62 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Z2).
assert (V634 : bv_unsigned (ew E6 34) = sp1) by (rewrite OLD6 by lia; exact Z34).
assert (V61028 : bv_unsigned (ew E6 1028) = F) by (rewrite OLD6 by lia; exact Z1028).
assert (V61040 : bv_unsigned (ew E6 1040) = FL) by (rewrite OLD6 by lia; exact Z1040).
assert (V61041 : bv_unsigned (ew E6 1041) = SB + F / 8) by (rewrite OLD6 by lia; exact Z1041).
(* run 6 (0x8bcb4 .. 0x8bcbc): a1 = the shape, a0 = the slot, a2 = 0 (no change) *)
paj_run_shc RUNP RUNC HS HJ9.
{ sii_awr6 fpos sp1 regs FS V61041 V61028 V62 V634 EFA7. }
rename ms into ms10, mat into mat10, HF into HFl10, HFr into HFr10, HG into HG10.
pmkst HS.
preg HS (10%bv : bv 5) N10. preg HS (11%bv : bv 5) N11. preg HS (12%bv : bv 5) N12. preg HS (1%bv : bv 5) N1.
preg HS (2%bv : bv 5) N2. preg HS (3%bv : bv 5) N3. preg HS (4%bv : bv 5) N4. preg HS (8%bv : bv 5) N8.
rewrite sii_denot_off0, OLD6, OLD5, OLD4, E1062 in N10 by lia.
rewrite sii_denot_off0, E1110 in N11.
cbn [sv_denot] in N12, N1. rewrite (img_env_codeptr E6 HEI6 22420) in N1.
rewrite sii_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, E34 in N2 by lia.
rewrite sii_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in N3 by lia.
rewrite sii_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in N4 by lia.
rewrite sii_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, Esp in N8 by lia.
pose proof (proj1 HJ9) as HAR10.
assert (Qsp10 : spZ (ms_regs ms10) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite N2, unsigned_lit_small by lia; lia).
assert (GD3 : getr (ms_regs ms10) 3 = w64 (as_gp B)) by (rewrite N3; exact Hgp).
assert (GD4 : getr (ms_regs ms10) 4 = w64 (as_tp B)) by (rewrite N4; exact Htp).
assert (GD1r : YK0s.ret_ok (getr (ms_regs ms10) 1)) by (rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GD1a : 4096 <= bv_unsigned (getr (ms_regs ms10) 1))
  by (rewrite N1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
assert (GD8 : s0Z (ms_regs ms10) = spZ regs) by (unfold s0Z; rewrite N8, unsigned_lit_small by lia; reflexivity).
assert (HROD10 : arodata_okP SEGS RLO RHI B (rdW W9 (ms_mem ms10)))
  by exact (sii_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJ9 HREP HROD).
pose proof (cmd_ro_ok_of_aro _ _ _ _ _ HAR10 HROD10) as HRO10.
(* the recorder's bytes from arg_s's return to answer's entry: run 5 writes b's shadow, rec_shape_of nothing of the
   recorder's (its footprint is empty), run 6 nothing *)
assert (K7_10 : forall a, KA7 a -> rdW W9 (ms_mem ms10) a = rdW W7 mem7 a).
{ intros a Ha. destruct (KLOC7 a Ha) as (Hb & HnF & HnS & _).
  rewrite (sii_aview_frame_pt E6 _ (w_H W9) mem9 (ms_mem ms10) a HFr10);
  [| lia | nwin_tac ltac:(fun H => rewrite ?V62, ?V634, ?V61028, ?V61041 in H; lia)].
  rewrite <- (sii_aview_frame_pt E5 _ (w_H W7) mem7 (ms_mem ms8) a HFr8);
  [| lia | nwin_tac ltac:(fun H => rewrite ?Z2, ?Z34, ?Z1028, ?Z1041 in H; lia)].
  destruct Ha as [Ha | [Ha | (b & m & Hbm & Hba)]].
  - exact (sii_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc9 (Forall_nil _) (inFP_nil a) (sii_grec_in a Ha)).
  - exact (sii_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc9 (Forall_nil _) (inFP_nil a) (sii_spill_in a Ha)).
  - replace a with (b + (a - b)) by lia.
    exact (sii_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (a - b) HJc9 Hbm Hbm ltac:(lia) (inFP_nil _)). }
assert (HO2in7 : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B ly7 S7))
  by exact (sii_rec_repA_in B ly7 S7 _ _ _ HREP7).
assert (HREP10 : rec_repA B ly7 S7 (rdW W9 (ms_mem ms10)) (rec_record R SII_FN [y]) ((p, n) :: O1)).
{ apply (sii_rec_repA_kept B ly7 S7 (rdW W7 mem7) ly7 S7 (rdW W9 (ms_mem ms10)) _ _ HREP7).
  - exact HO2in7.
  - intros a Ha. apply K7_10. left. exact Ha.
  - intros a Ha. apply K7_10. right. left. exact Ha.
  - intros p0 n0 i Hpn Hi. apply K7_10. right. right. exists p0, n0. split; [exact (HO2in7 _ Hpn)|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HAR7 (HO2in7 _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos n0 ltac:(lia)). lia. }
(* the answer the recorder holds: 0 or the start of one of its blocks *)
pose proof HREP10 as (QD & HQD & HOQD).
destruct (sii_old_at _ _ _ _ HQD) as [HOLD HOLDin'].
set (old := sii_old QD) in *.
assert (HoldO2 : old = 0 \/ exists m, In (old, m) ((p, n) :: O1)).
{ unfold old, sii_old. destruct (l_answer QD) as [[a1 a2]|] eqn:Ean; [right; exists a2 | left; reflexivity].
  apply HOQD. exact (HOLDin' _ eq_refl). }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct HoldO2 as [-> | (m & Hm)]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old m HAR10 (HO2in7 _ Hm)) as (_ & Hb0 & Hb1 & _ & _ & _ & Hm0).
  pose proof (req_size_pos m ltac:(lia)). pose proof (YM05.alloc_ceiling_lt (rc := rc)). lia. }
(* the shape rec_shape_of returned: its bytes are the image's or a live block's, none in the frame or its shadow *)
assert (HQOFF : forall i, 0 <= i < Z.of_nat (length (shape_of sii_verb)) + 1 ->
  0 <= q + i < alloc_ceiling /\ ~ (F <= q + i < F + 64) /\ ~ (SB + F / 8 <= q + i < SB + F / 8 + 8)).
{ intros i Hi. pose proof (HqA []) as HA0. cbn [astr_argA] in HA0.
  destruct HA0 as (_ & _ & _ & [((b & m & Hbm & Hb1 & Hb2) & _) | (Hro & _)]).
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR9 Hbm) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hm).
    pose proof (sep_block_frame SEGS B LAWS ly7 S7 W9 mem9 md9 b m 0 fpos HAR9 Hbm Hfin7) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA7 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. pose proof (req_size_pos m ltac:(lia)) as Hrq.
    split; [lia|]. split; [lia|]. unfold SB. lia.
  - destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))) as Hir.
    split; [lia|]. split; [lia|]. unfold SB. lia. }
assert (HSH : r_refuse (rec_record R SII_FN [y]) = 0 ->
  astr_argA B ly7 S7 (rdW W9 (ms_mem ms10)) (in_roP SEGS RLO RHI) ((p, n) :: O1) q (Some (shape_of sii_verb)) /\
  fits (shape_of sii_verb)).
{ intros _. split; [|exact sii_fits].
  apply (sii_argA_kept _ _ (rdW W9 mem9)); [exact (HqA _)|]. intros i Hi.
  destruct (HQOFF i Hi) as (Hb & HnF & HnS).
  apply (sii_aview_frame_pt E6 _ (w_H W9) mem9 (ms_mem ms10) (q + i) HFr10); [lia|].
  nwin_tac ltac:(fun H => rewrite ?V62, ?V634, ?V61028, ?V61041 in H; lia). }
assert (HCHG : false = negb (bv_unsigned (getr (ms_regs ms10) 12) =? 0)) by (rewrite N12; reflexivity).
assert (HFR10 : Z.of_nat (length (frames S7)) <= 8).
{ rewrite Hfrs7, Hfrs4, Hfrs2. cbn [length]. lia. }
set (t := snd (rec_answer (rec_record R SII_FN [y]) (SII_FN, [y]) (shape_of sii_verb) false)).
assert (Ht : snd (sup_instance_info_m R id) = t) by (rewrite sii_m; reflexivity).
assert (HEV10 : st_nev S7 + EV_ANSWER <= EV_MAX).
{ pose proof HJ9 as (_ & _ & _ & _ & _ & _ & Hnev9 & _).
  unfold EV_SUP_INSTANCE_INFO, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
assert (HLIVE10 : blocks_bytes S7 + LIVE_ANSWER t <= LIVE_MAX).
{ unfold LIVE_SUP_INSTANCE_INFO in Hlive. rewrite Ht in Hlive. lia. }
assert (MLE7' : mo_le MT S S7 (XM_RECORD MT R + XM_ARG_S MT (Some (dec id))))
  by exact (mle_station MT S S4 S7 _ _ MTL MLE4' MLE7).
assert (HMOK10 : mo_ok MT S7 (XM_ANSWER MT t)).
{ apply (mok_station MT S S7 (XM_SUP_INSTANCE_INFO MT R id) _ (XM_ANSWER MT t) MTL MOK MLE7' (XN0 t)).
  unfold XM_SUP_INSTANCE_INFO. rewrite Ht. lia. }
(* the frame chain for s0 = the entry sp, read at answer's entry *)
assert (FW8c : rdword (rdW W9 (ms_mem ms10)) (spZ regs - 8) = Some (raZ regs)).
{ pose proof (st_ok_region_nth E6 _ _ 4 _ HS eq_refl) as HR1. cbn [ms_mem restrict mkst] in HR1.
  apply (rdword_of_val_mem SEGS); [|unfold raZ; exact (bv_unsigned_in_range 64 (getr regs 1))].
  replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (field_of_region E6 _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR1 V62 _ _ _ _);
  [cbn [In]; tauto | rewrite sii_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ;
    symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; exact (bv_unsigned_in_range 64 (getr regs 1)) | lia]. }
assert (FW16c : rdword (rdW W9 (ms_mem ms10)) (spZ regs - 16) = Some (s0Z regs)).
{ pose proof (st_ok_region_nth E6 _ _ 4 _ HS eq_refl) as HR1. cbn [ms_mem restrict mkst] in HR1.
  apply (rdword_of_val_mem SEGS); [|unfold s0Z; exact (bv_unsigned_in_range 64 (getr regs 8))].
  replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (field_of_region E6 _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR1 V62 _ _ _ _);
  [cbn [In]; tauto | rewrite sii_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z;
    symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; exact (bv_unsigned_in_range 64 (getr regs 8)) | lia]. }
destruct (sii_chain_at B SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md _ ly7 S7 W9 (ms_mem ms10) _ _ (s0Z regs) ch
  (raZ regs) (spZ regs + (sp1 - spZ regs)) HJ9 HFPlow Hch FW8c FW16c Hra4 ltac:(lia)) as (ch10 & Hch10).
assert (Hch10' : achain ly7 (rdW W9 (ms_mem ms10)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms10)) ch10)
  by (rewrite GD8; exact Hch10).
assert (HNS : ANSWER_STK = 16592) by (vm_compute; reflexivity).
(* ---- the call of answer(slot, shape, 0) (0x8bcc0): its post is FP-existential (PaFx.callS_wideF) ---- *)
rewrite (sii_sig_answer cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (callS_wideF B LAWS W9 (ms_regs ms10) (ms_mem ms10) _ SUP_INSTANCE_INFO_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly7 S7 _ _ ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) ((p, n) :: O1)))
    EV_ANSWER (sp1 - spZ regs) (getr (ms_regs ms10) 1) ch10 _ HJ9 Qsp10 Hsp1b
    ltac:(lia) ltac:(rewrite HNS; lia) ltac:(rewrite HNS, FS; lia) GD3 GD4 eq_refl GD1r GD1a Hch10').
  - intros HPRE10. eapply SRr_mono.
    + exact (TANSWER fx1 ly7 S7 W9 (ms_regs ms10) (ms_mem ms10) _ ch10 (rec_slot R) q old (SII_FN, [y])
        (shape_of sii_verb) false (rec_record R SII_FN [y]) ((p, n) :: O1)
        HPRE10 HFRM1 HFR10 HROD10 HRO10 N10
        ltac:(destruct HSLOT as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in Hs |- *; lia
              | rewrite Hs; unfold A_REC_SPILL; lia]) N11 Hq64 HCHG HREP10
        HOLD Hold64 HSH (fun _ Hf => False_ind _ (Bool.diff_false_true Hf)) HEV10 HLIVE10 HMOK10).
    + cbv beta. intros Wx cx _ (fx' & lyx & Sx & regsx & memx & mdx & -> & HFx & HCx & HJx & HPx & HKx).
      exists fx', lyx, Sx, regsx, memx, mdx. split; [reflexivity|]. split; [exact HFx|]. split; [exact HCx|].
      split; [exact HJx|]. split; [exact HPx | exact HKx].
  - intros a Hfp. apply inFP_cons in Hfp as [Ha | Hfp]; [|apply inFP_cons in Hfp as [Ha | Hfp]].
    + right; right; right; right; left. apply AWRG. unfold OFF_ANSWER, REC_SIZE in Ha |- *. lia.
    + right; right; right; right; left. apply AWRG. unfold OFF_STATE, REC_SIZE in Ha |- *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (pb & nb & Hin & Hr).
      apply sii_in_filter in Hin as [Hin _].
      pose proof (HO2in7 _ Hin) as HinT.
      destruct (in_dec sii_pair_dec (pb, nb) O) as [HO | HnO].
      * right; left. split; [|exists pb, nb; split; [exact HinT | exact Hr]].
        unfold FP. apply inFP_cons. right. apply inFP_cons. right.
        replace a with (pb + (a - pb)) by lia. apply (inFP_ablocks_fp O pb nb (a - pb)); [exact HO | lia].
      * right; right; left. exists pb, nb. split; [exact HinT|]. split; [|exact Hr].
        intros H0. destruct Hin as [Hpn | Hin1].
        -- rewrite <- Hpn in H0, HnO. rewrite <- Eab in H0. apply (Permutation_in _ HPermF) in H0.
           apply in_app_or in H0 as [H0 | H0]; [|exact (HnO (HFO _ H0))].
           rewrite Forall_forall in Hfresh7. specialize (Hfresh7 _ H0). cbn [fst snd] in Hfresh7.
           unfold iv_apart, n in Hfresh7. lia.
        -- exact (HnO (proj1 (proj1 (HO1 _) Hin1))).
  - intros ly5' S5' W5' regs5' mem5' md5' _ a Hfp Hw _. exfalso.
    apply inFP_cons in Hfp as [Ha | Hfp]; [|apply inFP_cons in Hfp as [Ha | Hfp]].
    + destruct (KLOC7 a ltac:(left; unfold OFF_ANSWER, REC_SIZE in Ha |- *; lia)) as (Hb & _). rewrite FS in Hw. lia.
    + destruct (KLOC7 a ltac:(left; unfold OFF_STATE, REC_SIZE in Ha |- *; lia)) as (Hb & _). rewrite FS in Hw. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (pb & nb & Hin & Hr).
      apply sii_in_filter in Hin as [Hin _].
      destruct (KLOC7 a ltac:(right; right; exists pb, nb; split; [exact (HO2in7 _ Hin) | exact Hr])) as (Hb & _).
      rewrite FS in Hw. lia. }
cbv beta. intros W11 c11 Hwle11 (fx2 & ly11 & S11 & regs11 & mem11 & md11 & -> & Hfx11 & Hcsr11 & HJ11 & HJc11 &
  HP11 & HK11).
destruct HK11 as (p1 & p2 & O' & HK11). cbv zeta in HK11.
destruct HK11 as (Hp2r & Hp24096 & H12 & Hfr12 & Hbl11 & HREP11 & HO'iff & Hstr11 & Hbb11 & HMLE11).
pose proof (proj1 HJ11) as HAR11.
rewrite N1.
(* the frame after answer *)
pose proof HJc11 as (_ & Hly11 & _ & _ & _ & Hfrs11 & _). cbn [app] in Hfrs11.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly11 HAR10 Hly11) as (Eab11 & Efa11 & _).
assert (EFA11 : frame_addr ly11 0 fpos = F) by (rewrite Efa11; exact EFA7).
assert (Hfin11 : In (0, fpos) (frames S11)) by (rewrite Hfrs11; exact Hfin7).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR11 Hfin11) as (_ & _ & HFpres11 & HFSpres11).
rewrite EFA11 in HFpres11, HFSpres11.
change (fs_frame_bytes 0) with 64 in HFpres11, HFSpres11. change (64 / 8) with 8 in HFSpres11.
lazymatch type of HJc11 with ajournal _ _ _ _ ?FPn _ _ _ _ _ _ _ _ _ _ _ _ =>
  assert (HFPN : forall a, inFP FPn a -> KA7 a) end.
{ intros a HFa. apply inFP_cons in HFa as [HFa | HFa]; [left; unfold OFF_ANSWER, REC_SIZE in HFa |- *; lia|].
  apply inFP_cons in HFa as [HFa | HFa]; [left; unfold OFF_STATE, REC_SIZE in HFa |- *; lia|].
  apply inFP_ablocks_fp_inv in HFa as (b & m & Hbm & Hba). apply sii_in_filter in Hbm as [Hbm _].
  right; right. exists b, m. split; [exact (HO2in7 _ Hbm) | exact Hba]. }
jafter_call_keep_hi HS 1122%nat regs11 (mrestrict (w_H W11) mem11) HP11 [0;1;2;3;4;5]%nat HS11.
match type of HS11 with ?tq -> _ => assert (HRK : tq); [|specialize (HS11 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E6 _ _ _ ly7 S7 W9 (ms_mem ms10) _ ly11 S11 W11 mem11 md11 _ 1041
      (SB + F / 8) _ _ _ _ _ 0 fpos HJc11 V61041 Hfin7);
    [ unfold shadow_addr; rewrite EFA7, <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA7, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (KLOC7 a (HFPN a HFa)) as (_ & _ & HnS & _); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8)))
        by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres11 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E6 _ _ _ ly7 S7 W9 (ms_mem ms10) _ ly11 S11 W11 mem11 md11 _ 1028 F
      _ _ _ _ _ 0 fpos HJc11 V61028 Hfin7);
    [ rewrite EFA7; lia | rewrite EFA7; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC7 a (HFPN a HFa)) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E6 _ _ _ ly7 S7 W9 (ms_mem ms10) _ ly11 S11 W11 mem11 md11 _ 1028 F
      _ _ _ _ _ 0 fpos HJc11 V61028 Hfin7);
    [ rewrite EFA7; lia | rewrite EFA7; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC7 a (HFPN a HFa)) as (_ & HnF & _); lia
    | intros a Ha; exact (proj1 (HFpres11 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc11 HJ11 V62);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC7 a (HFPN a HFa)); lia].
  - eapply (region_kept_stack_sub SEGS B E6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _
      HJc11 HJ11 V62);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC7 a (HFPN a HFa)); lia].
  - eapply (region_kept_stack_sub SEGS B E6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _
      HJc11 HJ11 V634);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC7 a (HFPN a HFa)); lia]. }
rewrite <- restrict_mkst_fx in HS11. clear HS. rename HS11 into HS.
(* the code after answer runs at the FP state fx2 it returned *)
pose proof (st_ok_pi_restrict_xfx fx1 fx2 SEGS VAL _ _ _ _ _ _ _ HS) as HS1. clear HS. rename HS1 into HS.
eapply (srr_apost_baseF_lift (fx := fx1) SEGS fx2); [exact (conj Hfx11 Hcsr11)|].
clear RUNP RUNC Hfx11 Hcsr11 HFRM1.
repeat match goal with H : context [fx1] |- _ => clear H end.
clear fx1.
pose (RUNP := @SRr_run_pi_AJ fx2 rc SK cmd_listing PL_cmd PI B LAWS).
pose (RUNC := @SRr_run_pi_AJ_call fx2 rc SK cmd_listing PL_cmd PI B LAWS).
pose proof (YM05.alloc_ceiling_lt (rc := rc)) as Hac47.
remember (havoc E6 1122 (map (getr regs11) CLOB)) as E7 eqn:HE7 in HS.
assert (HAE7 : env_agree 32 (Ereg regs (sii_extra (as_uar_cell B) sp1)) E7)
  by (rewrite HE7; apply env_agree_havoc_ge; [lia | exact HAE6]).
assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc_hi; [exact HEI6 | unfold A_LIM; lia]).
assert (OLD7 : forall n0, (n0 < 1122)%nat -> ew E7 n0 = ew E6 n0)
  by (intros n0 Hn0; rewrite HE7; apply ew_havoc_old; exact Hn0).
assert (E1126 : ew E7 1126 = w64 p2).
{ rewrite HE7. change 1126%nat with (1122 + 4)%nat. rewrite (ew_havoc_new E6 1122 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact Hp2r. }
clear HE7.
assert (W72 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact V62).
assert (W734 : bv_unsigned (ew E7 34) = sp1) by (rewrite OLD7 by lia; exact V634).
assert (W71028 : bv_unsigned (ew E7 1028) = F) by (rewrite OLD7 by lia; exact V61028).
assert (W71040 : bv_unsigned (ew E7 1040) = FL) by (rewrite OLD7 by lia; exact V61040).
assert (W71041 : bv_unsigned (ew E7 1041) = SB + F / 8) by (rewrite OLD7 by lia; exact V61041).
(* the flag byte: its address in ly11, and a region for it in the symbolic state *)
assert (EFL11 : flag_addr ly11 0 fpos = FL).
{ pose proof EFA11 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
destruct (sii_FFL _ _ _ _ _ 0 fpos HAR11 Hfin11) as (HFLp11 & HFLo11 & _ & _). rewrite EFL11 in HFLp11, HFLo11.
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 8)).
{ intros Hx. apply (proj2 (HFSpres11 (FL - (SB + F / 8)) ltac:(lia))).
  replace (shadow_addr F + (FL - (SB + F / 8))) with FL by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
  exact HFLo11. }
assert (HFLnF : ~ (F <= FL < F + 64)) by (intros Hx; exact (proj2 (HFpres11 FL Hx) HFLo11)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 1040%nat) 0 1 0 1 []) HS eq_refl
    ltac:(unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite W71040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp11)
    ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite W71040, W71041, W71028, W72, W734; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* the release (0x8bcc4 .. 0x8bd00: the frame's magic, its shadow f5 x8, the flag byte 0 through frame + 56), the
   epilogue and `ret` *)
pose (RUNF := @aj_flag_store_pi fx2 rc SK cmd_listing PL_cmd PI B LAWS ML AFREE_LAW sii_FFL).
paj_run_flag_sh RUNF HS HJ11.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  destruct Hin as [<- | Hin].
  { right. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite W71040 in Hr. rewrite EFL11. lia. }
  left.
  destruct Hin as [<- | Hin].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite W71041 in Hr.
    right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA11, <- SB_SHADOW_OFF.
    change (fs_frame_bytes 0 / 8) with 8. lia. }
  destruct Hin as [<- | Hin].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. exfalso. lia. }
  destruct Hin as [<- | Hin].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite W71028 in Hr.
    right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA11. change (fs_frame_bytes 0) with 64. lia. }
  destruct Hin as [<- | Hin].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite W72 in Hr. left. rewrite FS. lia. }
  destruct Hin as [<- | Hin].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite W72 in Hr. left. rewrite FS. lia. }
  destruct Hin as [<- | Hin].
  { cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite W734 in Hr. left. rewrite FS. lia. }
  destruct Hin.
- intros msr HSr. rewrite EFL11.
  pose proof (st_ok_pi_region_nth E7 _ _ 0 _ HSr eq_refl) as HR0.
  pose proof (field_of_region E7 _ 1040 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR0 W71040 ltac:(cbn [In]; tauto) eq_refl
    ltac:(lia) ltac:(lia)) as HV.
  specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
- rename ms into ms12, mat into mat12, HF into HFl12, HFr into HFr12, HG into HG12.
  preg HS (1%bv : bv 5) X1r. preg HS (10%bv : bv 5) X10r.
  rewrite sii_denot_off0, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) in X1r by lia.
  rewrite sii_denot_off0, E1126 in X10r.
  (* the recorder's bytes and answer's copy from answer's return to the end *)
  set (KB := fun a : Z => (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
    (exists p0 n0, In (p0, n0) (ablocks B ly11 S11) /\ p0 <= a < p0 + req_size n0)).
  assert (KBLOC : forall a, KB a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\
    ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
  { intros a Ha. destruct Ha as [Ha | [Ha | (p0 & n0 & Hpn & Hpa)]].
    - apply KLOC. left. exact Ha.
    - apply KLOC. right. left. exact Ha.
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HAR11 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres11 & _).
      pose proof (sep_block_frame SEGS B LAWS ly11 S11 W11 mem11 md11 p0 n0 0 fpos HAR11 Hpn Hfin11) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA11 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
      split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
      intros ->. exact (proj2 (Hpres11 FL ltac:(lia)) HFLo11). }
  assert (KF12 : forall a, KB a -> rdW W11 (ms_mem ms12) a = rdW W11 mem11 a).
  { intros a Ha. destruct (KBLOC a Ha) as (Hb & HnF & HnS & HnFL).
    apply (sii_aview_frame_pt E7 _ (w_H W11) mem11 (ms_mem ms12) a HFr12); [lia|].
    nwin_tac ltac:(fun H => rewrite ?W72, ?W734, ?W71028, ?W71040, ?W71041 in H; lia). }
  assert (EABF : ablocks B ly11 (stack_free_state 0 fpos S11) = ablocks B ly11 S11).
  { unfold ablocks. rewrite blocks_stack_free_state. reflexivity. }
  assert (Hq11 : In (p2, Z.of_nat (length t) + 1) (ablocks B ly11 S11)) by (apply Hbl11; right; right; reflexivity).
  eapply (paj_ret_at (PL := PL_cmd) (PI := PI) W11 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_baseF.
  eexists fx2, ly11, (stack_free_state 0 fpos S11), (ms_regs ms12), (ms_mem ms12), _.
  pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  split; [rewrite X1r, Hra'; reflexivity|].
  split; [intros k0 _; reflexivity|].
  split; [left; reflexivity|].
  split.
  { eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ11|].
    unfold EV_SUP_INSTANCE_INFO, EV_REC_SHAPE_OF. lia. }
  split; [eapply (aregs_preserved_of_st_ok SEGS (w_H W11) E7 _ ms12 regs (sii_extra (as_uar_cell B) sp1) HS HAE7);
    vm_compute; reflexivity|].
  pose proof (proj1 HJ11) as HARF.
  eapply (siq_post_of ly S R id O ly4 S4 O1 ly7 S7 ly7 S7 W9 (ms_mem ms10) _ ly11 (stack_free_state 0 fpos S11) W11
    (ms_regs ms12) (ms_mem ms12) _ y p p1 p2 old ((p, n) :: O1) O'
    (fst (rec_answer (rec_record R SII_FN [y]) (SII_FN, [y]) (shape_of sii_verb) false)) t).
  + apply (siq_blk_of_record ly S W mem md O ly4 S4 Fr O1 HAR); [rewrite <- Eab; exact HPermF | exact HFO | exact HO1].
  + exact Hperm7.
  + exact Hfresh7.
  + apply Permutation_refl.
  + exact HAR10.
  + exact HARF.
  + intros pn. split; [intros [H | H]; [right; symmetry; exact H | left; exact H]
    | intros [H | H]; [right; exact H | left; symmetry; exact H]].
  + exact HO2in7.
  + exact HoldO2.
  + exact Hp24096.
  + exact H12.
  + exact Hfr12.
  + rewrite EABF. exact Hbl11.
  + apply (sii_rec_repA_kept B ly11 S11 (rdW W11 mem11) ly11 (stack_free_state 0 fpos S11) (rdW W11 (ms_mem ms12))
      _ O' HREP11).
    * rewrite EABF. exact (sii_rec_repA_in B ly11 S11 _ _ O' HREP11).
    * intros a Ha. apply KF12. left. exact Ha.
    * intros a Ha. apply KF12. right. left. exact Ha.
    * intros p0 n0 i Hpn Hi. apply KF12. right. right. exists p0, n0.
      split; [exact (sii_rec_repA_in B ly11 S11 _ _ O' HREP11 _ Hpn)|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HAR11 (sii_rec_repA_in B ly11 S11 _ _ O' HREP11 _ Hpn))
        as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n0 ltac:(lia)). lia.
  + exact HO'iff.
  + apply (sii_astr_kept (rdW W11 mem11)); [exact Hstr11|]. intros a Ha. apply KF12. right. right.
    exists p2, (Z.of_nat (length t) + 1). split; [exact Hq11|].
    pose proof (req_size_pos (Z.of_nat (length t) + 1) ltac:(lia)). lia.
  + exact X10r.
  + rewrite sii_m. apply surjective_pairing.
  + assert (B12 : blocks_bytes (stack_free_state 0 fpos S11) = bsum (ablocks B ly11 (stack_free_state 0 fpos S11)))
      by apply blocks_bytes_bsum.
    assert (B11 : blocks_bytes S11 = bsum (ablocks B ly11 S11)) by apply blocks_bytes_bsum.
    rewrite B12, EABF, <- B11.
    unfold LIVE_SUP_INSTANCE_INFO. rewrite Ht. unfold t in *. lia.
  + unfold stack_free_state. apply (mo_le_set_fs_r MT MTLF).
    apply (mle_weaken MT S S11 _ _ MTL (mle_station MT S S7 S11 _ _ MTL MLE7' HMLE11)).
    unfold XM_SUP_INSTANCE_INFO. rewrite Ht. unfold t in *. lia.
Qed.

End e.
End f.
End d.

(* the statement at the ambient FP state *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
@asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_frame_flag_law : forall B0, frame_flag_lawP SEGS B0.
Theorem tsup_instance_info_holds : tsup_instance_info_spec B MT.
Proof. apply tsup_instance_info_holds_any; assumption. Qed.
End e2.
End f2.
End d2.
