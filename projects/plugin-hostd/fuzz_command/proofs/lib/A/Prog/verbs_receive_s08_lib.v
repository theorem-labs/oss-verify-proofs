(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the shared part of the segments S08 DGET, S09 PGET and S12 IINFO of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v). Each of the
   three routes tests ntok = 2 (`li a0,2; bne s5,a0,0x8da28`), loads tok[1], calls one recorder function (S12 through
   atoi first) and jumps to the join JB at 0x8dad4. This file holds
   - the reader transports of the boundary facts (a state whose memory reads the same, vr_core_same),
   - the seed of the symbolic state at a route and at a return pc (ss_tok, ss_ret),
   - the refusal exit (vr_pr_build: the step is reject, the recorder untouched),
   - the generic arm vr_call_arm: from the state at the callee's entry (vr_cs) through the callee's contract (the
     recorder-call shape rc_post, its frame chain the achain_push chain of vr_chain: verbs_receive's frame pointer
     sp0 is s0 at every program call) and the jump to 0x8dad4, to vr_hd at 0x8dad4. The meter goes through the
     interface's vri_meter_ok (the call's mo_ok) and vri_meter_step (vr_meter after it): one recorder call spends at
     most 3 mallocs of at most VERBS_RECEIVE_REQ bytes and 1 free, over its EV1 >= 3 events. Since statement pass 4
     the three callees are FP-existential (apost_baseF): the call half vr_call_ret (PaFx's cl_callS_wideF) is proved
     at the caller's FP state fx and returns at some fx' with fxrel fx fx'; vr_call_arm, in the second section block,
     takes the jump (vr_jmp) and the join's state (vr_hd_build) at fx'.
   The record facts are named Section hypotheses (HB, MTL, ROA, RRO, RPG, RECC, PROGU); the read-only
   range is CmdGlob's fixed CMD_RLO / CMD_RHI. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import Setoid Morphisms.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_get_c descriptors_panel_get_c sup_instance_info_c sup_reply_code_c
reply_c socket_send_c sup_after_reply_c arg_i_c xstrdup_c sup_resp_c answer_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain verbs_receive_live PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

(* the symbolic states the walk seeds: at a route, the registers as atoms and tok[1] (8 bytes at s6 + 8) as the
   atom 32; at a return pc, the registers alone *)
Definition ss_tok (pc : Z) : sstate :=
mkSS pc sr_atoms [YP09.mkRegion (Some 22%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []).
Definition ss_ret (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* the text of a recorder stub is at most 28 bytes (the plain proof's verbs_receive_br.v stub_text_len) *)
Lemma stub_len : forall R fn As v ch, -2^31 <= r_code R < 2^31 ->
(length (snd (rec_stub R fn As (shape_of v) ch)) <= 28)%nat.
Proof.
intros R fn As v ch HC. unfold rec_stub. rewrite rec_answer_text.
assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (r_refuse (rec_record R fn As) =? 0).
- exact (proj1 (proj2 (shape_of_facts v))).
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.
Lemma spill_frees0 : forall R, r_calls R = [] -> rec_spill_frees R = 0.
Proof. intros R H. unfold rec_spill_frees. rewrite H. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Readers that read the same *)
Definition rdeq (rd rd' : reader) : Prop := forall a, rd' a = rd a.

Lemma aval_mem_eq : forall rd rd' a n v, rdeq rd rd' -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma abytes_atR_eq : forall rd rd' a l, rdeq rd rd' -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l E H i Hi. rewrite E. exact (H i Hi). Qed.
Lemma astr_atR_eq : forall rd rd' a s, rdeq rd rd' -> astr_atR rd a s -> astr_atR rd' a s.
Proof. intros rd rd' a s E [H1 H2]. split; [exact (abytes_atR_eq rd rd' a _ E H1) | exact H2]. Qed.
Lemma rdword_eq : forall rd rd' a, rdeq rd rd' -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a E. apply rdword_ext. intros k _. apply E. Qed.
Lemma rd32_eq : forall rd rd' a v, rdeq rd rd' -> rd32 rd a v -> rd32 rd' a v.
Proof. intros rd rd' a v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma atoks_atA_eq : forall rd rd' tok ptrs tks cb ncb, rdeq rd rd' ->
atoks_atA rd tok ptrs tks cb ncb -> atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb E (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros i p Hp. exact (aval_mem_eq rd rd' _ 8 p E (H3 i p Hp)).
- intros i p w Hp Hw. destruct (H4 i p w Hp Hw) as (A1 & A2 & A3 & A4).
  split; [exact (astr_atR_eq rd rd' p w E A1) | auto].
Qed.
Lemma cmd_got_ok_eq : forall rd rd', rdeq rd rd' -> cmd_got_ok rd -> cmd_got_ok rd'.
Proof.
intros rd rd' E (H1 & H2 & H3 & H4).
split; [exact (aval_mem_eq _ _ _ _ _ E H1)|]. split; [exact (aval_mem_eq _ _ _ _ _ E H2)|].
split; [exact (aval_mem_eq _ _ _ _ _ E H3) | exact (aval_mem_eq _ _ _ _ _ E H4)].
Qed.
Lemma cmd_ro_ok_eq : forall rd rd', rdeq rd rd' -> cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' E [Hb Ht]. split.
- unfold cmd_ro_bytes in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply abytes_atR_eq; [exact E | eassumption]).
- intros e' He a Ha. rewrite E. exact (Ht e' He a Ha).
Qed.

(* the 8-byte value of aval_mem, as rdword reads it *)
Lemma rdword_of_aval : forall (rd : reader) a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v H Hr. unfold rdword.
assert (B0 : rd a = Some (le_byte v 8 0)) by (rewrite <- (Z.add_0_r a) at 1; exact (H 0%nat ltac:(lia))).
change (rd (a + 1)) with (rd (a + Z.of_nat 1)). change (rd (a + 2)) with (rd (a + Z.of_nat 2)).
change (rd (a + 3)) with (rd (a + Z.of_nat 3)). change (rd (a + 4)) with (rd (a + Z.of_nat 4)).
change (rd (a + 5)) with (rd (a + Z.of_nat 5)). change (rd (a + 6)) with (rd (a + Z.of_nat 6)).
change (rd (a + 7)) with (rd (a + Z.of_nat 7)).
rewrite B0, (H 1%nat), (H 2%nat), (H 3%nat), (H 4%nat), (H 5%nat), (H 6%nat), (H 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma val_mem_of_aval : forall H mem a n v, aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

Lemma arodata_okP_eq : forall rd rd', rdeq rd rd' -> arodata_okP SEGS RLO RHI B rd -> arodata_okP SEGS RLO RHI B rd'.
Proof. intros rd rd' E H a H1 H2 H3. rewrite E. exact (H a H1 H2 H3). Qed.

Lemma vr_env_same : forall W mem W' mem', rdeq (rdW W mem) (rdW W' mem') ->
vr_env B W mem -> vr_env B W' mem'.
Proof.
intros W mem W' mem' E (H1 & H2 & H3 & (G1 & c & G2) & H5 & ev & H6).
split; [exact (arodata_okP_eq _ _ E H1)|]. split; [exact (cmd_got_ok_eq _ _ E H2)|].
split; [exact (cmd_ro_ok_eq _ _ E H3)|].
split; [split; [rewrite (rdword_eq _ _ _ E); exact G1 | exists c; rewrite (rdword_eq _ _ _ E); exact G2]|].
split; [rewrite E; exact H5 | exists ev; exact (rd32_eq _ _ _ _ E H6)].
Qed.

Lemma vr_core_same : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md W' regs' mem' md',
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W' mem' md' k ->
rdeq (rdW W mem) (rdW W' mem') ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W' regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md W' regs' mem' md'
(HJ & Hk & Hm & Hnm & (HF1 & HF2 & HF3) & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq) HJ' E Hrv'.
split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|].
split; [split; [exact HF1|]; split; [rewrite (rdword_eq _ _ _ E); exact HF2 | intros i Hi; rewrite E; exact (HF3 i Hi)]|].
split; [exact Hrv'|].
split; [intros j r Hj; exact (aval_mem_eq _ _ _ _ _ E (Hsv j r Hj))|].
split; [unfold vr_spill in *; eapply Forall_impl; [|exact Hsp]; intros ov Hov; exact (aval_mem_eq _ _ _ _ _ E Hov)|].
split; [exact (vr_env_same W mem W' mem' E Henv)|].
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)); intros; apply E. }
split; [exact Hdat|]. split; [exact Hperm | exact (aval_mem_eq _ _ _ _ _ E Hq)].
Qed.

Lemma vr_line_same : forall e q W mem W' mem', rdeq (rdW W mem) (rdW W' mem') ->
vr_line B e q W mem -> vr_line B e q W' mem'.
Proof. intros e q W mem W' mem' E [H1 H2]. split; [exact H1 | exact (astr_atR_eq _ _ _ _ E H2)]. Qed.
Lemma vr_copy_same : forall e F c tp W mem W' mem', rdeq (rdW W mem) (rdW W' mem') ->
vr_copy B e F c tp W mem -> vr_copy B e F c tp W' mem'.
Proof. intros e F c tp W mem W' mem' E [H1 H2]. split; [exact H1 | exact (atoks_atA_eq _ _ _ _ _ _ _ E H2)]. Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The record facts (names and types as the assembly collects them) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------------------------------------------------------------------------------------------------------------
   What a recorder call keeps: its footprint is g_rec, record.spill and the recorder's blocks *)
Definition fp1 (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma fp1_cases : forall O a, inFP (fp1 O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a H. unfold fp1 in H. apply inFP_cons in H as [H|H]; [left; exact H|].
apply inFP_cons in H as [H|H]; [right; left; exact H|]. right; right. exact (inFP_ablocks_fp_inv O a H).
Qed.
Lemma inFP_PG_rec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma inFP_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.
Lemma inFP_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn; lia]. Qed.

Lemma O_pos : forall ly S (W : world SEGS) mem md (O : list (Z * Z)), AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> Forall (fun pn => 0 < fst pn) O.
Proof.
intros ly S W mem md O HAR HO. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hin)) as (_ & H4 & _). cbn. lia.
Qed.
Lemma fp1_closed : forall O, Forall (fun pn => 0 < fst pn) O -> ~ YI16.sink_open_fp (fp1 O).
Proof.
intros O HO. unfold fp1. apply sink_closed_cons; [unfold A_G_REC; cbn; lia|].
apply sink_closed_cons; [unfold A_REC_SPILL; cbn; lia|]. apply sink_closed_ablocks_fp. exact HO.
Qed.

Section ck.
Variables (O : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (STK1 sp1 : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte) (md2 : Model) (k1 : Z).
Hypothesis HAR : AR SEGS B lyc Sc W mem md.
Hypothesis HJc : ajournal SEGS B STK1 sp1 (fp1 O) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 k1.
Hypothesis HO : forall pn, In pn O -> In pn (ablocks B lyc Sc).

Lemma ck_stack : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) -> rdW W2 mem2 a = rdW W mem a.
Proof.
intros a Ha Hw. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [exact Ha | exact Hw |]. pose proof asan_consts as (C1 & _).
intros Hf. destruct (fp1_cases O a Hf) as [G|[G|(p & n & Hpn & Hr)]].
- unfold A_G_REC, REC_SIZE in G. lia.
- unfold A_REC_SPILL, SC_SIZE in G. lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma ck_block : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) O ->
0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i).
Proof.
intros p n i H1 H2 HnO Hi. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i H1 H2 Hi). intros Hf.
assert (Himg : ~ in_img SEGS (p + i)) by exact (blk_img SEGS B LAWS _ _ _ _ _ p n (p + i) HAR H1 ltac:(lia)).
destruct (fp1_cases O _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
- exact (Himg (proj1 (PROGU _ (inFP_PG_rec _ G)))).
- exact (Himg (proj1 (PROGU _ (inFP_PG_spill _ G)))).
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (HnO Hbm)).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md b m p n HAR (HO _ Hbm) H1 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma ck_frame : forall cid pos a, In (cid, pos) (frames Sc) ->
(frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
 shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
rdW W2 mem2 a = rdW W mem a.
Proof.
intros cid pos a Hin Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin); [unfold frame_rng, in_zr; cbn [fst snd]; lia |].
intros Hf. pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as Hdl.
destruct Ha as [Ha | Ha].
- assert (Himg : ~ in_img SEGS a) by exact (frm_img SEGS B LAWS lyc Sc W mem md cid pos a HAR Hin Ha).
  destruct (fp1_cases O _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
  + exact (Himg (proj1 (PROGU _ (inFP_PG_rec _ G)))).
  + exact (Himg (proj1 (PROGU _ (inFP_PG_spill _ G)))).
  + pose proof (sep_block_frame SEGS B LAWS lyc Sc W mem md b m cid pos HAR (HO _ Hbm) Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as Hdp.
  destruct (fp1_cases O _ Hf) as [G|[G|(b & m & Hbm & Hr)]].
  + unfold shadow_addr, SHADOW_OFF, A_G_REC, REC_SIZE in *. lia.
  + unfold shadow_addr, SHADOW_OFF, A_REC_SPILL, SC_SIZE in *. lia.
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HO _ Hbm)) as (_ & _ & _ & Happ & _).
    apply (fshadow_not_app (frame_addr lyc cid pos) (fs_frame_bytes cid / 8) b (req_size m) a); [lia | lia | exact Happ | | exact Hr].
    unfold shadow_addr, SHADOW_OFF in Ha. lia.
Qed.

Lemma ck_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ (A_G_REC <= a < A_G_REC + REC_SIZE) -> ~ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
rdW W2 mem2 a = rdW W mem a.
Proof.
intros a Himg Ho He Hg Hs. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply (F3 a Himg Ho He). apply fp_spares_closed; [exact (fp1_closed O (O_pos lyc Sc W mem md O HAR HO))|].
intros Hf. destruct (fp1_cases O _ Hf) as [G|[G|(b & m & Hbm & Hr)]]; [exact (Hg G) | exact (Hs G) |].
exact (blk_img SEGS B LAWS lyc Sc W mem md b m a HAR (HO _ Hbm) Hr Himg).
Qed.

Lemma ck_arodata : arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W2 mem2).
Proof.
intros HR a Hro Ho He.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
rewrite (ck_img a Himg Ho He); [exact (HR a Hro Ho He) | |].
- intros G. exact (RPG a (inFP_PG_rec a G) Hro).
- intros G. exact (RPG a (inFP_PG_spill a G) Hro).
Qed.

Lemma ck_quit : forall v, aval_mem (rdW W mem) A_G_QUITTING 4 v -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 v.
Proof.
intros v Hq kk Hk.
assert (Ha : A_G_QUITTING <= A_G_QUITTING + Z.of_nat kk < A_G_QUITTING + 4) by lia.
destruct (PROGU _ (inFP_PG_quit _ Ha)) as (Hi & Ho & He).
rewrite (ck_img _ Hi Ho He); [exact (Hq kk Hk) | |].
- unfold A_G_QUITTING, A_G_REC, REC_SIZE. lia.
- unfold A_G_QUITTING, A_REC_SPILL, SC_SIZE. lia.
Qed.
End ck.

(* ---------------------------------------------------------------------------------------------------------------
   Small facts *)
Lemma vr_rv_get : forall regs l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma vr_rv_intro : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
Lemma vr_s1_cases : forall e, vr_sp0 e mod 16 = 0 -> vr_s1 e = vr_sp0 e - 192 \/ vr_s1 e = vr_sp0 e - 208.
Proof.
intros e H. unfold vr_s1. pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as M2.
rewrite H in D1. lia.
Qed.
Lemma find0_upto0n : forall M : list byte,
match StrFun.find_byte 0 M with Some i => i | None => length M end = length (Verbs.upto0 M).
Proof.
unfold Verbs.upto0. induction M as [|b M IH]; [reflexivity|].
cbn [StrFun.find_byte Verbs.upto]. destruct (bv_unsigned b =? 0); [reflexivity|].
destruct (StrFun.find_byte 0 M) as [i|] eqn:Fb; try rewrite Fb in IH; cbn; lia.
Qed.
Lemma line_le_strnlen : forall D n, Z.of_nat (length D) = n -> Z.of_nat (length (Verbs.line D)) <= StrFun.strnlen_res n D.
Proof.
intros D n <-. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all.
assert (L : (length (Verbs.line D) <= length (Verbs.upto0 D))%nat).
{ unfold Verbs.line, Verbs.trim. rewrite length_rev.
  pose proof (verbs_receive_route.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as H1. rewrite length_rev in H1. exact H1. }
pose proof (find0_upto0n D) as E. destruct (StrFun.find_byte 0 D) as [i|]; lia.
Qed.
Lemma nodup_of_pw : forall l : list (Z * Z), Forall (fun b => 0 <= snd b) l ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hnn Hpw; [constructor|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hx Hl]. inversion Hnn as [|? ? Hx0 Hl0]; subst.
constructor; [|exact (IH Hl0 Hl)].
intros Hin. rewrite Forall_forall in Hx.
pose proof (Hx (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) l x Hin)) as Hd.
pose proof (req_size_pos (snd x) Hx0). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma nodup_app_r : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros A l1. induction l1 as [|x l1 IH]; intros l2 H; [exact H|]. cbn in H. apply NoDup_cons_iff in H as [_ Hd].
exact (IH _ Hd).
Qed.
Lemma nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x H Hx; [destruct Hx|]. cbn in H. apply NoDup_cons_iff in H as [Hn Hd].
destruct Hx as [<- | Hx]; [intros H'; apply Hn; apply in_or_app; right; exact H' | exact (IH _ _ Hd Hx)].
Qed.
Lemma nodup_app_intro : forall {A} (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
List.NoDup (l1 ++ l2).
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. apply NoDup_cons_iff in H1 as [Hn H1].
cbn. apply NoDup_cons_iff. split.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hn Hin) | exact (Hd y (or_introl eq_refl) Hin)].
- apply IH; [exact H1 | exact H2 | intros x Hx; apply Hd; right; exact Hx].
Qed.
Lemma nodup_ablocks : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply nodup_of_pw.
- apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn. lia.
- destruct (ablocks B ly S) as [|[p n] l] eqn:E; [exact I|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR ltac:(rewrite E; left; reflexivity)) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite E in Hpw. exact Hpw.
Qed.
Lemma aval_of_abytes8 : forall rd a l v, abytes_atR rd a l -> length l = 8%nat ->
(forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hkk. rewrite (H k ltac:(lia)). rewrite (Hk k Hkk). reflexivity. Qed.
Lemma cmd_got_ok_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb.
assert (G1 : abytes_atR rd 0xa7068 RO_ptr_a7068) by (decompose [and] Hb; assumption).
assert (G2 : abytes_atR rd 0xa7070 RO_ptr_a7070) by (decompose [and] Hb; assumption).
assert (G3 : abytes_atR rd 0xa7078 RO_ptr_a7078) by (decompose [and] Hb; assumption).
assert (G4 : abytes_atR rd 0xa7080 RO_ptr_a7080) by (decompose [and] Hb; assumption).
unfold cmd_got_ok.
split; [apply (aval_of_abytes8 rd _ _ _ G1 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
split; [apply (aval_of_abytes8 rd _ _ _ G2 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
split; [apply (aval_of_abytes8 rd _ _ _ G3 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
apply (aval_of_abytes8 rd _ _ _ G4 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.
Lemma vr_k1_ev : forall R D, vr_k1 R D + 5 <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2, ev_after, EV_REPLY, EV_SOCKET_SEND.
destruct (vr_aft D) as [[i v]|]; [|lia].
unfold EV_SUP_AFTER_REPLY, rec_spill_frees, EV_ARG_I, EV_XSTRDUP. destruct (Nat.ltb _ _); lia.
Qed.

(* the frame record at the entry sp: the saved ra and s0, and the caller's chain above *)
Lemma vr_chain : forall e pos lyc Sc W mem md k sp',
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md k ->
vr_saved e W mem -> sp' + 16 <= vr_sp0 e ->
exists ch1, achain lyc (rdW W mem) sp' (vr_sp0 e) ch1.
Proof.
intros e pos lyc Sc W mem md k sp' Hent HJ Hsv Hsp'.
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec0 & _).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (Hk : forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW W mem a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. apply F1; [lia | lia |].
  intros (r & Hr & Hra). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - unfold VERBS_RECEIVE_PG in Hr. cbn in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn in Hra;
    unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hra; lia.
  - apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn in Hra.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec0 Hpn) as Hb.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hb) as (_ & _ & Hc & _). lia. }
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW W mem) (vr_sp0 e) (s0Z (e_regs e)) (raZ (e_regs e)) (e_ch e) sp' Hch0).
  + lia.
  + intros a Ha. exact (Hk a Ha).
  + apply rdword_of_aval; [|unfold raZ; apply bv_unsigned_in_range].
    replace (vr_sp0 e - 8) with (vr_sp0 e - 8 - 8 * Z.of_nat 0) by lia. exact (Hsv 0%nat 1 eq_refl).
  + apply rdword_of_aval; [|unfold s0Z; apply bv_unsigned_in_range].
    replace (vr_sp0 e - 16) with (vr_sp0 e - 8 - 8 * Z.of_nat 1) by lia. exact (Hsv 1%nat 8 eq_refl).
  + exact Hra40.
  + lia.
  + apply Z.mod_divide; [lia|]. pose proof Hal16 as H16. apply Z.mod_divide in H16; [|lia].
    destruct H16 as [z Hz]. exists (2 * z). lia.
  + exact Hlt.
  + exact Hsp'.
- exists []. left. split; [right; left; rewrite Etop; exact Hge | reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The state at a callee's entry (after the `jal`): vr_core of the route with ra, a0, s2 and s6 named, the line and
   the copy *)
Definition vr_cs (e : vrE) (pos F q c x retk : Z) (tp : list Z) (lyc : alayout) (Sc : astate) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k nm : Z) : Prop :=
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(1, BASE + retk); (10, x); (18, q); (22, F + 32)] (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md /\
vr_line B e q W mem /\ vr_copy B e F c tp W mem.

(* the post of a recorder call that returns a text (descriptors_get_c.v:92-108 and its siblings) *)
Definition rc_post (R : rstate) (O : list (Z * Z)) (m : rstate * list byte) (XM1 LIVE1 : Z) (ly : alayout) (S : astate)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 m = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE1 /\
 mo_le MT S S' XM1.

(* the refusal stub's state at 0x8da28 from the route's, the step being reject *)
Lemma vr_pr_build : forall e W pos F q c tp lyc Sc regs mem md k nm,
vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
Verbs.toks (e_D e) <> [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) [(18, q); (21, vr_ntok (e_D e)); (22, F + 32)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
vr_pr B MT e 0x8da28 W (cfg_at SEGS (vr_pc 0x8da28) regs mem md).
Proof.
intros e W pos F q c tp lyc Sc regs mem md k nm Hvh Hk1 Hne Hcore Hline Hcopy.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, regs, mem, md, k, nm.
split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|]. split; [exact Hvh|]. split; [exact Hne|].
split; [unfold vr_pr_ntok; change (0x8da28 =? 0x8dacc) with false; cbv beta iota;
  destruct (Verbs.toks (e_D e)); [congruence | cbn [length]; lia]|].
split; [|split; [exact Hline | exact Hcopy]].
replace (vr_rl_pr e F q c 0x8da28 (-902)) with [(18, q); (21, vr_ntok (e_D e)); (22, F + 32)] by reflexivity.
destruct Hcore as (H1 & H2 & H3 & H4 & H5).
split; [exact H1|]. split; [rewrite Hk1; unfold EV_SUP_RESP, EV_XSTRDUP; lia|]. split; [exact H3|].
split; [unfold VR_NM_PR, VR_NM_PRE in *; lia | exact H5].
Qed.

(* the join JB at 0x8dad4 after the recorder call *)
Lemma vr_hd_build : forall e W pos F q c x retk tp lyc Sc regs mem md k nm STK1 EV1 XM1 LIVE1 (m : rstate * list byte)
  W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3,
vr_ent B MT e ->
vr_cs e pos F q c x retk tp lyc Sc W regs mem md k nm ->
length (Verbs.toks (e_D e)) = 2%nat ->
vr_h (e_R e) (e_D e) = (m, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
3 <= EV1 -> XM1 <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
ajournal SEGS B STK1 (vr_s1 e) (fp1 (e_O e)) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
aregs_preserved regs regs2 ->
rc_post (e_R e) (e_O e) m XM1 LIVE1 lyc Sc ly2 S2 W2 regs2 mem2 md2 ->
(forall r, getr regs3 r = getr regs2 r) -> rdeq (rdW W2 mem2) (rdW W2 mem3) ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem3 md3 (k + EV1) ->
vr_hd B MT e 0x8dad4 W2 (cfg_at SEGS (vr_pc 0x8dad4) regs3 mem3 md3).
Proof.
intros e W pos F q c x retk tp lyc Sc regs mem md k nm STK1 EV1 XM1 LIVE1 m W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3
  Hent Hcs Hlen Hvh Hk1 HEV1 HXM1 HST0 HSTK1 HJc HP HK Er Em HJ3.
destruct Hcs as (Hcore & Hline & Hcopy).
destruct Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnotO & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & _).
pose proof HJc as (HAR2 & Hly2 & _).
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (HO : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
pose proof (ck_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO) as KS.
pose proof (ck_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO) as KB.
pose proof (ck_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO) as KF.
pose proof (ck_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO) as KA.
pose proof (ck_quit _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HJc HO) as KQ.
destruct HK as (R' & t & qq & O' & Em' & Ha0 & Hq4096 & Hrec' & HO'1 & Hqin & Hqnot & HqnotO' & Hstr & Hkeep & Hall
  & _ & Hmle).
destruct Hrec' as (Q' & HarQ & HOQ).
assert (EX : vr_x (e_R e) (e_D e) = t) by (unfold vr_x; rewrite Hvh, Em'; reflexivity).
assert (ER1 : vr_R1 (e_R e) (e_D e) = R') by (unfold vr_R1; rewrite Hvh, Em'; reflexivity).
assert (EQV : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hvh; reflexivity).
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Efr : frame_addr ly2 4 pos = frame_addr lyc 4 pos)
  by (unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos)
  by (unfold flag_addr; destruct Hly2 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e))
  by (pose proof (Permutation_in _ Hperm0 HinD) as H0; apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]).
set (T0 := [vr_lb e q; vr_cb e c] ++ e_rest e) in *.
assert (HndOT : List.NoDup (e_O e ++ T0)) by exact (Permutation_NoDup Hperm (nodup_ablocks _ _ _ _ _ HAR)).
assert (HinT0 : forall y, In y T0 -> In y (ablocks B lyc Sc) /\ ~ In y (e_O e)).
{ intros y Hy. split.
  - apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hy.
  - intros Hy2. exact (nodup_app_disj _ _ y HndOT Hy2 Hy). }
assert (HFsz : fs_frame_bytes 4 = 1024) by reflexivity.
unfold vr_hd. exists qq, (lay_blocks Q'), pos, F, q, c, tp, ly2, S2, regs3, mem3, md3, (k + EV1), (nm + 3).
split; [reflexivity|].
split; [unfold vr_hd_ntok; rewrite Hlen; simpl; lia|].
split; [lia|].
split; [rewrite EX; exact (astr_atR_eq _ _ _ _ Em Hstr)|].
split.
{ rewrite ER1, EQV, EX. unfold vr_core.
  replace (vr_rl_hd e F q c 0x8dad4 qq) with [(10, qq); (18, q); (22, F + 32)] by reflexivity.
  split; [exact HJ3|].
  split; [rewrite Hk1; lia|].
  (* the meter after the call (one recorder call: at most 3 mallocs and 1 free, EV1 >= 3 events) *)
  split; [exact (vri_meter_step MT e Sc S2 k nm XM1 3 1 EV1 MTL Hmet Hmle ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [unfold VR_NM_HD, VR_NM_PRE in *; lia|].
  split.
  { destruct Hfr as (EF & HF2 & HF3).
    split; [rewrite Efr; exact EF|].
    split.
    - rewrite (rdword_eq _ _ _ Em), Efl, <- HF2. apply rdword_ext. intros kk Hkk.
      apply (KF 4 pos _ HinF). left. rewrite <- EF, HFsz. lia.
    - intros i Hi. rewrite Em. rewrite (KF 4 pos _ HinF); [exact (HF3 i Hi)|].
      right. rewrite <- EF, HFsz. change (1024 / 8) with 128. lia. }
  split.
  { apply vr_rv_intro. intros r v Hin. rewrite Er.
    apply in_app_or in Hin as [Hin | Hin].
    - unfold vr_base in Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
      (match goal with |- getr _ (Z_to_bv 5 ?r) = _ => rewrite (HP r ltac:(unfold acallee_saved; lia)) end;
       apply (vr_rv_get regs _ _ _ Hrv); apply in_or_app; left; cbn; tauto).
    - cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; [exact Ha0 | |];
      (match goal with |- getr _ (Z_to_bv 5 ?r) = _ => rewrite (HP r ltac:(unfold acallee_saved; lia)) end;
       apply (vr_rv_get regs _ _ _ Hrv); apply in_or_app; right; cbn; tauto). }
  split.
  { intros j r Hj. pose proof (Hsv j r Hj) as H.
    assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length vr_saved_regs] in Hj13.
    intros kk Hkk. rewrite Em, KS; [exact (H kk Hkk) | lia | lia]. }
  split.
  { unfold vr_spill in *. apply Forall_forall. intros [off v] Hin. rewrite Forall_forall in Hsp. pose proof (Hsp _ Hin) as H.
    cbn [fst snd] in H |- *.
    assert (Hoff : 8 <= off <= 72).
    { unfold vr_sl3 in Hin. cbn in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
    intros kk Hkk. rewrite Em, KS; [exact (H kk Hkk) | lia | lia]. }
  split.
  { destruct Henv as (HR1 & _).
    assert (HR3 : arodata_okP SEGS RLO RHI B (rdW W2 mem3)) by exact (arodata_okP_eq _ _ Em (KA HR1)).
    assert (HAR3 : AR SEGS B ly2 S2 W2 mem3 md3) by exact (proj1 HJ3).
    assert (HRO3 : cmd_ro_ok (rdW W2 mem3)) by exact (ROA ly2 S2 W2 mem3 md3 HAR3 HR3).
    destruct (RECC ly2 S2 W2 mem3 md3 HAR3) as (Hfl & Hgd & Herr).
    split; [exact HR3|]. split; [exact (cmd_got_ok_of_ro _ HRO3)|]. split; [exact HRO3|].
    split; [exact Hgd|]. split; [exact Hfl | exact Herr]. }
  split.
  { exists Q'. split.
    - apply (arep_at_agree (ablocks B ly2 S2) (ablocks B ly2 S2) (rdW W2 mem2) (rdW W2 mem3) A_G_REC A_REC_SPILL R' Q' HarQ);
      [intros pn _ Hb; exact Hb | intros; apply Em | intros; apply Em | intros; apply Em].
    - intros pn. split; intros H; exact H. }
  split.
  { intros Hin. apply HOQ in Hin. destruct (HO'1 _ Hin) as [H|H]; [exact (Hdat H)|]. apply H.
    apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. exact HinR. }
  split.
  { change ([(qq, Z.of_nat (length t) + 1); vr_lb e q; vr_cb e c] ++ e_rest e) with ((qq, Z.of_nat (length t) + 1) :: T0).
    apply NoDup_Permutation.
    - exact (nodup_ablocks _ _ _ _ _ HAR2).
    - apply nodup_app_intro.
      + destruct HarQ as (_ & _ & _ & _ & _ & _ & _ & (Hnd & _)).
        first [exact (NoDup_map_inv _ _ Hnd) | exact (NoDup_map_inv _ _ (proj1 (NoDup_ListNoDup _) Hnd))].
      + constructor; [intros Hin; destruct (HinT0 _ Hin) as [H1 H2]; exact (Hqnot _ H1 H2 eq_refl)
                     | exact (nodup_app_r _ _ HndOT)].
      + intros y Hy Hy2. apply HOQ in Hy. destruct Hy2 as [<- | Hy2].
        * apply HqnotO'. apply in_map_iff. exists (qq, Z.of_nat (length t) + 1). split; [reflexivity | exact Hy].
        * destruct (HinT0 _ Hy2) as [H1 H2]. destruct (HO'1 _ Hy) as [H3|H3]; [exact (H2 H3) | exact (H3 H1)].
    - intros y. split.
      + intros Hy. destruct (Hall y Hy) as [(H1 & H2) | [H1 | H1]].
        * apply in_or_app; right; right. pose proof (Permutation_in _ Hperm H1) as H3.
          apply in_app_or in H3 as [H3|H3]; [contradiction | exact H3].
        * apply in_or_app; left. apply HOQ. exact H1.
        * apply in_or_app; right; left. symmetry. exact H1.
      + intros Hy. apply in_app_or in Hy as [Hy | [Hy | Hy]].
        * apply HOQ in Hy. exact (rec_repA_in_blocks B _ _ _ _ _ _ (ex_intro _ Q' (conj HarQ HOQ)) Hy).
        * rewrite <- Hy. exact Hqin.
        * destruct (HinT0 _ Hy) as [H1 H2]. exact (proj1 (Hkeep _ H1 H2)). }
  exact (aval_mem_eq _ _ _ _ _ Em (KQ _ Hq)). }
split.
{ destruct Hline as (Hfl & Hls). split; [exact Hfl|].
  apply (astr_atR_eq _ _ _ _ Em).
  destruct (HinT0 (vr_lb e q) ltac:(left; reflexivity)) as [H1 H2]. pose proof (proj1 (Hkeep _ H1 H2)) as H3.
  unfold vr_lb in H1, H2, H3.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR H1) as (_ & _ & _ & _ & _ & _ & Hn1).
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrs.
  apply (astr_atR_agree (rdW W mem) (rdW W2 mem2) q (Verbs.line (e_D e)) (vr_l (e_n e) (e_D e) + 1) Hls).
  - pose proof (line_le_strnlen (e_D e) (e_n e) HlenD). unfold vr_l. lia.
  - intros kk Hkk. apply (KB q (vr_l (e_n e) (e_D e) + 1) kk H1 H3 H2). lia. }
{ destruct Hcopy as (Hfc & (Hmod & HlenP & Hptr & Hw)). split; [exact Hfc|].
  apply (atoks_atA_eq _ _ _ _ _ _ _ Em).
  destruct Hfr as (EF & _).
  split; [exact Hmod|]. split; [exact HlenP|]. split.
  - intros i p Hp. pose proof (Hptr i p Hp) as H.
    assert (Hi : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hp; discriminate).
    rewrite HlenP, Hlen in Hi.
    intros kk Hkk. rewrite (KF 4 pos _ HinF); [exact (H kk Hkk)|]. left. rewrite <- EF, HFsz. lia.
  - intros i p w Hp Hwi. destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
    split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
    destruct (HinT0 (vr_cb e c) ltac:(right; left; reflexivity)) as [H1 H2]. pose proof (proj1 (Hkeep _ H1 H2)) as H3.
    unfold vr_cb in H1, H2, H3.
    pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
    apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) A1); [lia|].
    intros kk Hkk. replace (p + kk) with (c + (p - c + kk)) by lia.
    apply (KB c _ (p - c + kk) H1 H3 H2). lia. }
Qed.

Lemma strnlen_le : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof.
intros n D Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The call half of the generic arm: from the callee's entry through its contract (CALL, an FP-existential post,
   CmdBase.v apost_baseF) to its return at some FP state fx' with fxrel fx fx'. The callee's live-bytes premise
   comes from verbs_receive_live.v's vr_live_le (the entry's recorder holds no call), its rounding mode 0 from
   vr_ent's last conjunct (vr_ent_frm0). The rest of the arm runs at fx': vr_call_arm, in the section below. *)
Lemma vr_ent_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e He. unfold vr_ent in He. cbv zeta in He.
repeat lazymatch type of He with _ /\ _ => apply proj2 in He end. exact He.
Qed.
Lemma vr_call_ret : forall e W pos F q c x retk tp lyc Sc regs mem md k nm AF STK1 EV1 XM1 LIVE1 (m : rstate * list byte),
vr_ent B MT e ->
vr_cs e pos F q c x retk tp lyc Sc W regs mem md k nm ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
3 <= EV1 -> XM1 <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT -> LIVE1 <= 20 * VERBS_RECEIVE_REQ ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regs mem md ch -> frm0 fx ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
  rec_repA B lyc Sc (rdW W mem) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 8 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE1 <= LIVE_MAX -> mo_ok MT Sc XM1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (apost_baseF SEGS B STK1 (fp1 (e_O e)) regs lyc Sc W mem md EV1 (rc_post (e_R e) (e_O e) m XM1 LIVE1 lyc Sc))) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
(fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
 c2 = mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\ fxrel fx fx' /\
 ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
   ly2 S2 W2 mem2 md2 (k + EV1) /\
 ajournal SEGS B STK1 (vr_s1 e) (fp1 (e_O e)) lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 /\
 aregs_preserved regs regs2 /\ rc_post (e_R e) (e_O e) m XM1 LIVE1 lyc Sc ly2 S2 W2 regs2 mem2 md2).
Proof.
intros e W pos F q c x retk tp lyc Sc regs mem md k nm AF STK1 EV1 XM1 LIVE1 m
  Hent Hcs Hk1 HEV1 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 CALL.
pose proof Hcs as (Hcore & Hline & Hcopy).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & Hrec0 & Hcalls & _ & _ & _ & _
  & Hperm0 & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm0 & Hev0 & Hlive0 & Hmok0).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & _).
pose proof (vr_s1_cases e Hal16) as Hs1.
assert (R1 : getr regs 1 = Z_to_bv 64 (BASE + retk))
  by (apply (vr_rv_get regs _ 1 _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (vr_rv_get regs _ 8 _ Hrv); apply in_or_app; left; cbn; tauto).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = vr_sp0 e) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (vr_chain e pos lyc Sc W mem md k (vr_s1 e) Hent HJ Hsv ltac:(lia)) as (ch1 & Hch1).
assert (HO : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn)).
(* the meter allows the call: k <= 2 events so far, the call's EV1 more, within the route's ev_vr *)
pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmm.
pose proof (mo_free_nonneg MT MTL) as Hmf.
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hkev.
assert (Ho16 : (vr_s1 e - vr_sp0 e) mod 16 = 0)
  by (destruct Hs1 as [E|E]; rewrite E; [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia
      | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia]; reflexivity).
(* the live bytes now: the entry's, the recorder's (no call yet) and the line and copy blocks *)
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) + 10 * VERBS_RECEIVE_REQ).
{ pose proof (vr_live_le SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) lyc Sc W mem md (rdW W mem) (e_R e)
    (e_O e) (e_O e) [vr_lb e q; vr_cb e c] (e_rest e) HAR0 HAR Hperm0 Hperm Hrec) as HL.
  rewrite Hcalls in HL. cbn [length Z.of_nat] in HL. rewrite !bsum_cons in HL. unfold bsum in HL. cbn [fold_right] in HL.
  unfold vr_lb, vr_cb, vr_l in HL. cbn [snd] in HL.
  pose proof (strnlen_le (e_n e) (e_D e) ltac:(lia)) as Hsl.
  pose proof (line_le_strnlen (e_D e) (e_n e) HlenD) as Hll.
  unfold LMAX, VERBS_RECEIVE_REQ in *. lia. }
unfold cfg_at, w64.
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS W regs mem _ VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc md k STK1 (fp1 (e_O e)) EV1 (vr_s1 e - vr_sp0 e) (Z_to_bv 64 (BASE + retk)) ch1
    (rc_post (e_R e) (e_O e) m XM1 LIVE1 lyc Sc) HJ).
  - rewrite Hsp1. lia.
  - exact Ho16.
  - lia.
  - exact HST0.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { apply (CALL ch1 HPRE1 (vr_ent_frm0 e Hent)).
      - exact (proj1 Henv).
      - exact (proj1 (proj2 (proj2 Henv))).
      - exact Hrec.
      - rewrite Hfrs. cbn [length app]. lia.
      - lia.
      - unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
      - exact (vri_meter_ok B MT e Sc k nm XM1 3 1 EV1 MTL Hent Hmet ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR & HC & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR|]. split; [exact HC|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. destruct (fp1_cases (e_O e) a Ha) as [G|[G|(p & n & Hpn & Hr)]].
    + right; right; right; right; left. split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (inFP_PG_rec a G)))].
      rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_hd.
      unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
    + right; right; right; right; left. split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
        [unfold vr_fp, VERBS_RECEIVE_PG; apply in_or_app; left; right; left; reflexivity | exact G]|].
      split; [|exact (proj1 (PROGU a (inFP_PG_spill a G)))].
      rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
    + right; left. split; [exists (p, p + req_size n); split; [unfold vr_fp; apply in_or_app; right; unfold ablocks_fp;
        exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) Hpn) | cbn; lia]|].
      exists p, n. split; [exact (HO _ Hpn) | exact Hr].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    destruct (fp1_cases (e_O e) a Ha) as [G|[G|(p & n & Hpn & Hr)]].
    + unfold A_G_REC, REC_SIZE in G. lia.
    + unfold A_REC_SPILL, SC_SIZE in G. lia.
    + destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP & HK).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
apply SRr_ret. cbv beta. exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfx|].
split; [exact HJ2|]. split; [exact HJc|]. split; [exact HP | exact HK].
Qed.

Lemma rec_code_range : forall ly S rd R O, rec_repA B ly S rd R O -> -2^31 <= r_code R < 2^31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

Lemma rdeq_of_frame : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
rdeq (aview SEGS H m) (aview SEGS H m').
Proof.
intros E rs H m m' Hf Hro a. apply (aview_eq_of SEGS). apply Hf.
intros (r & Hr & Ha). rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.

Lemma vr_rv_keep : forall e (regs regsc : bvmap 5 word) rl rl',
vr_rv regsc (vr_base B e ++ rl) ->
(forall r, In r [2; 3; 4; 8; 9] -> getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall r v, In (r, v) rl' ->
  (In (r, v) rl /\ getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) \/ getr regs (Z_to_bv 5 r) = w64 v) ->
vr_rv regs (vr_base B e ++ rl').
Proof.
intros e regs regsc rl rl' Hrv Hb Hl. apply vr_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
- assert (Hr : In r [2; 3; 4; 8; 9]).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; cbn; tauto. }
  rewrite (Hb r Hr). apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app; left; exact Hin.
- destruct (Hl r v Hin) as [[H1 H2] | H]; [|exact H].
  rewrite H2. apply (vr_rv_get regsc _ _ _ Hrv). apply in_or_app; right; exact H1.
Qed.

Lemma kept_regs_st_ok : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.

Lemma env_agree_Eimg : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* the jump of a return pc to the join (one `j`), run from a state that names only the registers *)
Lemma vr_jmp : forall retk stopk, 0 <= retk ->
sym_run_toN_pi pl_tpi FUEL stopk (ss_ret retk) = (ss_ret stopk, PRS_running) ->
forall W2 (regs2 : bvmap 5 word) mem2 md2 (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem md own ly2 S2 kk,
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 kk ->
(forall regs3 mem3 md3, (forall r, getr regs3 r = getr regs2 r) -> rdeq (rdW W2 mem2) (rdW W2 mem3) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem3 md3 kk ->
  Q W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + stopk)) mem3 (seg_rom SEGS)) md3)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros retk stopk Hk Hrun W2 regs2 mem2 md2 Q STK sp0 FP ly S W0 mem md own ly2 S2 kk HJ HQ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) (ss_ret retk)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ret. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
eapply (SRr_run_to_pi_AJ B LAWS W2 FUEL stopk (Eimg (Ereg regs2 [])) (ss_ret retk) (ss_ret stopk) PRS_running _
  STK sp0 FP ly S W0 mem md own ly2 S2 md2 kk Q HEI HS Hrun I HJ).
- apply awr_ok_nil.
- intros ms' mat HS' HJ' HF HFr HG.
  rewrite (st_ok_pi_restrict_mkst (w_H W2) _ (ss_ret stopk) ms' HS' eq_refl). cbn [ss_pc ss_ret].
  apply SRr_ret. apply HQ.
  + intros r. rewrite (st_ok_pi_restrict_reg (w_H W2) _ (ss_ret stopk) ms' r HS'). cbn [ss_regs ss_ret].
    symmetry. exact (regs_ok_Eimg_Ereg regs2 [] r).
  + cbn [ms_mem mkst ss_mem ss_ret] in HFr. exact (rdeq_of_frame _ [] _ _ _ HFr (Forall_nil _)).
  + exact HJ'.
Qed.

(* a word of tok[] handed to a recorder function: a C string in the copy block, none of the recorder's (the callees'
   uri premise, descriptors_get_c.v:86-89) *)
Lemma vr_tok_arg : forall e F q c tp lyc Sc (W : world SEGS) mem md i p w,
AR SEGS B lyc Sc W mem md ->
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e) ->
vr_copy B e F c tp W mem ->
nth_error tp i = Some p -> nth_error (Verbs.toks (e_D e)) i = Some w ->
(in_blockA (ablocks B lyc Sc) p (Z.of_nat (length w) + 1) /\ astr_atR (rdW W mem) p w /\
 Z.of_nat (length w) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) (e_O e)) /\
aval_mem (rdW W mem) (F + 32 + 8 * Z.of_nat i) 8 p /\ 4096 <= p /\ p + Z.of_nat (length w) + 1 <= alloc_ceiling /\
Z.of_nat (length w) <= 8192.
Proof.
intros e F q c tp lyc Sc W mem md i p w HAR Hperm (Hfc & (Hmod & HlenP & Hptr & Hw)) Hp Hwi.
destruct (Hw i p w Hp Hwi) as (A1 & A2 & A3 & A4).
assert (HndOT : List.NoDup (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e))
  by exact (Permutation_NoDup Hperm (nodup_ablocks _ _ _ _ _ HAR)).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. right; left; reflexivity. }
assert (HcbO : ~ In (vr_cb e c) (e_O e)).
{ intros H. exact (nodup_app_disj _ _ _ HndOT H (or_intror (or_introl eq_refl))). }
unfold vr_cb in Hcb, HcbO.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
split; [|split; [exact (Hptr i p Hp) | split; [lia | split; [lia | exact A2]]]].
split; [|split; [exact A1 | split; [unfold LMAX; lia |]]].
- exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1). split; [exact Hcb | lia].
- apply Forall_forall. intros [p' n'] Hin'.
  assert (Hin2 : In (p', n') (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin').
  assert (Hne : (p', n') <> (c, Z.of_nat (length (Verbs.line (e_D e))) + 1)) by (intros E; rewrite E in Hin'; exact (HcbO Hin')).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W mem md p' n' _ _ HAR Hin2 Hcb Hne) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin2) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos n' ltac:(lia)) as Hrs'.
  unfold zdisjoint in Hd. unfold iv_apart. cbn [fst snd] in *. lia.
Qed.

End e.
End f.
End d.

(* ---------------------------------------------------------------------------------------------------------------
   The generic arm at the caller's FP state fx (statement pass 4): the call half vr_call_ret
   (at fx) returns at some FP state fx' with fxrel fx fx'; the jump to 0x8dad4 (vr_jmp) and the join's state
   (vr_hd_build) are the closed section's lemmas taken at fx', where the entry's facts hold again (vr_ent_at:
   vr_ent's one FP clause is rounding mode 0, which fxrel keeps, PaFx's fxrel_frm0). *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

(* vr_ent at another FP state: every conjunct but the last is FP-free, the last is rounding mode 0 (fx is named: the
   bound f1 would otherwise be found for the implicit FP state) *)
Lemma vr_ent_at : forall (f1 : YK11.FPState) e, vr_ent (fx := fx) B MT e -> frm0 f1 -> vr_ent (fx := f1) B MT e.
Proof.
intros f1 e H Hf. unfold vr_ent in *. cbv zeta in *.
repeat lazymatch type of H with
| _ /\ _ => let A := fresh "A" in destruct H as [A H]; split; [exact A|]
end.
exact Hf.
Qed.

Lemma vr_call_arm : forall e W pos F q c x retk tp lyc Sc regs mem md k nm AF STK1 EV1 XM1 LIVE1 (m : rstate * list byte),
vr_ent B MT e ->
vr_cs B MT e pos F q c x retk tp lyc Sc W regs mem md k nm ->
length (Verbs.toks (e_D e)) = 2%nat ->
vr_h (e_R e) (e_D e) = (m, false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV1 ->
3 <= EV1 -> XM1 <= 3 * mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT -> LIVE1 <= 20 * VERBS_RECEIVE_REQ ->
0 <= STK1 -> STK1 + 208 <= VERBS_RECEIVE_STK ->
0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
sym_run_toN_pi pl_tpi FUEL 0x75f0 (ss_ret retk) = (ss_ret 0x75f0, PRS_running) ->
(forall ch, afn_pre SEGS B STK1 lyc Sc W regs mem md ch -> frm0 fx ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) ->
  rec_repA B lyc Sc (rdW W mem) (e_R e) (e_O e) -> Z.of_nat (length (frames Sc)) <= 8 ->
  st_nev Sc + EV1 <= EV_MAX -> blocks_bytes Sc + LIVE1 <= LIVE_MAX -> mo_ok MT Sc XM1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (apost_baseF SEGS B STK1 (fp1 (e_O e)) regs lyc Sc W mem md EV1 (rc_post B MT (e_R e) (e_O e) m XM1 LIVE1 lyc Sc))) ->
SRr SEGS W (cfg_at SEGS (BASE + AF) regs mem md)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ vr_hd (fx := fq) B MT e 0x8dad4 W' cf').
Proof.
intros e W pos F q c x retk tp lyc Sc regs mem md k nm AF STK1 EV1 XM1 LIVE1 m
  Hent Hcs Hlen Hvh Hk1 HEV1 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 Hrun CALL.
pose proof (vr_ent_frm0 B MT e Hent) as HF0.
eapply SRr_bind.
{ exact (vr_call_ret B MT HB MTL PROGU e W pos F q c x retk tp lyc Sc regs mem md k nm AF STK1 EV1 XM1 LIVE1 m
    Hent Hcs Hk1 HEV1 HXM1 HLV1 HST0 HSTK1 Hretk Hretk2 CALL). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfx & HJ2 & HJc & HP & HK).
apply (vr_jmp (fx := fx') B retk 0x75f0 ltac:(lia) Hrun W2 regs2 mem2 md2 _ _ _ _ _ _ _ _ _ _ ly2 S2 (k + EV1) HJ2).
intros regs3 mem3 md3 Er Em HJ3.
exists fx'. split; [exact Hfx|].
pose proof (vr_hd_build (fx := fx') B MT MTL ROA RRO RPG RECC PROGU e W pos F q c x retk tp lyc Sc regs mem md k nm
  STK1 EV1 XM1 LIVE1 m W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3
  (vr_ent_at fx' e Hent (fxrel_frm0 fx fx' HF0 Hfx)) Hcs Hlen Hvh Hk1 HEV1 HXM1 HST0 HSTK1 HJc HP HK Er Em HJ3) as HH.
unfold cfg_at, w64 in HH. replace (vr_pc 0x8dad4) with (BASE + 0x75f0) in HH by (unfold vr_pc, AF_verbs_receive; lia).
exact HH.
Qed.

End e2.
End f2.
End d2.
