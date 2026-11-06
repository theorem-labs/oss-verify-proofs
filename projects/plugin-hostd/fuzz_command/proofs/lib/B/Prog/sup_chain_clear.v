(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_chain_clear on plugin-hostd/fuzz_command's ASan+UBSan build
   (fuzz_command.asan-ubsan, entry 0x8c570, 122 instructions to the `ret` at 0x8c754), proving a Theorem Labs lane's
   tsup_chain_clear_spec (lib/B/Prog/sup_chain_clear_c.v). A B re-walk of lib/A/Prog/sup_chain_clear.v and its _s1,
   _s2 (a working branch abd8a14a6b8): B calls record (A inlines it) and inlines arg_i (A calls it), so the
   frame, snprintf and release steps follow lib/A/Prog/answer_code.v (a working branch 2ba4488ce71). The B
   code: a 96-byte frame realigned by `andi sp,sp,-32`; a class-0 side-stack frame from __asan_stack_malloc_0
   (0x8c5d0, the use-after-return flag read through the record's const cell) with its header and shadow; record(18)
   at 0x8c668; snprintf(b, 16, "%d", id) at 0x8c68c into the frame's buffer b = F + 32, in pass 4b's art form
   (PASS4-REFIT.md E, the `+ 8` destination band of E.0 from the frame's room); arg_s(slot, b) at 0x8c698;
   rec_shape_of("chain_clear", 11) at 0x8c6b0; answer(slot, shape, 1) at 0x8c6c0 by PaFx.callS_wideF; the frame's
   release (magic, shadow f5, the flag byte through F + 56) and the epilogue. No __asan_report call and no UBSan trap
   site lies in [0x8c570, 0x8c758). Every call's frame chain is afn_pre's chain pushed at the frame pointer
   (achain_push, scc_chain_call). After the snprintf and answer, whose posts are at a new FP state, the walk goes on
   at that state (scc_st_ok_fx, PASS4-REFIT.md A.5's second way). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c rec_calls_free_c hand_back_c mix_call_c record_c arg_s_c rec_shape_of_c answer_c sup_chain_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFShared RtPFCmd RtPFSx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_chain_clear_rec sup_chain_clear_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require arg_i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* PaDenot.v's division flag is Local since a later change, so this file sets the form its lia calls were written for
   (a Theorem Labs lane 11:47Z's ZIFY NOTE) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module PAI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.arg_i.

(* the recorder's bytes: g_rec and record.spill (CmdRep's in_recA, in lib/B/Prog/sup_chain_clear_rec.v) *)

Ltac norm_ssp HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* a register's symbolic value in a symbolic state, without normalising the denotation (CmdPaLib's prreg
   normalises it); answer_code.v's preg (a working branch 2ba4488ce71) *)
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
(* PaLibH's jafter_call_keep_hi at a named FP state: the state a printf wrapper returns at (pass 4b) *)
Ltac jafter_call_fx fxq HS k regs2 mem2 HP idxs HS2 :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "jafter_call_fx: no img_env" end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call_hi (fx := fxq) k E (abs_ss val ss) ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call (abs_ss val ss) rs k retk) with ss2 in HS2
| st_ok ?segs ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "jafter_call_fx: no img_env" end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call_hi (fx := fxq) k E ss ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call ss rs k retk) with ss2 in HS2
end.
(* an address outside every write window of a symbolic memory (answer_code.v's nwin_tac) *)
Ltac nwin_tac rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.
(* the write windows of the six regions the walk carries from the frame setup on (the frame's shadow, its flag
   word, its header, the two pieces of the own stack frame, the realigned stack word): answer_code.v's awr6 for the
   class-0 frame *)
Ltac scc_awr6 fpos sp1 regs FS Vs Vf V2 V34 EFA :=
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
(* --- the text snprintf writes for "%d" (.str 0x21f40) and the record's constant-shadow cells of that format:
   lib/B/Prog/sup_after_reply_aux.v's sar_* helpers (a working branch 8c121344905), themselves ported
   from the ASan arg_i walk -------------------------------------------------------------------------------------- *)
Lemma scc_dec_len : forall v, -2^31 <= v < 2^31 -> length (PF.pf_dec v) = length (dec v).
Proof. intros v Hv. rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity. Qed.
Lemma scc_dec_text : forall v, -2^31 <= v < 2^31 ->
PF.pf_bytes (firstn (Z.to_nat (16 - 1)) (PF.pf_dec v) ++ [0]) = dec v ++ [Z_to_bv 8 0].
Proof.
intros v Hv. pose proof (dec_length v Hv) as Hl. pose proof (scc_dec_len v Hv) as Hl2.
rewrite firstn_all2 by (rewrite Hl2; change (Z.to_nat (16 - 1)) with 15%nat; lia).
unfold PF.pf_bytes in *. rewrite map_app. rewrite <- (PAI.ai_pf_dec v Hv). reflexivity.
Qed.
Definition scc_cell_is (a v : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum a') (S O) (AV (ANum v')) => (a' =? a) && (v' =? v)
  | _ => false
  end.
Lemma scc_cell_in : forall a v l, existsb (scc_cell_is a v) l = true -> In (z1 (ANum a) v) l.
Proof.
intros a v l. induction l as [|c l IH]; cbn [existsb In]; [discriminate|].
intros H. apply orb_true_iff in H as [H|H]; [left | right; exact (IH H)].
destruct c as [ca cw cv]. unfold scc_cell_is in H.
destruct ca; try discriminate H. destruct cw as [|[|cw]]; try discriminate H.
destruct cv as [e|m w]; try discriminate H. destruct e; try discriminate H.
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. reflexivity.
Qed.
Lemma scc_cs_3e8 : In (z1 (ANum 0x7fffc3e8) 0x3) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
Lemma scc_cs_3e9 : In (z1 (ANum 0x7fffc3e9) 0xf9) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
Lemma scc_cs_3ea : In (z1 (ANum 0x7fffc3ea) 0xf9) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
Lemma scc_cs_3eb : In (z1 (ANum 0x7fffc3eb) 0xf9) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
Lemma scc_cs_3ec : In (z1 (ANum 0x7fffc3ec) 0x6) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
Lemma scc_cs_3ed : In (z1 (ANum 0x7fffc3ed) 0xf9) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
Lemma scc_cs_3ee : In (z1 (ANum 0x7fffc3ee) 0xf9) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
Lemma scc_cs_3ef : In (z1 (ANum 0x7fffc3ef) 0xf9) Tfib_const_shadow.
Proof. apply scc_cell_in. vm_compute. reflexivity. Qed.
(* the conjunct of a long conjunction that holds the literal address [a] *)
Local Ltac scc_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* answer_code.v's region_kept_hi / region_kept_hi2 / aview_frame_pt (a working branch 2ba4488ce71) *)
Lemma region_kept_hi : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma region_kept_hi2 : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma aview_frame_pt : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_chain_clear_c.v, Section e) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses: the per-binary allocator record, the shadow / use-after-return GOT words (PALib, PALibF),
   the meter's laws, the program functions' call targets, and a Theorem Labs lane's per-binary image facts in the form of its
   lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib at this walk's abstract segments (Wb_sup_reset's convention, relayed
   by a Theorem Labs lane 09:2xZ): every other per-binary fact is a Theorem Labs lane's lemma over it, by exact *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
(* a Theorem Labs lane's facts at this walk's segs and B *)
Let scc_ro_in : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.
Let scc_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a := CmdRecRo.RELRO_IMG (SK := SK) SEGS B LAWS HB IMG.
Let scc_rob : ro_below_ofl SEGS CMD_RLO CMD_RHI := CmdRecRo.ROB (SK := SK) SEGS B LAWS HB IMG.
Let scc_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let scc_ro_apart : forall a, in_roP SEGS CMD_RLO CMD_RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC
  := CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let scc_ro_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem)
  := CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let scc_cells : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  rdW W mem 0xae455 = Some 1 /\ aguard_ok SEGS W mem 0xa6bf8 0x604158 /\
  exists ev, rd32 (rdW W mem) (as_errno B) ev := CmdRecCells.cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG.

Lemma scc_FFL : frame_flag_lawP SEGS B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (pa_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* g_rec's and record.spill's bytes are none of the runtime's statics (HB's ts_owned) and not the errno cell *)
Lemma scc_rec_unowned : forall a, in_recA a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold in_recA in Ha.
split.
- intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (Hb1 : forallb (fun r => (0x5e3680 <=? fst r) || (fst r + snd r <=? 0x5e32c0)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  assert (Hb2 : forallb (fun r => (0x5e3798 <=? fst r) || (fst r + snd r <=? 0x5e3760)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb1 _ Hin) as Hq1. pose proof (proj1 (forallb_forall _ _) Hb2 _ Hin) as Hq2.
  cbn beta in Hq1, Hq2. cbn [fst snd] in Hq1, Hq2.
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha.
  apply Bool.orb_true_iff in Hq1 as [Hq1 | Hq1]; apply Z.leb_le in Hq1;
  apply Bool.orb_true_iff in Hq2 as [Hq2 | Hq2]; apply Z.leb_le in Hq2; lia.
- unfold TFIB_ERRNO, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
Qed.
Lemma scc_in_PG : forall a, in_recA a -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a [Ha | Ha]; apply Exists_exists.
- exists (0x5e32c0, 960). split; [left; reflexivity | unfold in_zr, A_G_REC, REC_SIZE in *; cbn [fst snd]; exact Ha].
- exists (0x5e3760, 56). split; [right; left; reflexivity | unfold in_zr, A_REC_SPILL, SC_SIZE in *; cbn [fst snd]; exact Ha].
Qed.
Definition scc_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* a write of the walk to g_rec or record.spill is one the footprint names: a Theorem Labs lane's program-static disjunct *)
Lemma scc_awr_rec : forall STK sp0 O bl0 blc fr0 lyc own a, in_recA a ->
awr_byte SEGS B STK sp0 (scc_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha.
right; right; right; right; left.
assert (HP : Exists (in_zr a) TFIB_PROG_STATIC) by exact (scc_in_PG a Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (scc_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.
(* where the recorder's bytes lie: g_rec and record.spill are image bytes; a live block is a heap byte *)
Lemma scc_rec_loc : forall a, in_recA a -> in_img SEGS a /\ 0x10000 <= a < 0x606000.
Proof.
intros a Ha. split; [apply scc_prog_img; apply scc_in_PG; exact Ha|].
unfold in_recA, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

(* no read-only byte is in the contract's footprint (arodata_ok_journalP's premise); sup_chain_clear_s2.v's *)
Lemma scc_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (scc_FP O) a.
Proof.
intros ly S W mem md O HAR HOS a Hro (r & Hr & Ha).
destruct (scc_ro_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply Hnp. apply scc_in_PG. left. exact Ha.
- apply Hnp. apply scc_in_PG. right. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HOS _ Hin) Ha Himg).
Qed.
(* no footprint byte lies on the stack above the entry sp (astack_pres_journal's premise) *)
Lemma scc_FP_low : forall ly S (W : world SEGS) mem md O sp0, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> alloc_ceiling <= sp0 ->
forall a, inFP (scc_FP O) a -> a < sp0.
Proof.
intros ly S W mem md O sp0 HAR HOS Hsp a (r & Hr & Ha).
pose proof asan_consts as (C1 & _).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, REC_SIZE in Ha. lia.
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HOS _ Hin)) as (_ & _ & Hc & _). lia.
Qed.
(* the frame chain a callee's afn_pre asks of s0 = the entry sp (the frame pointer, class B of a Theorem Labs lane's S0-SITES.md):
   afn_pre's chain pushed at the frame pointer (achain_push), with the ra and the caller's s0 the prologue saved at
   sp0 - 8 and sp0 - 16; the journal keeps every byte above sp0 (the footprint lies below it). When sp0 is within
   16 bytes of the stack top the chain is achain's empty case. *)
Lemma scc_chain_call : forall STK sp0 FP ly S (W0 : world SEGS) mem md own lyc Sc (W : world SEGS) memc mdc k ch ra s0e sp',
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
achain ly (rdW W0 mem) sp0 s0e ch ->
(forall a, inFP FP a -> a < sp0) ->
rdword (rdW W memc) (sp0 - 8) = Some ra -> rdword (rdW W memc) (sp0 - 16) = Some s0e -> 4096 <= ra ->
sp' + 16 <= sp0 ->
exists ch1, achain lyc (rdW W memc) sp' sp0 ch1.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ch ra s0e sp' HJ Hch HFP H8 H16 Hra Hsp'.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & _ & _).
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, s0e) :: ch). apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly (rdW W0 mem) (rdW W memc) sp0 s0e ra ch sp' Hch);
  [ lia
  | intros a Ha; apply F1; [lia | lia | intros Hf; pose proof (HFP a Hf); lia]
  | exact H8 | exact H16 | lia | lia
  | pose proof (Z.mod_pos_bound sp0 16 ltac:(lia)); pose proof (Z.div_mod sp0 16 ltac:(lia));
    pose proof (Z.div_mod sp0 8 ltac:(lia)); pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)); lia
  | lia | lia ].
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
(* the record's footprint (record_c.v): g_rec.ncalls, the slot's first 8 bytes, and in the spill arm the
   recorder's blocks *)
Lemma scc_rec_fp_in : forall (R : rstate) (O : list (Z * Z)) a,
inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
      (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a ->
(length (r_calls R) <= 16)%nat ->
in_recA a \/ (exists p n, In (p, n) O /\ p <= a < p + req_size n).
Proof.
intros R O a (r & Hr & Ha) Hlen.
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. left. unfold OFF_NCALLS, REC_SIZE in *. lia.
- left. pose proof (rec_slotA_home R Hlen) as (_ & Hc1 & Hc2 & _ & Hc3). change (rec_slot R) with (rec_slotA R) in Ha.
  unfold in_recA. destruct Hc3 as [Hc3 | Hc3]; [left | right]; unfold CALL_SIZE, SC_SIZE, A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia.
- right. destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha. exists p, n. auto.
Qed.

(* arg_s's footprint (arg_s_c.v, the arm with fewer than six arguments): the slot's nargs and args[0] fields *)
Lemma scc_args_fp_in : forall (R : rstate) a, (length (r_calls R) <= 16)%nat ->
inFP [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
      (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))),
       rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))) + 8)] a -> in_recA a.
Proof.
intros R a Hlen (r & Hr & Ha). pose proof (rec_slotA_home R Hlen) as (_ & Hc1 & Hc2 & _ & Hc3).
assert (ERS : rec_slot R = rec_slotA R) by reflexivity.
unfold in_recA, CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, SC_SIZE, REC_SIZE, OFF_CALLS in *.
destruct Hr as [<- | [<- | []]]; cbn [fst snd length Z.of_nat Z.mul] in Ha; rewrite ERS in Ha;
(destruct Hc3 as [Hc3 | Hc3]; [left | right]; lia).
Qed.
(* the meter the arg_s and answer calls spend is nonnegative *)
Lemma scc_xm_pos : forall v t, 0 <= XM_ARG_S MT v /\ 0 <= XM_ANSWER MT t.
Proof.
intros v t. unfold XM_ARG_S, XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
pose proof (mo_free_nonneg MT MTL).
pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length (sarg v)) + 1) 1) ltac:(lia)).
pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)).
lia.
Qed.

(* a one-byte cell of the record's constant shadow holds under AR (sup_after_reply_aux.v's sar_cshadow) *)
Lemma scc_cshadow : forall ly S (W : world SEGS) mem md a v,
AR SEGS B ly S W mem md -> In (z1 (ANum a) v) Tfib_const_shadow -> 0 <= v < 256 ->
rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. destruct HAR as (M & _).
pose proof (am_const _ _ _ _ M) as C. rewrite (ts_const B HB ly) in C. rewrite Forall_forall in C.
specialize (C (z1 (ANum a) v) ltac:(unfold Tfib_const; apply in_or_app; right; apply in_or_app; right; exact Hin)).
unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
specialize (C 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in C. rewrite Z.add_0_r in C. rewrite C. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
Lemma scc_fmt_addressable : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (rdW W mem) SHADOW_OFF 0x21f40 3.
Proof.
intros ly S W mem md HAR x Hx. unfold shadow_of_addr.
assert (Hq : x / 8 = 0x21f40 / 8) by (Z.div_mod_to_equations; lia). rewrite Hq.
exists 3. split.
- replace (SHADOW_OFF + 0x21f40 / 8) with 0x7fffc3e8 by (vm_compute; reflexivity).
  exact (scc_cshadow ly S W mem md _ _ HAR scc_cs_3e8 ltac:(lia)).
- right. split; [Z.div_mod_to_equations; lia | lia].
Qed.
Lemma scc_fmt_hull : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> shadow_hull_vis (rdW W mem) 0x21f40 3.
Proof.
intros ly S W mem md HAR s Hs.
assert (E1 : shadow_addr 0x21f40 / 8 * 8 = 0x7fffc3e8) by (vm_compute; reflexivity).
assert (E2 : shadow_addr (0x21f40 + 3 - 1) / 8 * 8 + 8 = 0x7fffc3f0) by (vm_compute; reflexivity).
rewrite E1, E2 in Hs.
assert (Hs8 : s = 0x7fffc3e8 \/ s = 0x7fffc3e9 \/ s = 0x7fffc3ea \/ s = 0x7fffc3eb \/ s = 0x7fffc3ec \/
  s = 0x7fffc3ed \/ s = 0x7fffc3ee \/ s = 0x7fffc3ef) by lia.
destruct Hs8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3e8 ltac:(lia)). discriminate.
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3e9 ltac:(lia)). discriminate.
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3ea ltac:(lia)). discriminate.
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3eb ltac:(lia)). discriminate.
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3ec ltac:(lia)). discriminate.
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3ed ltac:(lia)). discriminate.
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3ee ltac:(lia)). discriminate.
- rewrite (scc_cshadow ly S W mem md _ _ HAR scc_cs_3ef ltac:(lia)). discriminate.
Qed.
Lemma scc_ro_fmt : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f40 RO_lit_21f40.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. scc_projz H 0x21f40. Qed.
(* the text the snprintf leaves at b, as the string arg_s reads: dec id and its terminator *)
Lemma scc_buf_str : forall (W : world SEGS) mem p v, -2 ^ 31 <= v < 2 ^ 31 ->
(forall i, 0 <= i < sn_len (16 - 1) (PF.pf_dec v) ->
 aview SEGS (w_H W) mem (p + i) = Some (nth (Z.to_nat i) (sn_bytes (16 - 1) (PF.pf_dec v)) 0)) ->
astr_atR (rdW W mem) p (dec v).
Proof.
intros W mem p v Hv H.
assert (EB : PF.pf_bytes (sn_bytes (16 - 1) (PF.pf_dec v)) = dec v ++ [Z_to_bv 8 0]) by (unfold sn_bytes; exact (scc_dec_text v Hv)).
assert (EL : sn_len (16 - 1) (PF.pf_dec v) = Z.of_nat (length (dec v)) + 1).
{ unfold sn_len. rewrite <- (length_map (Z_to_bv 8)).
  change (map (Z_to_bv 8) (sn_bytes (16 - 1) (PF.pf_dec v))) with (PF.pf_bytes (sn_bytes (16 - 1) (PF.pf_dec v))).
  rewrite EB, length_app. cbn [length]. lia. }
split; [|exact (dec_no0 v)].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
pose proof (H (Z.of_nat i) ltac:(rewrite EL; lia)) as Hi'. rewrite Nat2Z.id in Hi'.
destruct (aview_byte SEGS _ _ _ _ Hi') as (b & _ & _ & Hz).
refine (eq_trans Hi' _). f_equal. rewrite <- EB. unfold PF.pf_bytes.
change (Z_to_bv 8 0) with (Z_to_bv 8 0). rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite Z.mod_small by exact Hz. reflexivity.
Qed.
Lemma scc_sn_len : forall v, -2 ^ 31 <= v < 2 ^ 31 -> sn_len (16 - 1) (PF.pf_dec v) = Z.of_nat (length (dec v)) + 1.
Proof.
intros v Hv. pose proof (scc_dec_len v Hv) as Hl. pose proof (dec_length v Hv) as Hd.
unfold sn_len, sn_bytes. rewrite length_app, firstn_all2 by (change (Z.to_nat (16 - 1)) with 15%nat; lia).
cbn [length]. lia.
Qed.
Lemma scc_mod32 : forall z, z mod 2 ^ 64 mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. rewrite (Z.mod_eq z (2 ^ 64)) by lia.
replace (z - 2 ^ 64 * (z / 2 ^ 64)) with (z + (- (2 ^ 32 * (z / 2 ^ 64))) * 2 ^ 32)
  by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); ring).
apply Z_mod_plus_full.
Qed.
(* the snprintf chain's read-only words lie in the image, below 0x606000 *)
Lemma scc_cr_low : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x606000) RtPFCmd.CMD_SNP_CR.
Proof. unfold RtPFCmd.CMD_SNP_CR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.
(* A symbolic state says nothing about the FP registers: the machine state takes them from the instance, so a state
   that holds at one FP state holds at another, of the machine state rebuilt there. This is how a walk goes on after
   a call whose post is at a new FP state (PASS4-REFIT.md A.5's second way). *)
Lemma scc_st_ok_fx : forall (fx0 fx1 : YK11.FPState) E ss ms, ss_resv ss = None ->
st_ok (fx := fx0) SEGS E ss ms ->
st_ok (fx := fx1) SEGS E ss (@mkst fx1 (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms)).
Proof.
intros fx0 fx1 E ss ms Hrv (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkst].
split; [reflexivity|]. split; [exact H2|]. split; [reflexivity|].
split; [rewrite Hrv; reflexivity|]. split; [reflexivity|]. split; [exact H6|].
split; [exact H7|]. split; [exact H8 | exact H9].
Qed.

(* the verb the call records, "chain_clear": the literal .str at 0x21f80 without its terminator *)
Definition scc_verb : list byte := bstr "chain_clear"%string.
Lemma scc_verb_ro : scc_verb ++ [Z_to_bv 8 0] = RO_lit_21f80.
Proof. vm_compute. reflexivity. Qed.
Lemma scc_verb_len : length scc_verb = 11%nat.
Proof. reflexivity. Qed.
Lemma scc_abytes_prefix : forall rd a (l1 l2 : list byte), abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by exact Hi. reflexivity.
Qed.
Lemma scc_ro_verb : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f80 RO_lit_21f80.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. scc_projz H 0x21f80. Qed.
(* the verb as rec_shape_of's string argument: astr_argA's read-only arm, with the record's checks decided on the
   concrete lists (lib/A/Prog/sup_chain_clear_s2.v's scc_verb_argA at this image's address) *)
Lemma scc_verb_argA : forall ly S rd O, abytes_atR rd 0x21f80 RO_lit_21f80 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O 0x21f80 (Some scc_verb).
Proof.
intros ly S rd O HL. unfold astr_argA. cbv zeta. rewrite scc_verb_len. change (Z.of_nat 11) with 11.
split; [lia|]. split.
{ split; [rewrite scc_verb_ro; exact HL|].
  assert (E : scc_verb = map (Z_to_bv 8) [99; 104; 97; 105; 110; 95; 99; 108; 101; 97; 114]) by (vm_compute; reflexivity).
  rewrite E. cbn [map In]. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. }
split; [unfold LMAX; lia|]. right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]].
- intros i Hi. split; [|split].
  + pose proof scc_ro_in as H. unfold cmd_ro_in in H.
    assert (Hr : forall j, 0 <= j < 12 -> in_roP SEGS CMD_RLO CMD_RHI (0x21f80 + j)) by scc_projz H 0x21f80.
    exact (Hr i Hi).
  + rewrite (ts_owned B HB). intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz.
    cbn [fst snd] in Hz.
    assert (Hb : forallb (fun r => (0x21f8c <=? fst r) || (fst r + snd r <=? 0x21f80)) Tfib_owned_static = true)
      by (vm_compute; reflexivity).
    pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Hq. cbn beta in Hq. cbn [fst snd] in Hq.
    apply Bool.orb_true_iff in Hq as [Hq | Hq]; apply Z.leb_le in Hq; lia.
  + rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
- assert (Hb : existsb (Z.eqb (0x21f80 + 11)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (e & He & Heq). apply Z.eqb_eq in Heq. rewrite Heq. exact He.
Qed.

Lemma scc_fits : fits (shape_of scc_verb).
Proof. unfold fits. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* a member of a filtered list is a member of the list (the filter answer_c.v's footprint uses) *)
Lemma scc_filter_in : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|a l IH]; intros H; cbn in H; [exact H|].
repeat match type of H with context [match ?d with left _ => _ | right _ => _ end] => destruct d end;
repeat match type of H with context [if ?b then _ else _] => destruct b end;
first [ destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H) ].
Qed.
(* two live blocks with the same start are the same block (the allocator record keeps them disjoint) *)
Lemma scc_same_start : forall ly S (W : world SEGS) mem md a b, AR SEGS B ly S W mem md ->
In a (ablocks B ly S) -> In b (ablocks B ly S) -> fst a = fst b -> a = b.
Proof.
intros ly S W mem md [pa na] [pb nb] HAR Ha Hb E. cbn [fst] in E. subst pb.
destruct (decide ((pa, na) = (pa, nb))) as [Heq | Hne]; [exact Heq|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md pa na pa nb HAR Ha Hb Hne) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa na HAR Ha) as (_ & _ & _ & _ & _ & _ & Hna).
destruct (al_blocks _ _ LAWS ly S W mem md pa nb HAR Hb) as (_ & _ & _ & _ & _ & _ & Hnb).
pose proof (req_size_pos na ltac:(lia)) as [Ra _]. pose proof (req_size_pos nb ltac:(lia)) as [Rb _].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a callee whose footprint misses a byte of g_rec / record.spill leaves it as it was (the journal's image clause) *)
Lemma scc_rec_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP1 -> in_recA a -> ~ inFP FP1 a -> rdW W' mem' a = rdW Wc memc a.
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k a HJ Hsk Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (scc_rec_unowned a Ha) as [Ho He].
apply F3; [| exact Ho | exact He | exact (fp_spares_closed FP1 a Hsk Hn)].
apply scc_prog_img. apply scc_in_PG. exact Ha.
Qed.
(* a block live across a callee whose footprint lies in g_rec / record.spill keeps its bytes *)
Lemma scc_blk_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k p n i,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
AR SEGS B lyc Sc Wc memc mdc ->
(forall a, inFP FP1 a -> in_recA a) ->
In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly' S') -> 0 <= i < n ->
rdW W' mem' (p + i) = rdW Wc memc (p + i).
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k p n i HJ HAR HFP Hin Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos n ltac:(lia)) as [R1 R2].
apply (F2 p n i); [exact Hin | exact Hin' | lia |].
intros Hf. apply HFP in Hf.
apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc p n (p + i) HAR Hin); [lia|].
apply scc_prog_img. apply scc_in_PG. exact Hf.
Qed.
(* astr_argA reads its reader only through the string's bytes *)
Lemma scc_argA_rd : forall ly S rd rd' O p x, astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (p + i)) ->
astr_argA B ly S rd' (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S rd rd' O p x H Hk. unfold astr_argA in *. cbv zeta in *.
destruct H as (H0 & [Hb Hnz] & Hl & Harm). split; [exact H0|]. split; [|split; [exact Hl | exact Harm]].
split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
(* the bytes of such a string lie below the stack (a heap block or the image) *)
Lemma scc_argA_bound : forall ly S (W : world SEGS) mem md rd O p x, AR SEGS B ly S W mem md -> 0 <= p ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i < 2 ^ 64.
Proof.
intros ly S W mem md rd O p x HAR Hp H i Hi. unfold astr_argA in H. cbv zeta in H.
pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [((pb & kb & Hin & Hlo & Hhi) & _) | (Hro & _)]).
- destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hin) as (_ & _ & Hc & _ & _ & _ & Hk).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Rk]. lia.
- destruct (Hro i Hi) as (Hr & _). destruct (scc_ro_apart _ Hr) as [Himg _].
  pose proof (pa_img_range _ Himg). lia.
Qed.

(* the block bookkeeping of the post, over the block lists of the entry (bl0), the join (blc), answer's entry (bl4)
   and the end (bl5) *)
Lemma scc_post_lists : forall (bl0 blc bl4 bl5 O O1 O' : list (Z * Z)) pnew p1 p2 old,
(forall pn, In pn bl0 -> ~ In pn O -> In pn blc) ->
(forall pn, In pn blc -> In pn bl0) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn blc -> In pn O1) ->
(forall pn, In pn O1 -> In pn blc) ->
~ In pnew blc ->
(forall pn, In pn bl4 <-> pn = pnew \/ In pn blc) ->
(forall pn, In pn bl4 -> fst pn <> old -> pn <> p1 /\ pn <> p2) -> p1 <> p2 ->
(forall pn, In pn bl5 <-> (In pn bl4 /\ fst pn <> old) \/ pn = p1 \/ pn = p2) ->
(forall pn, In pn O' <-> (In pn (O1 ++ [pnew]) /\ fst pn <> old) \/ pn = p1) ->
(forall pn, In pn bl4 -> fst pn = old -> In pn (O1 ++ [pnew])) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
In p2 bl5 /\
(In p2 bl0 -> In p2 O) /\
~ In p2 O' /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl5 /\ In pn bl4) /\
(forall pn, In pn bl5 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = p2).
Proof.
intros bl0 blc bl4 bl5 O O1 O' pnew p1 p2 old HB2 HB1 HO1 HO2 HO1c Hnew H4 Hfr H12 H5 HO' Hold.
assert (Hdec : forall pn (l : list (Z * Z)), In pn l \/ ~ In pn l)
  by (intros pn l; destruct (in_dec (fun x y : Z * Z => decide (x = y)) pn l); tauto).
assert (Hnew0 : In pnew bl0 -> In pnew O).
{ intros H0. destruct (Hdec pnew O) as [H|H]; [exact H | exfalso; exact (Hnew (HB2 _ H0 H))]. }
(* a fresh copy that was a block of the entry was one of the recorder's (freed on the spill arm or as the old answer) *)
assert (Cp : forall pp, pp = p1 \/ pp = p2 -> In pp bl0 -> In pp O).
{ intros pp Hpp H0. destruct (Hdec pp O) as [H|H]; [exact H|]. exfalso.
  assert (Hc : In pp blc) by exact (HB2 _ H0 H).
  assert (H4' : In pp bl4) by (apply H4; right; exact Hc).
  destruct (Z.eq_dec (fst pp) old) as [Eo | Ne].
  - pose proof (Hold _ H4' Eo) as Hin. apply in_app_or in Hin as [Hin | [E | []]].
    + exact (H (HO1 _ Hin)).
    + subst pp. exact (Hnew Hc).
  - destruct (Hfr _ H4' Ne) as [N1 N2]. destruct Hpp as [-> | ->]; [exact (N1 eq_refl) | exact (N2 eq_refl)]. }
split; [|split; [|split; [|split; [|split]]]].
- intros pn Hpn. apply HO' in Hpn as [(Hin & _) | ->].
  + apply in_app_or in Hin as [Hin | [<- | []]]; [left; exact (HO1 _ Hin)|].
    destruct (Hdec pnew bl0) as [H|H]; [left; exact (Hnew0 H) | right; exact H].
  + destruct (Hdec p1 bl0) as [H|H]; [left; exact (Cp p1 (or_introl eq_refl) H) | right; exact H].
- apply H5. right; right. reflexivity.
- intros H0. exact (Cp p2 (or_intror eq_refl) H0).
- intros Hin. apply HO' in Hin as [(Hin & Hne) | E]; [|exact (H12 (eq_sym E))].
  assert (H4' : In p2 bl4).
  { apply in_app_or in Hin as [Hin | [E | []]]; apply H4; [right; exact (HO1c _ Hin) | left; symmetry; exact E]. }
  exact (proj2 (Hfr _ H4' Hne) eq_refl).
- intros pn H0 HnO. assert (Hc : In pn blc) by exact (HB2 _ H0 HnO).
  assert (H4' : In pn bl4) by (apply H4; right; exact Hc).
  split; [|exact H4']. apply H5. left. split; [exact H4'|]. intros Eo.
  pose proof (Hold _ H4' Eo) as Hin. apply in_app_or in Hin as [Hin | [E | []]].
  + exact (HnO (HO1 _ Hin)).
  + subst pn. exact (Hnew Hc).
- intros pn Hpn. apply H5 in Hpn as [(Hin4 & Hne) | [-> | ->]].
  + apply H4 in Hin4 as [-> | Hc].
    * right; left. apply HO'. left. split; [apply in_or_app; right; left; reflexivity | exact Hne].
    * destruct (Hdec pn O) as [HinO' | HnO].
      -- right; left. apply HO'. left. split; [apply in_or_app; left; exact (HO2 _ HinO' Hc) | exact Hne].
      -- left. split; [exact (HB1 _ Hc) | exact HnO].
  + right; left. apply HO'. right. reflexivity.
  + right; right. reflexivity.
Qed.


(* no block is live twice (the allocator record keeps the blocks pairwise disjoint): RecBLemmas.v's
   recb_ablocks_nodup_m at this walk's segments *)
Lemma scc_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _].
assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
{ intros [p n] Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  exact (proj1 (req_size_pos n ltac:(lia))). }
revert Hp Hpos. generalize (ablocks B ly S) as l. induction l as [|y l IH]; intros Hp Hpos; [constructor|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor.
- intros Hin. rewrite Forall_forall in Hf.
  pose proof (Hf (fst y, req_size (snd y)) (in_map (fun b => (fst b, req_size (snd b))) l y Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (Hpos y (or_introl eq_refl)). lia.
- apply IH; [exact Hp | intros b Hb; apply Hpos; right; exact Hb].
Qed.

Lemma scc_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x. induction l1 as [|y l1 IH]; intros ND H1 H2; [exact H1|].
cbn [app] in ND. inversion ND as [|y' l' Hn ND' E]. subst.
destruct H1 as [<- | H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH ND' H1 H2)].
Qed.

(* the closing meter and live-byte sums of the post *)
Lemma scc_mle_final : forall (S S2 S4 S8 S12 : astate) fS2 (R : rstate) id t fpos,
  S2 = set_fs fS2 S -> mo_le MT S2 S4 (XM_RECORD MT R) -> mo_le MT S4 S8 (XM_ARG_S MT (Some (dec id))) ->
  mo_le MT S8 S12 (XM_ANSWER MT t) -> snd (sup_chain_clear_m R id) = t ->
  mo_le MT S (stack_free_state 0 fpos S12) (XM_SUP_CHAIN_CLEAR MT R id).
Proof.
intros S S2 S4 S8 S12 fS2 R id t fpos ES2 Hmle4 Hmle8 HMLE12 Ht.
unfold stack_free_state. apply (mo_le_set_fs_r MT MTLF).
eapply (mle_weaken MT S S12 _ _ MTL).
- eapply (mle_station MT S S8 S12 _ _ MTL); [| exact HMLE12].
  eapply (mle_station MT S S4 S8 _ _ MTL); [| exact Hmle8].
  apply (mo_le_set_fs_l MT MTLF S S4 fS2). rewrite <- ES2. exact Hmle4.
- unfold XM_SUP_CHAIN_CLEAR. rewrite Ht. lia.
Qed.
Lemma scc_bb_final : forall ly12 (S S2 S4 S8 S12 : astate) fpos (R : rstate) id t nd,
  -2 ^ 31 <= id < 2 ^ 31 ->
  ablocks B ly12 (stack_free_state 0 fpos S12) = ablocks B ly12 S12 ->
  blocks_bytes S2 = blocks_bytes S ->
  blocks_bytes S4 <= blocks_bytes S2 -> blocks_bytes S8 = nd + blocks_bytes S4 ->
  blocks_bytes S12 <= blocks_bytes S8 + LIVE_ANSWER t ->
  nd = Z.of_nat (length (dec id)) + 1 ->
  snd (sup_chain_clear_m R id) = t ->
  blocks_bytes (stack_free_state 0 fpos S12) <= blocks_bytes S + LIVE_SUP_CHAIN_CLEAR R id.
Proof.
intros ly12 S S2 S4 S8 S12 fpos R id t nd Hid EAB13 HBB2 Hbb4 HBB8 Hbb12 End Ht.
assert (B13 : blocks_bytes (stack_free_state 0 fpos S12) = blocks_bytes S12)
  by (rewrite (blocks_bytes_bsum B ly12 (stack_free_state 0 fpos S12)), (blocks_bytes_bsum B ly12 S12), EAB13; reflexivity).
unfold LIVE_SUP_CHAIN_CLEAR, LIVE_ARG_S, LIVE_XMALLOC in *. cbn [sarg] in *. rewrite Ht.
pose proof (dec_length id Hid). lia.
Qed.

Theorem tsup_chain_clear_holds : tsup_chain_clear_spec B MT.
Proof.
unfold tsup_chain_clear_spec.
intros ly S W regs mem md ch id R O HPRE HFRM HROD HRO H10 Hid HREP HFR Hev Hlive MOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (scc_entry B TL TLF SUP_CHAIN_CLEAR_STK W ly S regs mem md ch ltac:(vm_compute; congruence) HPRE) as HS.
set (FP := (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
pose proof (ajournal_init SEGS B SUP_CHAIN_CLEAR_STK FP ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SUP_CHAIN_CLEAR_STK = 16704) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
set (sp1 := 32 * ((spZ regs - 96) / 32)) in HS.
destruct (scc_sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
remember (Eimg (Ereg regs (scc_extra B sp1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (scc_extra B sp1)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_sup_chain_clear)) with (Z_to_bv 64 (BASE + AF_sup_chain_clear)).
(* run 1: 0x8c570 .. 0x8c5d0, the prologue, the use-after-return flag (1, the record's const cell) and the call of
   __asan_stack_malloc_0 *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold ss_scc0, scc_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
preg HS (2%bv : bv 5) R2. preg HS (9%bv : bv 5) R9. preg HS (1%bv : bv 5) R1. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
rewrite (scc_denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R2. fold sp1 in R2.
rewrite scc_denot_add0, (scc_denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R9. fold sp1 in R9.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E HEI 24740) in R1.
rewrite scc_denot_off0, (EE 3%nat 3%bv eq_refl) in R3. rewrite scc_denot_off0, (EE 4%nat 4%bv eq_refl) in R4.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl ltac:(rewrite scc_denot_off0, E34; cbn [ms_regs restrict]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl ltac:(rewrite scc_denot_off0, E34; cbn [ms_regs restrict]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
pose proof (palf_sm B TLF 0 ltac:(cbn; tauto)) as SM0. change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in SM0.
rewrite SM0.
assert (Qsp : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML (CmdRecRest.cmd_stack_malloc_progress B) 0 (ASTACK_MALLOC0 fx) ltac:(lia) W (ms_regs ms1) (ms_mem ms1)
SUP_CHAIN_CLEAR_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24740)) HJ);
[ exact Qsp | exact Hsp1b | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
| pose proof (count_cid_le_length 0 (frames S)); assert (Hfs0 : 8 <= fs_frames 0) by (vm_compute; intros Hx; discriminate Hx); lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJS & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & _ & HK3 & _ & _ & _).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
- eapply region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
- eapply region_kept_hi; [exact U34 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 R9 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HAE1 : env_agree 32 (Ereg regs (scc_extra B sp1)) E1) by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres). fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
destruct (scc_FFL _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)). fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
replace (F + 64 - 8) with (F + 56) in Hflag by lia.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HFm8 : F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
assert (HFd8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
assert (HFin : in_app F 64) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HAE2 : env_agree 32 (Ereg regs (scc_extra B sp1)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1040 : ew E2 1040 = Z_to_bv 64 FL) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (SB + F / 8)) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
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
pose proof (st_ok_pi_add_alias Ev _ msv scc_shx_F (SOff 1041 0) HS (shadow_decl_ok Ev 1028 32 1041 F SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scc_fr_hdr HS eq_refl
ltac:(unfold region_ok, scc_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scc_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scc_fr_flg HS eq_refl
ltac:(unfold region_ok, scc_fr_flg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ F 56 8 (SOff 1040 0) FL); [rewrite scc_denot_off0; exact E1040 | lia | lia |];
exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scc_fr_flg, scc_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scc_fr_shd HS eq_refl
ltac:(unfold region_ok, scc_fr_shd; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS);
replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres o ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, scc_fr_shd, scc_fr_flg, scc_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1041, V1028, V2, V34; unfold SB; pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
assert (EFA : frame_addr ly 0 fpos = F) by reflexivity.
(* run 2: 0x8c5d4 .. 0x8c668, s2 := the frame (not 0: the bnez is decided by the frame's fact), the frame's slot at
   sp1 + 8, its header (magic, descriptor, pc), its shadow f1 f1 f1 f1 f8 f8 f3 f3, a0 := 18, the call of record *)
paj_run_shc RUNP RUNC HS HJ2.
{ scc_awr6 fpos sp1 regs FS V1041 V1028 V2 V34 EFA. }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
(* the recorder's bytes and blocks at the entry: none of them in the frame, its shadow, its flag or the stack *)
set (KA := fun a : Z => in_recA a \/ (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n)).
assert (KLOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a [Ha | (p & n & Hpn & Hpa)].
- destruct (scc_rec_loc a Ha) as [Hi Hr]. split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (HFLimg Hi).
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & _ & _).
  assert (Hpn2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hpn).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hpn2) as (_ & _ & _ & _ & Hpres2 & _).
  pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p n 0 fpos HAR2 Hpn2 Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
  intros ->. exact (proj2 (Hpres2 FL ltac:(lia)) HFLo). }
assert (K01 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & _). apply (aview_frame_pt E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
nwin_tac ltac:(fun H => rewrite ?Usp, ?U34 in H; lia). }
assert (K12 : forall a, KA a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms1) a).
{ pose proof HK as (_ & HK2 & _ & _ & _ & _).
intros a [Ha | (p & n & Hpn & Hpa)].
- destruct (scc_rec_unowned a Ha) as [Ho He]. exact (HK3 a (proj1 (scc_rec_loc a Ha)) Ho He).
- replace a with (p + (a - p)) by lia. apply (HK2 p n (a - p) Hpn); [lia | intros []]. }
assert (K23 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (aview_frame_pt E2 _ (w_H W) mem2 (ms_mem ms3) a HFr3); [lia|].
nwin_tac ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; lia). }
assert (K03 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (K23 a Ha), (K12 a Ha), (K01 a Ha); reflexivity).
assert (HOS : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (proj1 (rec_repA_blocks B ly S _ R O HREP pn Hpn))).
assert (HREP3 : rec_repA B ly S2 (rdW W (ms_mem ms3)) R O).
{ apply (rec_repA_keep B ly S (rdW W mem) ly S2 (rdW W (ms_mem ms3)) R O HREP).
- intros a Ha. apply K03. left. exact Ha.
- intros [p n] Hpn. split; [rewrite Eab; exact (HOS _ Hpn)|]. intros i Hi. cbn [fst snd] in Hi |- *. apply K03. right.
  exists p, n. split; [exact (HOS _ Hpn)|]. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
(* the call of record(18) at 0x8c668, through its contract and cl_callS_wide *)
pmkst HS.
preg HS (10%bv : bv 5) P10. preg HS (1%bv : bv 5) P1. preg HS (2%bv : bv 5) P2. preg HS (3%bv : bv 5) P3.
preg HS (4%bv : bv 5) P4. preg HS (8%bv : bv 5) P8.
cbn [sv_denot] in P1, P10. rewrite (img_env_codeptr E2 HEI2 24892) in P1.
rewrite scc_denot_off0, OLD2, E34 in P2 by lia.
rewrite scc_denot_off0, OLD2, (EE 3%nat 3%bv eq_refl) in P3 by lia.
rewrite scc_denot_off0, OLD2, (EE 4%nat 4%bv eq_refl) in P4 by lia.
rewrite scc_denot_off0, OLD2, Esp in P8 by lia.
assert (Qsp3 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite P2, unsigned_lit_small by lia; lia).
assert (HSIGR : SIG CS_record = BASE + AF_record).
{ rewrite (cmd_sig_prog_PB CS_record ltac:(cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]))). reflexivity. }
pose proof (proj1 HJ2) as HAR3.
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms3)))
by exact (arodata_ok_journalP SEGS RLO RHI scc_relro_img (RO := scc_rob) B _ _ (scc_FP O) ly S W mem md _ ly S2 W (ms_mem ms3) _ 0 HJ2
   (scc_ro_off ly S W mem md O HAR HOS) HROD).
pose proof (st_ok_region_nth E2 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
assert (SRA3 : rdword (rdW W (ms_mem ms3)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
  refine (field_of_region E2 _ 2 (spZ regs) _ (-80) 0 (-80) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 V2 _ _ _ _);
  [cbn [In]; tauto | rewrite scc_denot_off0, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; apply bv_unsigned_in_range | lia]. }
assert (SS03 : rdword (rdW W (ms_mem ms3)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (spZ regs + (-16)) by lia.
  refine (field_of_region E2 _ 2 (spZ regs) _ (-80) 0 (-80) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 V2 _ _ _ _);
  [cbn [In]; tauto | rewrite scc_denot_off0, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; apply bv_unsigned_in_range | lia]. }
clear HR4.
destruct (scc_chain_call SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms3) _ 0 ch
  (raZ regs) (s0Z regs) (spZ regs + (sp1 - spZ regs)) HJ2 Hch
  (scc_FP_low ly S W mem md O (spZ regs) HAR HOS ltac:(rewrite FS in Hslo; lia)) SRA3 SS03 Hra4 ltac:(lia)) as (ch3 & HCH3).
pose proof (rec_repA_ncalls B ly S2 _ R O HREP3) as [Hlen HNC].
assert (HEV3 : st_nev S2 + EV_RECORD R <= EV_MAX).
{ rewrite Hnev2. unfold EV_SUP_CHAIN_CLEAR, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in Hev. unfold EV_RECORD in *. lia. }
assert (HMOK3 : mo_ok MT S2 (XM_RECORD MT R)).
{ rewrite ES2. apply (mo_ok_set_fs MT MTLF). apply (mo_ok_le MT MTL _ _ (XM_SUP_CHAIN_CLEAR MT R id)); [exact MOK|].
unfold XM_SUP_CHAIN_CLEAR.
pose proof (proj1 (scc_xm_pos (Some (dec id)) (snd (sup_chain_clear_m R id)))).
pose proof (proj2 (scc_xm_pos (Some (dec id)) (snd (sup_chain_clear_m R id)))). lia. }
rewrite HSIGR.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms3) (ms_mem ms3) _ SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md
    [(0, fpos)] ly S2 _ 0 RECORD_STK
    ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
     (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O))
    (EV_RECORD R) (sp1 - spZ regs) (getr (ms_regs ms3) 1) ch3 _ HJ2 Qsp3 Hsp1b);
  [ lia | unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK; lia
  | rewrite FS; unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK; lia
  | rewrite P3; exact Hgp | rewrite P4; exact Htp | reflexivity
  | rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | unfold s0Z; rewrite P8, unsigned_lit_small by lia; exact HCH3
  | intros HPRE3; eapply SRr_mono;
    [ exact (TRECORD fx ly S2 W (ms_regs ms3) (ms_mem ms3) _ ch3 REC_CHAIN_CLEAR R O HPRE3 HROD3
        ltac:(rewrite P10; reflexivity) ltac:(unfold REC_CHAIN_CLEAR, REC_FN_COUNT; lia) HREP3 HEV3 HMOK3)
    | cbv beta; unfold apost_base; intros Wq cq _ (lyq & Sq & regsq & memq & mdq & -> & HJq & HPq & HKq);
      exists lyq, Sq, regsq, memq, mdq; split; [rewrite P1; reflexivity | split; [exact HJq | split; [exact HPq | exact HKq]]] ]
  | intros a Ha; destruct (scc_rec_fp_in R O a Ha Hlen) as [Hr | (p & n & Hpn & Hpa)];
    [ apply scc_awr_rec; exact Hr
    | right; left; split;
      [ destruct (inFP_ablocks_fp O p n (a - p) Hpn ltac:(lia)) as (r & Hr & Hrr); exists r; split; [right; right; exact Hr|];
        replace (p + (a - p)) with a in Hrr by lia; exact Hrr
      | exists p, n; split; [rewrite Eab; exact (HOS _ Hpn) | exact Hpa] ] ]
  | intros ly2 S2' W2' regs2' mem2' md2' _ a Ha Hw _; exfalso;
    destruct (scc_rec_fp_in R O a Ha Hlen) as [Hr | (p & n & Hpn & Hpa)];
    [ destruct (scc_rec_loc a Hr) as [_ Hb]; rewrite FS in Hw; lia
    | destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOS _ Hpn)) as (_ & _ & Hc & _); rewrite FS in Hw; lia ] ]. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HK4).
rewrite P1.
(* the record's footprint lies in the recorder's bytes, so the frame, its shadow, its flag and the stack are kept *)
assert (HFPKA : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> KA a).
{ intros a Ha. destruct (scc_rec_fp_in R O a Ha Hlen) as [Hr | (p & n & Hpn & Hpa)];
  [left; exact Hr | right; exists p, n; split; [exact (HOS _ Hpn) | exact Hpa]]. }
pose proof (proj1 HJc4) as HAR4.
pose proof HJ4 as (_ & _ & _ & _ & _ & Hfrs4 & _).
assert (Hfin4 : In (0, fpos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
pose proof HJc4 as (_ & Hly4 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR3 Hly4) as (Eab4 & Efa4 & _).
assert (EFA4 : frame_addr ly4 0 fpos = F) by (rewrite Efa4; reflexivity).
rewrite EFA4 in HFpres4, HFSpres4. change (fs_frame_bytes 0) with 64 in HFpres4, HFSpres4. change (64 / 8) with 8 in HFSpres4.
jafter_call_keep_hi HS 1042%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0;1;2;3;4;5]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc4 V1041 Hfin);
  [ unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; lia
  | unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
  | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & _ & HnS & _); lia
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres4 (a - (SB + F / 8)) ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1028 F _ _ _ _ _ 0 fpos HJc4 V1028 Hfin);
  [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & HnF & _); lia
  | intros a Ha; exact (proj1 (HFpres4 a ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _ 1028 F _ _ _ _ _ 0 fpos HJc4 V1028 Hfin);
  [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & HnF & _); lia
  | intros a Ha; exact (proj1 (HFpres4 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc4 HJ4 V2);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (Hb & _); lia].
- eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc4 HJ4 V2);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (Hb & _); lia].
- eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc4 HJ4 V34);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (Hb & _); lia]. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
clear P2 P3 P4 P8 P10 Qsp3.
remember (havoc E2 1042 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HAE3 : env_agree 32 (Ereg regs (scc_extra B sp1)) E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (OLD3 : forall n, (n < 1042)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (E1046 : ew E3 1046 = getr regs4 10).
{ rewrite HE3. change 1046%nat with (1042 + 4)%nat. rewrite (ew_havoc_new E2 1042 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. reflexivity. }
clear HE3.
assert (W2v : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact V2).
assert (W34v : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3 by lia; exact V34).
assert (W1028 : bv_unsigned (ew E3 1028) = F) by (rewrite OLD3 by lia; exact V1028).
assert (W1040 : bv_unsigned (ew E3 1040) = FL) by (rewrite OLD3 by lia; exact V1040).
assert (W1041 : bv_unsigned (ew E3 1041) = SB + F / 8) by (rewrite OLD3 by lia; exact V1041).
(* run 3: 0x8c66c .. 0x8c68c, s5 := the slot, b's shadow bytes 4 and 5 := 00 (the buffer is usable for the
   snprintf and the arg_s that follow), a0 := b = F + 32, a1 := 16, a2 := "%d" (A_OBJ 51), a3 := id, and the call
   of the snprintf wrapper *)
paj_run_shc RUNP RUNC HS HJ4.
{ scc_awr6 fpos sp1 regs FS W1041 W1028 W2v W34v EFA4. }
rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
pmkst HS.
preg HS (1%bv : bv 5) Q1. preg HS (2%bv : bv 5) Q2. preg HS (3%bv : bv 5) Q3. preg HS (4%bv : bv 5) Q4.
preg HS (10%bv : bv 5) Q10. preg HS (11%bv : bv 5) Q11. preg HS (12%bv : bv 5) Q12. preg HS (13%bv : bv 5) Q13.
cbn [sv_denot] in Q1, Q10. rewrite (img_env_codeptr E3 HEI3 24928) in Q1.
rewrite scc_denot_off0, OLD3, OLD2, E34 in Q2 by lia.
rewrite scc_denot_off0, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in Q3 by lia.
rewrite scc_denot_off0, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in Q4 by lia.
rewrite scc_denot_off0, OLD3, OLD2, (EE 10%nat 10%bv eq_refl), H10 in Q13 by lia.
assert (Q10' : getr (ms_regs ms5) 10 = w64 (F + 32)).
{ rewrite Q10. cbn [sv_denot]. rewrite OLD3 by lia. rewrite E2028. unfold w64.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
assert (Q12' : getr (ms_regs ms5) 12 = w64 0x21f40).
{ rewrite Q12, scc_denot_off0. change 292%nat with (A_OBJ 51).
  rewrite (img_env_atomP E3 (A_OBJ 51) HEI3 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). reflexivity. }
assert (Qsp5 : spZ (ms_regs ms5) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite Q2, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ4) as HAR5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR5 Hfin4) as (_ & _ & HFpres5 & HFSpres5).
rewrite EFA4 in HFpres5, HFSpres5. change (fs_frame_bytes 0) with 64 in HFpres5, HFSpres5.
change (64 / 8) with 8 in HFSpres5.
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms5)))
by exact (arodata_ok_journalP SEGS RLO RHI scc_relro_img (RO := scc_rob) B _ _ (scc_FP O) ly S W mem md _ ly4 S4 W4 (ms_mem ms5) _ _ HJ4
   (scc_ro_off ly S W mem md O HAR HOS) HROD).
(* the snprintf(b, 16, "%d", id) at 0x8c68c, through pass 4b's contract in art form (PASS4-REFIT.md section E):
   the contract, srr_art_postF_of_pf, aj_art_own_atF (b lies in this call's own side-stack frame) *)
pose proof (scc_sn_len id Hid) as EL5. pose proof (dec_length id Hid) as HDL.
pose proof (scc_ro_of_aro ly4 S4 W4 (ms_mem ms5) _ HAR5 HROD5) as HRO5.
destruct (scc_cells ly4 S4 W4 (ms_mem ms5) _ HAR5) as (_ & (HGW1 & cval & HGW2) & _).
pose proof HJ4 as (_ & Hly4' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres4 & _ & _ & _).
pose proof Hly4' as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & Eslo4 & Eshi4 & _).
assert (ZS5 : forall j, 4 <= j < 6 -> rdW W4 (ms_mem ms5) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E3 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
  assert (Hj4 : j = 4 \/ j = 5) by lia. destruct Hj4 as [-> | ->];
  (apply (aview_of_val_mem1 SEGS); [|lia]);
  (lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
   refine (field_of_region E3 _ 1041 (SB + F / 8) _ 0 8 0 8 od 1%N (SLit 0) 0 HR0 W1041 _ _ _ _) end;
   [cbn [In]; tauto | reflexivity | lia | lia]). }
assert (HF8m : F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
assert (HRA5 : range_addressable (rdW W4 (ms_mem ms5)) SHADOW_OFF (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
  assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS5.
  split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia]. }
assert (HFHI : F + 64 <= 0x10000 \/ 0x606000 <= F) by (clear - HFoff HF4096; lia).
assert (HSPHI : F + 64 <= spZ regs + (sp1 - spZ regs) - CMD_SNP_K) by (unfold CMD_SNP_K, ESTACK; rewrite FS in Hslo; lia).
assert (HSPL : 0x606000 + CMD_SNP_K <= spZ regs + (sp1 - spZ regs)) by (unfold CMD_SNP_K, ESTACK; rewrite FS in Hslo; lia).
assert (HSPU : spZ regs <= 2 ^ 47) by lia.
assert (Q13' : argZ (ms_regs ms5) 3 = bv_unsigned (w64 id)).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q13. reflexivity. }
pose proof (ASNPRINTF fx) as ASN. unfold asnprintf_realizes, RtPFCmd.asnprintf_sh, sh_asnprintf_realizes in ASN.
eapply SRr_bind.
{ eapply (aj_art_own_atF (fx := fx) SEGS B LAWS pa_segs_low CMD_SNP_K
    (fun a => F + 32 <= a < F + 32 + sn_len (16 - 1) (PF.pf_dec id))
    (SIG CS___interceptor_trampoline_snprintf) W4 (ms_regs ms5) (ms_mem ms5) SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md
    [(0, fpos)] ly4 S4 _ _ (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24928)) _ HJ4 Qsp5 Hsp1b ltac:(lia)
    ltac:(unfold CMD_SNP_K, ESTACK; lia) ltac:(unfold CMD_SNP_K, ESTACK; rewrite FS; lia) Q1).
  - intros a Ha. rewrite EL5 in Ha. right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA4. change (fs_frame_bytes 0) with 64. lia.
  - apply (srr_art_postF_of_pf (fx := fx) SEGS B).
    { intros a Ha. apply HJpres4. rewrite Qsp5 in Ha. unfold CMD_SNP_K, ESTACK in Ha. rewrite FS. lia. }
    apply (ASN ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _ (F + 32) 16 0x21f40 [] (map (argZ (ms_regs ms5)) [3; 4; 5; 6; 7] ++ [])
      (PF.pf_dec id) cval).
    + exact (ecall_pre_at SEGS B SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md [(0, fpos)] ly4 S4 W4 (ms_mem ms5) _ _
        (ms_regs ms5) (sp1 - spZ regs) HJ4 Qsp5 Hsp1b ltac:(lia) ltac:(rewrite FS; unfold ESTACK; lia)
        ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp)).
    + rewrite Eslo4, Qsp5. unfold CMD_SNP_K, ESTACK. rewrite FS in Hslo. lia.
    + intros a Ha. apply HJpres4. rewrite Qsp5 in Ha. unfold CMD_SNP_K, ESTACK in Ha. rewrite FS. lia.
    + exact Q10'.
    + exact Q11.
    + exact Q12'.
    + exact (CmdRecImg.cmd_consts_view_snp (SK := SK) SEGS B LAWS HB IMG RLO RHI W4 (ms_mem ms5) HROD5).
    + eapply Forall_impl; [|exact scc_cr_low]. intros r Hr. cbv beta in Hr |- *. lia.
    + eapply Forall_impl; [|exact scc_cr_low]. intros r Hr. cbv beta in Hr |- *. rewrite Qsp5, EL5. unfold snp_out.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    + exact HGW1.
    + exact HGW2.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite Qsp5, EL5. unfold snp_out. repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    + rewrite Qsp5, EL5. unfold snp_out. repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + rewrite Qsp5. cbn [length]. lia.
    + rewrite Qsp5, EL5. unfold snp_out. cbn [length]. repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    + apply (FR_cmd_intro _ _ _ _ _ PAI.AI_FMT PAI.AI_PS [PF.AInt id]).
      * split; [lia|]. split.
        { intros i Hi. pose proof (scc_ro_fmt _ HRO5) as HB3. change (Z.of_nat (length PAI.AI_FMT)) with 2 in Hi.
          assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
          destruct Hi3 as [-> | [-> | ->]];
          [ pose proof (HB3 0%nat ltac:(cbn; lia)) as Hb | pose proof (HB3 1%nat ltac:(cbn; lia)) as Hb | pose proof (HB3 2%nat ltac:(cbn; lia)) as Hb ];
          refine (eq_trans Hb _); vm_compute; reflexivity. }
        change (Z.of_nat (length PAI.AI_FMT) + 1) with 3.
        split; [rewrite Qsp5, EL5; unfold snp_out; repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia|].
        split; [left; unfold kLowMemEnd; lia|]. split.
        { change (Z.of_nat (length PAI.AI_FMT) + 1) with 3. exact (scc_fmt_addressable ly4 S4 W4 (ms_mem ms5) _ HAR5). }
        change (Z.of_nat (length PAI.AI_FMT) + 1) with 3. exact (scc_fmt_hull ly4 S4 W4 (ms_mem ms5) _ HAR5).
      * exact PAI.ai_parse.
      * cbn [map arg_of pf_args_asan]. split; [|exact I]. cbn [pf_arg_asan]. split; [exact Hid|].
        cbn [app map]. rewrite Q13'. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        exact (scc_mod32 id).
      * exact (PAI.ai_text id).
      * cbn. exact I.
      * vm_compute. reflexivity.
    + lia.
    + rewrite (scc_dec_len id Hid). lia.
    + lia.
    + rewrite EL5. lia.
    + rewrite Qsp5, EL5. unfold snp_out. cbn [pairwise]. repeat split; try (repeat apply Forall_cons; try apply Forall_nil);
      try (intros y Hy; cbn [In] in Hy; repeat destruct Hy as [<- | Hy]; try destruct Hy); unfold zdisjoint; cbn [fst snd]; lia.
    + rewrite EL5. intros a Ha. destruct (HFpres5 a ltac:(lia)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite Qsp5. unfold ESTACK. lia.
    + rewrite EL5. exact (amem_range_sub_app F 64 (F + 32) (Z.of_nat (length (dec id)) + 1 + 8) HFapp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite EL5. exact HRA5.
    + rewrite EL5. apply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 (ms_mem ms5) _ 0 fpos (F + 32) (Z.of_nat (length (dec id)) + 1) HAR5 Hfin4);
      [rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia | lia].
    + rewrite EL5. unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. lia.
    + exact HFRM. }
cbv beta. intros W6 c6 _ (-> & fx6 & regs6 & mem6 & md6 & Hfx6 & -> & HJ6 & HP6 & (HA06 & HBUF6) & HKEEP6).
apply (srr_apost_baseF_lift (fx := fx) SEGS fx6); [exact Hfx6|].
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (scc_st_ok_fx fx fx6 Ev ssv msv ltac:(reflexivity) HS) as HSx end.
cbn [ms_regs ms_pc_val ms_mem ms_rom restrict mkst] in HSx.
clear HS. rename HSx into HS.
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR6 Hfin4) as (_ & _ & HFpres6 & HFSpres6).
rewrite EFA4 in HFpres6, HFSpres6. change (fs_frame_bytes 0) with 64 in HFpres6, HFSpres6.
change (64 / 8) with 8 in HFSpres6.
pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres6 & _ & _ & _).
assert (HSH1 : 0 <= SB + F / 8 /\ SB + F / 8 + 8 <= 2 ^ 64) by (unfold SB; lia).
assert (HSPAC : alloc_ceiling + 8192 <= spZ regs + (sp1 - spZ regs) - CMD_SNP_K)
  by (unfold CMD_SNP_K, ESTACK; rewrite FS in Hslo; lia).
(* the frame, its flag, its shadow and the two stack pieces across the snprintf: it writes only b and its scratch *)
jafter_call_fx fx6 HS 1058%nat regs6 (mrestrict (w_H W4) mem6) HP6 [0;1;2;3;4;5]%nat HS6.
match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply region_kept_hi; [exact W1041 | intros a Ha; apply HKEEP6; cbv beta; unfold SB, CMD_SNP_K, ESTACK in *; rewrite ?EL5, ?Qsp5 in *; lia |].
  intros a Ha. replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
  exact (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(lia))).
- eapply region_kept_hi; [exact W1028 | intros a Ha; apply HKEEP6; cbv beta; unfold SB, CMD_SNP_K, ESTACK in *; rewrite ?EL5, ?Qsp5 in *; lia |].
  intros a Ha. exact (proj1 (HFpres6 a ltac:(lia))).
- eapply region_kept_hi; [exact W1028 | intros a Ha; apply HKEEP6; cbv beta; unfold SB, CMD_SNP_K, ESTACK in *; rewrite ?EL5, ?Qsp5 in *; lia |].
  intros a Ha. exact (proj1 (HFpres6 a ltac:(lia))).
- eapply region_kept_hi; [exact W2v | intros a Ha; apply HKEEP6; cbv beta; unfold SB, CMD_SNP_K, ESTACK in *; rewrite ?EL5, ?Qsp5 in *; lia |].
  intros a Ha. apply HJpres6. rewrite FS. lia.
- eapply region_kept_hi; [exact W2v | intros a Ha; apply HKEEP6; cbv beta; unfold SB, CMD_SNP_K, ESTACK in *; rewrite ?EL5, ?Qsp5 in *; lia |].
  intros a Ha. apply HJpres6. rewrite FS. lia.
- eapply region_kept_hi; [exact W34v | intros a Ha; apply HKEEP6; cbv beta; unfold SB, CMD_SNP_K, ESTACK in *; rewrite ?EL5, ?Qsp5 in *; lia |].
  intros a Ha. apply HJpres6. rewrite FS. lia. }
rewrite <- restrict_mkst_fx in HS6. clear HS. rename HS6 into HS.
remember (havoc E3 1058 (map (getr regs6) CLOB)) as E4 eqn:HE4 in HS.
assert (HAE4 : env_agree 32 (Ereg regs (scc_extra B sp1)) E4) by (rewrite HE4; apply env_agree_havoc_ge; [lia | exact HAE3]).
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (OLD4 : forall n, (n < 1058)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
clear HE4.
assert (X2v : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact W2v).
assert (X34v : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact W34v).
assert (X1028 : bv_unsigned (ew E4 1028) = F) by (rewrite OLD4 by lia; exact W1028).
assert (X1041 : bv_unsigned (ew E4 1041) = SB + F / 8) by (rewrite OLD4 by lia; exact W1041).
assert (E41028 : ew E4 1028 = Z_to_bv 64 F) by (rewrite OLD4 by lia; rewrite OLD3 by lia; exact E2028).
assert (E41046 : ew E4 1046 = getr regs4 10) by (rewrite OLD4 by lia; exact E1046).
pose proof (SRr_run_pi_AJ (fx := fx6) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNP6.
pose proof (SRr_run_pi_AJ_call (fx := fx6) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNC6.
(* run 4: 0x8c690 .. 0x8c698, a0 := the slot, a1 := b, the call of arg_s *)
paj_run_shc RUNP6 RUNC6 HS HJ6.
{ scc_awr6 fpos sp1 regs FS X1041 X1028 X2v X34v EFA4. }
rename ms into ms7, mat into mat7, HF into HF7, HFr into HFr7, HG into HG7.
(* the call of arg_s(slot, b) at 0x8c698 *)
destruct HK4 as (Fr4 & O1 & Ha04 & Hperm4 & HlenF4 & HFO4 & HREP4 & HO1 & Hbb4 & Hmle4).
assert (HO1live : forall pn, In pn O1 -> In pn (ablocks B ly4 S4))
  by (intros pn Hp; exact (proj1 (rec_repA_blocks B ly4 S4 _ _ O1 HREP4 pn Hp))).
set (KB := fun a : Z => in_recA a \/ (exists p n, In (p, n) O1 /\ p <= a < p + req_size n)).
assert (KBLOC : forall a, KB a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8)).
{ intros a [Ha | (p & n & Hpn & Hpa)].
- destruct (scc_rec_loc a Ha) as [Hi Hr]. split; [lia|]. split; [lia|]. unfold SB; lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR5 (HO1live _ Hpn)) as (_ & Hp4096 & Hpceil & Hpapp & Hpres' & _).
  pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 (ms_mem ms5) _ p n 0 fpos HAR5 (HO1live _ Hpn) Hfin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA4 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. unfold SB; lia. }
assert (K56 : forall a, KB a -> rdW W4 mem6 a = rdW W4 (ms_mem ms5) a).
{ intros a Ha. destruct (KBLOC a Ha) as (Hb & HnF & HnS). apply HKEEP6; rewrite ?EL5, ?Qsp5;
  unfold CMD_SNP_K, ESTACK in *; lia. }
assert (K67 : forall a, KB a -> rdW W4 (ms_mem ms7) a = rdW W4 mem6 a).
{ intros a Ha. destruct (KBLOC a Ha) as (Hb & HnF & HnS).
  apply (aview_frame_pt E4 _ (w_H W4) mem6 (ms_mem ms7) a HFr7); [lia|].
  nwin_tac ltac:(fun H => rewrite ?X2v, ?X34v, ?X1028, ?X1041 in H; unfold SB in *; lia). }
assert (K57 : forall a, KB a -> rdW W4 (ms_mem ms7) a = rdW W4 mem4 a).
{ intros a Ha. rewrite (K67 a Ha), (K56 a Ha). destruct (KBLOC a Ha) as (Hb & HnF & HnS).
  apply (aview_frame_pt E3 _ (w_H W4) mem4 (ms_mem ms5) a HFr5); [lia|].
  nwin_tac ltac:(fun H => rewrite ?W2v, ?W34v, ?W1028, ?W1041 in H; unfold SB in *; lia). }
assert (HREP7 : rec_repA B ly4 S4 (rdW W4 (ms_mem ms7)) (rec_record R REC_CHAIN_CLEAR []) O1).
{ apply (rec_repA_keep B ly4 S4 (rdW W4 mem4) ly4 S4 (rdW W4 (ms_mem ms7)) _ O1 HREP4).
- intros a Ha. apply K57. left. exact Ha.
- intros [p n] Hpn. split; [exact (HO1live _ Hpn)|]. intros i Hi. cbn [fst snd] in Hi |- *. apply K57. right.
  exists p, n. split; [exact Hpn|]. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
assert (HSTR7 : astr_atR (rdW W4 (ms_mem ms7)) (F + 32) (dec id)).
{ apply (scc_buf_str W4 (ms_mem ms7) (F + 32) id Hid). intros i Hi.
  rewrite (aview_frame_pt E4 _ (w_H W4) mem6 (ms_mem ms7) (F + 32 + i) HFr7);
  [ exact (HBUF6 i Hi) | rewrite EL5 in Hi; lia |].
  nwin_tac ltac:(fun H => rewrite ?X2v, ?X34v, ?X1028, ?X1041 in H; rewrite ?EL5 in Hi; unfold SB in *; lia). }
pose proof (proj1 HJ6) as HAR7p.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR7p Hfin4) as (_ & _ & HFpres7 & HFSpres7).
rewrite EFA4 in HFpres7, HFSpres7. change (fs_frame_bytes 0) with 64 in HFpres7, HFSpres7.
change (64 / 8) with 8 in HFSpres7.
pmkst HS.
preg HS (1%bv : bv 5) T1. preg HS (2%bv : bv 5) T2. preg HS (3%bv : bv 5) T3. preg HS (4%bv : bv 5) T4.
preg HS (8%bv : bv 5) T8. preg HS (10%bv : bv 5) T10. preg HS (11%bv : bv 5) T11.
cbn [sv_denot] in T1, T10, T11. rewrite (img_env_codeptr E4 HEI4 24940) in T1.
rewrite scc_denot_off0, OLD4 in T2 by lia. rewrite OLD3, OLD2, E34 in T2 by lia.
rewrite scc_denot_off0, OLD4 in T3 by lia. rewrite OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in T3 by lia.
rewrite scc_denot_off0, OLD4 in T4 by lia. rewrite OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in T4 by lia.
rewrite scc_denot_off0, OLD4 in T8 by lia. rewrite OLD3, OLD2, Esp in T8 by lia.
rewrite E41046, Ha04 in T10.
assert (T10' : getr (ms_regs ms7) 10 = w64 (rec_slot R)) by (rewrite T10, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (T11' : getr (ms_regs ms7) 11 = w64 (F + 32)).
{ rewrite T11, E41028. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
assert (Qsp7 : spZ (ms_regs ms7) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite T2, unsigned_lit_small by lia; lia).
assert (HROD7 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms7)))
by exact (arodata_ok_journalP SEGS RLO RHI scc_relro_img (RO := scc_rob) B _ _ (scc_FP O) ly S W mem md _ ly4 S4 W4 (ms_mem ms7) _ _ HJ6
   (scc_ro_off ly S W mem md O HAR HOS) HROD).
pose proof (scc_ro_of_aro ly4 S4 W4 (ms_mem ms7) _ HAR7p HROD7) as HRO7.
assert (ZS7 : forall j, 4 <= j < 6 -> rdW W4 (ms_mem ms7) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E4 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
  assert (Hj4 : j = 4 \/ j = 5) by lia. destruct Hj4 as [-> | ->];
  (apply (aview_of_val_mem1 SEGS); [|lia]);
  (lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
   refine (field_of_region E4 _ 1041 (SB + F / 8) _ 0 8 0 8 od 1%N (SLit 0) 0 HR0 X1041 _ _ _ _) end;
   [cbn [In]; tauto | reflexivity | lia | lia]). }
assert (HRA7 : range_addressable (rdW W4 (ms_mem ms7)) SHADOW_OFF (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by (pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
  rewrite Hx8, Z.add_assoc. apply ZS7.
  split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia]. }
assert (HSIGA : SIG CS_arg_s = BASE + AF_arg_s).
{ rewrite (cmd_sig_prog_PB CS_arg_s ltac:(cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]))). reflexivity. }
pose proof (rec_repA_ncalls B ly4 S4 _ _ O1 HREP7) as [Hlen7 HNC7].
assert (HEV7 : st_nev S4 + EV_ARG_S <= EV_MAX).
{ pose proof HJ6 as (_ & _ & _ & _ & _ & _ & Hnev6 & _). pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _).
  unfold EV_SUP_CHAIN_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC, EV_ARG_S, EV_RECORD in *. rewrite Hnev2 in *. lia. }
assert (HLIVE7 : blocks_bytes S4 + LIVE_ARG_S (Some (dec id)) <= LIVE_MAX).
{ assert (HBB2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
  assert (HL0 : 0 <= LIVE_ANSWER (snd (sup_chain_clear_m R id))) by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
  unfold LIVE_SUP_CHAIN_CLEAR in Hlive. lia. }
assert (HMOK7 : mo_ok MT S4 (XM_ARG_S MT (Some (dec id)))).
{ pose proof (scc_xm_pos (Some (dec id)) (snd (sup_chain_clear_m R id))) as [Hx1 Hx2].
  apply (mok_station MT S2 S4 (XM_SUP_CHAIN_CLEAR MT R id) (XM_RECORD MT R) _ MTL); [| exact Hmle4 | exact Hx1 | unfold XM_SUP_CHAIN_CLEAR; lia].
  rewrite ES2. apply (mo_ok_set_fs MT MTLF). exact MOK. }
pose proof (st_ok_region_nth E4 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
assert (SRA7 : rdword (rdW W4 (ms_mem ms7)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
  refine (field_of_region E4 _ 2 (spZ regs) _ (-80) 0 (-80) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 X2v _ _ _ _);
  [cbn [In]; tauto | rewrite scc_denot_off0, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; apply bv_unsigned_in_range | lia]. }
assert (SS07 : rdword (rdW W4 (ms_mem ms7)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (spZ regs + (-16)) by lia.
  refine (field_of_region E4 _ 2 (spZ regs) _ (-80) 0 (-80) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 X2v _ _ _ _);
  [cbn [In]; tauto | rewrite scc_denot_off0, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; apply bv_unsigned_in_range | lia]. }
clear HR4.
destruct (scc_chain_call SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md [(0, fpos)] ly4 S4 W4 (ms_mem ms7) _ _ ch
  (raZ regs) (s0Z regs) (spZ regs + (sp1 - spZ regs)) HJ6 Hch
  (scc_FP_low ly S W mem md O (spZ regs) HAR HOS ltac:(rewrite FS in Hslo; lia)) SRA7 SS07 Hra4 ltac:(lia)) as (ch7 & HCH7).
assert (HF32 : (F + 32) mod 8 = 0).
{ rewrite HFd8. replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by ring. apply Z_mod_mult. }
assert (HOBJ7 : afobj SEGS B ly4 S4 W4 (ms_mem ms7) (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ split; [|split; [exact HF32 | exact HRA7]].
  exists 0, fpos. rewrite EFA4. change (fs_frame_bytes 0) with 64.
  split; [exact Hfin4|]. split; [lia|]. split; [exact HFm8|]. split; lia. }
assert (HTAIL7 : forall x, Some (dec id) = Some x -> atail_vis SEGS W4 (ms_mem ms7) (F + 32 + Z.of_nat (length x))).
{ intros x Hx. injection Hx as <-. intros a Ha.
  pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length (dec id))) 8 ltac:(lia)).
  apply (aview_some_of_apresent SEGS). exact (proj1 (HFpres7 a ltac:(lia))). }
rewrite HSIGA.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W4 (ms_regs ms7) (ms_mem ms7) _ SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md
    [(0, fpos)] ly4 S4 _ _ ARG_S_STK
    [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
     (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))),
      rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))) + 8)]
    EV_ARG_S (sp1 - spZ regs) (getr (ms_regs ms7) 1) ch7 _ HJ6 Qsp7 Hsp1b);
  [ lia | unfold ARG_S_STK, XMALLOC_STK, ASTACK; lia
  | rewrite FS; unfold ARG_S_STK, XMALLOC_STK, ASTACK; lia
  | rewrite T3; exact Hgp | rewrite T4; exact Htp | reflexivity
  | rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite T1, unsigned_lit_small by lia; lia
  | unfold s0Z; rewrite T8, unsigned_lit_small by lia; exact HCH7
  | intros HPRE7; eapply SRr_mono;
    [ exact (TARG_S fx6 ly4 S4 W4 (ms_regs ms7) (ms_mem ms7) _ ch7 (rec_slot R) (F + 32) REC_CHAIN_CLEAR [] (Some (dec id)) R O1
        HPRE7 HROD7 HRO7 T10' T11' eq_refl HREP7
        ltac:(right; exists (dec id); split; [reflexivity|]; split; [exact HSTR7|]; split; [pose proof (dec_length id Hid); unfold LMAX; lia | exact HOBJ7])
        HTAIL7 HEV7 HLIVE7 HMOK7)
    | cbv beta; unfold apost_base; intros Wq cq _ (lyq & Sq & regsq & memq & mdq & -> & HJq & HPq & HKq);
      exists lyq, Sq, regsq, memq, mdq; split; [reflexivity | split; [exact HJq | split; [exact HPq | exact HKq]]] ]
  | intros a Ha; apply scc_awr_rec; exact (scc_args_fp_in R a Hlen Ha)
  | intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _; exfalso;
    destruct (scc_rec_loc a (scc_args_fp_in R a Hlen Ha)) as [_ Hb]; rewrite FS in Hw; lia ]. }
cbv beta. intros W8 c8 _ (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HJc8 & HP8 & HK8).
rewrite T1.
destruct HK8 as (Hbb8 & Hmle8 & [(Hl6 & _ & _) | (_ & pnew & Hpn64 & Hperm8 & Hfresh8 & HREP8)]);
  [cbn [length Z.of_nat] in Hl6; unfold REC_ARGS_MAX in Hl6; lia|].
pose proof (proj1 HJc8) as HAR8.
pose proof HJ8 as (_ & _ & _ & _ & _ & Hfrs8 & _).
assert (Hfin8 : In (0, fpos) (frames S8)) by (rewrite Hfrs8; left; reflexivity).
pose proof HJc8 as (_ & Hly8 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly8 HAR7p Hly8) as (Eab8 & Efa8 & _).
assert (EFA8 : frame_addr ly8 0 fpos = F) by (rewrite Efa8; exact EFA4).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8).
rewrite EFA8 in HFpres8, HFSpres8. change (fs_frame_bytes 0) with 64 in HFpres8, HFSpres8. change (64 / 8) with 8 in HFSpres8.
assert (HFPA : forall a, inFP [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
     (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))),
      rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))) + 8)] a ->
  0x10000 <= a < 0x606000).
{ intros a Ha. exact (proj2 (scc_rec_loc a (scc_args_fp_in R a Hlen Ha))). }
jafter_call_fx fx6 HS 1074%nat regs8 (mrestrict (w_H W8) mem8) HP8 [0;1;2;3;4;5]%nat HS8.
match type of HS8 with ?tq -> _ => assert (HRK : tq); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub (segs := SEGS) B E4 _ _ _ ly4 S4 W4 (ms_mem ms7) _ ly8 S8 W8 mem8 md8 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc8 X1041 Hfin4);
  [ unfold shadow_addr; rewrite EFA4; rewrite <- SB_SHADOW_OFF; lia
  | unfold shadow_addr; rewrite EFA4; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
  | intros a Ha HFa; pose proof (HFPA a HFa); unfold SB in *; lia
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres8 (a - (SB + F / 8)) ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E4 _ _ _ ly4 S4 W4 (ms_mem ms7) _ ly8 S8 W8 mem8 md8 _ 1028 F _ _ _ _ _ 0 fpos HJc8 X1028 Hfin4);
  [ rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; pose proof (HFPA a HFa); lia
  | intros a Ha; exact (proj1 (HFpres8 a ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E4 _ _ _ ly4 S4 W4 (ms_mem ms7) _ ly8 S8 W8 mem8 md8 _ 1028 F _ _ _ _ _ 0 fpos HJc8 X1028 Hfin4);
  [ rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; pose proof (HFPA a HFa); lia
  | intros a Ha; exact (proj1 (HFpres8 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc8 HJ8 X2v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; pose proof (HFPA a HFa); rewrite FS in Hslo; lia].
- eapply (region_kept_stack_sub SEGS B E4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc8 HJ8 X2v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; pose proof (HFPA a HFa); rewrite FS in Hslo; lia].
- eapply (region_kept_stack_sub SEGS B E4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc8 HJ8 X34v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; pose proof (HFPA a HFa); rewrite FS in Hslo; lia]. }
rewrite <- restrict_mkst_fx in HS8. clear HS. rename HS8 into HS.
remember (havoc E4 1074 (map (getr regs8) CLOB)) as E5 eqn:HE5 in HS.
assert (HAE5 : env_agree 32 (Ereg regs (scc_extra B sp1)) E5) by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact HAE4]).
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI4 | unfold A_LIM; lia]).
assert (OLD5 : forall n, (n < 1074)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
clear HE5.
assert (Y2v : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact X2v).
assert (Y34v : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact X34v).
assert (Y1028 : bv_unsigned (ew E5 1028) = F) by (rewrite OLD5 by lia; exact X1028).
assert (Y1041 : bv_unsigned (ew E5 1041) = SB + F / 8) by (rewrite OLD5 by lia; exact X1041).
(* run 5: 0x8c69c .. 0x8c6b0, b's shadow bytes 4 and 5 := f8 again, a0 := "chain_clear" (A_OBJ 82), a1 := 11, the
   call of rec_shape_of *)
paj_run_shc RUNP6 RUNC6 HS HJ8.
{ scc_awr6 fpos sp1 regs FS Y1041 Y1028 Y2v Y34v EFA8. }
rename ms into ms9, mat into mat9, HF into HF9, HFr into HFr9, HG into HG9.
pmkst HS.
preg HS (1%bv : bv 5) Z1. preg HS (2%bv : bv 5) Z2. preg HS (3%bv : bv 5) Z3. preg HS (4%bv : bv 5) Z4.
preg HS (10%bv : bv 5) Z10. preg HS (11%bv : bv 5) Z11.
cbn [sv_denot] in Z1, Z11. rewrite (img_env_codeptr E5 HEI5 24964) in Z1.
rewrite scc_denot_off0, OLD5, OLD4, OLD3, OLD2, E34 in Z2 by lia.
rewrite scc_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in Z3 by lia.
rewrite scc_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in Z4 by lia.
assert (Z10' : getr (ms_regs ms9) 10 = w64 0x21f80).
{ rewrite Z10, scc_denot_off0. change 323%nat with (A_OBJ 82).
  rewrite (img_env_atomP E5 (A_OBJ 82) HEI5 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 82%nat ltac:(vm_compute; lia)). reflexivity. }
assert (Z11' : getr (ms_regs ms9) 11 = w64 (Z.of_nat (length scc_verb))) by (rewrite Z11; reflexivity).
assert (Qsp9 : spZ (ms_regs ms9) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite Z2, unsigned_lit_small by lia; lia).
assert (HROD9 : arodata_okP SEGS RLO RHI B (rdW W8 (ms_mem ms9)))
by exact (arodata_ok_journalP SEGS RLO RHI scc_relro_img (RO := scc_rob) B _ _ (scc_FP O) ly S W mem md _ ly8 S8 W8 (ms_mem ms9) _ _ HJ8
   (scc_ro_off ly S W mem md O HAR HOS) HROD).
pose proof (proj1 HJ8) as HAR9.
pose proof (scc_ro_of_aro ly8 S8 W8 (ms_mem ms9) _ HAR9 HROD9) as HRO9.
assert (HSIGR2 : SIG CS_rec_shape_of = BASE + AF_rec_shape_of).
{ rewrite (cmd_sig_prog_PB CS_rec_shape_of ltac:(cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]))). reflexivity. }
assert (HEV9 : st_nev S8 + EV_REC_SHAPE_OF <= EV_MAX).
{ pose proof HJ8 as (_ & _ & _ & _ & _ & _ & Hnev8 & _). pose proof HJ6 as (_ & _ & _ & _ & _ & _ & Hnev6 & _).
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _).
  unfold EV_SUP_CHAIN_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC, EV_ARG_S, EV_RECORD, EV_REC_SHAPE_OF in *. rewrite Hnev2 in *. lia. }
rewrite HSIGR2.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W8 (ms_regs ms9) (ms_mem ms9) _ SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md
    [(0, fpos)] ly8 S8 _ _ REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (sp1 - spZ regs) (getr (ms_regs ms9) 1) _ HJ8 Qsp9 Hsp1b);
  [ lia | unfold REC_SHAPE_OF_STK, ESTACK; lia
  | rewrite FS; unfold REC_SHAPE_OF_STK, ESTACK; lia
  | rewrite Z3; exact Hgp | rewrite Z4; exact Htp | reflexivity
  | rewrite Z1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite Z1, unsigned_lit_small by lia; lia
  | intros HPRE9; eapply SRr_mono;
    [ exact (TREC_SHAPE_OF fx6 ly8 S8 W8 (ms_regs ms9) (ms_mem ms9) _ 0x21f80 scc_verb HPRE9 HROD9 Z10' ltac:(lia) Z11'
        ltac:(rewrite scc_verb_len; lia) HRO9 VOBJS
        (fun _ => conj (scc_abytes_prefix _ _ _ _ ltac:(rewrite scc_verb_ro; exact (scc_ro_verb _ HRO9)))
                       (or_intror (scc_verb_argA ly8 S8 _ [] (scc_ro_verb _ HRO9))))
        HEV9)
    | cbv beta; unfold apost_base; intros Wq cq _ (lyq & Sq & regsq & memq & mdq & -> & HJq & HPq & HKq);
      exists lyq, Sq, regsq, memq, mdq; split; [reflexivity | split; [exact HJq | split; [exact HPq | exact HKq]]] ]
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]. }
cbv beta. intros W10 c10 _ (ly10 & S10 & regs10 & mem10 & md10 & -> & HJ10 & HJc10 & HP10 & HK10).
rewrite Z1.
destruct HK10 as ((q & Hq10 & Hq64 & HqA) & Hperm10 & -> & ->).
pose proof (proj1 HJc10) as HAR10.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR10 Hfin8) as (_ & _ & HFpres10 & HFSpres10).
rewrite EFA8 in HFpres10, HFSpres10. change (fs_frame_bytes 0) with 64 in HFpres10, HFSpres10. change (64 / 8) with 8 in HFSpres10.
jafter_call_fx fx6 HS 1090%nat regs10 (mrestrict (w_H W10) mem10) HP10 [0;1;2;3;4;5]%nat HS10.
match type of HS10 with ?tq -> _ => assert (HRK : tq); [|specialize (HS10 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub (segs := SEGS) B E5 _ _ _ ly8 S8 W8 (ms_mem ms9) _ ly8 S8 W10 mem10 md10 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc10 Y1041 Hfin8);
  [ unfold shadow_addr; rewrite EFA8; rewrite <- SB_SHADOW_OFF; lia
  | unfold shadow_addr; rewrite EFA8; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
  | intros a Ha HFa; exfalso; exact (inFP_nil a HFa)
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres10 (a - (SB + F / 8)) ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E5 _ _ _ ly8 S8 W8 (ms_mem ms9) _ ly8 S8 W10 mem10 md10 _ 1028 F _ _ _ _ _ 0 fpos HJc10 Y1028 Hfin8);
  [ rewrite EFA8; lia | rewrite EFA8; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; exfalso; exact (inFP_nil a HFa)
  | intros a Ha; exact (proj1 (HFpres10 a ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E5 _ _ _ ly8 S8 W8 (ms_mem ms9) _ ly8 S8 W10 mem10 md10 _ 1028 F _ _ _ _ _ 0 fpos HJc10 Y1028 Hfin8);
  [ rewrite EFA8; lia | rewrite EFA8; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; exfalso; exact (inFP_nil a HFa)
  | intros a Ha; exact (proj1 (HFpres10 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc10 HJ10 Y2v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; exfalso; exact (inFP_nil a HFa)].
- eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc10 HJ10 Y2v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; exfalso; exact (inFP_nil a HFa)].
- eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc10 HJ10 Y34v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; exfalso; exact (inFP_nil a HFa)]. }
rewrite <- restrict_mkst_fx in HS10. clear HS. rename HS10 into HS.
remember (havoc E5 1090 (map (getr regs10) CLOB)) as E6 eqn:HE6 in HS.
assert (HAE6 : env_agree 32 (Ereg regs (scc_extra B sp1)) E6) by (rewrite HE6; apply env_agree_havoc_ge; [lia | exact HAE5]).
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc_hi; [exact HEI5 | unfold A_LIM; lia]).
assert (OLD6 : forall n, (n < 1090)%nat -> ew E6 n = ew E5 n) by (intros n Hn; rewrite HE6; apply ew_havoc_old; exact Hn).
assert (E61094 : ew E6 1094 = getr regs10 10).
{ rewrite HE6. change 1094%nat with (1090 + 4)%nat. rewrite (ew_havoc_new E5 1090 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE6.
assert (Z2v : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Y2v).
assert (Z34v : bv_unsigned (ew E6 34) = sp1) by (rewrite OLD6 by lia; exact Y34v).
assert (Z1028 : bv_unsigned (ew E6 1028) = F) by (rewrite OLD6 by lia; exact Y1028).
assert (Z1041 : bv_unsigned (ew E6 1041) = SB + F / 8) by (rewrite OLD6 by lia; exact Y1041).
(* run 6: 0x8c6b4 .. 0x8c6c0, a1 := the shape, a2 := 1, a0 := the slot, the call of answer *)
paj_run_shc RUNP6 RUNC6 HS HJ10.
{ scc_awr6 fpos sp1 regs FS Z1041 Z1028 Z2v Z34v EFA8. }
rename ms into ms11, mat into mat11, HF into HF11, HFr into HFr11, HG into HG11.
(* the call of answer(slot, shape, 1) at 0x8c6c0, whose post is FP-existential (its chain reaches the snprintf) *)
pmkst HS.
preg HS (1%bv : bv 5) U1. preg HS (2%bv : bv 5) U2. preg HS (3%bv : bv 5) U3. preg HS (4%bv : bv 5) U4.
preg HS (8%bv : bv 5) U8. preg HS (10%bv : bv 5) U10. preg HS (11%bv : bv 5) U11. preg HS (12%bv : bv 5) U12.
cbn [sv_denot] in U1, U11, U12. rewrite (img_env_codeptr E6 HEI6 24980) in U1.
rewrite scc_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, E34 in U2 by lia.
rewrite scc_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in U3 by lia.
rewrite scc_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in U4 by lia.
rewrite scc_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, Esp in U8 by lia.
rewrite scc_denot_off0 in U10. rewrite OLD6, OLD5 in U10 by lia. rewrite E41046, Ha04 in U10.
assert (U10' : getr (ms_regs ms11) 10 = w64 (rec_slot R)) by exact U10.
assert (U11' : getr (ms_regs ms11) 11 = w64 q) by (rewrite U11, Z.add_0_r, E61094, Hq10; apply Z_to_bv_bv_unsigned).
assert (Qsp11 : spZ (ms_regs ms11) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite U2, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ10) as HAR11.
assert (HROD11 : arodata_okP SEGS RLO RHI B (rdW W10 (ms_mem ms11)))
by exact (arodata_ok_journalP SEGS RLO RHI scc_relro_img (RO := scc_rob) B _ _ (scc_FP O) ly S W mem md _ ly8 S8 W10 (ms_mem ms11) _ _ HJ10
   (scc_ro_off ly S W mem md O HAR HOS) HROD).
pose proof (scc_ro_of_aro ly8 S8 W10 (ms_mem ms11) _ HAR11 HROD11) as HRO11.
(* the recorder, its blocks and the shape across rec_shape_of and this run *)
cbn [sarg app] in Hpn64, Hperm8, Hfresh8, HREP8.
set (nd := Z.of_nat (length (dec id)) + 1) in *.
set (O2 := (pnew, nd) :: O1) in *.
set (R2 := rec_record R REC_CHAIN_CLEAR [dec id]) in *.
assert (HO2live : forall pn, In pn O2 -> In pn (ablocks B ly8 S8))
  by (intros pn Hp; exact (proj1 (rec_repA_blocks B ly8 S8 _ _ O2 HREP8 pn Hp))).
assert (KLOC2 : forall a, in_recA a \/ (exists p n, In (p, n) O2 /\ p <= a < p + req_size n) ->
  0 <= a < 2 ^ 64 /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a < alloc_ceiling).
{ intros a [Ha | (p & n & Hpn & Hpa)].
  - destruct (scc_rec_loc a Ha) as [Hi Hr]. split; [lia|]. split; [lia|]. split; [unfold SB; lia | lia].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR11 (HO2live _ Hpn)) as (_ & Hp4096 & Hpceil & Hpapp & _ & _).
    pose proof (sep_block_frame SEGS B LAWS ly8 S8 W10 (ms_mem ms11) _ p n 0 fpos HAR11 (HO2live _ Hpn) Hfin8) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA8 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    split; [lia|]. split; [lia|]. split; [unfold SB; lia | lia]. }
assert (KREC : forall a, in_recA a -> rdW W10 (ms_mem ms11) a = rdW W8 mem8 a).
{ intros a Ha. destruct (KLOC2 a (or_introl Ha)) as (Hb64 & HnF & HnS & Hac).
  rewrite (aview_frame_pt E6 _ (w_H W10) mem10 (ms_mem ms11) a HFr11);
  [| lia | nwin_tac ltac:(fun H => rewrite ?Z2v, ?Z34v, ?Z1028, ?Z1041 in H; unfold SB in *; lia)].
  rewrite (scc_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc10 (sink_closed_pos [] (Forall_nil _)) Ha (inFP_nil a)).
  exact (aview_frame_pt E5 _ (w_H W8) mem8 (ms_mem ms9) a HFr9 ltac:(lia)
    ltac:(nwin_tac ltac:(fun H => rewrite ?Y2v, ?Y34v, ?Y1028, ?Y1041 in H; unfold SB in *; lia))). }
assert (KBLK : forall p n i, In (p, n) O2 -> 0 <= i < n -> rdW W10 (ms_mem ms11) (p + i) = rdW W8 mem8 (p + i)).
{ intros p n i Hpn Hi.
  assert (Hmem : In (p, n) (ablocks B ly8 S8)) by exact (HO2live _ Hpn).
  assert (Hri : p <= p + i < p + req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  destruct (KLOC2 (p + i) (or_intror (ex_intro _ p (ex_intro _ n (conj Hpn Hri))))) as (Hb64 & HnF & HnS & Hac).
  rewrite (aview_frame_pt E6 _ (w_H W10) mem10 (ms_mem ms11) (p + i) HFr11);
  [| lia | nwin_tac ltac:(fun H => rewrite ?Z2v, ?Z34v, ?Z1028, ?Z1041 in H; unfold SB in *; lia)].
  rewrite (scc_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n i HJc10 HAR9 (fun a Ha => False_ind _ (inFP_nil a Ha))
    Hmem Hmem Hi).
  exact (aview_frame_pt E5 _ (w_H W8) mem8 (ms_mem ms9) (p + i) HFr9 ltac:(lia)
    ltac:(nwin_tac ltac:(fun H => rewrite ?Y2v, ?Y34v, ?Y1028, ?Y1041 in H; unfold SB in *; lia))). }
assert (HREP11 : rec_repA B ly8 S8 (rdW W10 (ms_mem ms11)) R2 O2).
{ apply (rec_repA_keep B ly8 S8 (rdW W8 mem8) ly8 S8 (rdW W10 (ms_mem ms11)) R2 O2 HREP8).
  - intros a Ha. exact (KREC a Ha).
  - intros [p n] Hpn. split; [exact (HO2live _ Hpn)|]. intros i Hi. cbn [fst snd] in Hi |- *.
    exact (KBLK p n i Hpn ltac:(cbn [snd] in Hi; lia)). }
(* the frame chain answer's afn_pre asks of s0 = the entry sp (class B), as at every call of this walk *)
pose proof (st_ok_region_nth E6 _ _ 4 _ HS eq_refl) as HR4b. cbn [ms_mem restrict mkst] in HR4b.
assert (SRA11 : rdword (rdW W10 (ms_mem ms11)) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
  refine (field_of_region E6 _ 2 (spZ regs) _ (-80) 0 (-80) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4b Z2v _ _ _ _);
  [cbn [In]; tauto
  | rewrite scc_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; apply bv_unsigned_in_range | lia]. }
assert (SS011 : rdword (rdW W10 (ms_mem ms11)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (spZ regs + (-16)) by lia.
  refine (field_of_region E6 _ 2 (spZ regs) _ (-80) 0 (-80) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4b Z2v _ _ _ _);
  [cbn [In]; tauto
  | rewrite scc_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; apply bv_unsigned_in_range | lia]. }
clear HR4b.
destruct (scc_chain_call SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md [(0, fpos)] ly8 S8 W10 (ms_mem ms11) _ _ ch
  (raZ regs) (s0Z regs) (spZ regs + (sp1 - spZ regs)) HJ10 Hch
  (scc_FP_low ly S W mem md O (spZ regs) HAR HOS ltac:(rewrite FS in Hslo; lia)) SRA11 SS011 Hra4 ltac:(lia)) as (ch11 & HCH11).
(* answer's own premises *)
pose proof HJ10 as (_ & _ & _ & _ & _ & Hfrs10 & _).
assert (HFR11 : Z.of_nat (length (frames S8)) <= 8).
{ pose proof HJ8 as (_ & _ & _ & _ & _ & Hfrs8' & _). rewrite Hfrs8'. cbn [length app]. lia. }
destruct (rec_repA_answer B ly8 S8 _ _ _ HREP11) as (old & Hold & Holdc).
assert (Hold64 : 0 <= old < 2 ^ 64).
{ pose proof asan_consts as (Ca & _). destruct Holdc as [-> | (pn' & Hpn' & Eo')]; [lia|].
  destruct pn' as [a k]. cbn [fst] in Eo'. subst a.
  pose proof (proj1 (rec_repA_blocks B ly8 S8 _ _ _ HREP11 _ Hpn')) as Hin11.
  destruct (al_blocks _ _ LAWS ly8 S8 W10 (ms_mem ms11) _ old k HAR11 Hin11) as (_ & H4096 & Hoc & _ & _ & _ & Hk).
  pose proof (req_size_pos k ltac:(lia)) as [_ Rk]. lia. }
assert (Hqb : forall i, 0 <= i < Z.of_nat (length (shape_of scc_verb)) + 1 -> 0 <= q + i < 2 ^ 64)
  by exact (scc_argA_bound ly8 S8 W10 mem10 _ _ [] q (shape_of scc_verb) HAR10 (proj1 Hq64) (HqA [])).
(* where the shape lies: a live block or a read-only byte of the image, so apart from this frame, its shadow and
   the stack *)
assert (Hqloc : forall i, 0 <= i < Z.of_nat (length (shape_of scc_verb)) + 1 ->
  0 <= q + i < alloc_ceiling /\ ~ (F <= q + i < F + 64) /\ ~ (SB + F / 8 <= q + i < SB + F / 8 + 8)).
{ intros i Hi. pose proof asan_consts as (Ca & _). pose proof (HqA [] : astr_argA B ly8 S8 (rdW W10 mem10) (in_roP SEGS RLO RHI) [] q (Some (shape_of scc_verb))) as Hqa.
  unfold astr_argA in Hqa. cbv zeta in Hqa.
  destruct Hqa as (_ & _ & _ & [((pb & kb & Hin & Hlo & Hhi) & _) | (Hro & _)]).
  - destruct (al_blocks _ _ LAWS ly8 S8 W10 mem10 _ pb kb HAR10 Hin) as (_ & Hb4096 & Hbc & Hbapp & _ & _ & Hbk).
    pose proof (req_size_pos kb ltac:(lia)) as [_ Rk].
    pose proof (sep_block_frame SEGS B LAWS ly8 S8 W10 mem10 _ pb kb 0 fpos HAR10 Hin Hfin8) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA8 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
    split; [lia|]. split; [lia | unfold SB; lia].
  - destruct (Hro i Hi) as (Hr & _). destruct (scc_ro_apart _ Hr) as [Himg _].
    pose proof (pa_img_range _ Himg) as Hrange.
    split; [lia|]. split; [lia | unfold SB; lia]. }
assert (HSH11 : r_refuse R2 = 0 ->
  astr_argA B ly8 S8 (rdW W10 (ms_mem ms11)) (in_roP SEGS RLO RHI) O2 q (Some (shape_of scc_verb)) /\ fits (shape_of scc_verb)).
{ intros _. split; [|exact scc_fits].
  apply (scc_argA_rd ly8 S8 (rdW W10 mem10) (rdW W10 (ms_mem ms11)) O2 q (shape_of scc_verb) (HqA O2)).
  intros i Hi. pose proof (Hqb i Hi) as Hqi. destruct (Hqloc i Hi) as (Hq1 & Hq2 & Hq3).
  exact (aview_frame_pt E6 _ (w_H W10) mem10 (ms_mem ms11) (q + i) HFr11 ltac:(lia)
    ltac:(nwin_tac ltac:(fun H => rewrite ?Z2v, ?Z34v, ?Z1028, ?Z1041 in H; unfold SB in *; rewrite FS in Hslo; lia))). }
assert (HSLOT11 : r_refuse R2 = 0 -> true = true ->
  (exists k, nth_error (r_calls R2) k = Some (REC_CHAIN_CLEAR, [dec id]) /\
     rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (rec_slot R = A_REC_SPILL /\ (REC_CHAIN_CLEAR, [dec id]) = r_spill R2)).
{ intros _ _. exact (rec_slotA_entry R REC_CHAIN_CLEAR [dec id] Hlen). }
assert (Hchg11 : true = negb (bv_unsigned (getr (ms_regs ms11) 12) =? 0)) by (rewrite U12; reflexivity).
set (t := snd (rec_answer R2 (REC_CHAIN_CLEAR, [dec id]) (shape_of scc_verb) true)) in *.
assert (Ht : snd (sup_chain_clear_m R id) = t) by reflexivity.
assert (HBB8 : blocks_bytes S8 = nd + blocks_bytes S4).
{ rewrite (blocks_bytes_bsum B ly8 S8), (blocks_bytes_bsum B ly4 S4), (bsum_perm _ _ Hperm8), bsum_cons. reflexivity. }
assert (HEV11 : st_nev S8 + EV_ANSWER <= EV_MAX).
{ pose proof HJ8 as (_ & _ & _ & _ & _ & _ & Hnev8 & _). pose proof HJ6 as (_ & _ & _ & _ & _ & _ & Hnev6 & _).
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _).
  unfold EV_SUP_CHAIN_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC, EV_ARG_S, EV_RECORD in *. rewrite Hnev2 in *. lia. }
assert (HLIVE11 : blocks_bytes S8 + LIVE_ANSWER t <= LIVE_MAX).
{ assert (HBB2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
  unfold LIVE_SUP_CHAIN_CLEAR, LIVE_ARG_S in Hlive. cbn [sarg] in Hlive.
  unfold LIVE_XMALLOC in Hlive. rewrite Ht in Hlive. unfold nd in HBB8. pose proof (dec_length id Hid). lia. }
assert (HMOK11 : mo_ok MT S8 (XM_ANSWER MT t)).
{ pose proof (scc_xm_pos (Some (dec id)) (snd (sup_chain_clear_m R id))) as [Hx1 Hx2].
  apply (mok_station MT S2 S8 (XM_SUP_CHAIN_CLEAR MT R id) (XM_RECORD MT R + XM_ARG_S MT (Some (dec id))) _ MTL).
  - rewrite ES2. apply (mo_ok_set_fs MT MTLF). exact MOK.
  - exact (mle_station MT S2 S4 S8 _ _ MTL Hmle4 Hmle8).
  - rewrite <- Ht. exact Hx2.
  - unfold XM_SUP_CHAIN_CLEAR. rewrite Ht. lia. }
assert (Hc64 : 0 <= rec_slot R < 2 ^ 64).
{ assert (ERS : rec_slot R = rec_slotA R) by reflexivity. rewrite ERS.
  pose proof (rec_slotA_home R Hlen) as (_ & Hc1 & Hc2 & _ & _).
  unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
assert (HSIGA2 : SIG CS_answer = BASE + AF_answer).
{ rewrite (cmd_sig_prog_PB CS_answer ltac:(cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right]))). reflexivity. }
rewrite HSIGA2.
eapply SRr_bind.
{ eapply (callS_wideF (fx := fx6) B LAWS W10 (ms_regs ms11) (ms_mem ms11) _ SUP_CHAIN_CLEAR_STK (spZ regs) (scc_FP O) ly S W mem md
    [(0, fpos)] ly8 S8 _ _ ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER (sp1 - spZ regs) (getr (ms_regs ms11) 1) ch11 _ HJ10 Qsp11 Hsp1b);
  [ lia | unfold ANSWER_STK, HAND_BACK_STK, MIX_CALL_STK, XMALLOC_STK, ESTACK, ASTACK; lia
  | rewrite FS; unfold ANSWER_STK, HAND_BACK_STK, MIX_CALL_STK, XMALLOC_STK, ESTACK, ASTACK; lia
  | rewrite U3; exact Hgp | rewrite U4; exact Htp | reflexivity
  | rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite U1, unsigned_lit_small by lia; lia
  | unfold s0Z; rewrite U8, unsigned_lit_small by lia; exact HCH11
  | intros HPRE11; eapply SRr_mono;
    [ exact (TANSWER fx6 ly8 S8 W10 (ms_regs ms11) (ms_mem ms11) _ ch11 (rec_slot R) q old (REC_CHAIN_CLEAR, [dec id])
        (shape_of scc_verb) true R2 O2 HPRE11 (fxrel_frm0 fx fx6 HFRM Hfx6) HFR11 HROD11 HRO11 U10'
        Hc64 U11' Hq64 Hchg11 HREP11 Hold Hold64 HSH11 HSLOT11 HEV11 HLIVE11 HMOK11)
    | cbv beta; unfold apost_baseF; intros Wq cq _ (fxq & lyq & Sq & regsq & memq & mdq & -> & Hf1 & Hf2 & HJq & HPq & HKq);
      exists fxq, lyq, Sq, regsq, memq, mdq;
      split; [reflexivity | split; [exact Hf1 | split; [exact Hf2 | split; [exact HJq | split; [exact HPq | exact HKq]]]]] ]
  | intros a (r & Hr & Ha); destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha;
    [ apply scc_awr_rec; left; unfold A_G_REC, OFF_ANSWER, REC_SIZE in *; lia
    | apply scc_awr_rec; left; unfold A_G_REC, OFF_STATE, REC_SIZE in *; lia
    | unfold ablocks_fp in Hr; apply in_map_iff in Hr as ([pb nb] & <- & Hin); cbn [fst snd] in Ha;
      apply scc_filter_in in Hin;
      assert (HinT : In (pb, nb) (ablocks B ly8 S8)) by exact (HO2live _ Hin);
      destruct (in_dec (fun u v : Z * Z => decide (u = v)) (pb, nb) O) as [HO | HnO];
      [ right; left; split;
        [ exists (pb, pb + req_size nb); split; [right; right; apply in_map_iff; exists (pb, nb); split; [reflexivity | exact HO] | cbn [fst snd]; exact Ha]
        | exists pb, nb; split; [exact HinT | exact Ha] ]
      | right; right; left; exists pb, nb; split; [exact HinT|]; split; [|exact Ha];
        intros H0;
        assert (H4 : In (pb, nb) (ablocks B ly4 S4))
          by (rewrite <- Eab in H0; apply (Permutation_in _ Hperm4) in H0; apply in_app_or in H0 as [H0 | H0]; [exact H0 | exfalso; exact (HnO (HFO4 _ H0))]);
        destruct Hin as [E' | Hin];
        [ injection E' as <- <-; pose proof (proj1 (Forall_forall _ _) Hfresh8 _ H4) as Hap; cbn [fst snd] in Hap;
          unfold iv_apart, nd in Hap; pose proof (dec_length id Hid); lia
        | exact (HnO (proj1 (proj1 (HO1 _) Hin))) ] ] ]
  | intros ly2' S2' W2' regs2' mem2' md2' _ a (r & Hr & Ha) Hw _; exfalso; rewrite FS in Hw;
    pose proof asan_consts as (Ca & _);
    destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha;
    [ unfold A_G_REC, OFF_ANSWER in Ha; rewrite FS in Hslo; lia
    | unfold A_G_REC, OFF_STATE in Ha; rewrite FS in Hslo; lia
    | unfold ablocks_fp in Hr; apply in_map_iff in Hr as ([pb nb] & <- & Hin); cbn [fst snd] in Ha;
      apply scc_filter_in in Hin;
      destruct (al_blocks _ _ LAWS ly8 S8 W10 (ms_mem ms11) _ pb nb HAR11 (HO2live _ Hin)) as (_ & _ & Hbc & _);
      rewrite FS in Hslo; lia ] ]. }
cbv beta. intros W12 c12 _ (fx12 & ly12 & S12 & regs12 & mem12 & md12 & -> & Hfr12a & Hfc12 & HJ12 & HJc12 & HP12 & HK12).
rewrite U1.
apply (srr_apost_baseF_lift (fx := fx6) SEGS fx12); [exact (conj Hfr12a Hfc12)|].
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (scc_st_ok_fx fx6 fx12 Ev ssv msv ltac:(reflexivity) HS) as HSx end.
cbn [ms_regs ms_pc_val ms_mem ms_rom restrict mkst] in HSx. clear HS. rename HSx into HS.
destruct HK12 as (p1 & p2 & O' & HK12). cbv zeta in HK12.
destruct HK12 as (Hp2r & Hp24096 & H12 & Hfr12 & Hbl12 & HREP12 & HO'iff & Hstr12 & Hbb12 & HMLE12).
pose proof (proj1 HJc12) as HAR12.
pose proof HJc12 as (_ & Hly12 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly12 HAR11 Hly12) as (Eab12 & Efa12 & _).
assert (EFA12 : frame_addr ly12 0 fpos = F) by (rewrite Efa12; exact EFA8).
pose proof HJ12 as (_ & _ & _ & _ & _ & Hfrs12 & _).
assert (Hfin12 : In (0, fpos) (frames S12)) by (rewrite Hfrs12; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR12 Hfin12) as (_ & _ & HFpres12 & HFSpres12).
rewrite EFA12 in HFpres12, HFSpres12. change (fs_frame_bytes 0) with 64 in HFpres12, HFSpres12. change (64 / 8) with 8 in HFSpres12.
(* answer's footprint: g_rec's answer and state fields and the recorder's blocks with the old answer's address *)
assert (HFPANS : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) O2)) a ->
  0 <= a < 2 ^ 64 /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a < alloc_ceiling).
{ intros a (r & Hr & Ha). apply KLOC2. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
  - left. left. unfold A_G_REC, OFF_ANSWER, REC_SIZE in *. lia.
  - left. left. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb nb] & <- & Hin). cbn [fst snd] in Ha.
    apply scc_filter_in in Hin. right. exists pb, nb. split; [exact Hin | exact Ha]. }
jafter_call_fx fx12 HS 1106%nat regs12 (mrestrict (w_H W12) mem12) HP12 [0;1;2;3;4;5]%nat HS12.
match type of HS12 with ?tq -> _ => assert (HRK : tq); [|specialize (HS12 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- (eapply (region_kept_fshadow_sub (segs := SEGS) B E6 _ _ _ ly8 S8 W10 (ms_mem ms11) _ ly12 S12 W12 mem12 md12 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc12 Z1041 Hfin8);
  [ unfold shadow_addr; rewrite EFA8; rewrite <- SB_SHADOW_OFF; lia
  | unfold shadow_addr; rewrite EFA8; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
  | intros a Ha HFa; destruct (HFPANS a HFa) as (_ & _ & HnS & _); lia
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres12 (a - (SB + F / 8)) ltac:(lia))) ]).
- (eapply (region_kept_frame_sub (segs := SEGS) B E6 _ _ _ ly8 S8 W10 (ms_mem ms11) _ ly12 S12 W12 mem12 md12 _ 1028 F _ _ _ _ _ 0 fpos HJc12 Z1028 Hfin8);
  [ rewrite EFA8; lia | rewrite EFA8; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HFPANS a HFa) as (_ & HnF & _ & _); lia
  | intros a Ha; exact (proj1 (HFpres12 a ltac:(lia))) ]).
- (eapply (region_kept_frame_sub (segs := SEGS) B E6 _ _ _ ly8 S8 W10 (ms_mem ms11) _ ly12 S12 W12 mem12 md12 _ 1028 F _ _ _ _ _ 0 fpos HJc12 Z1028 Hfin8);
  [ rewrite EFA8; lia | rewrite EFA8; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HFPANS a HFa) as (_ & HnF & _ & _); lia
  | intros a Ha; exact (proj1 (HFpres12 a ltac:(lia))) ]).
- (eapply (region_kept_stack_sub SEGS B E6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc12 HJ12 Z2v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HFPANS a HFa) as (_ & _ & _ & Hac); rewrite FS in Hslo; lia]).
- (eapply (region_kept_stack_sub SEGS B E6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc12 HJ12 Z2v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HFPANS a HFa) as (_ & _ & _ & Hac); rewrite FS in Hslo; lia]).
- (eapply (region_kept_stack_sub SEGS B E6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc12 HJ12 Z34v);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HFPANS a HFa) as (_ & _ & _ & Hac); rewrite FS in Hslo; lia]). }
rewrite <- restrict_mkst_fx in HS12. clear HS. rename HS12 into HS.
remember (havoc E6 1106 (map (getr regs12) CLOB)) as E7 eqn:HE7 in HS.
assert (HAE7 : env_agree 32 (Ereg regs (scc_extra B sp1)) E7) by (rewrite HE7; apply env_agree_havoc_ge; [lia | exact HAE6]).
assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc_hi; [exact HEI6 | unfold A_LIM; lia]).
assert (OLD7 : forall n, (n < 1106)%nat -> ew E7 n = ew E6 n) by (intros n Hn; rewrite HE7; apply ew_havoc_old; exact Hn).
assert (E71110 : ew E7 1110 = getr regs12 10).
{ rewrite HE7. change 1110%nat with (1106 + 4)%nat. rewrite (ew_havoc_new E6 1106 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE7.
assert (A2v : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact Z2v).
assert (A34v : bv_unsigned (ew E7 34) = sp1) by (rewrite OLD7 by lia; exact Z34v).
assert (A1028 : bv_unsigned (ew E7 1028) = F) by (rewrite OLD7 by lia; exact Z1028).
assert (A1041 : bv_unsigned (ew E7 1041) = SB + F / 8) by (rewrite OLD7 by lia; exact Z1041).
assert (A1040 : bv_unsigned (ew E7 1040) = FL) by (rewrite OLD7, OLD6, OLD5, OLD4, OLD3 by lia; exact V1040).
(* the release: the frame's magic retired, its shadow := f5, its flag byte := 0, the saved registers back, return *)
assert (EFL12 : flag_addr ly12 0 fpos = FL).
{ pose proof EFA12 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
destruct (scc_FFL _ _ _ _ _ 0 fpos HAR12 Hfin12) as (HFLp12 & HFLo12 & _ & _). rewrite EFL12 in HFLp12, HFLo12.
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 8)).
{ intros Hx. apply (proj2 (HFSpres12 (FL - (SB + F / 8)) ltac:(lia))).
  replace (shadow_addr F + (FL - (SB + F / 8))) with FL by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia). exact HFLo12. }
assert (HFLnF : ~ (F <= FL < F + 64)) by (intros Hx; exact (proj2 (HFpres12 FL Hx) HFLo12)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 1040%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite A1040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp12)
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite A1040, A1041, A1028, A2v, A34v; rewrite FS in Hslo; unfold SB in *; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
pose (RUNF := aj_flag_store_pi (fx := fx12) B LAWS ML AFREE_LAW scc_FFL).
paj_run_flag_sh RUNF HS HJ12.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  destruct Hin as [<- | Hin]; [right; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite A1040 in Hr; rewrite EFL12; lia|]. left.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?A1041, ?A1028, ?A2v, ?A34v in Hr;
  first [ exfalso; lia | left; rewrite FS; lia
  | right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    first [ left; unfold in_zr; cbn [fst snd]; rewrite EFA12; change (fs_frame_bytes 0) with 64; lia
    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA12, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia ] ] |]).
  destruct Hin.
- intros msr HSr. rewrite EFL12.
  pose proof (st_ok_pi_region_nth E7 _ _ 0 _ HSr eq_refl) as HR0.
  pose proof (field_of_region E7 _ 1040 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR0 A1040 ltac:(cbn [In]; tauto) eq_refl ltac:(lia) ltac:(lia)) as HV.
  specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
- rename ms into ms13, mat into mat13, HF into HF13, HFr into HFr13, HG into HG13.
  preg HS (1%bv : bv 5) R1f. preg HS (10%bv : bv 5) R10f.
  rewrite scc_denot_off0, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) in R1f by lia.
  rewrite scc_denot_off0, E71110, Hp2r in R10f.
  assert (HP13 : aregs_preserved regs (ms_regs ms13)).
  { (eapply (aregs_preserved_of_st_ok SEGS (w_H W12) E7 _ ms13 regs (scc_extra B sp1) HS HAE7); vm_compute; reflexivity). }
  pose proof (proj1 HJ12) as HAR13.
  set (S13 := stack_free_state 0 fpos S12) in *.
  assert (EAB13 : ablocks B ly12 S13 = ablocks B ly12 S12).
  { unfold S13, ablocks. rewrite blocks_stack_free_state. reflexivity. }
  (* the recorder's bytes and O''s blocks across the release (it writes the frame, its shadow and its flag) *)
  assert (HO'live : forall pn, In pn O' -> In pn (ablocks B ly12 S12))
    by (intros pn Hp; exact (proj1 (rec_repA_blocks B ly12 S12 _ _ O' HREP12 pn Hp))).
  assert (KLOC3 : forall a, in_recA a \/ (exists p n, In (p, n) (ablocks B ly12 S12) /\ p <= a < p + req_size n) ->
    0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
  { intros a [Ha | (p & n & Hpn & Hpa)].
    - destruct (scc_rec_loc a Ha) as [Hi Hr]. split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
      intros ->. exact (HFLimg Hi).
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR12 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres' & _).
      pose proof (sep_block_frame SEGS B LAWS ly12 S12 W12 mem12 md12 p n 0 fpos HAR12 Hpn Hfin12) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA12 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
      split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
      intros ->. exact (proj2 (Hpres' FL ltac:(lia)) HFLo12). }
  assert (K13 : forall a, in_recA a \/ (exists p n, In (p, n) (ablocks B ly12 S12) /\ p <= a < p + req_size n) ->
    rdW W12 (ms_mem ms13) a = rdW W12 mem12 a).
  { intros a Ha. destruct (KLOC3 a Ha) as (Hb & HnF & HnS & HnFL).
    (apply (aview_frame_pt E7 _ (w_H W12) mem12 (ms_mem ms13) a HFr13); [lia|];
      nwin_tac ltac:(fun H => rewrite ?A2v, ?A34v, ?A1028, ?A1040, ?A1041 in H; unfold SB in *; rewrite FS in Hslo; lia)). }
  assert (HREP13 : rec_repA B ly12 S13 (rdW W12 (ms_mem ms13)) (fst (rec_answer R2 (REC_CHAIN_CLEAR, [dec id]) (shape_of scc_verb) true)) O').
  { (apply (rec_repA_keep B ly12 S12 (rdW W12 mem12) ly12 S13 (rdW W12 (ms_mem ms13)) _ O' HREP12);
    [ intros a Ha; exact (K13 a (or_introl Ha))
    | intros [p n] Hpn; split; [rewrite EAB13; exact (HO'live _ Hpn)|]; intros i Hi; cbn [fst snd] in Hi |- *;
      apply K13; right; exists p, n; split; [exact (HO'live _ Hpn)|]; unfold req_size; destruct (Z.eqb_spec n 0); lia ]). }
  assert (HSTR13 : astr_atR (rdW W12 (ms_mem ms13)) p2 t).
  { (apply (astr_atR_keep (rdW W12 mem12)); [exact Hstr12|];
      intros i Hi; apply K13; right; exists p2, (Z.of_nat (length t) + 1);
      split; [apply Hbl12; right; right; reflexivity | unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length t) + 1) 0); rewrite ?length_app in Hi; cbn [length] in Hi; lia]). }
  (* the return *)
  eapply (paj_ret_at (fx := fx12) (PL := PL_cmd) (PI := PI) W12 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  lazymatch goal with |- context [mkCfg (mkst ?rg (v_jalr ?x 0) ?mm ?rom) ?mdq] =>
    replace (v_jalr x 0) with (getr regs 1) by (rewrite R1f, Hra'; reflexivity) end.
  apply (apost_baseF_intro (fx := fx12) SEGS fx12 B _ _ regs ly S W mem md _ _ W12 ly12 S13).
  + exact (fxrel_refl fx12).
  + (eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ12 |];
      unfold EV_SUP_CHAIN_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC, EV_ARG_S, EV_RECORD, EV_REC_SHAPE_OF in *; lia).
  + exact HP13.
  + cbv beta. exists (fst (rec_answer R2 (REC_CHAIN_CLEAR, [dec id]) (shape_of scc_verb) true)), t, p2, O'.
    rewrite EAB13.
    set (n := Z.of_nat (length t) + 1) in *.
    assert (HB2' : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly4 S4)).
    { intros pn H0 HnO. rewrite <- Eab in H0. apply (Permutation_in _ Hperm4) in H0.
      apply in_app_or in H0 as [H | H]; [exact H | exfalso; exact (HnO (HFO4 _ H))]. }
    assert (HB1' : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly S)).
    { intros pn H. rewrite <- Eab. apply (Permutation_in _ (Permutation_sym Hperm4)). apply in_or_app. left. exact H. }
    assert (HO1' : forall pn, In pn O1 -> In pn O) by (intros pn H; exact (proj1 (proj1 (HO1 pn) H))).
    assert (HO2' : forall pn, In pn O -> In pn (ablocks B ly4 S4) -> In pn O1).
    { intros pn HO Hc. apply HO1. split; [exact HO|]. intros HF.
      pose proof (scc_ablocks_nodup ly S2 W mem2 md2 HAR2) as ND.
      apply (Permutation_NoDup Hperm4) in ND. exact (scc_nodup_app _ _ pn ND Hc HF). }
    assert (Hnew' : ~ In (pnew, nd) (ablocks B ly4 S4)).
    { intros Hin. pose proof (proj1 (Forall_forall _ _) Hfresh8 _ Hin) as Hap. cbn [fst snd] in Hap.
      unfold iv_apart, nd in Hap. pose proof (dec_length id Hid). lia. }
    assert (H4' : forall pn, In pn (ablocks B ly8 S8) <-> pn = (pnew, nd) \/ In pn (ablocks B ly4 S4)).
    { intros pn. split; intros Hpn.
      - apply (Permutation_in _ Hperm8) in Hpn. destruct Hpn as [<- | Hpn]; [left; reflexivity | right; exact Hpn].
      - apply (Permutation_in _ (Permutation_sym Hperm8)). destruct Hpn as [-> | Hpn]; [left; reflexivity | right; exact Hpn]. }
    assert (HOq : forall pn, In pn O' <-> (In pn (O1 ++ [(pnew, nd)]) /\ fst pn <> old) \/ pn = (p1, n)).
    { intros pn. rewrite HO'iff. unfold O2. rewrite in_app_iff. cbn [In]. tauto. }
    assert (Holdq : forall pn, In pn (ablocks B ly8 S8) -> fst pn = old -> In pn (O1 ++ [(pnew, nd)])).
    { intros pn Hpn Eo. destruct Holdc as [Eold | (pn' & Hpn' & Eo')].
      - destruct pn as [a k]. destruct (al_blocks _ _ LAWS ly8 S8 W10 (ms_mem ms11) _ a k HAR11 Hpn) as (_ & H4096 & _).
        cbn [fst] in Eo. lia.
      - assert (Hpn'4 : In pn' (ablocks B ly8 S8)) by exact (HO2live _ Hpn').
        rewrite (scc_same_start ly8 S8 W10 (ms_mem ms11) _ pn pn' HAR11 Hpn Hpn'4 ltac:(congruence)).
        unfold O2 in Hpn'. apply in_app_iff. destruct Hpn' as [E' | Hpn']; [right; left; exact E' | left; exact Hpn']. }
    destruct (scc_post_lists (ablocks B ly S) (ablocks B ly4 S4) (ablocks B ly8 S8) (ablocks B ly12 S12) O O1 O'
      (pnew, nd) (p1, n) (p2, n) old HB2' HB1' HO1' HO2' HO1live Hnew' H4' Hfr12
      ltac:(intros E'; injection E' as E'; exact (H12 E')) Hbl12 HOq Holdq) as (L1 & L2 & L3 & L4 & L5 & L6).
    split; [exact (surjective_pairing _)|].
    split; [exact R10f|]. split; [exact Hp24096|]. split; [exact HREP13|].
    split; [exact L1|]. split; [exact L2|].
    split; [intros pn H0 HnO E'; subst pn; exact (HnO (L3 H0))|].
    split.
    { intros Hq. apply in_map_iff in Hq as (pn & Ep & Hpn).
      assert (Hpn5 : In pn (ablocks B ly12 S12)) by exact (HO'live _ Hpn).
      apply L4. rewrite <- (scc_same_start ly12 S12 W12 mem12 md12 pn (p2, n) HAR12 Hpn5 L2 Ep). exact Hpn. }
    split; [exact HSTR13|].
    split.
    { intros pn H0 HnO. destruct (L5 pn H0 HnO) as [H5q H4q]. split; [exact H5q|].
      assert (Hne : pn <> (p2, n)) by (intros ->; exact (HnO (L3 H0))).
      destruct pn as [a k].
      pose proof (sep_blocks SEGS B LAWS ly12 S12 W12 mem12 md12 a k p2 n HAR12 H5q L2 Hne) as Hd.
      destruct (al_blocks _ _ LAWS ly12 S12 W12 mem12 md12 a k HAR12 H5q) as (_ & _ & _ & _ & _ & _ & Hk).
      destruct (al_blocks _ _ LAWS ly12 S12 W12 mem12 md12 p2 n HAR12 L2) as (_ & _ & _ & _ & _ & _ & Hn).
      pose proof (req_size_pos k ltac:(lia)) as [_ Rk]. pose proof (req_size_pos n ltac:(lia)) as [_ Rn].
      unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. unfold iv_apart. lia. }
    split; [exact L6|].
    split.
    { assert (HBB2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
      exact (scc_bb_final ly12 S S2 S4 S8 S12 fpos R id t nd Hid EAB13 HBB2 Hbb4 HBB8 Hbb12 eq_refl Ht). }
    exact (scc_mle_final S S2 S4 S8 S12 fS2 R id t fpos ES2 Hmle4 Hmle8 HMLE12 Ht).
Qed.
End e.
End f.
End d.
Print Assumptions tsup_chain_clear_holds.
