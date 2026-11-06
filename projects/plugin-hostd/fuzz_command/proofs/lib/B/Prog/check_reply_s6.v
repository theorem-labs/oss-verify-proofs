(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_s6.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): B's addresses; the transfer of astr_argA between readers in lib/B/Prog/CmdRep.v's form. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 917ca7ac6b1: astr_argA's read-only arm there names no reader (CmdChk's cmd_addr_b / cmd_hull_b, the end in CmdRo's cmd_ro_ends), so s6_argA_eq carries that arm unchanged. *)
(* Modified by Theorem Labs, 2026-10: the segment of check_reply's walk (fuzz_command.asan-ubsan, 0x86e64) from the strlen
   call 0x87080 through rec_shape_of (0x8708c) and `j 0x870e4` to the shape join, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's call steps: cl_callS,
   jafter_call_keep_pi) at origin/ossv/recipes c8557374ad2e.

   The symbolic state carries the registers only (no regions): the segment loads and stores nothing, so each run
   keeps every byte (frame_of with no window). cr_mid goes from point to point by cr_mid_step: the journal from the
   entry, the blocks, the frame area, and the bytes crK names, which the strlen call keeps outside its scratch window
   and rec_shape_of's journal keeps (the stack above sp, the caller's frame and its shadow, the program statics).

   rec_shape_of's post (rec_shape_of_c.v) gives the returned string as astr_argA for every owned-block list, which
   is the join's premise (CR_JOIN_stmt) at the list []; its `ly' = ly /\ S' = S` carries cr_ls to the join. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo CmdZsh PaArt
  PaNoChain CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_reply_k check_reply_m check_reply_sd
  check_reply_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a byte range read the same through two views keeps its little-endian value *)
Lemma val_mem_aview_tr : forall (H H' : word -> bool) (m m' : word -> option byte) a n x,
(forall k, (k < n)%nat -> aview SEGS H' m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict H m) a n x -> val_mem SEGS (mrestrict H' m') a n x.
Proof.
intros H H' m m' a n x K V k Hk. specialize (K k Hk). specialize (V k Hk). unfold aview in K. rewrite V in K.
cbn [option_map] in K. destruct (mbyte SEGS (mrestrict H' m') (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in K;
[|discriminate]. injection K as K. f_equal. apply bv_eq. exact K.
Qed.
(* a run that names no write window leaves every byte as it was *)
Lemma aview_frame_nil : forall E (H : word -> bool) (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E H m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hr & _). destruct Hr. Qed.
(* astr_argA over two readers that agree everywhere (only the string's bytes are read through the reader: the
   block arm and the read-only arm's checks cmd_addr_b, cmd_hull_b and cmd_ro_ends do not name it) *)
Lemma s6_argA_eq : forall B ly S (rd rd' : reader) ro O p x,
(forall a, rd' a = rd a) -> astr_argA B ly S rd ro O p (Some x) -> astr_argA B ly S rd' ro O p (Some x).
Proof.
intros B ly S rd rd' ro O p x K HA. unfold astr_argA in HA |- *. cbv zeta in HA |- *.
destruct HA as (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [apply (astr_atR_agree rd); [intros y _; apply K | exact H2]|]. exact (conj H3 H4).
Qed.

(* the bytes cr_mid names besides the journal: the flag pointer F + 120, the shadow bytes 4..7 of the frame, the
   entry's callee-saved registers below sp0, g_rec.reply and g_rec.reply_size *)
Definition crK (v : crv) (F : Z) (a : Z) : Prop :=
F + 120 <= a < F + 128 \/ SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 8 \/ c_sp v - 96 <= a < c_sp v \/
A_G_REC + OFF_REPLY <= a < A_G_REC + OFF_REPLY_SIZE + 8.

(* the model after a run, named so that the goal and the journal share one term *)
Ltac name_md :=
lazymatch goal with |- context [with_vm_backing ?a ?b ?c] =>
let m := fresh "mdv" in set (m := with_vm_backing a b c) in *; clearbody m end.
(* the section hypotheses of check_reply_t.v's lemmas, from this file's own *)
Ltac tinst H :=
repeat lazymatch type of H with
| forall _ : crv, _ => fail
| forall _ : alayout, _ => fail
| forall _ : ?T, _ => let h := fresh "h" in assert (h : T) by (first [assumption | exact _]); specialize (H h); clear h
end.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.

(* cr_mid at a later state of the walk: the journal from the entry reaches it, the blocks are the same, the frame
   area does not move, and the bytes crK names read the same *)
Lemma cr_mid_step : forall v lyc Sc Wc memc mdc lyc' Sc' Wc' memc' mdc' pos,
cr_mid B v lyc Sc Wc memc mdc pos ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc' Sc' Wc' memc' mdc' 0 ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) -> ly_F lyc' = ly_F lyc ->
(forall a, crK v (frame_addr lyc 1 pos) a -> rdW Wc' memc' a = rdW Wc memc a) ->
cr_mid B v lyc' Sc' Wc' memc' mdc' pos.
Proof.
intros v lyc Sc Wc memc mdc lyc' Sc' Wc' memc' mdc' pos MID HJ' HP' HF K.
destruct MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
assert (EF : frame_addr lyc' 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite HF; reflexivity).
assert (EFL : flag_addr lyc' 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HF; reflexivity).
unfold cr_mid. cbv zeta. rewrite EF, EFL. unfold crK in K. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
split; [exact HJ'|]. split; [exact (Permutation_trans HP' HPerm)|].
split; [apply (val_mem_aview_tr (w_H Wc) (w_H Wc') memc memc'); [|exact VFL]; intros k Hk; apply K; left; lia|].
split; [intros i Hi; apply (val_mem_aview_tr (w_H Wc) (w_H Wc') memc memc'); [|exact (VSH i Hi)];
  intros k Hk; apply K; right; left; lia|].
split; [|split].
- unfold cr_saved in *. intros j r Hj.
  assert (Hj12 : (j < length cr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length cr_saved_regs) with 12%nat in Hj12.
  apply (val_mem_aview_tr (w_H Wc) (w_H Wc') memc memc'); [|exact (VSV j r Hj)].
  intros k Hk. apply K. right; right; left. lia.
- apply (val_mem_aview_tr (w_H Wc) (w_H Wc') memc memc'); [|exact VREP]. intros k Hk. apply K. right; right; right. lia.
- apply (val_mem_aview_tr (w_H Wc) (w_H Wc') memc memc'); [|exact VSZ]. intros k Hk. apply K. right; right; right. lia.
Qed.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis RSO : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

Theorem cr_s6_of : CR_JOIN_stmt B RLO RHI -> CR_STRLEN_stmt B RLO RHI.
Proof.
intros JOIN v lyc Sc Wc regs1 memc mdc pos CX MID RA Hcode Hn0 R19 R10 LS.
pose proof CX as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw8 & Hspw & _ & _ & _ & Hn
  & _ & _ & _ & _ & _ & HEV & Hwhi).
pose proof HPRE0 as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
set (sp0 := c_sp v) in *. set (F := frame_addr lyc 1 pos) in *.
unfold c_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi, Hbot, Htop, Htop2, Hspw, Hpres0.
assert (Hsp1 : sp1_of sp0 = sp0 - 128 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16)).
{ unfold sp1_of. replace ((sp0 - 128) mod 32) with (sp0 mod 32) by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
set (sp1 := sp1_of sp0) in *. destruct Hsp1 as [Hsp1 Hsp1m].
(* the symbolic state at 0x87080: the registers as atoms, no regions *)
set (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
assert (HS : st_ok_pi SEGS VAL E (mkSS CR_STRLEN sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + CR_STRLEN)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply (regs_ok_agree 32 (Ereg regs1 [])).
    + split; [intros n0 Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    + vm_compute. reflexivity.
    + apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - cbn. repeat split. }
assert (SHOK : sh_ok SEGS crBx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cr_at.
(* the bytes cr_mid names lie below the heap's ceiling or in the frame above the realigned sp *)
assert (CK : forall a, crK v F a -> (0 <= a < alloc_ceiling) \/ (sp1 + 32 <= a < sp0)).
{ intros a Ha. unfold crK in Ha. change (c_sp v) with sp0 in Ha. unfold OFF_REPLY, OFF_REPLY_SIZE, A_G_REC, SHADOW_OFF in Ha.
  pose proof (Z.mul_div_le F 8 ltac:(lia)). pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [left; lia | left; lia | right; lia | left; lia]. }
assert (Hsp0hi : sp0 < 2 ^ 64) by lia.
assert (Hsp1lo : alloc_ceiling + 4096 <= sp1) by (rewrite HSTK in Hslo; lia).
assert (Hsp1d : (sp1 - sp0) mod 16 = 0).
{ destruct Hsp1m as [Hm|Hm]; rewrite Hsp1, Hm;
  [replace (sp0 - 128 - 0 - sp0) with (-8 * 16) by lia | replace (sp0 - 128 - 16 - sp0) with (-9 * 16) by lia]; apply Z_mod_mult. }
(* 0x87080: to the strlen call *)
paj_run_tok RUN HS HJ SHOK crSpan.
{ apply awr_ok_nil. }
pmkst HS. name_md.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
rewrite (EE 2%nat 2%bv eq_refl), R2 in Q2. rewrite (EE 3%nat 3%bv eq_refl), R3 in Q3.
rewrite (EE 4%nat 4%bv eq_refl), R4 in Q4. rewrite (EE 10%nat 10%bv eq_refl), R10 in Q10.
pose proof (cr_mid_step v lyc Sc Wc memc mdc lyc Sc Wc _ _ pos MID HJ (Permutation_refl _) eq_refl
  (fun a _ => aview_frame_nil E (w_H Wc) memc _ HFr a)) as MID1.
clear HF HFr HG.
pose proof (cr_words_facts B RLO RHI) as WF. tinst WF.
pose proof (cr_state_facts B RLO RHI) as SF. tinst SF.
destruct (WF v lyc Sc Wc _ _ pos CX MID1) as (_ & _ & _ & _ & WF1).
destruct (WF1 Hn0) as (_ & _ & _ & (pb & kb & Hpb & Hpb1 & Hpb2) & Hp0s & Hp0t). clear WF1.
pose proof (SF v lyc Sc Wc _ _ pos CX MID1) as (_ & _ & _ & _ & _ & _ & HROM1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb HAR Hpb) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbk).
pose proof (req_size_pos kb ltac:(lia)) as [_ Hbreq].
assert (Ep0 : c_p0 v mod 2 ^ 64 = c_p0 v) by (apply Z.mod_small; lia).
rewrite Ep0 in Q10, R19.
pose proof (proj1 HJ) as HAR1.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS Hsegs errno_low ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen) Wc
    _ _ CHECK_REPLY_STK sp0 [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc _ 0 (sp1 - sp0) _
    (fun regs' _ => getr regs' 10 = w64 (astr_len (c_w0 v))) HJ).
  - unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Hsp1d.
  - lia.
  - unfold ESTACK. lia.
  - unfold ESTACK. rewrite HSTK. lia.
  - exact Q1.
  - intros a [].
  - eapply (ASTRLEN fx lyc Sc Wc _ _ _ (c_p0 v) (c_w0 v)).
    + apply (ecall_pre_stk_at SEGS B ESTACK CHECK_REPLY_STK sp0 [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)]
        lyc Sc Wc _ _ 0 _ (sp1 - sp0) HJ).
      * unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
      * exact Hsp1d.
      * lia.
      * lia.
      * unfold ESTACK. rewrite HSTK. lia.
      * rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
      * exact Q3.
      * exact Q4.
    + exact Q10.
    + lia.
    + apply astr_atR_view. exact Hp0s.
    + apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc Wc _ _ _ pb kb (c_p0 v) (astr_len (c_w0 v) + 1) HAR1 Hpb);
        unfold astr_len; try lia.
      unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
    + exact Hp0t.
    + exact HROM1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
pose proof (cr_mid_step v lyc Sc Wc _ _ lyc Sc Wc mem2 md2 pos MID1 HJ2 (Permutation_refl _) eq_refl) as MID2.
specialize (MID2 ltac:(intros a Ha; apply HK2; [destruct (CK a Ha); lia | destruct (CK a Ha); unfold ESTACK; lia | tauto])).
(* 0x87084: after strlen, to the rec_shape_of call *)
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H Wc) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (HEI2 : img_env VAL A_LIM (havoc E 32 (map (getr regs2) CLOB))) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (SHOK2 : sh_ok SEGS crBx [] (havoc E 32 (map (getr regs2) CLOB)) (mrestrict (w_H Wc) mem2)) by constructor.
clear SHOK.
paj_run_tok RUN HS HJ2 SHOK2 crSpan.
{ apply awr_ok_nil. }
pmkst HS. name_md.
prreg HS (1%bv : bv 5) Q1'. prreg HS (2%bv : bv 5) Q2'. prreg HS (3%bv : bv 5) Q3'. prreg HS (4%bv : bv 5) Q4'.
prreg HS (8%bv : bv 5) Q8'. prreg HS (10%bv : bv 5) Q10'. prreg HS (11%bv : bv 5) Q11'.
rewrite (EE 2%nat 2%bv eq_refl), R2 in Q2'. rewrite (EE 3%nat 3%bv eq_refl), R3 in Q3'.
rewrite (EE 4%nat 4%bv eq_refl), R4 in Q4'. rewrite (EE 8%nat 8%bv eq_refl), R8 in Q8'.
rewrite (EE 19%nat 19%bv eq_refl), R19 in Q10'. cbn [map CLOB nth] in Q11'. rewrite HQ2 in Q11'. unfold astr_len in Q11'.
pose proof (cr_mid_step v lyc Sc Wc _ _ lyc Sc Wc _ _ pos MID2 HJ2 (Permutation_refl _) eq_refl
  (fun a _ => aview_frame_nil _ (w_H Wc) mem2 _ HFr a)) as MID3.
clear HF HFr HG.
destruct (WF v lyc Sc Wc _ _ pos CX MID3) as (_ & _ & _ & _ & WF3).
destruct (WF3 Hn0) as (_ & _ & _ & Hp0b3 & Hp0s3 & _). clear WF3.
pose proof (SF v lyc Sc Wc _ _ pos CX MID3) as (HRO3 & HROK3 & _ & _ & _ & _ & _ & HROIN3 & HVAL3).
assert (Psp : spZ (ms_regs ms0) = sp0 + (sp1 - sp0)) by (unfold spZ; rewrite Q2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Ps0 : s0Z (ms_regs ms0) = sp0) by (unfold s0Z; rewrite Q8'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* the frame chain at the call: check_reply's s0 is the entry's sp, and the entry's ra and s0 lie below it *)
assert (HCH : exists ch1, achain lyc (rdW Wc (ms_mem ms0)) (sp0 + (sp1 - sp0)) sp0 ch1).
{ destruct (Z_lt_le_dec sp0 (ly_top (c_ly v) - 16)) as [Hlt|Hge].
  - pose proof MID3 as (_ & _ & _ & _ & VSV3 & _).
    assert (V0 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (sp0 - 8) 8 (raZ (c_regs v))).
    { pose proof (VSV3 0%nat 1 eq_refl) as V. unfold raZ.
      change (c_sp v) with sp0 in V. replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) in V by lia.
      replace (1%bv : bv 5) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity). exact V. }
    assert (V1 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (sp0 - 16) 8 (s0Z (c_regs v))).
    { pose proof (VSV3 1%nat 8 eq_refl) as V. unfold s0Z.
      change (c_sp v) with sp0 in V. replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) in V by lia.
      replace (8%bv : bv 5) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity). exact V. }
    exists ((sp0, raZ (c_regs v), s0Z (c_regs v)) :: c_ch v).
    apply (achain_ly_top (c_ly v) lyc); [exact Etop|].
    apply (achain_push (c_ly v) (rdW (c_W v) (c_mem v)) (rdW Wc (ms_mem ms0)) sp0 (s0Z (c_regs v)) (raZ (c_regs v)) (c_ch v)).
    + exact Hch.
    + lia.
    + intros a Ha. eapply aview_above_of_journal; [exact HJ2 | exact Ha | apply inFP_nil].
    + apply rdword_of_val_mem; [exact V0 | unfold raZ; apply bv_unsigned_in_range].
    + apply rdword_of_val_mem; [exact V1 | unfold s0Z; apply bv_unsigned_in_range].
    + exact Hra4.
    + rewrite HSTK in Hslo. lia.
    + replace sp0 with ((sp0 / 16 * 2) * 8) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia). apply Z_mod_mult.
    + exact Hlt.
    + lia.
  - exists []. left. split; [right; left; rewrite Etop; lia | reflexivity]. }
destruct HCH as (ch1 & HCH).
(* 0x8708c: rec_shape_of(w0, |w0|) *)
rewrite (SIGP CS_rec_shape_of ltac:(cbv [cmd_prog_syms In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_rec_shape_of) with AF_rec_shape_of by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc (ms_regs ms0) (ms_mem ms0) _ CHECK_REPLY_STK sp0 [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v)
    [(1, pos)] lyc Sc _ 0 REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (sp1 - sp0) _ ch1
    (fun ly3 S3 W3 regs3 mem3 md3 =>
      (exists q, getr regs3 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
        forall O, astr_argA B ly3 S3 (rdW W3 mem3) (in_roP SEGS RLO RHI) O q (Some (shape_of (c_w0 v)))) /\
      Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) /\ ly3 = lyc /\ S3 = Sc) HJ2).
  - exact Psp.
  - exact Hsp1d.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. rewrite HSTK. lia.
  - exact Q3'.
  - exact Q4'.
  - exact Q1'.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof pa_base_lo as HBLO. rewrite unsigned_lit_small by lia. lia.
  - rewrite Ps0. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    + eapply (RSO fx lyc Sc Wc _ _ _ (c_p0 v) (c_w0 v) ltac:(eapply afn_pre_na_of; exact HPRE1)).
      * exact HRO3.
      * exact Q10'.
      * rewrite <- Ep0. apply Z.mod_pos_bound. lia.
      * exact Q11'.
      * lia.
      * exact HROK3.
      * exact HVAL3.
      * intros _. split.
        -- destruct Hp0s3 as [Hb _]. intros i Hi. specialize (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
           rewrite app_nth1 in Hb by exact Hi. exact Hb.
        -- left. destruct Hp0b3 as (pb3 & kb3 & Hin3 & H31 & H32). exists pb3, kb3. split; [exact Hin3 | lia].
      * unfold EV_REC_SHAPE_OF, EV_CHECK_REPLY in *. lia.
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite Q1'; reflexivity|]. split; [exact HJ1|]. split; [exact HP | exact HK].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (Hq & HPerm3 & Ely3 & ES3)).
destruct Hq as (q & Hq10 & Hq64 & HqA).
assert (HJ3' : ajournal SEGS B CHECK_REPLY_STK sp0 [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)]
  ly3 S3 W3 mem3 md3 0) by exact HJ3.
clear HJ3.
pose proof HJc3 as (_ & Hly3 & _ & _ & _ & _ & _ & _ & J9 & _ & J11 & J12 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
pose proof (cr_mid_step v lyc Sc Wc _ _ ly3 S3 W3 mem3 md3 pos MID3 HJ3' HPerm3 EF3) as MID4.
specialize (MID4 ltac:(
  intros a Ha; unfold crK in Ha; change (c_sp v) with sp0 in Ha; fold F in Ha;
  destruct Ha as [Ha|[Ha|[Ha|Ha]]];
  [ apply (J12 1 pos a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia | apply inFP_nil]
  | apply (J12 1 pos a Hfin); [right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; fold F; lia | apply inFP_nil]
  | apply J9; [lia | lia | apply inFP_nil]
  | destruct (cmd_prog_unowned SEGS B LAWS HB IMG a ltac:(exists (A_G_REC, A_G_REC + 960); split; [unfold cmd_PG; cbn [In]; tauto | cbn [fst snd]; unfold OFF_REPLY, OFF_REPLY_SIZE in Ha; lia])) as (I1 & I2 & I3);
    exact (J11 a I1 I2 I3 (fp_spares_nil a)) ])).
(* 0x87090: back from rec_shape_of, `j 0x870e4` *)
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 (@nil nat) HS3.
specialize (HS3 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
assert (HEI3 : img_env VAL A_LIM (havoc (havoc E 32 (map (getr regs2) CLOB)) 48 (map (getr regs3) CLOB)))
  by (apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (SHOK3 : sh_ok SEGS crBx [] (havoc (havoc E 32 (map (getr regs2) CLOB)) 48 (map (getr regs3) CLOB))
  (mrestrict (w_H W3) mem3)) by constructor.
clear SHOK2.
paj_run_to_tok RUNTO HS HJ3' SHOK3 crSpan CR_JOIN.
{ apply awr_ok_nil. }
pmkst HS. name_md.
pose proof (cr_mid_step v ly3 S3 W3 _ _ ly3 S3 W3 _ _ pos MID4 HJ3' (Permutation_refl _) eq_refl
  (fun a _ => aview_frame_nil _ (w_H W3) mem3 _ HFr a)) as MID5.
pose proof (aview_frame_nil _ (w_H W3) mem3 _ HFr) as K5.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22.
prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
prreg HS (27%bv : bv 5) P27. prreg HS (10%bv : bv 5) P10.
cbn [map CLOB nth] in P10. rewrite Hq10 in P10.
eapply (JOIN v ly3 S3 W3 _ _ _ pos q CX MID5).
- unfold cr_regs_at. cbv zeta.
  assert (EF3' : frame_addr ly3 1 pos = F) by (unfold F, frame_addr; rewrite EF3; reflexivity).
  rewrite EF3'.
  repeat split;
  lazymatch goal with |- getr ?rg ?r = _ =>
    match goal with P : getr rg r = ew E ?n |- _ => rewrite P, (EE n r eq_refl); assumption end end.
- exact Hcode.
- exact P10.
- exact Hq64.
- assert (Esh : shape_strA (c_n v) (c_w0 v) = shape_of (c_w0 v))
    by (unfold shape_strA; replace (c_n v =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn0); reflexivity).
  rewrite Esh. apply (s6_argA_eq B ly3 S3 (rdW W3 mem3)); [intros a; apply K5 | exact (HqA [])].
- rewrite Ely3, ES3. exact LS.
Qed.
End e.
End f.
End d.
