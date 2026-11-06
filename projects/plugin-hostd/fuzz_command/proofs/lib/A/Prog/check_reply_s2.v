(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   memchr call 0x86ef8 to the return of sup_reply_code 0x86f18, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's call steps: cl_callS, the state
   after the return) at c8557374ad2e.

   The pieces: 0x86ef8 jal memchr (the reply holds no NUL, so the wrapper returns 0: the not-found contract
   through PaArt.v's aj_art_at); 0x86efc bnez a0 (not taken); 0x86f00 mv a0,s3; 0x86f04 jal check_reply_answer
   (cl_callS); 0x86f08 the inline check of &g_rec.reply (a shadow entry of g_rec makes it a literal 0); 0x86f10
   ld a0,928(s9); 0x86f14 jal sup_reply_code (cl_callS), whose return point 0x86f18 is CR_CODE_stmt's.
   After each call the mid-walk invariant cr_mid and the registers cr_regs_at are rebuilt from the callee's journal
   (the frame (1, pos) is among the caller's frames, the saved registers lie above the callee's stack pointer, g_rec
   is a program static), and the walk is seeded again with check_reply_sd.v's cr_seed. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo CmdZsh PaArt
  PaNoChain CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_reply_k check_reply_m check_reply_sd
  check_reply_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Lemma cr2_sp1 : forall sp0, sp0 mod 16 = 0 ->
sp1_of sp0 = sp0 - 128 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16) /\ sp1_of sp0 mod 32 = 0 /\
(sp1_of sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H16.
assert (E : sp1_of sp0 = sp0 - 128 - sp0 mod 32).
{ unfold sp1_of. replace ((sp0 - 128) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity). reflexivity. }
pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)).
assert (D : sp0 mod 32 = 0 \/ sp0 mod 32 = 16) by lia.
split; [exact E|]. split; [exact D|]. rewrite E. split.
- replace (sp0 - 128 - sp0 mod 32) with ((sp0 / 32 - 4) * 32) by lia. apply Z_mod_mult.
- destruct D as [D|D]; rewrite D; [replace (sp0 - 128 - 0 - sp0) with (-8 * 16) by lia | replace (sp0 - 128 - 16 - sp0) with (-9 * 16) by lia];
  apply Z_mod_mult.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma cr2_fp_spares_nil : forall a, fp_spares [] a.
Proof. intros a. apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil]. Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the bytes cr_mid names: the flag pointer at F + 120, the shadow bytes 4..7 of the frame, the entry's saved registers
   below sp0, and g_rec.reply / g_rec.reply_size *)
Definition cr_cells (v : crv) (ly : alayout) (pos a : Z) : Prop :=
frame_addr ly 1 pos + 120 <= a < frame_addr ly 1 pos + 128 \/
SHADOW_OFF + frame_addr ly 1 pos / 8 + 4 <= a < SHADOW_OFF + frame_addr ly 1 pos / 8 + 8 \/
c_sp v - 96 <= a < c_sp v \/
A_G_REC + OFF_REPLY <= a < A_G_REC + OFF_REPLY + 16.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis CRA : forall fx0 : YK11.FPState, @tcheck_reply_answer_spec fx0 rc SK PI B MT.
Hypothesis SRC : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState, @amemchr0_nf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_memchr).
Hypothesis SIGP : cmd_sig_prog.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.

(* a lemma of check_reply_t.v at this Section's hypotheses *)
Ltac crt lem H :=
  first [ pose proof (lem B RLO RHI) as H | pose proof (lem B) as H ];
  repeat first [ specialize (H LAWS) | specialize (H HB) | specialize (H RELRO_IMG) | specialize (H IMG)
  | specialize (H CMD_RO_AT) | specialize (H RO) ].

(* the four numbers cr_seed asks, from the reply's block at the entry *)
Lemma cr2_nums : forall v, cr_cx B RLO RHI v ->
4096 <= c_p v /\ c_p v mod 16 = 0 /\ c_p v + c_nr v + 1 <= 140737479966720 /\ c_nr v + 1 <= 8194.
Proof.
intros v HCX.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _ & HRR & _ & HREPV & _).
destruct HREP as (Q & (_ & _ & _ & _ & _ & HRP & _) & _).
rewrite HRR in HRP. unfold areply_at in HRP. destruct (l_reply Q) as [[p m]|]; [|contradiction].
destruct HRP as (P1 & _ & _ & _ & P5 & P6 & _ & P8). cbn [fst snd] in *.
pose proof HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR P5) as (Hp16 & Hp4096 & Hpceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
pose proof asan_consts as (C1 & _).
assert (Ep : c_p v = p).
{ unfold c_p. rewrite (aval_mem_mod64 _ _ _ _ HREPV P1). apply Z.mod_small. lia. }
rewrite length_app in P6, P8. cbn [length] in P6, P8. unfold LMAX in *. unfold c_nr. rewrite Ep. lia.
Qed.

(* cr_mid carried to a later state whose journal goes on from the entry with the same frame, whose blocks are a
   permutation, and whose reader agrees on the cells cr_mid names *)
Lemma cr2_mid_keep : forall v lyc Sc Wc memc mdc pos ly2 S2 W2 mem2 md2,
cr_mid B v lyc Sc Wc memc mdc pos ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] ly2 S2 W2 mem2 md2 0 ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> ly_F ly2 = ly_F lyc ->
(forall a, cr_cells v lyc pos a -> rdW W2 mem2 a = rdW Wc memc a) ->
cr_mid B v ly2 S2 W2 mem2 md2 pos.
Proof.
intros v lyc Sc Wc memc mdc pos ly2 S2 W2 mem2 md2 MID HJ HP HF K.
pose proof MID as (HJ0 & HP0 & VFL & VSH & VSV & VREP & VSZ).
assert (EF : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite HF; reflexivity).
assert (EFL : flag_addr ly2 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite HF; reflexivity).
assert (VK : forall a n x, (forall k, (k < n)%nat -> cr_cells v lyc pos (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a n x -> val_mem SEGS (mrestrict (w_H W2) mem2) a n x).
{ intros a n x Hk Hv k Hlt. rewrite (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2 (a + Z.of_nat k) (K _ (Hk k Hlt))).
  exact (Hv k Hlt). }
unfold cr_mid. rewrite EF, EFL.
split; [exact HJ|]. split; [exact (perm_trans HP HP0)|].
split; [apply VK; [intros k Hk; unfold cr_cells; left; lia | exact VFL]|].
split; [intros i Hi; apply VK; [intros k Hk; unfold cr_cells; right; left; lia | exact (VSH i Hi)]|].
split.
{ intros j r Hj. assert (Hjl : (j < length cr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length cr_saved_regs] in Hjl.
  apply VK; [intros k Hk; unfold cr_cells; right; right; left; lia | exact (VSV j r Hj)]. }
split; [apply VK; [intros k Hk; unfold cr_cells, OFF_REPLY in *; right; right; right; lia | exact VREP]|].
apply VK; [intros k Hk; unfold cr_cells, OFF_REPLY, OFF_REPLY_SIZE in *; right; right; right; lia | exact VSZ].
Qed.

(* the registers cr_regs_at names are callee-saved *)
Lemma cr2_regs_keep : forall v lyc ly2 pos regs1 regs2,
cr_regs_at B v lyc pos regs1 -> aregs_preserved regs1 regs2 -> ly_F ly2 = ly_F lyc ->
cr_regs_at B v ly2 pos regs2.
Proof.
intros v lyc ly2 pos regs1 regs2 RA HP HF.
assert (EF : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite HF; reflexivity).
unfold cr_regs_at in *. rewrite EF.
destruct RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
assert (G : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HP.
split; [rewrite <- R2; exact (G 2 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R3; exact (G 3 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R4; exact (G 4 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R8; exact (G 8 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R9; exact (G 9 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R18; exact (G 18 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R23; exact (G 23 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R22; exact (G 22 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R24; exact (G 24 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R25; exact (G 25 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R20; exact (G 20 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R26; exact (G 26 ltac:(unfold acallee_saved; lia))|].
rewrite <- R27; exact (G 27 ltac:(unfold acallee_saved; lia)).
Qed.

(* where the cells lie: none in the frame header [F, F + 32) the walk may write, and each one below the allocator
   ceiling (the frame, its shadow, g_rec) or at most 96 bytes below sp0 *)
Lemma cr2_cells_geo : forall v lyc Sc Wc memc mdc pos a,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_cells v lyc pos a ->
0 <= a < 2 ^ 64 /\ ~ (frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 32) /\
(a + 1 <= alloc_ceiling \/ c_sp v - 96 <= a < c_sp v) /\ alloc_ceiling + CHECK_REPLY_STK <= c_sp v.
Proof.
intros v lyc Sc Wc memc mdc pos a CX MID Ha.
pose proof CX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof MID as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as HFimg.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold cr_cells in Ha. change (fs_frame_bytes 1) with 128 in *. unfold c_sp in *.
set (F := frame_addr lyc 1 pos) in *. set (sp0 := spZ (c_regs v)) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold off_img in HFimg.
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (HC : alloc_ceiling + CHECK_REPLY_STK <= sp0) by lia.
assert (H47' : sp0 <= 2 ^ 47) by lia.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
clear - Ha HF4096 HFceil HFapp HFimg C1 HC H47' HSTK H H0.
unfold SHADOW_OFF, A_G_REC, OFF_REPLY in *.
refine (conj _ (conj _ (conj _ HC))); destruct Ha as [Ha|[Ha|[Ha|Ha]]]; first [ lia | left; lia | right; lia ].
Qed.

(* the frame chain from sp1 with s0 = sp0: the entry's ra and s0 lie at sp0 - 8 and sp0 - 16 (cr_saved) *)
Lemma cr2_chain : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
exists ch1, achain lyc (rdW Wc memc) (sp1_of (c_sp v)) (c_sp v) ch1.
Proof.
intros v lyc Sc Wc memc mdc pos CX MID.
pose proof CX as (HPRE & _).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & _ & _ & _ & VSV & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & Kst & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
destruct (cr2_sp1 (c_sp v) Hal16) as (Hs1 & Hs2 & _).
unfold c_sp in *. set (sp0 := spZ (c_regs v)) in *.
destruct (Z_lt_le_dec sp0 (ly_top (c_ly v) - 16)) as [Hlt|Hge].
- exists ((sp0, raZ (c_regs v), s0Z (c_regs v)) :: c_ch v).
  apply (achain_ly_top (c_ly v)); [exact Etop|].
  apply (achain_push (c_ly v) (rdW (c_W v) (c_mem v))); [exact Hch0 | lia | | | | exact Hra40 | lia | | lia | lia].
  + intros a Ha. apply Kst; [lia | lia | apply inFP_nil].
  + replace (sp0 - 8) with (sp0 - 8 - 8 * Z.of_nat 0) by lia.
    apply (rdword_of_val_mem SEGS); [exact (VSV 0%nat 1 eq_refl)|].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs v) 1)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + replace (sp0 - 16) with (sp0 - 8 - 8 * Z.of_nat 1) by lia.
    apply (rdword_of_val_mem SEGS); [exact (VSV 1%nat 8 eq_refl)|].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs v) 8)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.div_mod sp0 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)). lia.
- exists []. unfold achain. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* after a program call (cl_callS): the callee's journal keeps every cell cr_mid names *)
Lemma cr2_after_call : forall v lyc Sc Wc memc mdc pos regs1 regsc STK1 sp1 ly2 S2 W2 regs2 mem2 md2 k0 k1,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regs1 ->
aregs_preserved regs1 regsc -> sp1 = sp1_of (c_sp v) -> 0 <= STK1 ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] ly2 S2 W2 mem2 md2 k0 ->
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 -> k0 = 0 ->
aregs_preserved regsc regs2 -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
cr_mid B v ly2 S2 W2 mem2 md2 pos /\ cr_regs_at B v ly2 pos regs2 /\ getr regs2 19 = getr regs1 19.
Proof.
intros v lyc Sc Wc memc mdc pos regs1 regsc STK1 sp1 ly2 S2 W2 regs2 mem2 md2 k0 k1 CX MID RA HP1 Hsp1 HSTK1 HJo HJi Hk0 HP2 HPm.
subst k0.
pose proof MID as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof HJi as (_ & Hly & _ & _ & _ & _ & _ & _ & Kst & _ & Kimg & Kfr & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof CX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _).
destruct (cr2_sp1 (c_sp v) Hal16) as (Hs1 & Hs2 & _).
split; [|split].
- apply (cr2_mid_keep v lyc Sc Wc memc mdc pos ly2 S2 W2 mem2 md2 MID HJo HPm HlyF).
  intros a Ha. destruct (cr2_cells_geo v lyc Sc Wc memc mdc pos a CX MID Ha) as (Ha64 & _ & Hlo & HCEIL).
  unfold cr_cells in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  + apply (Kfr 1 pos a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia | apply inFP_nil].
  + apply (Kfr 1 pos a Hfin); [right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; lia | apply inFP_nil].
  + assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
    apply Kst; [lia | | apply inFP_nil]. subst sp1. rewrite Hs1. lia.
  + destruct (cmd_prog_unowned SEGS B LAWS HB IMG a) as (I1 & I2 & I3).
    { exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_REPLY in Ha; lia]. }
    exact (Kimg a I1 I2 I3 (cr2_fp_spares_nil a)).
- exact (cr2_regs_keep v lyc ly2 pos regs1 regs2 RA (aregs_preserved_trans _ _ _ HP1 HP2) HlyF).
- transitivity (getr regsc 19).
  + exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  + exact (HP1 19 ltac:(unfold acallee_saved; lia)).
Qed.

(* the event budget at a mid-walk state: the journal adds no event (k = 0) and EV_CHECK_REPLY = 0 *)
Lemma cr2_nev : forall v lyc Sc Wc memc mdc pos, cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
st_nev Sc <= EV_MAX.
Proof.
intros v lyc Sc Wc memc mdc pos CX MID.
destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _).
pose proof MID as (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
unfold EV_CHECK_REPLY in HEV. lia.
Qed.

(* the walk's tactics: the frame facts, the atoms of crM the walk reads, the shadow entries, the write windows *)
Ltac cr2_frame MID :=
  pose proof MID as (HJ & HPm & _);
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _);
  assert (Hfin : In (1, _) (frames _)) by (rewrite Hfrs; left; reflexivity);
  destruct (frames_bounds _ B LAWS _ _ _ _ _ 1 _ HAR Hfin) as (HF4096 & HFceil & HFapp);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
Ltac cr2_env HS :=
  lazymatch type of HS with st_ok_pi _ _ (crM ?regs1 ?v ?lyc ?pos) _ _ =>
  pose proof (crM_extra_nth regs1 v lyc pos 0 ltac:(lia)) as E32;
  pose proof (crM_extra_nth regs1 v lyc pos 1 ltac:(lia)) as E33;
  pose proof (crM_extra_nth regs1 v lyc pos 2 ltac:(lia)) as E34;
  pose proof (crM_extra_nth regs1 v lyc pos 4 ltac:(lia)) as E36;
  cbn [Nat.add nth crM_extra map app] in E32, E33, E34, E36;
  assert (HEI : img_env VAL A_LIM (crM regs1 v lyc pos)) by (unfold crM; apply Eimg_env);
  let E := fresh "E" in set (E := crM regs1 v lyc pos) in *;
  assert (UB : U E crBx = SHADOW_OFF) by (unfold crBx; rewrite (U_atom E 32 SBc E32) by (unfold SBc; lia); reflexivity);
  assert (U33 : U E (SOff 33 0) = A_G_REC) by (rewrite (U_atom E 33 0x5e3740 E33) by lia; reflexivity);
  assert (U36 : U E (SOff 36 0) = frame_addr lyc 1 pos) by (apply (U_atom E 36 _ E36); lia);
  assert (B36 : bv_unsigned (ew E 36) = frame_addr lyc 1 pos) by (rewrite E36; apply unsigned_lit_small; lia)
  end.
Ltac cr2_shent UB U33 U36 GR HAR Hfin :=
  lazymatch goal with
  | |- shent_ok ?sg _ _ (mrestrict ?H ?m) (mkSHE 33 928 944) =>
    apply (shent_ok_of_range sg H m _ crBx 33 A_G_REC 960 A_G_REC 928 944 GR UB U33);
    [unfold A_G_REC; lia | unfold A_G_REC; lia | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF, A_G_REC in *; lia]
  | |- shent_ok ?sg _ ?Ev ?M (mkSHE 36 ?whi ?wlo) =>
    eapply (shent_app_of_frame sg B LAWS); [exact HAR | exact Hfin | exact UB | exact U36 | lia | lia |
      change (fs_frame_bytes 1) with 128; lia]
  | |- _ => fail "cr2_shent: no rule for this shadow entry"
  end.
Ltac cr2_shok HS SHOK M UB U33 U36 GR HAR Hfin :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ev ?ss _ =>
  let SH := eval lazy in (crSH_mid ++ app_entries (ss_facts ss) (ss_mem ss)) in
  assert (SHOK : sh_ok sg crBx SH Ev M);
  [ unfold sh_ok; repeat (apply Forall_cons; [ cr2_shent UB U33 U36 GR HAR Hfin | ]); apply Forall_nil | ] end.
Ltac cr2_awr B36 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | exact B36 | |];
    [ intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; do 2 eexists; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia | ] ].
(* name the model after a run (else the model term grows at each run) *)
Ltac cr2_name_md mdq := lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the stack pointer facts of the entry *)
Ltac cr2_sp CX :=
  lazymatch type of CX with cr_cx _ _ _ ?v =>
  pose proof CX as (HPRE & _);
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _);
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _);
  change (spZ (c_regs v)) with (c_sp v) in Hal16, Hslo0, Hshi0;
  destruct (cr2_sp1 (c_sp v) Hal16) as (Hs1 & Hs2 & Hs3 & Ho16);
  assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity end.
(* the cells cr_mid names are kept by a run that writes only the frame header [F, F + 32) *)
Ltac cr2_mid_run CX MID HJ HFr B36 :=
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc ?Wc ?mm ?mdq _ =>
  lazymatch type of MID with cr_mid _ ?v ?lyc0 ?Sc0 ?Wc0 ?memc ?mdc ?pos =>
  apply (cr2_mid_keep v lyc0 Sc0 Wc0 memc mdc pos lyc Sc Wc mm mdq MID HJ (Permutation_refl _) eq_refl);
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  let Ha64 := fresh in let HaF := fresh in
  destruct (cr2_cells_geo v lyc0 Sc0 Wc0 memc mdc pos a CX MID Ha) as (Ha64 & HaF & _ & _);
  apply (kept_of_frame _ _ (w_H Wc) memc mm (fun x => frame_addr lyc0 1 pos <= x < frame_addr lyc0 1 pos + 32) HFr);
  [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi x Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?B36 in Hrr; lia|]);
    destruct Hin
  | exact Ha64 | exact HaF ] end end.
(* a callee-saved register at a stop of a run equals its value at the run's start: both are the same symbolic value *)
Ltac cr2_reg_eq HS0 HS :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
  lazymatch type of HS with st_ok ?sg ?Ev ?ss (restrict ?H ?ms) =>
  lazymatch type of HS0 with st_ok_pi _ _ ?Ev0 ?ss0 (restrict ?H0 ?ms0) =>
  transitivity (sv_denot Ev (sr_get (ss_regs ss) r)); [exact (st_ok_restrict_reg sg H Ev ss ms r HS)|];
  etransitivity; [| symmetry; exact (st_ok_pi_restrict_reg H0 Ev0 ss0 ms0 r HS0)];
  f_equal; vm_compute; reflexivity end end end.
Ltac cr2_regs_pres HS0 HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [-> | Hc]; [cr2_reg_eq HS0 HS |]); subst r; cr2_reg_eq HS0 HS.

Definition CR_RCRA_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regs1 ->
getr regs1 19 = w64 (c_w v) -> cr_ls v lyc Sc -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
cr_at B v Wc regs1 memc mdc CR_RET_CRA.

(* 0x86f08 .. 0x86f14: the check of &g_rec.reply, the load of the reply, and sup_reply_code *)
Lemma cr2_src : CR_CODE_stmt B RLO RHI -> CR_RCRA_stmt.
Proof.
intros CODE v lyc Sc Wc regs1 memc mdc pos CX MID RA R19 LS HFRM.
unfold cr_at.
destruct (cr2_nums v CX) as (N1 & N2 & N3 & N4).
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_RET_CRA false CX MID RA N1 N2 N3 N4) as HS.
cr2_frame MID.
cr2_env HS.
assert (GR : range_addressable (rdW Wc memc) SHADOW_OFF A_G_REC 960)
  by (crt cr_grec_addressable G; exact (G _ _ _ _ _ A_G_REC 960 HAR ltac:(lia) ltac:(lia))).
cr2_shok HS SHOK (mrestrict (w_H Wc) memc) UB U33 U36 GR HAR Hfin.
pose proof HS as HS0.
paj_run_tok RUN HS HJ SHOK crSpan.
{ cr2_awr B36. }
cr2_name_md mdq.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (HPc : aregs_preserved regs1 (ms_regs ms)) by (cr2_regs_pres HS0 HS).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) _) _ => set (rg := r) in *; set (mm := m) in * end.
assert (MIDq : cr_mid B v lyc Sc Wc mm mdq pos) by (cr2_mid_run CX MID HJ HFr B36).
rewrite E34 in Q10.
pose proof (cr2_regs_keep v lyc lyc pos regs1 rg RA HPc eq_refl) as RAq.
pose proof RAq as (Q2 & Q3 & Q4 & Q8 & _).
cr2_sp CX.
crt cr_state_facts SF.
destruct (SF v lyc Sc Wc mm mdq pos CX MIDq) as (ROq & ROKq & GOTq & GRDq & FLq & (ev & ERRq) & ROMq & ROIq & VOq).
crt cr_reply_facts RF.
destruct (RF v lyc Sc Wc mm mdq pos CX MIDq) as (m & Hinm & Hm & STRq & TAILq & INBq & NZq).
destruct (cr2_chain v lyc Sc Wc mm mdq pos CX MIDq) as (ch1 & CHq).
pose proof (cr2_nev v lyc Sc Wc mm mdq pos CX MIDq) as NEVq.
assert (SIG_SRC : SIG CS_sup_reply_code = BASE + AF_sup_reply_code)
  by (rewrite (SIGP CS_sup_reply_code) by (unfold cmd_prog_syms; repeat (first [left; reflexivity | right])); reflexivity).
rewrite SIG_SRC.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
assert (Hsp : spZ rg = c_sp v + (sp1_of (c_sp v) - c_sp v)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc rg mm (Z_to_bv 64 (BASE + AF_sup_reply_code)) CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v)
    (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc mdq 0 SUP_REPLY_CODE_STK [] EV_SUP_REPLY_CODE (sp1_of (c_sp v) - c_sp v)
    (Z_to_bv 64 (BASE + CR_RET_SRC)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (reply_code_a (c_xr v)) /\
       Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ ly2 = lyc /\ S2 = Sc)
    HJ Hsp Ho16).
  - lia.
  - unfold SUP_REPLY_CODE_STK, ESTACK; lia.
  - rewrite HSTK; unfold SUP_REPLY_CODE_STK, ESTACK; lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold CR_RET_SRC; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold CR_RET_SRC; lia). unfold CR_RET_SRC; lia.
  - replace (c_sp v + (sp1_of (c_sp v) - c_sp v)) with (sp1_of (c_sp v)) by lia.
    unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. exact CHq.
  - intros HPRE1. eapply SRr_mono.
    + apply (SRC fx lyc Sc Wc rg mm mdq (c_p v) (c_xr v) ltac:(eapply afn_pre_na_of; exact HPRE1) ROq Q10
        ltac:(unfold c_p; apply Z.mod_pos_bound; lia) INBq STRq TAILq ROKq VOq).
      unfold EV_SUP_REPLY_CODE. lia.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, Q1; reflexivity|]. split; [exact HJc|].
      split; [exact HPr | exact HK].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (A0 & HPm3 & Ely3 & ES3)).
destruct (cr2_after_call v lyc Sc Wc mm mdq pos rg rg SUP_REPLY_CODE_STK (c_sp v + (sp1_of (c_sp v) - c_sp v))
  ly3 S3 W3 regs3 mem3 md3 _ _ CX MIDq RAq (fun r _ => eq_refl) ltac:(lia) ltac:(unfold SUP_REPLY_CODE_STK, ESTACK; lia)
  HJo HJi ltac:(reflexivity) HP3 HPm3) as (MID3 & RA3 & S19).
apply (CODE v ly3 S3 W3 regs3 mem3 md3 pos CX MID3 RA3).
- rewrite S19, <- R19. exact (HPc 19 ltac:(unfold acallee_saved; lia)).
- exact A0.
- rewrite Ely3, ES3. exact LS.
- exact HFRM.
Qed.

Definition CR_RMC_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> cr_regs_at B v lyc pos regs1 ->
getr regs1 19 = w64 (c_w v) -> getr regs1 10 = w64 0 -> cr_bd v -> cr_ls v lyc Sc ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
cr_at B v Wc regs1 memc mdc CR_RET_MEMCHR.

(* 0x86efc .. 0x86f04: memchr's 0 decides `bnez a0` (the abort branch is not taken); check_reply_answer(w) *)
Lemma cr2_cra : CR_RCRA_stmt -> CR_RMC_stmt.
Proof.
intros RCRA v lyc Sc Wc regs1 memc mdc pos CX MID RA R19 R10 BD LS HFRM.
unfold cr_at.
destruct (cr2_nums v CX) as (N1 & N2 & N3 & N4).
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_RET_MEMCHR false CX MID RA N1 N2 N3 N4) as HS.
cr2_frame MID.
cr2_env HS.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS ltac:(exact R10) eq_refl) as HSp.
lazymatch type of HSp with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HSp end.
clear HS. rename HSp into HS.
assert (GR : range_addressable (rdW Wc memc) SHADOW_OFF A_G_REC 960)
  by (crt cr_grec_addressable G; exact (G _ _ _ _ _ A_G_REC 960 HAR ltac:(lia) ltac:(lia))).
cr2_shok HS SHOK (mrestrict (w_H Wc) memc) UB U33 U36 GR HAR Hfin.
pose proof HS as HS0.
paj_run_tok RUN HS HJ SHOK crSpan.
{ cr2_awr B36. }
cr2_name_md mdq.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (HPc : aregs_preserved regs1 (ms_regs ms)) by (cr2_regs_pres HS0 HS).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) _) _ => set (rg := r) in *; set (mm := m) in * end.
assert (MIDq : cr_mid B v lyc Sc Wc mm mdq pos) by (cr2_mid_run CX MID HJ HFr B36).
assert (Q10' : getr rg 10 = w64 (c_w v))
  by (rewrite Q10, <- R19; exact (crM_reg regs1 v lyc pos 19 (19%bv : bv 5) eq_refl)).
pose proof (cr2_regs_keep v lyc lyc pos regs1 rg RA HPc eq_refl) as RAq.
pose proof RAq as (Q2 & Q3 & Q4 & Q8 & _).
cr2_sp CX.
crt cr_state_facts SF.
destruct (SF v lyc Sc Wc mm mdq pos CX MIDq) as (ROq & ROKq & GOTq & GRDq & FLq & (ev & ERRq) & ROMq & ROIq & VOq).
crt cr_rec_facts RCF. pose proof (RCF v lyc Sc Wc mm mdq pos CX MIDq) as RECq.
crt cr_words_facts WF. destruct (WF v lyc Sc Wc mm mdq pos CX MIDq) as (W8 & WRA & WWq & WNq & WBq).
crt cr_answer_facts ANF. destruct (ANF v lyc Sc Wc mm mdq pos CX MIDq) as (ANSq & REPq & TREPq & TANSq).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hry & Hno0 & _ & _ & _ & _ & _ & Hspw & _ & _ & _ & Hn & _ & HAOK & _).
change (spZ (c_regs v)) with (c_sp v) in Hspw.
assert (HWHI : c_w v + 32 <= ly_stk_hi (c_ly v)) by (unfold cr_cx in CX; do 29 (apply proj2 in CX); exact CX).
destruct BD as (BW & BREP & BANS & BWW & BP0 & BWA).
(* check_reply_answer's word premise under n = 1, with the slot's alignment from check_reply's own (cr_bd) *)
assert (WB1 : c_n v = 1 ->
  in_blockA (ablocks B lyc Sc) (c_ww v) 8 /\ c_ww v mod 8 = 0 /\ aval_mem (rdW Wc mm) (c_ww v) 8 (c_p0 v) /\
  0 <= c_p0 v < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (c_p0 v) (Z.of_nat (length (c_w0 v)) + 1) /\ astr_atR (rdW Wc mm) (c_p0 v) (c_w0 v) /\
  atail_vis SEGS Wc mm (c_p0 v + Z.of_nat (length (c_w0 v)))).
{ intros H1. destruct (WBq ltac:(lia)) as (A1 & A2 & A3 & A4 & A5). pose proof (BP0 ltac:(lia)) as A6.
  pose proof (BWA ltac:(lia)) as A7. tauto. }
destruct (cr2_chain v lyc Sc Wc mm mdq pos CX MIDq) as (ch1 & CHq).
pose proof (cr2_nev v lyc Sc Wc mm mdq pos CX MIDq) as NEVq.
assert (SIG_CRA : SIG CS_check_reply_answer = BASE + AF_check_reply_answer)
  by (rewrite (SIGP CS_check_reply_answer) by (unfold cmd_prog_syms; repeat (first [left; reflexivity | right])); reflexivity).
rewrite SIG_CRA.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
assert (Hsp : spZ rg = c_sp v + (sp1_of (c_sp v) - c_sp v)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc rg mm (Z_to_bv 64 (BASE + AF_check_reply_answer)) CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v)
    (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc mdq 0 CHECK_REPLY_ANSWER_STK [] EV_CHECK_REPLY_ANSWER
    (sp1_of (c_sp v) - c_sp v) (Z_to_bv 64 (BASE + CR_RET_CRA)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ ly2 = lyc /\ S2 = Sc)
    HJ Hsp Ho16).
  - lia.
  - unfold CHECK_REPLY_ANSWER_STK, SUP_REPLY_CODE_STK, ESTACK; lia.
  - rewrite HSTK; unfold CHECK_REPLY_ANSWER_STK, SUP_REPLY_CODE_STK, ESTACK; lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold CR_RET_CRA; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold CR_RET_CRA; lia). unfold CR_RET_CRA; lia.
  - replace (c_sp v + (sp1_of (c_sp v) - c_sp v)) with (sp1_of (c_sp v)) by lia.
    unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. exact CHq.
  - intros HPRE1. eapply SRr_mono.
    + apply (CRA fx lyc Sc Wc rg mm mdq (c_w v) (c_ww v) (c_p0 v) (c_n v) (c_rep v) (c_ans v) (c_xr v) (c_w0 v)
        (c_R v) (c_O v) ltac:(eapply afn_pre_na_of; exact HPRE1) ROq ROKq VOq Q10' BW RECq Hry Hno0 REPq BREP TREPq
        ANSq BANS TANSq W8 ltac:(rewrite Hsp; lia)
        ltac:(destruct LS as (Ely & _); rewrite Ely; unfold WORDS_W; lia) WWq BWW WNq Hn WB1 HAOK).
      unfold EV_CHECK_REPLY_ANSWER. lia.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, Q1; reflexivity|]. split; [exact HJc|].
      split; [exact HPr | exact HK].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (HPm3 & Ely3 & ES3)).
destruct (cr2_after_call v lyc Sc Wc mm mdq pos rg rg CHECK_REPLY_ANSWER_STK (c_sp v + (sp1_of (c_sp v) - c_sp v))
  ly3 S3 W3 regs3 mem3 md3 _ _ CX MIDq RAq (fun r _ => eq_refl) ltac:(lia)
  ltac:(unfold CHECK_REPLY_ANSWER_STK, SUP_REPLY_CODE_STK, ESTACK; lia)
  HJo HJi ltac:(reflexivity) HP3 HPm3) as (MID3 & RA3 & S19).
apply (RCRA v ly3 S3 W3 regs3 mem3 md3 pos CX MID3 RA3).
- rewrite S19, <- R19. exact (HPc 19 ltac:(unfold acallee_saved; lia)).
- rewrite Ely3, ES3. exact LS.
- exact HFRM.
Qed.

(* 0x86ef8 jal memchr: the reply holds no NUL, so the wrapper returns 0 (the not-found contract amemchr0_nf_realizes) *)
Theorem cr_s2 : CR_CODE_stmt B RLO RHI -> CR_MC_stmt B RLO RHI.
Proof.
intros CODE. pose proof (cr2_cra (cr2_src CODE)) as RMC.
intros v lyc Sc Wc regs1 memc mdc pos CX MID RA R19 R10 R11 R12 BD LS HFRM.
unfold cr_at.
destruct (cr2_nums v CX) as (N1 & N2 & N3 & N4).
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_MEMCHR false CX MID RA N1 N2 N3 N4) as HS.
cr2_frame MID.
cr2_env HS.
assert (GR : range_addressable (rdW Wc memc) SHADOW_OFF A_G_REC 960)
  by (crt cr_grec_addressable G; exact (G _ _ _ _ _ A_G_REC 960 HAR ltac:(lia) ltac:(lia))).
cr2_shok HS SHOK (mrestrict (w_H Wc) memc) UB U33 U36 GR HAR Hfin.
pose proof HS as HS0.
paj_run_tok RUN HS HJ SHOK crSpan.
{ cr2_awr B36. }
cr2_name_md mdq.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
assert (HPc : aregs_preserved regs1 (ms_regs ms)) by (cr2_regs_pres HS0 HS).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) _) _ => set (rg := r) in *; set (mm := m) in * end.
assert (MIDq : cr_mid B v lyc Sc Wc mm mdq pos) by (cr2_mid_run CX MID HJ HFr B36).
assert (Q10' : getr rg 10 = w64 (c_p v))
  by (rewrite Q10, <- R10; exact (crM_reg regs1 v lyc pos 10 (10%bv : bv 5) eq_refl)).
assert (Q11' : getr rg 11 = w64 0)
  by (rewrite Q11, <- R11; exact (crM_reg regs1 v lyc pos 11 (11%bv : bv 5) eq_refl)).
assert (Q12' : getr rg 12 = w64 (c_nr v))
  by (rewrite Q12, <- R12; exact (crM_reg regs1 v lyc pos 12 (12%bv : bv 5) eq_refl)).
pose proof (cr2_regs_keep v lyc lyc pos regs1 rg RA HPc eq_refl) as RAq.
pose proof RAq as (Q2 & Q3 & Q4 & Q8 & _).
cr2_sp CX.
crt cr_state_facts SF.
destruct (SF v lyc Sc Wc mm mdq pos CX MIDq) as (ROq & ROKq & GOTq & GRDq & FLq & (ev & ERRq) & ROMq & ROIq & VOq).
crt cr_reply_facts RF.
destruct (RF v lyc Sc Wc mm mdq pos CX MIDq) as (m & Hinm & Hm & STRq & TAILq & INBq & NZq).
pose proof HJ as (HARq & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
assert (Hsp : spZ rg = c_sp v + (sp1_of (c_sp v) - c_sp v)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ apply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_memchr)
    Wc rg mm CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc mdq 0
    (sp1_of (c_sp v) - c_sp v) (Z_to_bv 64 (BASE + CR_RET_MEMCHR)) (fun regs' _ => getr regs' 10 = w64 0) HJ Hsp Ho16).
  - lia.
  - unfold ESTACK; lia.
  - rewrite HSTK; unfold ESTACK; lia.
  - exact Q1.
  - intros a [].
  - apply (AMEMCHR fx lyc Sc Wc rg mm mdq (c_p v) (c_nr v)).
    + apply (ecall_pre_stk_at SEGS B ESTACK CHECK_REPLY_STK (c_sp v) [] _ _ _ _ _ _ lyc Sc Wc mm mdq 0 rg
        (sp1_of (c_sp v) - c_sp v) HJ Hsp Ho16);
      [lia | lia | rewrite HSTK; unfold ESTACK; lia | rewrite Q1; apply ret_ok_codeptr_v; [unfold CR_RET_MEMCHR; lia | reflexivity]
      | exact Q3 | exact Q4].
    + exact Q10'.
    + exact Q11'.
    + exact Q12'.
    + unfold c_nr in *; lia.
    + lia.
    + split; [unfold c_nr; lia|]. split; [intros i Hi; exact (NZq i Hi) | intros Hlt; lia].
    + apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc Wc rg mm mdq (c_p v) m (c_p v) (c_nr v) HARq Hinm);
        [lia | lia | unfold c_nr; lia | rewrite Hsp; unfold ESTACK; lia].
    + exact ROMq. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & A0 & HK).
assert (MID2 : cr_mid B v lyc Sc Wc mem2 md2 pos).
{ apply (cr2_mid_keep v lyc Sc Wc mm mdq pos lyc Sc Wc mem2 md2 MIDq HJ2 (Permutation_refl _) eq_refl).
  intros a Ha. destruct (cr2_cells_geo v lyc Sc Wc mm mdq pos a CX MIDq Ha) as (Ha64 & _ & Hlo & HCEIL).
  apply HK; [exact Ha64 | | intros []].
  unfold ESTACK. lia. }
pose proof (cr2_regs_keep v lyc lyc pos rg regs2 RAq HP2 eq_refl) as RA2.
apply (RMC v lyc Sc Wc regs2 mem2 md2 pos CX MID2 RA2).
- transitivity (getr rg 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) |].
  rewrite <- R19. exact (HPc 19 ltac:(unfold acallee_saved; lia)).
- exact A0.
- exact BD.
- exact LS.
- exact HFRM.
Qed.

End e.
End f.
End d.
