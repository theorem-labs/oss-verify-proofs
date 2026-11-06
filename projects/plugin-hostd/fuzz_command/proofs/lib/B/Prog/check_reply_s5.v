(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_s5.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): B's addresses (a Theorem Labs lane's pairing, a Theorem Labs lane's reloc). *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan-ubsan, 0x86e64), the
   strcmp call of the refusal path (0x870d0) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x870d0  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x870d4  beqz a0, 0x87114          equal: the epilogue; else j 0x871f4, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x870d8 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall PaArt CmdBase CmdRep CmdObj CmdRo CmdZsh
  CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_reply_k check_reply_m check_reply_sd check_reply_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* every declared code has a short refusal text, so the reply and the frame's copy fit in refusal[32] *)
Lemma refusal_len_declared : forall c, declared c = true -> (length (refusal_text c) <= 16)%nat.
Proof.
intros c Hc. unfold declared in Hc.
pose proof (In_of_existsb c rec_codes Hc) as Hin.
assert (Hall : forallb (fun x => Nat.leb (length (refusal_text x)) 16) rec_codes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall c Hin). apply Nat.leb_le in Hall. exact Hall.
Qed.

(* two values whose 8 little-endian bytes agree are equal mod 2^64 (check_reply_s8.v s8_le_byte8) *)
Lemma s5_le_byte8 : forall x y, (forall k, (k < 8)%nat -> le_byte x 8 k = le_byte y 8 k) -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
intros x y H.
assert (E : forall z k, le_byte (z mod 2 ^ 64) 8 k = le_byte z 8 k)
  by (intros z k; unfold le_byte; change (8 * Z.of_nat 8) with 64; rewrite Z.mod_mod by lia; reflexivity).
rewrite <- (le_bytes8 (x mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
rewrite <- (le_bytes8 (y mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
rewrite !E. rewrite !H by lia. reflexivity.
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

(* a step that writes nothing keeps every byte the walk reads *)
Lemma aview_same : forall (H : word -> bool) (m m' : word -> option byte) a,
(forall x, m' x = m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hm. unfold aview, mbyte, mrestrict. rewrite Hm. reflexivity. Qed.
Lemma atail_vis_same : forall (W : world SEGS) m m' e,
(forall x, m' x = m x) -> atail_vis SEGS W m e -> atail_vis SEGS W m' e.
Proof. intros W m m' e Hm H a Ha. rewrite (aview_same (w_H W) m m' a Hm). exact (H a Ha). Qed.
Lemma rt_rom_view_same : forall (B : asyms) (W : world SEGS) m m',
(forall x, m' x = m x) -> rt_rom_view SEGS B W m -> rt_rom_view SEGS B W m'.
Proof.
intros B W m m' Hm H a Hr Ho He. rewrite (aview_same (w_H W) m m' a Hm). exact (H a Hr Ho He).
Qed.
(* a register the symbolic state still names by its mid-walk expression holds its mid-walk value *)
Lemma regs_eq_of_sr : forall E E' K ss ms (H : word -> bool) (regs1 : bvmap 5 word) (r : bv 5),
st_ok_pi SEGS VAL E' ss (restrict H ms) ->
regs_ok E sr_mid regs1 -> env_agree K E E' ->
sv_eqb (sr_get (ss_regs ss) r) (sr_get sr_mid r) = true ->
sv_atoms_lt K (sr_get sr_mid r) = true ->
getr (ms_regs ms) r = getr regs1 r.
Proof.
intros E E' K ss ms H regs1 r HS HR HA Hq Hlt.
rewrite (st_ok_pi_restrict_reg H E' ss ms r HS).
apply sv_eqb_eq in Hq. rewrite Hq.
rewrite (sv_denot_agree K E E' _ HA Hlt).
symmetry. exact (HR r).
Qed.
Lemma regs_eq_of_st : forall E E' K ss ms (H : word -> bool) (regs1 : bvmap 5 word) (r : bv 5),
st_ok SEGS E' ss (restrict H ms) ->
regs_ok E sr_mid regs1 -> env_agree K E E' ->
sv_eqb (sr_get (ss_regs ss) r) (sr_get sr_mid r) = true ->
sv_atoms_lt K (sr_get sr_mid r) = true ->
getr (ms_regs ms) r = getr regs1 r.
Proof.
intros E E' K ss ms H regs1 r HS HR HA Hq Hlt.
rewrite (st_ok_restrict_reg SEGS H E' ss ms r HS).
apply sv_eqb_eq in Hq. rewrite Hq.
rewrite (sv_denot_agree K E E' _ HA Hlt).
symmetry. exact (HR r).
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* the reply block's address and size as cr_seed takes them (check_reply_s8.v cr_s8_nums) *)
Lemma cr_s5_nums : forall v, cr_cx B RLO RHI v ->
4096 <= c_p v /\ c_p v mod 16 = 0 /\ c_p v + c_nr v + 1 <= 140737479966720 /\ c_nr v + 1 <= 8194.
Proof.
intros v HCX.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _ & HRR & _ & HREPV & _).
destruct HREP as (Q & (_ & _ & _ & _ & _ & HRP & _) & _).
rewrite HRR in HRP. unfold areply_at in HRP. destruct (l_reply Q) as [[p m]|]; [|cbn in HRP; contradiction].
destruct HRP as (P1 & _ & _ & _ & P5 & P6 & _ & P8). cbn [fst snd] in *.
pose proof HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR P5) as (Hp16 & Hp4096 & Hpceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hr].
pose proof asan_consts as (C1 & _).
assert (Ep : c_p v = p).
{ unfold c_p. assert (Hpm : p mod 2 ^ 64 = p) by (apply Z.mod_small; lia).
  rewrite <- Hpm. apply s5_le_byte8. intros k Hk.
  pose proof (HREPV k Hk) as E1. pose proof (P1 k Hk) as E2. rewrite E1 in E2. injection E2 as E. exact E. }
rewrite length_app in P6, P8. cbn [length] in P6, P8. unfold c_nr, LMAX in *. rewrite Ep. lia.
Qed.

(* the kept registers carry cr_regs_at *)
Lemma cr_regs_at_of_eq : forall v lyc pos (regs regs' : bvmap 5 word),
cr_regs_at B v lyc pos regs ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
getr regs' 20 = getr regs 20 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 ->
cr_regs_at B v lyc pos regs'.
Proof.
intros v lyc pos regs regs' RA K2 K3 K4 K8 K9 K18 K20 K22 K23 K24 K25 K26 K27.
unfold cr_regs_at. rewrite K2, K3, K4, K8, K9, K18, K20, K22, K23, K24, K25, K26, K27. exact RA.
Qed.
Lemma cr_regs_at_pres : forall v lyc pos (regs regs' : bvmap 5 word),
cr_regs_at B v lyc pos regs -> aregs_preserved regs regs' -> cr_regs_at B v lyc pos regs'.
Proof.
intros v lyc pos regs regs' RA HP.
apply (cr_regs_at_of_eq v lyc pos regs regs' RA);
first
[ apply (HP 2); unfold acallee_saved; lia | apply (HP 3); unfold acallee_saved; lia
| apply (HP 4); unfold acallee_saved; lia | apply (HP 8); unfold acallee_saved; lia
| apply (HP 9); unfold acallee_saved; lia | apply (HP 18); unfold acallee_saved; lia
| apply (HP 20); unfold acallee_saved; lia | apply (HP 22); unfold acallee_saved; lia
| apply (HP 23); unfold acallee_saved; lia | apply (HP 24); unfold acallee_saved; lia
| apply (HP 25); unfold acallee_saved; lia | apply (HP 26); unfold acallee_saved; lia
| apply (HP 27); unfold acallee_saved; lia ].
Qed.

(* the mid-walk invariant at a state whose memory differs only inside a window above the heap and below the
   entry's saved registers: the frame, its flag word, its shadow and g_rec's fields lie below the window, the
   saved registers above it *)
Lemma cr_mid_kept : forall v lyc Sc Wc memc mdc pos memc' mdc' lo hi,
cr_mid B v lyc Sc Wc memc mdc pos ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW Wc memc' a = rdW Wc memc a) ->
alloc_ceiling <= lo -> hi <= c_sp v - 96 ->
cr_mid B v lyc Sc Wc memc' mdc' pos.
Proof.
intros v lyc Sc Wc memc mdc pos memc' mdc' lo hi MID HJ' K Hlo Hhi.
pose proof MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil.
assert (HF8 : frame_addr lyc 1 pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (HF8a : 0 <= frame_addr lyc 1 pos / 8) by (apply Z.div_pos; lia).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
split; [exact HJ'|]. split; [exact HPerm|].
split.
{ apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc'
    (frame_addr lyc 1 pos + 120) (frame_addr lyc 1 pos + 120) 8 (flag_addr lyc 1 pos));
  [intros k Hk; apply K; lia | exact VFL]. }
split.
{ intros i Hi.
  apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc'
    (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 0);
  [intros k Hk; apply K; unfold SHADOW_OFF; lia | exact (VSH i Hi)]. }
split.
{ intros j r Hj.
  assert (Hj12 : (j < 12)%nat)
    by (change 12%nat with (length cr_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
  apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc'
    (c_sp v - 8 - 8 * Z.of_nat j) (c_sp v - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr (c_regs v) (Z_to_bv 5 r))));
  [intros k Hk; apply K; unfold c_sp in *; lia | exact (VSV j r Hj)]. }
split.
{ apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc' (A_G_REC + OFF_REPLY) (A_G_REC + OFF_REPLY) 8 (c_p v));
  [intros k Hk; apply K; unfold A_G_REC, OFF_REPLY; lia | exact VREP]. }
{ apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc' (A_G_REC + OFF_REPLY_SIZE) (A_G_REC + OFF_REPLY_SIZE) 8
    (c_nr v + 1));
  [intros k Hk; apply K; unfold A_G_REC, OFF_REPLY_SIZE; lia | exact VSZ]. }
Qed.

Theorem cr_s5 : CR_EPI_stmt B RLO RHI -> CR_STRCMP_stmt B RLO RHI.
Proof.
intros EPI v lyc Sc Wc regs1 memc mdc pos CX MID RA Hneg Hr19 Hr21 Hr10 Hr11 HFB LS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof CX as (HPRE & Hfr7 & HROD & HGOT & HROK & HROI & HVO & HGRD & Hw10 & HREC & Hn1 & Hry & Hno0 & Hrep & Htr
  & Hans & Hta & Hw8 & Hspw & HWRA & Hww & Hnv & Hn & HN0 & HAOK & HRY & HFL & HERR & HEV & HWHI).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ0 & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HJ0 as (HARc & _ & _ & _ & _ & Hfrs & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
destruct (cr_s5_nums v CX) as (Hp4096 & Hp16 & Hphi & Hnr8194).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
(* the refusal text: the reply is exactly what the frame holds, and it is short *)
destruct (proj1 HRY Hneg) as [Hdecl0 Hxr0].
assert (Hdecl : declared (c_code v) = true) by exact Hdecl0.
assert (Hxr : c_xr v = refusal_text (c_code v)) by exact Hxr0.
clear Hdecl0 Hxr0.
pose proof (refusal_len_declared _ Hdecl) as Hlen16.
assert (Hnr16 : c_nr v <= 16) by (unfold c_nr; rewrite Hxr; lia).
assert (Hnr0 : 0 <= c_nr v) by (unfold c_nr; lia).
assert (Hno0' : ~ In (Z_to_bv 8 0) (refusal_text (c_code v))) by (rewrite <- Hxr; exact Hno0).
assert (Hrlen : astr_len (refusal_text (c_code v)) = c_nr v) by (unfold astr_len, c_nr; rewrite Hxr; reflexivity).
(* the frame and the reply block *)
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HFal & HFinapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFpres, HFSpres, HFceil, HFapp.
assert (HF8m : frame_addr lyc 1 pos mod 8 = 0)
  by (pose proof (Z.div_mod (frame_addr lyc 1 pos) 32 ltac:(lia)) as D; rewrite HFal, Z.add_0_r in D; rewrite D;
      replace (32 * (frame_addr lyc 1 pos / 32)) with ((4 * (frame_addr lyc 1 pos / 32)) * 8) by lia; apply Z_mod_mult).
destruct (cr_reply_facts B RLO RHI LAWS HB v lyc Sc Wc memc mdc pos CX MID)
  as (bm & Hbin & Hbm & Hbstr & Hbtail & Hbblk & Hbnz).
destruct (cr_state_facts B RLO RHI LAWS HB RELRO_IMG IMG CMD_RO_AT v lyc Sc Wc memc mdc pos CX MID)
  as (_ & _ & _ & _ & _ & _ & HROMc & _).
(* the entry's stack bounds and the offset of the call *)
assert (HSP : alloc_ceiling + CHECK_REPLY_STK <= c_sp v <= 2 ^ 47) by (unfold c_sp in *; lia).
assert (Hsp1 : sp1_of (c_sp v) = c_sp v - 128 - c_sp v mod 32 /\ (c_sp v mod 32 = 0 \/ c_sp v mod 32 = 16)).
{ unfold sp1_of. replace ((c_sp v - 128) mod 32) with (c_sp v mod 32)
    by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. unfold c_sp in *.
  pose proof (Z.mod_pos_bound (spZ (c_regs v)) 32 ltac:(lia)).
  pose proof (Z.div_mod (spZ (c_regs v)) 32 ltac:(lia)). pose proof (Z.div_mod (spZ (c_regs v)) 16 ltac:(lia)). lia. }
destruct Hsp1 as [Hsp1e Hsp1m].
assert (Ho16 : (sp1_of (c_sp v) - c_sp v) mod 16 = 0).
{ replace (sp1_of (c_sp v) - c_sp v) with (-128 - c_sp v mod 32) by (rewrite Hsp1e; lia).
  destruct Hsp1m as [Hm | Hm]; rewrite Hm; reflexivity. }
assert (Hole : sp1_of (c_sp v) - c_sp v <= 0) by lia.
assert (Hoge : -144 <= sp1_of (c_sp v) - c_sp v) by lia.
assert (Hsp1b : 0 <= sp1_of (c_sp v) < 2 ^ 64) by lia.
(* the seed at the call, with the regions dropped: the two instructions write nothing *)
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_STRCMP false CX MID RA Hp4096 Hp16 Hphi Hnr8194)
  as HS0.
pose proof (regs_ok_mid B v lyc pos regs1 RA) as HRO.
assert (HEI : img_env VAL A_LIM (crM regs1 v lyc pos)) by (unfold crM; apply Eimg_env).
remember (crM regs1 v lyc pos) as Ev eqn:HEv.
assert (HS : st_ok_pi SEGS VAL Ev (mkSS CR_STRCMP sr_mid [] None cr_facts_mid)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + CR_STRCMP)) memc (seg_rom SEGS))))
  by (exact (st_ok_pi_submem Ev (ss_mid CR_STRCMP false) _ [] HS0 (submem_nil _) eq_refl)).
clear HS0.
assert (SHOK : sh_ok SEGS crBx (@nil shent) Ev (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof HJ0 as HJ.
unfold cr_at.
(* 0x870d0: the call of the strcmp interceptor *)
paj_run_tok RUN HS HJ SHOK crSpan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdv := dM) in *; clearbody mdv end.
assert (HMEQ : forall x : word, ms_mem ms x = memc x)
  by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a) by (intros a; apply aview_same; exact HMEQ).
clear HF HFr HG.
lazymatch type of HS with
| st_ok _ ?Ew _ _ =>
  assert (HAG : env_agree 64 Ev Ew)
    by (split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | cbn [ed ewset]; reflexivity])
end.
assert (K2 : getr (ms_regs ms) 2 = getr regs1 2)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K3 : getr (ms_regs ms) 3 = getr regs1 3)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K4 : getr (ms_regs ms) 4 = getr regs1 4)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K8 : getr (ms_regs ms) 8 = getr regs1 8)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K9 : getr (ms_regs ms) 9 = getr regs1 9)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K18 : getr (ms_regs ms) 18 = getr regs1 18)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K20 : getr (ms_regs ms) 20 = getr regs1 20)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K22 : getr (ms_regs ms) 22 = getr regs1 22)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K23 : getr (ms_regs ms) 23 = getr regs1 23)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K24 : getr (ms_regs ms) 24 = getr regs1 24)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K25 : getr (ms_regs ms) 25 = getr regs1 25)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K26 : getr (ms_regs ms) 26 = getr regs1 26)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K27 : getr (ms_regs ms) 27 = getr regs1 27)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K10 : getr (ms_regs ms) 10 = getr regs1 10)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (K11 : getr (ms_regs ms) 11 = getr regs1 11)
  by (eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity]).
assert (HspT : spZ (ms_regs ms) = c_sp v + (sp1_of (c_sp v) - c_sp v))
  by (unfold spZ; rewrite K2, R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (proj1 HJ) as HARt.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARt Hfin) as (_ & _ & HFpresT & _).
change (fs_frame_bytes 1) with 128 in HFpresT.
pmkst HS.
prreg HS (1%bv : bv 5) P1.
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the two strings the interceptor compares *)
assert (HRDF : aread_ok SEGS (2 * ESTACK) Wc (ms_regs ms) (ms_mem ms)
  (frame_addr lyc 1 pos + 32) (astr_len (refusal_text (c_code v)) + 1)).
{ rewrite Hrlen. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - apply (aview_some_of_apresent SEGS). exact (proj1 (HFpresT a ltac:(lia))).
    - unfold ascratch_stk. rewrite HspT. lia. }
  split; [exact (amem_range_sub_app (frame_addr lyc 1 pos) 128 (frame_addr lyc 1 pos + 32) (c_nr v + 1) HFapp
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))|].
  split.
  { intros x Hx. exists 0. split.
    - assert (Hd : 4 <= (x - frame_addr lyc 1 pos) / 8 < 8)
        by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
      assert (Hxd : x / 8 = frame_addr lyc 1 pos / 8 + (x - frame_addr lyc 1 pos) / 8).
      { rewrite <- (Z.div_add_l (frame_addr lyc 1 pos / 8) 8 (x - frame_addr lyc 1 pos) ltac:(lia)).
        f_equal. pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)). lia. }
      rewrite (EQV (shadow_of_addr SHADOW_OFF x)). unfold shadow_of_addr. rewrite Hxd.
      replace (SHADOW_OFF + (frame_addr lyc 1 pos / 8 + (x - frame_addr lyc 1 pos) / 8))
        with (SHADOW_OFF + frame_addr lyc 1 pos / 8 + (x - frame_addr lyc 1 pos) / 8) by lia.
      exact (aview_of_val_mem1 SEGS (w_H Wc) memc _ 0 (VSH _ Hd) ltac:(lia)).
    - left. reflexivity. }
  intros _.
  exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv 1 pos (frame_addr lyc 1 pos + 32)
    (c_nr v + 1) HARt Hfin ltac:(lia) ltac:(change (fs_frame_bytes 1) with 128; lia) ltac:(lia)). }
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS Hsegs errno_low (2 * ESTACK) (fun _ => False)
    (SIG CS___interceptor_trampoline_strcmp) Wc (ms_regs ms) (ms_mem ms) CHECK_REPLY_STK (c_sp v) []
    (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc _ 0 (sp1_of (c_sp v) - c_sp v)
    (Z_to_bv 64 (BASE + CR_RET_STRCMP)) _ HJ HspT Ho16 Hole ltac:(lia) ltac:(rewrite HSTK, Hes; lia) P1
    (fun a (Hf : False) => False_ind _ Hf)).
  apply (ASTRCMP fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (c_p v) (frame_addr lyc 1 pos + 32)
    (c_xr v) (refusal_text (c_code v))).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v)
      (c_md v) [(1, pos)] lyc Sc Wc (ms_mem ms) mdv 0 (ms_regs ms) (sp1_of (c_sp v) - c_sp v) HJ HspT Ho16 Hole
      ltac:(rewrite Hes; lia) ltac:(rewrite HSTK, Hes; lia) HraT
      ltac:(rewrite K3; exact R3) ltac:(rewrite K4; exact R4)).
  - rewrite K10. exact Hr10.
  - rewrite K11. exact Hr11.
  - lia.
  - lia.
  - apply (astr_atR_view SEGS).
    apply (astr_atR_agree (rdW Wc memc)); [intros x _; apply EQV | exact Hbstr].
  - apply (astr_atR_view SEGS). split.
    + apply (abytes_atR_agree (rdW Wc memc)); [intros x _; apply EQV | exact HFB].
    + exact Hno0'.
  - apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (c_p v) bm (c_p v)
      (astr_len (c_xr v) + 1) HARt Hbin ltac:(lia) ltac:(unfold astr_len, c_nr in *; lia) ltac:(unfold astr_len; lia)
      ltac:(rewrite HspT; rewrite Hes; lia)).
  - exact HRDF.
  - apply (atail_vis_same Wc memc (ms_mem ms) _ HMEQ). unfold astr_len. exact Hbtail.
  - rewrite Hrlen. intros a Ha.
    pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos + 32 + c_nr v) 8 ltac:(lia)).
    apply (aview_some_of_apresent SEGS). exact (proj1 (HFpresT a ltac:(lia))).
  - exact (rt_rom_view_same B Wc memc (ms_mem ms) HMEQ HROMc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x870d4 with a0 = 0: the strings are equal *)
assert (RAT : cr_regs_at B v lyc pos (ms_regs ms))
  by (apply (cr_regs_at_of_eq v lyc pos regs1 (ms_regs ms) RA); assumption).
assert (RA2 : cr_regs_at B v lyc pos regs2) by (exact (cr_regs_at_pres v lyc pos _ _ RAT HP2)).
assert (MID2 : cr_mid B v lyc Sc Wc mem2 md2 pos).
{ apply (cr_mid_kept v lyc Sc Wc memc mdc pos mem2 md2
    (c_sp v + (sp1_of (c_sp v) - c_sp v) - 2 * ESTACK) (c_sp v + (sp1_of (c_sp v) - c_sp v)) MID HJ2);
  [| rewrite Hes; lia | lia].
  intros a Ha Hnn. rewrite (HK2 a Ha Hnn (fun x : False => x)). apply EQV. }
assert (HZ : getr regs2 10 = Z_to_bv 64 0) by (apply HQ2; rewrite Hxr; reflexivity).
(* 0x870d4: the branch into the epilogue *)
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs2 mem2 md2 pos CR_RET_STRCMP false CX MID2 RA2 Hp4096 Hp16 Hphi
  Hnr8194) as HT0.
pose proof (regs_ok_mid B v lyc pos regs2 RA2) as HRO2.
assert (HEI2 : img_env VAL A_LIM (crM regs2 v lyc pos)) by (unfold crM; apply Eimg_env).
remember (crM regs2 v lyc pos) as Ew eqn:HEw.
assert (HT : st_ok_pi SEGS VAL Ew (mkSS CR_RET_STRCMP (sr_set sr_mid (10%bv : bv 5) (SLit 0)) [] None cr_facts_mid)
  (restrict (w_H Wc) (mkst regs2 (Z_to_bv 64 (BASE + CR_RET_STRCMP)) mem2 (seg_rom SEGS)))).
{ apply (st_ok_pi_pin_reg' Ew (mkSS CR_RET_STRCMP sr_mid [] None cr_facts_mid) _ (10%bv : bv 5) 0).
  - exact (st_ok_pi_submem Ew (ss_mid CR_RET_STRCMP false) _ [] HT0 (submem_nil _) eq_refl).
  - cbn [ms_regs restrict]. exact HZ.
  - reflexivity. }
clear HT0.
assert (SHOK2 : sh_ok SEGS crBx (@nil shent) Ew (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; apply Forall_nil).
paj_run_to_tok RUNTO HT HJ2 SHOK2 crSpan CR_EPI.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdw := dM) in *; clearbody mdw end.
assert (HMEQ2 : forall x : word, ms_mem ms0 x = mem2 x)
  by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
lazymatch type of HT with
| st_ok_pi _ _ ?Ex _ _ =>
  assert (HAG2 : env_agree 64 Ew Ex)
    by (split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | cbn [ed ewset]; reflexivity])
end.
assert (MID3 : cr_mid B v lyc Sc Wc (ms_mem ms0) mdw pos).
{ apply (cr_mid_kept v lyc Sc Wc mem2 md2 pos (ms_mem ms0) mdw alloc_ceiling alloc_ceiling MID2 HJ2);
  [| lia | unfold c_sp in *; lia].
  intros a Ha Hnn. apply aview_same. exact HMEQ2. }
assert (RA3 : cr_regs_at B v lyc pos (ms_regs ms0)).
{ apply (cr_regs_at_of_eq v lyc pos regs2 (ms_regs ms0) RA2);
  (eapply regs_eq_of_sr; [exact HT | exact HRO2 | exact HAG2 | vm_compute; reflexivity | vm_compute; reflexivity]). }
pmkst HT.
exact (EPI v lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdw pos CX MID3 RA3 LS).
Qed.

End e.
End f.
End d.
