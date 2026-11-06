(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_s4.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): B's addresses ("resp %d" at 0x21100). *)
(* Modified by Theorem Labs, 2026-10: segment 4 of check_reply's walk (fuzz_command.asan-ubsan, 0x86e64): the snprintf call
   of the refusal path at 0x870b0, to its return 0x870b4 (cr_s4 : CR_RSNP_stmt at every FP state -> CR_SNP_stmt,
   lib/B/Prog/check_reply_m.v), after lib/B/Prog/check_reply_s5.v (a runtime entry from the mid-walk seed with the
   regions dropped) and the printf call step of a Theorem Labs lane's PASS4-REFIT.md section E.

   0x870b0 jal snprintf(F + 32, 32, "resp %d", code). The contract is a Theorem Labs lane's shared one (RtFormat.v
   asnprintf_realizes = RtPFCmd.v asnprintf_sh: the window CMD_SNP_K = 2 * ESTACK, the read-only words CMD_SNP_CR,
   the format family FR_cmd) at the entry's FP state, whose rounding mode is 0 by the statement's premise. Its post
   is FP-existential: PaFx.v srr_art_postF_of_pf turns it into art_postF, aj_art_own_atF takes the journal step (the
   destination lies in the walk's own side-stack frame) and srr_after_artF continues at the FP state fx1 the wrapper
   returns, where CR_RSNP_stmt is used (check_reply_s4b.v proves it at every FP state). The text is at most 17 bytes,
   so snprintf writes all of it and its NUL into refusal[32] at F + 32. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall PaArt CmdBase CmdRep CmdObj CmdRo CmdZsh
  PaNoChain PaArtOwn PaFx CmdRecBase CmdRecCells CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_reply_k check_reply_m check_reply_sd
  check_reply_t check_reply_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the format "resp %d" at 0x21100, its pieces and the text it writes *)
Definition s4_fmt : list Z := [114; 101; 115; 112; 32; 37; 100].
Definition s4_ps : list PF.pf_piece := [PF.PLit 114; PF.PLit 101; PF.PLit 115; PF.PLit 112; PF.PLit 32; PF.Pd].
Definition s4_text (c : Z) : list Z := [114; 101; 115; 112; 32] ++ PF.pf_dec c.

Lemma s4_parse : PF.pf_parse s4_fmt = Some s4_ps.
Proof. reflexivity. Qed.
Lemma s4_text_ok : forall c, PF.pf_text s4_ps [PF.AInt c] = Some (s4_text c).
Proof. intros c. cbn [PF.pf_text s4_ps option_map]. rewrite app_nil_r. reflexivity. Qed.
Lemma s4_digits_len : forall f x acc, (length (PF.pf_digits f x acc) <= f + length acc)%nat.
Proof.
induction f as [|f IH]; intros x acc; cbn [PF.pf_digits]; [lia|].
destruct (x <? 10); cbn [length]; [lia|].
specialize (IH (x / 10) (48 + x mod 10 :: acc)). cbn [length] in IH. lia.
Qed.
Lemma s4_text_len : forall c, (length (s4_text c) <= 17)%nat.
Proof.
intros c. unfold s4_text. rewrite length_app. cbn [length]. unfold PF.pf_dec.
pose proof (s4_digits_len 11 (- c) []) as H1. pose proof (s4_digits_len 11 c []) as H2. cbn [length] in H1, H2.
destruct (c <? 0); cbn [length]; lia.
Qed.
Lemma s4_refusal_eq : forall c, PF.pf_bytes (s4_text c ++ [0]) = refusal_text c ++ [Z_to_bv 8 0].
Proof. intros c. unfold PF.pf_bytes, refusal_text, s4_text. rewrite map_app. reflexivity. Qed.
Lemma s4_refusal_len : forall c, length (refusal_text c ++ [Z_to_bv 8 0]) = S (length (s4_text c)).
Proof.
intros c. rewrite length_app. cbn [length]. unfold refusal_text, PF.pf_bytes. rewrite length_map.
unfold s4_text. lia.
Qed.
Lemma s4_fmt_ro : PF.pf_bytes s4_fmt ++ [Z_to_bv 8 0] = RO_lit_21100.
Proof. reflexivity. Qed.
Lemma s4_swrap32 : forall z, - 2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
change (2 ^ 32 / 2) with (2 ^ 31). pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma s4_code_range : forall x, - 2 ^ 31 <= reply_code_a x < 2 ^ 31.
Proof.
intros x. unfold reply_code_a, atoi_a. destruct (list_eq_dec Z.eq_dec _ _); [apply s4_swrap32 | lia].
Qed.
Lemma s4_mod32 : forall c, (c mod 2 ^ 64) mod 2 ^ 32 = c mod 2 ^ 32.
Proof.
intros c. symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity].
Qed.
(* the text's values are bytes, so the shared post's values at F + 32 are the bytes refusal_text names *)
Lemma s4_digits_range : forall f x acc, 0 <= x -> Forall (fun z => 0 <= z < 256) acc ->
Forall (fun z => 0 <= z < 256) (PF.pf_digits f x acc).
Proof.
induction f as [|f IH]; intros x acc Hx Hacc; cbn [PF.pf_digits]; [exact Hacc|].
destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. constructor; [lia | exact Hacc].
- apply IH; [apply Z.div_pos; lia|]. constructor; [|exact Hacc]. pose proof (Z.mod_pos_bound x 10 ltac:(lia)). lia.
Qed.
Lemma s4_text_range : forall c, Forall (fun z => 0 <= z < 256) (s4_text c ++ [0]).
Proof.
intros c. apply Forall_app. split; [|constructor; [lia | constructor]].
unfold s4_text. apply Forall_app. split.
- apply Forall_forall. intros z Hz. cbn [In] in Hz. repeat (destruct Hz as [<- | Hz]; [lia|]). destruct Hz.
- unfold PF.pf_dec. destruct (c <? 0) eqn:E.
  + apply Z.ltb_lt in E. constructor; [lia|]. apply s4_digits_range; [lia | constructor].
  + apply Z.ltb_ge in E. apply s4_digits_range; [lia | constructor].
Qed.
Lemma s4_nth_byte : forall (l : list Z) i, Forall (fun z => 0 <= z < 256) l ->
bv_unsigned (nth i (map (Z_to_bv 8) l) (Z_to_bv 8 0)) = nth i l 0.
Proof.
induction l as [|z l IH]; intros i H; [destruct i; reflexivity|].
apply Forall_cons_iff in H as [Hz Hl]. destruct i as [|i]; cbn [nth map]; [|exact (IH i Hl)].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
(* the read-only words of the shared contract lie in the image range 0x10000 .. 0x606000 *)
Lemma s4_cr_img : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) RtPFCmd.cmd_snp_cr_img r Hr) as Hb.
unfold RtPFCmd.in_cmd_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in Hb.
apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
(* a register the symbolic state still names by its mid-walk expression (check_reply_s5.v regs_eq_of_st) *)
Ltac s4_keq HS HRO HAG :=
  eapply regs_eq_of_st; [exact HS | exact HRO | exact HAG | vm_compute; reflexivity | vm_compute; reflexivity].
(* a disjointness of two ranges the walk names, by arithmetic *)
Ltac s4_disj := unfold zdisjoint; cbn [fst snd]; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a memory fact carried to a memory the reader agrees with on the bytes it names *)
Lemma s4_val_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a (n : nat) val,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n val -> val_mem SEGS (mrestrict (w_H W') m') a n val.
Proof.
intros W W' m m' a n val K Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k) (K (a + Z.of_nat k) ltac:(lia))).
exact (Hv k Hk).
Qed.
Lemma s4_bytes_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
abytes_atR (rdW W m) a l -> abytes_atR (rdW W' m') a l.
Proof. intros W W' m m' a l K H i Hi. rewrite (K (a + Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_snprintf) A_SSP_GOT A_SSP_GUARD.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Let RUN := paj_run B LAWS.

(* the reply block's address and size as cr_seed takes them (check_reply_s8.v cr_s8_nums) *)
Lemma s4_nums : forall v, cr_cx B RLO RHI v ->
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
{ unfold c_p. rewrite (aval_mem_mod64 _ _ _ _ HREPV P1). apply Z.mod_small. lia. }
rewrite length_app in P6, P8. cbn [length] in P6, P8. unfold c_nr, LMAX in *. rewrite Ep. lia.
Qed.

(* the mid-walk invariant at a memory that differs from the walk's only inside a window above the heap and below the
   entry's saved registers (the wrapper's scratch window) and inside refusal[32] of the frame (its destination) *)
Lemma s4_mid_kept : forall v lyc Sc Wc memc mdc pos memc' mdc' lo hi,
cr_mid B v lyc Sc Wc memc mdc pos ->
ajournal SEGS B CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  ~ (frame_addr lyc 1 pos + 32 <= a < frame_addr lyc 1 pos + 64) -> rdW Wc memc' a = rdW Wc memc a) ->
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
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as HFoff.
change (fs_frame_bytes 1) with 128 in HFceil, HFapp, HFoff. red in HFoff.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HF8 : frame_addr lyc 1 pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (HF8a : 0 <= frame_addr lyc 1 pos / 8) by (apply Z.div_pos; lia).
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as HFd.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as HFm.
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

Theorem cr_s4 : (forall fx0 : YK11.FPState, CR_RSNP_stmt (fx := fx0) B RLO RHI) -> CR_SNP_stmt B RLO RHI.
Proof.
intros RSNP v lyc Sc Wc regs1 memc mdc pos CX MID RA Hneg R19 R21 R10 R11 R12 R13 LS HFRM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
destruct (s4_nums v CX) as (Hp4096 & Hp16 & Hphi & Hnr).
pose proof CX as (HPRE & Hfr7 & HROD & HGOT & HROK & HROI & HVO & HGRD & H10 & HREC & Hn1 & Hry & Hno0 & Hrepv & Htr
  & Hansv & Hta & Hw8 & Hspw & HWRA & Hww & Hnv & Hn & HN0 & HAOK & HRY & HFL & HERR & HEV & HWHI).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ0 & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HJ0 as (HARc & _ & _ & _ & _ & Hfrs & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
(* the frame: refusal[32] at F + 32, off the image, its shadow bytes 4..7 at 0 *)
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HFal & _ & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HARc Hfin) as HFoff.
change (fs_frame_bytes 1) with 128 in HFceil, HFapp, HFoff. red in HFoff.
assert (HF8m : frame_addr lyc 1 pos mod 8 = 0)
  by (pose proof (Z.div_mod (frame_addr lyc 1 pos) 32 ltac:(lia)) as D; rewrite HFal, Z.add_0_r in D; rewrite D;
      replace (32 * (frame_addr lyc 1 pos / 32)) with ((4 * (frame_addr lyc 1 pos / 32)) * 8) by lia; apply Z_mod_mult).
(* the text: at most 17 bytes, so the written part is all of it and its NUL *)
pose proof (s4_text_len (c_code v)) as HTl.
assert (Hsn : RtPFShared.sn_bytes (32 - 1) (s4_text (c_code v)) = s4_text (c_code v) ++ [0]).
{ unfold RtPFShared.sn_bytes. rewrite firstn_all2; [reflexivity | lia]. }
assert (Hsl : RtPFShared.sn_len (32 - 1) (s4_text (c_code v)) = Z.of_nat (length (s4_text (c_code v))) + 1).
{ unfold RtPFShared.sn_len. rewrite Hsn, length_app. cbn [length]. lia. }
assert (Hwb : 1 <= RtPFShared.sn_len (32 - 1) (s4_text (c_code v)) <= 18) by (rewrite Hsl; lia).
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
(* the seed at the call, with the regions dropped: the jal writes nothing *)
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_SNPRINTF false CX MID RA Hp4096 Hp16 Hphi Hnr)
  as HS0.
pose proof (regs_ok_mid B v lyc pos regs1 RA) as HRO.
assert (HEI : img_env VAL A_LIM (crM regs1 v lyc pos)) by (unfold crM; apply Eimg_env).
remember (crM regs1 v lyc pos) as Ev eqn:HEv.
assert (HS : st_ok_pi SEGS VAL Ev (mkSS CR_SNPRINTF sr_mid [] None cr_facts_mid)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + CR_SNPRINTF)) memc (seg_rom SEGS))))
  by (exact (st_ok_pi_submem Ev (ss_mid CR_SNPRINTF false) _ [] HS0 (submem_nil _) eq_refl)).
clear HS0.
assert (SHOK : sh_ok SEGS crBx (@nil shent) Ev (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof HJ0 as HJ.
unfold cr_at.
(* 0x870b0: the call of the snprintf wrapper *)
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
assert (K2 : getr (ms_regs ms) 2 = getr regs1 2) by (s4_keq HS HRO HAG).
assert (K3 : getr (ms_regs ms) 3 = getr regs1 3) by (s4_keq HS HRO HAG).
assert (K4 : getr (ms_regs ms) 4 = getr regs1 4) by (s4_keq HS HRO HAG).
assert (K8 : getr (ms_regs ms) 8 = getr regs1 8) by (s4_keq HS HRO HAG).
assert (K9 : getr (ms_regs ms) 9 = getr regs1 9) by (s4_keq HS HRO HAG).
assert (K18 : getr (ms_regs ms) 18 = getr regs1 18) by (s4_keq HS HRO HAG).
assert (K19 : getr (ms_regs ms) 19 = getr regs1 19) by (s4_keq HS HRO HAG).
assert (K20 : getr (ms_regs ms) 20 = getr regs1 20) by (s4_keq HS HRO HAG).
assert (K21 : getr (ms_regs ms) 21 = getr regs1 21) by (s4_keq HS HRO HAG).
assert (K22 : getr (ms_regs ms) 22 = getr regs1 22) by (s4_keq HS HRO HAG).
assert (K23 : getr (ms_regs ms) 23 = getr regs1 23) by (s4_keq HS HRO HAG).
assert (K24 : getr (ms_regs ms) 24 = getr regs1 24) by (s4_keq HS HRO HAG).
assert (K25 : getr (ms_regs ms) 25 = getr regs1 25) by (s4_keq HS HRO HAG).
assert (K26 : getr (ms_regs ms) 26 = getr regs1 26) by (s4_keq HS HRO HAG).
assert (K27 : getr (ms_regs ms) 27 = getr regs1 27) by (s4_keq HS HRO HAG).
assert (K10 : getr (ms_regs ms) 10 = getr regs1 10) by (s4_keq HS HRO HAG).
assert (K11 : getr (ms_regs ms) 11 = getr regs1 11) by (s4_keq HS HRO HAG).
assert (K12 : getr (ms_regs ms) 12 = getr regs1 12) by (s4_keq HS HRO HAG).
assert (K13 : getr (ms_regs ms) 13 = getr regs1 13) by (s4_keq HS HRO HAG).
assert (HspT : spZ (ms_regs ms) = c_sp v + (sp1_of (c_sp v) - c_sp v))
  by (unfold spZ; rewrite K2, R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (proj1 HJ) as HARt.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARt Hfin) as (_ & _ & HFpresT & _).
change (fs_frame_bytes 1) with 128 in HFpresT.
pmkst HS.
prreg HS (1%bv : bv 5) P1.
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the facts the contract reads at the call state *)
assert (HROm : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms))).
{ eapply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG B); [exact HJ | intros a _; apply inFP_nil | exact HROD]. }
assert (HROKm : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (CMD_RO_AT _ _ _ _ _ HARt HROm).
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HARt) as (_ & HGRDm & _).
destruct HGRDm as (HG1 & cval & HG2).
assert (HFMT : abytes_atR (rdW Wc (ms_mem ms)) 0x21100 (PF.pf_bytes s4_fmt ++ [Z_to_bv 8 0])).
{ rewrite s4_fmt_ro. destruct HROKm as [HRB _]. unfold cmd_ro_bytes in HRB.
  repeat lazymatch type of HRB with
  | abytes_atR _ 0x21100 _ /\ _ => fail
  | _ /\ _ => apply proj2 in HRB
  end.
  apply proj1 in HRB. exact HRB. }
destruct (ecall_pre_stk_at SEGS B RtPFCmd.CMD_SNP_K CHECK_REPLY_STK (c_sp v) [] (c_ly v) (c_S v) (c_W v) (c_mem v)
  (c_md v) [(1, pos)] lyc Sc Wc (ms_mem ms) mdv 0 (ms_regs ms) (sp1_of (c_sp v) - c_sp v) HJ HspT Ho16 Hole
  ltac:(unfold RtPFCmd.CMD_SNP_K, ESTACK; lia) ltac:(rewrite HSTK; unfold RtPFCmd.CMD_SNP_K, ESTACK; lia) HraT
  ltac:(rewrite K3; exact R3) ltac:(rewrite K4; exact R4)) as (EPRE & ESTK & EPRES).
(* 0x870b0: snprintf(F + 32, 32, "resp %d", code) writes the refusal text into the frame (section E) *)
unfold CR_POST.
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS Hsegs RtPFCmd.CMD_SNP_K
    (fun a => frame_addr lyc 1 pos + 32 <= a < frame_addr lyc 1 pos + 32 + RtPFShared.sn_len (32 - 1) (s4_text (c_code v)))
    (SIGMA CS___interceptor_trampoline_snprintf) Wc (ms_regs ms) (ms_mem ms) CHECK_REPLY_STK (c_sp v) []
    (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc mdv 0 (sp1_of (c_sp v) - c_sp v)
    (Z_to_bv 64 (BASE + CR_RET_SNP)) _ HJ HspT Ho16 Hole ltac:(unfold RtPFCmd.CMD_SNP_K, ESTACK; lia)
    ltac:(rewrite HSTK; unfold RtPFCmd.CMD_SNP_K, ESTACK; lia) P1).
  - intros a Ha. unfold awr_byte. right; right; right; left. exists 1, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
  - apply srr_art_postF_of_pf; [exact EPRES|].
    apply (ASNPRINTF fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (frame_addr lyc 1 pos + 32) 32 0x21100 []
      (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) (s4_text (c_code v)) cval).
    + exact EPRE.
    + exact ESTK.
    + exact EPRES.
    + rewrite K10. exact R10.
    + rewrite K11. exact R11.
    + rewrite K12. exact R12.
    + exact (cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI Wc (ms_mem ms) HROm).
    + apply Forall_forall. intros r Hr. cbv beta. destruct (s4_cr_img r Hr) as (A1 & A2 & A3). lia.
    + apply Forall_forall. intros r Hr. cbv beta. destruct (s4_cr_img r Hr) as (A1 & A2 & A3).
      unfold RtPFShared.snp_out. rewrite HspT. constructor; [s4_disj | constructor; [s4_disj | constructor]].
    + exact HG1.
    + exact HG2.
    + unfold A_SSP_GOT; lia.
    + unfold A_SSP_GOT; lia.
    + unfold A_SSP_GUARD; lia.
    + unfold A_SSP_GUARD; lia.
    + unfold RtPFShared.snp_out. rewrite HspT. unfold A_SSP_GOT.
      constructor; [s4_disj | constructor; [s4_disj | constructor]].
    + unfold RtPFShared.snp_out. rewrite HspT. unfold A_SSP_GUARD.
      constructor; [s4_disj | constructor; [s4_disj | constructor]].
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length]. rewrite HspT. lia.
    + unfold RtPFShared.snp_out. rewrite HspT. cbn [length].
      constructor; [s4_disj | constructor; [s4_disj | constructor]].
    + apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ s4_fmt s4_ps [PF.AInt (c_code v)]).
      * split; [lia|]. split.
        { intros i Hi. cbn [length s4_fmt] in Hi.
          replace (0x21100 + i) with (0x21100 + Z.of_nat (Z.to_nat i)) by lia.
          rewrite (HFMT (Z.to_nat i)) by (cbn [length PF.pf_bytes s4_fmt map app]; lia).
          f_equal. change (PF.pf_bytes s4_fmt ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (s4_fmt ++ [0])).
          apply s4_nth_byte. apply Forall_forall. intros z Hz. cbn [In s4_fmt app] in Hz.
          repeat (destruct Hz as [<- | Hz]; [lia|]). destruct Hz. }
        split.
        { unfold RtPFShared.snp_out. rewrite HspT. cbn [length s4_fmt].
          constructor; [s4_disj | constructor; [s4_disj | constructor]]. }
        split; [unfold amem_range, kLowMemEnd; cbn [length s4_fmt]; lia|].
        split.
        { cbn [length s4_fmt]. eapply (cmd_addressable_chk SEGS B LAWS HB); [exact HARt | vm_compute; reflexivity]. }
        { cbn [length s4_fmt]. eapply (cmd_hull_vis_chk SEGS B LAWS HB); [exact HARt | vm_compute; reflexivity]. }
      * exact s4_parse.
      * cbn [map RtPFCmd.arg_of RtPFShared.pf_args_asan app]. split; [|exact I].
        cbn [RtPFShared.pf_arg_asan]. split; [apply s4_code_range|].
        unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
        rewrite K13, R13. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). apply s4_mod32.
      * exact (s4_text_ok (c_code v)).
      * cbn. exact I.
      * vm_compute; reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold RtPFShared.snp_out. rewrite HspT. cbn [pairwise].
      split; [|split; [constructor | exact I]].
      constructor; [s4_disj | constructor].
    + intros a Ha. split; [apply (apresent_writable SEGS); exact (proj1 (HFpresT a ltac:(lia)))|].
      split; [exact (proj2 (HFpresT a ltac:(lia))) | rewrite HspT; unfold ESTACK; lia].
    + exact (amem_range_sub_app (frame_addr lyc 1 pos) 128 (frame_addr lyc 1 pos + 32)
        (RtPFShared.sn_len (32 - 1) (s4_text (c_code v)) + 8) HFapp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros x Hx. exists 0. split.
      * assert (Hd : 4 <= (x - frame_addr lyc 1 pos) / 8 < 8)
          by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
        assert (Hxd : x / 8 = frame_addr lyc 1 pos / 8 + (x - frame_addr lyc 1 pos) / 8).
        { rewrite <- (Z.div_add_l (frame_addr lyc 1 pos / 8) 8 (x - frame_addr lyc 1 pos) ltac:(lia)).
          f_equal. pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)). lia. }
        rewrite (EQV (shadow_of_addr SHADOW_OFF x)). unfold shadow_of_addr. rewrite Hxd.
        replace (SHADOW_OFF + (frame_addr lyc 1 pos / 8 + (x - frame_addr lyc 1 pos) / 8))
          with (SHADOW_OFF + frame_addr lyc 1 pos / 8 + (x - frame_addr lyc 1 pos) / 8) by lia.
        exact (aview_of_val_mem1 SEGS (w_H Wc) memc _ 0 (VSH _ Hd) ltac:(lia)).
      * left. reflexivity.
    + exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv 1 pos (frame_addr lyc 1 pos + 32)
        (RtPFShared.sn_len (32 - 1) (s4_text (c_code v))) HARt Hfin ltac:(lia)
        ltac:(change (fs_frame_bytes 1) with 128; lia) ltac:(lia)).
    + unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. lia.
    + exact HFRM. }
(* back at 0x870b4 at the FP state fx1 the wrapper returns *)
cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HA0 & HBY) & HK2).
assert (RAT : cr_regs_at B v lyc pos (ms_regs ms))
  by (apply (cr_regs_at_of_eq B v lyc pos regs1 (ms_regs ms) RA); assumption).
assert (RA2 : cr_regs_at B v lyc pos regs2) by exact (cr_regs_at_pres B v lyc pos _ _ RAT HP2).
assert (MID2 : cr_mid B v lyc Sc Wc mem2 md2 pos).
{ apply (s4_mid_kept v lyc Sc Wc memc mdc pos mem2 md2
    (c_sp v + (sp1_of (c_sp v) - c_sp v) - RtPFCmd.CMD_SNP_K) (c_sp v + (sp1_of (c_sp v) - c_sp v)) MID HJ2);
  [| unfold RtPFCmd.CMD_SNP_K, ESTACK; lia | lia].
  intros a Ha Hnn Hnf. rewrite (HK2 a Ha Hnn ltac:(lia)). apply EQV. }
(* the refusal text the wrapper wrote at F + 32 *)
assert (HTXT : abytes_atR (rdW Wc mem2) (frame_addr lyc 1 pos + 32) (refusal_text (c_code v) ++ [Z_to_bv 8 0])).
{ rewrite <- s4_refusal_eq. intros i Hi. unfold PF.pf_bytes in Hi |- *. rewrite length_map, length_app in Hi.
  cbn [length] in Hi.
  rewrite (HBY (Z.of_nat i)) by (rewrite Hsl; lia).
  rewrite Hsn, Nat2Z.id. f_equal. symmetry. apply s4_nth_byte. apply s4_text_range. }
assert (N19 : getr regs2 19 = w64 (frame_addr lyc 1 pos + 32)).
{ transitivity (getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia))|]. rewrite K19. exact R19. }
assert (N21 : getr regs2 21 = w64 (c_code v)).
{ transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia))|]. rewrite K21. exact R21. }
exact (RSNP fx1 v lyc Sc Wc regs2 mem2 md2 pos CX MID2 RA2 Hneg N19 N21 HTXT LS).
Qed.
End e.
End f.
End d.
