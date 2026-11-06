(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the member loop of sup_chain's ASan walk (plugin-hostd/fuzz_command,
   0x8c2b4): from the loop-skip test (0x8c3c4) through the per-member sprintf loop to the loop exit (0x8c438),
   in the continuation style of lib/A/Prog/sup_chain.v's sc_segA_table and lib/A/Prog/check_reply_s4.v's
   step through a runtime entry that writes a live block (s4_art_own). *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4, 4b and 5:
   the sprintf wrapper's contract is the shared RtPFCmd.asprintf_sh taken at every FP state
   and its post is FP-existential, so each pass returns at some fx1 with fxrel fxk fx1; scl_pass, sc_loop_body and
   scl_loop_from take the FP state of the pass explicitly, and sc_loop's continuation takes the FP state at the exit;
   PaFx.v's st_ok_restrict_xfx takes the call site's symbolic state to the FP state each pass returns. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaArt
PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFCmd RtPFShared RtPFSx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c xstrdup_c rec_shape_of_c answer_c sup_chain_c RecBLemmas sup_chain_s1 sup_chain_s2
sup_chain_s3 sup_chain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.printf_facts_c.

(* the offsets of the loop's boundaries (MEASURED: the disassembly of sup_chain) *)
Definition SCL_LOOP : Z := AF_sup_chain + 0x110. (* blez s1,8c438 (0x8c3c4): the loop-skip test *)
Definition SCL_HEAD : Z := AF_sup_chain + 0x130. (* mv a1,s11 (0x8c3e4): the body head *)
Definition SCL_CHK  : Z := AF_sup_chain + 0x13c. (* srli a0,s5,3 (0x8c3f0): the member-load shadow check *)
Definition SCL_RET  : Z := AF_sup_chain + 0x158. (* add s9,s9,a0 (0x8c40c): the return from the sprintf wrapper *)
Definition SCL_EXIT : Z := AF_sup_chain + 0x184. (* lb a0,0(s7) (0x8c438): the loop exit (S' guard) *)

(* the format member k is printed with: "%d" (.str.16 0x21f00) for k = 0, " %d" (.str.15 0x21ee0) otherwise *)
Definition scl_fmtv (k : nat) : Z := if Nat.eqb k 0 then 0x21f00 else 0x21ee0.
Definition scl_fmt (k : nat) : list Z := if Nat.eqb k 0 then sc_fmt0 else sc_fmt1.

(* --- the text and the format as the shared contract states them (bytes as Z) -------------------------------- *)
Lemma scl_digits_range : forall f x acc, 0 <= x -> Forall (fun c => 0 <= c < 256) acc ->
Forall (fun c => 0 <= c < 256) (PF.pf_digits f x acc).
Proof.
induction f as [|f IH]; intros x acc Hx Hacc; cbn [PF.pf_digits]; [exact Hacc|].
destruct (Z.ltb_spec x 10) as [H|H].
- apply Forall_cons; [lia | exact Hacc].
- apply IH; [apply Z.div_pos; lia|]. apply Forall_cons; [|exact Hacc].
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)). lia.
Qed.

Lemma scl_dec_range : forall v, Forall (fun c => 0 <= c < 256) (PF.pf_dec v).
Proof.
intros v. unfold PF.pf_dec. destruct (Z.ltb_spec v 0) as [H|H].
- apply Forall_cons; [lia|]. apply scl_digits_range; [lia | apply Forall_nil].
- apply scl_digits_range; [lia | apply Forall_nil].
Qed.

(* the text of member k is bytes, and the format has no %.*s (the family's precision clause) *)
Lemma scl_text_facts : forall (k : nat) vk ps T,
PF.pf_parse (scl_fmt k) = Some ps -> PF.pf_text ps [PF.AInt vk] = Some T ->
Forall (fun c => 0 <= c < 256) T /\
RtPFShared.pf_prec_pos (map RtPFCmd.piece_of ps) (map RtPFCmd.arg_of [PF.AInt vk]).
Proof.
intros k vk ps T Hp Ht. unfold scl_fmt in Hp. destruct (Nat.eqb k 0).
- rewrite sc_fmt0_parse in Hp. injection Hp as <-. rewrite sc_fmt0_text in Ht. injection Ht as <-.
  split; [apply scl_dec_range | exact I].
- rewrite sc_fmt1_parse in Hp. injection Hp as <-. rewrite sc_fmt1_text in Ht. injection Ht as <-.
  split; [apply Forall_cons; [lia | apply scl_dec_range] | exact I].
Qed.

Lemma scl_nth_range : forall (l : list Z) j, Forall (fun c => 0 <= c < 256) l -> 0 <= nth j l 0 < 256.
Proof.
intros l j H. destruct (Nat.lt_ge_cases j (length l)) as [Hj|Hj].
- rewrite Forall_forall in H. apply H. apply nth_In. exact Hj.
- rewrite nth_overflow by exact Hj. lia.
Qed.

Lemma scl_byteZ : forall (l : list Z) j, Forall (fun c => 0 <= c < 256) l ->
bv_unsigned (nth j (PF.pf_bytes l) (Z_to_bv 8 0)) = nth j l 0.
Proof.
intros l j H. unfold PF.pf_bytes. rewrite map_nth, Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. exact (scl_nth_range l j H).
Qed.

Lemma scl_app0_range : forall (l : list Z), Forall (fun c => 0 <= c < 256) l ->
Forall (fun c => 0 <= c < 256) (l ++ [0]).
Proof. intros l H. apply Forall_app. split; [exact H | apply Forall_cons; [lia | apply Forall_nil]]. Qed.

(* the shared post's bytes at the destination, as the loop's invariant states its text *)
Lemma scl_bytes_of_Z : forall (rd : reader) d (T : list Z), Forall (fun c => 0 <= c < 256) T ->
(forall i, 0 <= i < Z.of_nat (length T) + 1 -> rd (d + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)) ->
abytes_atR rd d (PF.pf_bytes (T ++ [0])).
Proof.
intros rd d T HT H j Hj. unfold PF.pf_bytes in Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
rewrite (scl_byteZ (T ++ [0]) j (scl_app0_range T HT)).
rewrite (H (Z.of_nat j)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* the image's bytes of a format literal, as the shared contract's fmt_at states them *)
Lemma scl_Z_of_bytes : forall (rd : reader) f (s : list Z), Forall (fun c => 0 <= c < 256) s ->
abytes_atR rd f (PF.pf_bytes s ++ [Z_to_bv 8 0]) ->
forall i, 0 <= i <= Z.of_nat (length s) -> rd (f + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0).
Proof.
intros rd f s Hs H i Hi.
assert (HE : PF.pf_bytes s ++ [Z_to_bv 8 0] = PF.pf_bytes (s ++ [0]))
  by (unfold PF.pf_bytes; rewrite map_app; reflexivity).
rewrite HE in H.
pose proof (H (Z.to_nat i)) as Hb. rewrite Z2Nat.id in Hb by lia.
rewrite Hb by (unfold PF.pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
rewrite (scl_byteZ (s ++ [0]) (Z.to_nat i) (scl_app0_range s Hs)). reflexivity.
Qed.

(* the sprintf argument in a2 *)
Lemma scl_argZ2 : forall regs : bvmap 5 word, argZ regs 2 = bv_unsigned (getr regs 12).
Proof.
intros regs. unfold argZ. assert (E : Z_to_bv 5 (10 + 2) = (12%bv : bv 5)) by (apply bv_eq; reflexivity).
rewrite E. reflexivity.
Qed.

(* --- the disjointness premises of the shared contract --------------------------------------------------------
   A range that ends at or below the image's start or starts at or above its end (0x10000 .. 0x606000). The text
   block is such a range (scl_blk_off_img); every read-only range the contract names lies inside the image, and the
   wrapper's stack window lies above alloc_ceiling. *)
Definition scl_off_img (d w : Z) : Prop := d + w <= 0x10000 \/ 0x606000 <= d.

Lemma scl_img_disj : forall K sp d w lst nb f n,
scl_off_img lst nb -> lst <= d -> d + w <= lst + nb -> 0x606000 <= sp - K -> 0 <= K ->
0x10000 <= f -> f + n <= 0x606000 -> 0 <= n ->
Forall (zdisjoint (f, n)) (RtPFShared.snp_out K sp d w).
Proof.
intros K sp d w lst nb f n Ho Hd Hw Hs HK Hf Hfn Hn. unfold RtPFShared.snp_out.
apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
apply Forall_cons; [|apply Forall_nil].
unfold zdisjoint, scl_off_img in *; cbn [fst snd]. destruct Ho as [Ho | Ho]; lia.
Qed.

Lemma scl_dog : forall d w lst nb, scl_off_img lst nb -> lst <= d -> d + w <= lst + nb ->
zdisjoint (d, w) (RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI - RtPFCmd.CMD_IMG_LO).
Proof.
intros d w lst nb Ho Hd Hw. unfold zdisjoint, scl_off_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in *.
cbn [fst snd]. destruct Ho as [Ho | Ho]; lia.
Qed.

Lemma scl_sp_side : forall K sp d w lst nb, lst <= d -> d + w <= lst + nb -> lst + nb <= sp - K -> 0 <= K ->
Forall (zdisjoint (sp, 8 * Z.of_nat (length (@nil Z)))) (RtPFShared.snp_out K sp d w) /\
pairwise zdisjoint (RtPFShared.snp_out K sp d w).
Proof.
intros K sp d w lst nb Hd Hw Hs HK. unfold RtPFShared.snp_out. cbn [length Z.of_nat]. split.
- apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
Qed.

Lemma scl_cr_ok : forall K sp d w lst nb, scl_off_img lst nb -> lst <= d -> d + w <= lst + nb ->
0x606000 <= sp - K -> 0 <= K ->
Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) RtPFCmd.CMD_SP_CR /\
Forall (fun r => Forall (zdisjoint r) (RtPFShared.snp_out K sp d w)) RtPFCmd.CMD_SP_CR.
Proof.
intros K sp d w lst nb Ho Hd Hw Hs HK.
assert (HB : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0x606000 /\ 0 <= snd r) RtPFCmd.CMD_SP_CR).
{ unfold RtPFCmd.CMD_SP_CR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
rewrite Forall_forall in HB. split; rewrite Forall_forall; intros [f n] Hr; destruct (HB (f, n) Hr) as (H1 & H2 & H3);
cbn [fst snd] in *; [lia|].
exact (scl_img_disj K sp d w lst nb f n Ho Hd Hw Hs HK H1 H2 H3).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* le_byte of a 32-bit word ignores bits above bit 32 *)
Lemma scl_lebyte : forall v j, le_byte (v mod 2 ^ 64) 4 j = le_byte (v mod 2 ^ 32) 4 j.
Proof.
intros v j. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
assert (H64 : (v mod 2 ^ 64) mod 2 ^ 32 = v mod 2 ^ 32).
{ symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]. }
assert (H32 : (v mod 2 ^ 32) mod 2 ^ 32 = v mod 2 ^ 32) by (apply Z.mod_mod; lia).
rewrite H64, H32. reflexivity.
Qed.

(* the j-th byte (j < 4) of a member's little-endian word *)
Lemma scl_byte_eq : forall v j, (j < 4)%nat ->
bv_unsigned (nth j (le32 v) (Z_to_bv 8 0)) = le_byte (v mod 2 ^ 32) 4 j.
Proof.
intros v j Hj.
assert (Hv' : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (Heq : Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
pose proof (word_to_le_bytes_nth 4 (v mod 2 ^ 64) j Hj Hv') as Hn. rewrite Heq in Hn.
assert (Hwe : word_to_le_bytes 4 (Z_to_bv 64 v) = le32 v) by reflexivity.
rewrite Hwe in Hn.
remember (le32 v) as L eqn:HL.
assert (Hlen : length L = 4%nat) by (rewrite HL; unfold le32, le4; apply length_Z_to_le_bytes).
assert (HH : nth_error L j = Some (nth j L (Z_to_bv 8 0)))
  by (apply nth_error_nth'; rewrite Hlen; lia).
rewrite Hn in HH. injection HH as HH. rewrite <- HH.
rewrite Z_to_bv_unsigned. unfold bv_wrap. unfold YO0f.le_byte, le_byte.
change (bv_modulus 8) with 256. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
assert (H64 : (v mod 2 ^ 64) mod 2 ^ 32 = v mod 2 ^ 32)
  by (symmetry; apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]).
assert (H32 : (v mod 2 ^ 32) mod 2 ^ 32 = v mod 2 ^ 32) by (apply Z.mod_mod; lia).
rewrite H64, H32. apply Z.mod_mod. lia.
Qed.

(* the member word's value as the 32-bit load sees it, bridged from the member array's bytes *)
Lemma scl_member : forall (W : world SEGS) mem pids ids k v,
abytes_atR (rdW W mem) pids (concat (map le32 ids)) ->
nth_error ids k = Some v ->
aval_mem (rdW W mem) (pids + 4 * Z.of_nat k) 4 (v mod 2 ^ 32).
Proof.
intros W mem pids ids. revert pids.
induction ids as [|x ids IH]; intros pids k v HB0 E; [destruct k; cbn in E; discriminate|].
cbn [map concat] in HB0.
assert (L4 : length (le32 x) = 4%nat) by (unfold le32, le4; apply length_Z_to_le_bytes).
destruct k as [|k]; cbn [nth_error] in E.
- injection E as <-. replace (pids + 4 * Z.of_nat 0) with pids by lia.
  intros j Hj. replace (pids + Z.of_nat j) with (pids + Z.of_nat (j + 0)) by (f_equal; lia).
  rewrite (HB0 (j + 0)%nat) by (rewrite length_app, L4; lia).
  rewrite app_nth1 by (rewrite L4; lia). replace (j + 0)%nat with j by lia.
  rewrite (scl_byte_eq x j Hj). reflexivity.
- assert (HB1 : abytes_atR (rdW W mem) (pids + 4) (concat (map le32 ids))).
  { intros i Hi. replace (pids + 4 + Z.of_nat i) with (pids + Z.of_nat (4 + i)) by lia.
    rewrite (HB0 (4 + i)%nat) by (rewrite length_app, L4; cbn [length] in *; lia).
    rewrite app_nth2 by (rewrite L4; lia). rewrite L4. replace (4 + i - 4)%nat with i by lia. reflexivity. }
  replace (pids + 4 * Z.of_nat (S k)) with ((pids + 4) + 4 * Z.of_nat k) by lia.
  exact (IH (pids + 4) k v HB1 E).
Qed.

(* the member array's bytes: four per member *)
Lemma scl_concat_len : forall l : list Z, length (concat (map le32 l)) = (4 * length l)%nat.
Proof.
induction l as [|x l IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, IH.
assert (L4 : length (le32 x) = 4%nat) by (unfold le32, le4; apply length_Z_to_le_bytes).
rewrite L4. cbn [length]. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis VOBJS : cmd_val_objs.
(* the sprintf wrapper's contract at every FP state: the statement's own hypothesis (sup_chain_c.v:87), the shared
   RtPFCmd.asprintf_sh *)
Hypothesis ASPRINTF : forall fx0 : YK11.FPState,
@asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa7098 0x6045d8.
(* read-only facts (the recorder walks' shared forms): cmd_ro_ok from arodata at a state of the walk, and a read-only
   byte is an image byte *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
(* the stack-protector cells the sprintf body reads (the recorder walks' shared hypothesis cmd_rec_cells) *)
Hypothesis cmd_rec_cells : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
rdW W mem A_FLAG_REPLACE_STR = Some 1 /\ aguard_ok SEGS W mem 0xa7098 0x6045d8 /\
exists ev, rd32 (rdW W mem) (as_errno B) ev.
(* the two format literals are not covered by the record's zero-shadow table (lib/A/AF0m.v Tfib_zero_shadow
   jumps 0x21ec0 -> 0x21f40); their granules are partial, so addressability and the shadow hull are carried as
   the canonical named Section hypotheses of the recorder walks, to be discharged by CmdRecFacts'
   cmd_addressable_chk from the const shadow cells 0x7fffc3dc / 0x7fffc3e0 (AF0m.v) *)
Hypothesis ZSH_lit_21ee0 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21ee0 4.
Hypothesis ZSH_lit_21f00 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21f00 3.
Hypothesis HULL_lit_21ee0 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21ee0 4.
Hypothesis HULL_lit_21f00 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21f00 3.
(* the allocator record and the image facts (CmdRecImg.v): the read-only bytes the sprintf body reads (the shared
   contract's rt_rom_view) come from arodata_okP by cmd_consts_view_sp; the closing file discharges IMG with
   cmd_img_facts_tfib B HB *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ============================================================================================================
   The call step: the sprintf wrapper writes a window of the list text block, so the journal stays put and the
   memory changes only in its scratch window and the written window, and the wrapper returns at some FP state fx1
   with fxrel fxk fx1.  The shape is PaFx.v's aj_art_own_atF, with the write set taken by the journal's awr_byte
   (check_reply_s4.v's s4_art_own); here every byte of the write set is a byte of the text block, which the
   section's HWR gives as awr_byte. *)
Lemma scl_art_blkF : forall (fxk : YK11.FPState) stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own
lyc Sc mdc k (o : Z) raw (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
(forall a, Eb a -> awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a) ->
SRr SEGS W (@cfg_at fxk SEGS pc regsT memT mdc) (art_postF (fx := fxk) SEGS B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr SEGS W (mkCfg (@mkst fxk regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fxk fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros fxk stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr
HJ Hsp Hneg Hstk Hbud Hraw HEb HC.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (fx1 & Hfx & -> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists fx1, regs2, mem2, md2. split; [exact Hfx|].
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => ascratch_stk stk regsT a \/ Eb a) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; unfold awr_byte.
    + left. unfold ascratch_stk in Ha. rewrite Hsp in Ha. lia.
    + exact (HEb a Ha).
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [unfold ascratch_stk; rewrite Hsp; exact Hw | exact He].
Qed.

(* ------------------------------------------------------------------------------------------------------
   The symbolic seeds of the loop.  Every point of the loop has the 32 register atoms; the member word the
   body loads is atom 32 (the region based on s2 = atom 18); the shadow base is s6 = atom 22, so Bx is the
   register atom itself.  The facts the token machinery needs: s5 (atom 21) in [0, alloc_ceiling] - the
   member array is in a live block or a side-stack frame, both below the ceiling - and s6 pinned to SB. *)
Definition scl_memreg : YP09.region :=
YP09.mkRegion (Some 18%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition scl_facts : facts := mkFacts [(21%nat, mkAF 0 140737488355324 0); (22%nat, mkAF SB SB 0)] [] [].
Definition scl_facts0 : facts := mkFacts [(22%nat, mkAF SB SB 0)] [] [].
Definition scl_Bx : sv := SOff 22 0.
Definition scl_SH : list shent := [].
Definition scl_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None scl_facts.
Definition scl_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None scl_facts0.
Definition scl_xs (vk : Z) : list word := [Z_to_bv 64 vk].
Definition scl_E (regs : bvmap 5 word) (vk : Z) : env := Eimg (Ereg regs (scl_xs vk)).

Lemma scl_E_reg : forall regs vk m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (scl_E regs vk) m = getr regs r.
Proof.
intros regs vk m r Hm. pose proof (bv_unsigned_in_range 5 r) as Hr5.
change (bv_modulus 5) with 32 in Hr5.
unfold scl_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.

Lemma scl_E_vk : forall regs vk, ew (scl_E regs vk) 32 = Z_to_bv 64 vk.
Proof.
intros regs vk. unfold scl_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs (scl_xs vk) 0).
Qed.

Lemma scl_E_img : forall regs vk, img_env VAL A_LIM (scl_E regs vk).
Proof. intros regs vk. unfold scl_E. apply Eimg_env. Qed.

Lemma scl_E_agree : forall regs vk, env_agree 32 (Ereg regs (scl_xs vk)) (scl_E regs vk).
Proof.
intros regs vk. split; [|reflexivity].
intros n Hn. unfold scl_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.

(* a field read, carried to a memory the reader agrees with on the bytes it names (check_reply_s4 s4_val_keep) *)
Lemma scl_val_keep : forall (W : world SEGS) (m m' : word -> option byte) a (n : nat) val,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n val -> val_mem SEGS (mrestrict (w_H W) m') a n val.
Proof.
intros W m m' a n val K Hv i Hi.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat i) (K (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.

(* the saved-register frame, carried the same way *)
Lemma scl_frame_keep : forall (W : world SEGS) (m m' : word -> option byte) sp regs,
(forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
112 <= sp -> sp <= 2 ^ 47 ->
sc_frame_at (mrestrict (w_H W) m) sp regs -> sc_frame_at (mrestrict (w_H W) m') sp regs.
Proof.
intros W m m' sp regs K Hlo Hhi HF j r Hj.
pose proof (sc_saved_range j r Hj) as _.
assert (Hj13 : (j < 13)%nat).
{ assert (HL : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length sc_saved) with 13%nat in HL. exact HL. }
apply (scl_val_keep W m m' (sp - 8 - 8 * Z.of_nat j) 8 _ ); [|exact (HF j r Hj)].
intros x Hx. apply K. cbn [Z.of_nat] in Hx. lia.
Qed.

(* the seed at a point with no memory region (the loop prologue, the body head, the wrapper's return), at any FP
   state fxk *)
Lemma scl_seed_nomem : forall (fxk : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem vk pc,
getr regs 22 = w64 SB ->
st_ok_pi (fx := fxk) SEGS VAL (scl_E regs vk) (scl_ss0 pc)
  (restrict (w_H W) (@mkst fxk regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scl_Bx scl_SH (scl_E regs vk) (mrestrict (w_H W) mem).
Proof.
intros fxk W regs mem vk pc H22.
set (E := scl_E regs vk).

assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (unfold E; rewrite (scl_E_reg regs vk 22%nat 22%bv eq_refl); exact H22).
split; [| unfold sh_ok, scl_SH; apply Forall_nil].
rewrite (restrict_mkst_fx (fx := fxk)). unfold scl_ss0. apply (pa_entry_st_ok_full (fx := fxk)).
- unfold E, scl_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold scl_facts0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E22, unsigned_lit_small by (unfold SB; lia).
  rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SB; lia].
Qed.

(* the seed at the member-load check: the member word's region is live *)
Lemma scl_seed_chk : forall (fxk : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem vk pc q,
getr regs 22 = w64 SB -> 0 <= q <= 140737488355324 -> getr regs 21 = w64 q ->
getr regs 18 = w64 q -> 0 <= vk < 2 ^ 32 ->
aval_mem (rdW W mem) q 4 vk ->
st_ok_pi (fx := fxk) SEGS VAL (scl_E regs vk) (scl_ss pc [scl_memreg])
  (restrict (w_H W) (@mkst fxk regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scl_Bx scl_SH (scl_E regs vk) (mrestrict (w_H W) mem).
Proof.
intros fxk W regs mem vk pc q H22 Hq H21 H18 Hvk HV.
set (E := scl_E regs vk).
assert (E18 : ew E 18 = Z_to_bv 64 q)
  by (unfold E; rewrite (scl_E_reg regs vk 18%nat 18%bv eq_refl); exact H18).
assert (E21 : ew E 21 = Z_to_bv 64 q)
  by (unfold E; rewrite (scl_E_reg regs vk 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (unfold E; rewrite (scl_E_reg regs vk 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 vk) by (unfold E; exact (scl_E_vk regs vk)).
assert (Hbq : base_val E (Some 18%nat) = q)
  by (cbn [base_val]; rewrite E18; apply unsigned_lit_small; lia).
split; [| unfold sh_ok, scl_SH; apply Forall_nil].
rewrite (restrict_mkst_fx (fx := fxk)). unfold scl_ss. apply (pa_entry_st_ok_full (fx := fxk)).
- unfold E, scl_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, scl_memreg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Hbq. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ q 0 4 (SOff 32 0) vk).
  + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  + cbn. lia.
  + rewrite Z.add_0_r. change (N.to_nat 4) with 4%nat.
    exact (val_mem_view SEGS (w_H W) mem q 4%nat vk HV).
- apply pairwise_disjoint_of_extents.
  unfold scl_memreg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- unfold scl_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E21, E22, !unsigned_lit_small by (unfold SB; lia).
  rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SB; lia].
Qed.

(* --- what a call keeps -------------------------------------------------------------------------------------
   The sprintf wrapper writes its scratch window (inside this walk's stack window) and the bytes of the list
   text block.  Every fact the loop carries about the image, the member array and the frame names bytes outside
   both, so each is carried by one agreement lemma. *)

(* a read-only byte of the image is neither a byte of a live block nor a byte of the stack window *)
Lemma scl_ro_apart : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> in_roP SEGS RLO RHI a ->
0 <= a < kLowMemEnd /\ (forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
Proof.
intros ly S W mem md a HAR Hro.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hgot]; [exists sg; split; [exact Hsg | exact Hr] | exact (RELRO_IMG a Hgot)]).
split; [exact (pa_segs_low a Himg)|].
intros p n Hin Hr.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
  (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hr))))) Himg).
Qed.

(* the read-only image is kept by a step that changes only the stack window and a live block *)
Lemma scl_aro_keep : forall ly S (W : world SEGS) (m m' : word -> option byte) md p n lo hi,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> kLowMemEnd <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (p <= a < p + req_size n) -> rdW W m' a = rdW W m a) ->
arodata_okP SEGS RLO RHI B (rdW W m) -> arodata_okP SEGS RLO RHI B (rdW W m').
Proof.
intros ly S W m m' md p n lo hi HAR Hin Hlo HK HRO a Hro Ho He.
destruct (scl_ro_apart ly S W m md a HAR Hro) as [Hlow Hblk].
unfold kLowMemEnd in Hlow, Hlo.
rewrite (HK a ltac:(lia) ltac:(lia) (Hblk p n Hin)). exact (HRO a Hro Ho He).
Qed.

(* a live block is apart from the image's range: its bytes are not in the layout's image region (AR_client_img_law),
   which covers 0x10000 .. 0x606000 (pa_img_cover) *)
Lemma scl_blk_off_img : forall ly S (W : world SEGS) mem md p n,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < req_size n -> scl_off_img p (req_size n).
Proof.
intros ly S W mem md p n HAR Hin Hn.
pose proof HAR as (_ & LG & _).
destruct (pa_img_cover ly S md LG) as [C1 C2].
unfold scl_off_img.
destruct (Z_le_gt_dec (p + req_size n) 0x10000) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec 0x606000 p) as [H2 | H2]; [right; exact H2|].
assert (Hm : p <= Z.max p 0x10000 < p + req_size n) by lia.
exfalso. apply (proj1 (al_client_img _ _ LAWS ly S W mem md (Z.max p 0x10000) HAR
  (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hm)))))).
unfold in_zr. lia.
Qed.

(* a shadow byte of an application address is no byte of a live block: the shadow band lies between the two
   application bands (in_app) *)
Lemma scl_shadow_apart : forall ly S (W : world SEGS) mem md p n x,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= x < kHighMemEnd ->
~ (p <= shadow_of_addr SHADOW_OFF x < p + req_size n).
Proof.
intros ly S W mem md p n x HAR Hin Hx Hr.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
unfold shadow_of_addr, SHADOW_OFF in Hr.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Hd0.
pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(unfold kHighMemEnd in Hx; lia)) as Hd1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
Qed.

(* the read-only image at a memory that agrees with this one everywhere *)
Lemma scl_aro_move : forall (W : world SEGS) (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a) ->
arodata_okP SEGS RLO RHI B (rdW W m) -> arodata_okP SEGS RLO RHI B (rdW W m').
Proof.
intros W m m' HK HRO a Hro Ho He.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hgot];
      [exists sg; split; [exact Hsg | exact Hr] | exact (RELRO_IMG a Hgot)]).
pose proof (pa_segs_low a Himg) as Hb. unfold kLowMemEnd in Hb.
rewrite (HK a ltac:(lia)). exact (HRO a Hro Ho He).
Qed.

(* the two bit-vector facts the call's registers need: the address the walk adds, and the member word the
   32-bit load sign-extends *)
Lemma scl_add64 : forall x y, alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros x y. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma scl_swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma scl_lw_mod : forall w,
bv_unsigned (sext 64 (bv_extract 0 32 (Z_to_bv 64 w))) mod 2 ^ 32 = w mod 2 ^ 32.
Proof.
intros w. assert (H64 : forall c, (c mod 2 ^ 64) mod 2 ^ 32 = c mod 2 ^ 32)
  by (intros c; symmetry; apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]).
rewrite b_lw_val. unfold v_lw. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite H64, scl_swrap32_mod, Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact (H64 w).
Qed.

(* --- the format the wrapper reads ---------------------------------------------------------------------------
   Each pass prints with one of the two read-only literals.  The shared contract asks of its format argument the
   string's bytes, that the regions the call writes miss it, and its range and shadow; the bytes come from
   cmd_ro_ok, the shadow from the two named shadow hypotheses of the literals. *)
Lemma scl_fmt_at : forall ly S (W : world SEGS) mem md (k : nat) rs,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) ->
Forall (zdisjoint (scl_fmtv k, Z.of_nat (length (scl_fmt k)) + 1)) rs ->
RtPFShared.fmt_at (rdW W mem) rs (scl_fmtv k) (scl_fmt k).
Proof.
intros ly S W mem md k rs HAR HRO Hrs.
destruct (cmd_ro_ok_of_aro ly S W mem md HAR HRO) as [HBY _].
unfold cmd_ro_bytes in HBY.
assert (HF1 : abytes_atR (rdW W mem) 0x21ee0 RO_lit_21ee0).
{ pose proof HBY as H.
  repeat lazymatch type of H with
  | abytes_atR _ 0x21ee0 _ /\ _ => fail
  | _ /\ _ => apply proj2 in H
  end. exact (proj1 H). }
assert (HF0 : abytes_atR (rdW W mem) 0x21f00 RO_lit_21f00).
{ pose proof HBY as H.
  repeat lazymatch type of H with
  | abytes_atR _ 0x21f00 _ /\ _ => fail
  | _ /\ _ => apply proj2 in H
  end. exact (proj1 H). }
clear HBY. revert Hrs. unfold scl_fmt, scl_fmtv. destruct (Nat.eqb k 0); intros Hrs.
- assert (HR : Forall (fun c => 0 <= c < 256) sc_fmt0)
    by (unfold sc_fmt0; repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  split; [lia|].
  split; [apply (scl_Z_of_bytes (rdW W mem) 0x21f00 sc_fmt0 HR); rewrite sc_fmt0_bytes; exact HF0|].
  split; [exact Hrs|]. split; [unfold amem_range, kLowMemEnd; left; cbn [length sc_fmt0]; lia|].
  split; [cbn [length sc_fmt0]; exact (ZSH_lit_21f00 ly S W mem md HAR)|].
  cbn [length sc_fmt0]. exact (HULL_lit_21f00 ly S W mem md HAR).
- assert (HR : Forall (fun c => 0 <= c < 256) sc_fmt1)
    by (unfold sc_fmt1; repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  split; [lia|].
  split; [apply (scl_Z_of_bytes (rdW W mem) 0x21ee0 sc_fmt1 HR); rewrite sc_fmt1_bytes; exact HF1|].
  split; [exact Hrs|]. split; [unfold amem_range, kLowMemEnd; left; cbn [length sc_fmt1]; lia|].
  split; [cbn [length sc_fmt1]; exact (ZSH_lit_21ee0 ly S W mem md HAR)|].
  cbn [length sc_fmt1]. exact (HULL_lit_21ee0 ly S W mem md HAR).
Qed.

(* ============================================================================================================
   The member loop.  Its fixed data: the function's entry journal state (ly S W0 mem0 md0 own FP STK sp0), the
   state at the loop (lyL SL WL, journal count kL), the member array (pids, ids), the list text block (lst, of
   12n + 1 bytes), and the registers the walk keeps (the slot c, the entry registers regs0 in the frame). *)
Section loop.
Variables STK sp0 : Z.
Variable FP : list (Z * Z).
Variables ly lyL : alayout.
Variables SE SL : astate.
Variables W0 WL : world SEGS.
Variables mem0 memL : word -> option byte.
Variable md0 : Model.
Variable own : list (Z * Z).
Variable kL : Z.
Variables pids lst c : Z.
Variable ids : list Z.
Variable regs0 : bvmap 5 word.

(* the member list and the text block *)
Hypothesis HIDS : (1 <= length ids <= 62)%nat.
Hypothesis HIDR : Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids.
Hypothesis HPIDS0 : 0 <= pids.
(* the text block: made by the malloc wrapper in this call, so it is live now; every one of its bytes is a byte
   this walk may write (it is a temporary block of the call, or a recorder block that record()'s spill arm
   freed and malloc handed back) *)
Hypothesis HBLK : In (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B lyL SL).
Hypothesis HWR : forall a, lst <= a < lst + 12 * Z.of_nat (length ids) + 1 ->
awr_byte SEGS B STK sp0 FP (ablocks B ly SE) (ablocks B lyL SL) (frames SE) lyL own a.
(* the member array is apart from the text block, and lies in the application's heap or side stack *)
Hypothesis HAPART : iv_apart pids (4 * Z.of_nat (length ids)) lst (12 * Z.of_nat (length ids) + 1).
Hypothesis HPIDC : pids + 4 * Z.of_nat (length ids) <= alloc_ceiling.
(* the walk's stack budget: the frame and the wrapper's scratch window both fit *)
Hypothesis HSTK : 112 + 3 * ESTACK <= STK.

(* the loop's invariant after k passes *)
Definition scl_inv (k : nat) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
(k <= length ids)%nat /\
(* the journal from the function's entry: the loop adds no allocator event *)
ajournal SEGS B STK sp0 FP ly SE W0 mem0 md0 own lyL SL WL mem md kL /\
(* the stack pointer and the registers the loop keeps *)
spZ regs = sp0 - 112 /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 c /\ getr regs 9 = w64 (Z.of_nat (length ids)) /\
getr regs 19 = w64 (c + 4) /\ getr regs 20 = w64 lst /\
getr regs 22 = w64 SB /\ getr regs 23 = w64 ((c + 4) / 8 + SB) /\
getr regs 26 = w64 0x21ee0 /\ getr regs 27 = w64 0x21f00 /\
(* the loop's own registers at pass k: s8 = k, s9 = o, s2 = s5 = pids + 4k *)
getr regs 24 = w64 (Z.of_nat k) /\
getr regs 25 = w64 (Z.of_nat (length (dec_list (firstn k ids)))) /\
getr regs 18 = w64 (pids + 4 * Z.of_nat k) /\ getr regs 21 = w64 (pids + 4 * Z.of_nat k) /\
(* the frame the prologue wrote is intact *)
sc_frame_at (mrestrict (w_H WL) mem) sp0 regs0 /\
(* the text the loop has written, and its terminator *)
abytes_atR (rdW WL mem) lst (dec_list (firstn k ids) ++ [Z_to_bv 8 0]) /\
(* the member array and its shadow, and the read-only image *)
abytes_atR (rdW WL mem) pids (concat (map le32 ids)) /\
range_addressable (rdW WL mem) SHADOW_OFF pids (4 * Z.of_nat (length ids)) /\
arodata_okP SEGS RLO RHI B (rdW WL mem) /\
(* what the loop leaves alone: every byte outside the text block and this walk's stack window *)
(forall a, 0 <= a < 2 ^ 64 -> ~ (lst <= a < lst + 12 * Z.of_nat (length ids) + 1) ->
   ~ (sp0 - STK <= a < sp0) -> rdW WL mem a = rdW WL memL a).

(* one pass of the body, from the member-load check (the format already chosen) to the back edge, at the FP state
   fxk of the pass; the sprintf wrapper returns at some fx1 with fxrel fxk fx1, and the pass ends at fx1 *)
Lemma scl_pass : forall (fxk : YK11.FPState) (k : nat) (vk : Z) regs mem md (Q : world SEGS -> config -> Prop),
frm0 fxk ->
(k < length ids)%nat ->
nth_error ids k = Some vk ->
scl_inv k regs mem md ->
getr regs 11 = w64 (scl_fmtv k) ->
(* the continuation at the head of the next pass *)
(forall (fx' : YK11.FPState) regs' mem' md', fxrel fxk fx' -> scl_inv (S k) regs' mem' md' ->
 (S k < length ids)%nat -> SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCL_HEAD) regs' mem' md') Q) ->
(* the continuation at the loop's exit *)
(forall (fx' : YK11.FPState) regs' mem' md', fxrel fxk fx' -> scl_inv (S k) regs' mem' md' ->
 S k = length ids -> SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCL_EXIT) regs' mem' md') Q) ->
SRr SEGS WL (@cfg_at fxk SEGS (BASE + SCL_CHK) regs mem md) Q.
Proof.
intros fxk k vk regs mem md Q HFRMk Hk Hnth HINV H11 KH KE.
pose proof (paj_run (fx := fxk) B LAWS) as RUNk.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HINV as (Hkle & HJ & Hsp & R3 & R4 & R8 & R9 & R19 & R20 & R22 & R23 & R26 & R27 & R24 & R25 & R18 &
  R21 & HFR & HTXT & HARR & HRADDR & HROD & HAG).
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & F5 & Hpres & Hstkok
  & F6 & HQT).
pose proof Hstkok as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hvk : - 2 ^ 31 <= vk < 2 ^ 31)
  by (rewrite Forall_forall in HIDR; apply HIDR; exact (nth_error_In ids k Hnth)).
assert (HW32 : 0 <= vk mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (HQR : 0 <= pids + 4 * Z.of_nat k <= 140737488355324)
  by (pose proof HPIDS0; pose proof HPIDC; pose proof alloc_ceiling_val; lia).
assert (HV : aval_mem (rdW WL mem) (pids + 4 * Z.of_nat k) 4 (vk mod 2 ^ 32))
  by exact (scl_member WL mem pids ids k vk HARR Hnth).
destruct (scl_seed_chk fxk WL regs mem (vk mod 2 ^ 32) SCL_CHK (pids + 4 * Z.of_nat k) R22 HQR R21 R18 HW32 HV)
  as [HS SHOK].
set (E := scl_E regs (vk mod 2 ^ 32)) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply scl_E_img).
assert (E21 : ew E 21 = Z_to_bv 64 (pids + 4 * Z.of_nat k))
  by (unfold E; rewrite (scl_E_reg regs (vk mod 2 ^ 32) 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (unfold E; rewrite (scl_E_reg regs (vk mod 2 ^ 32) 22%nat 22%bv eq_refl); exact R22).
assert (UB : U E scl_Bx = SHADOW_OFF)
  by (unfold scl_Bx; rewrite (sc_U_atom E 22%nat SB E22 ltac:(unfold SB; lia)); reflexivity).
assert (U21 : U E (SOff 21 0) = pids + 4 * Z.of_nat k)
  by (apply (sc_U_atom E 21%nat); [exact E21 | lia]).
unfold cfg_at, w64.
paj_run_tok RUNk HS HJ SHOK SC_Bspan.
{ eapply obl_of_range; [exact HRADDR | exact UB | rewrite U21; lia | rewrite U21; lia]. }
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv1 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv1 end).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
(* the memory the run leaves is the one it found: its one region is read-only *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms) a = rdW WL mem a).
{ intros a Ha.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
  [ intros b wlo whi x Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
  | exact Ha | intros [] ]. }
clear HF HFr HG.
pose proof (proj1 HJ) as HARm.
assert (HRODm : arodata_okP SEGS RLO RHI B (rdW WL (ms_mem ms)))
  by (apply (scl_aro_move WL mem (ms_mem ms) KEEP1); exact HROD).
(* the registers the call takes *)
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; unfold E; apply (scl_E_reg regs (vk mod 2 ^ 32) m r Hm)).
assert (E32 : ew E 32 = Z_to_bv 64 (vk mod 2 ^ 32)) by (unfold E; apply scl_E_vk).
set (ok := Z.of_nat (length (dec_list (firstn k ids)))) in *.
destruct (sc_fmt_text k vk Hvk) as (ps & T & Hparse & Htext & Hbytes).
assert (HlenT : length (PF.pf_bytes T) = length T) by (unfold PF.pf_bytes; apply length_map).
assert (Hpiece : Z.of_nat (length (dec_list (firstn (S k) ids))) = ok + Z.of_nat (length T)).
{ rewrite (sc_dec_list_step ids k vk Hnth), length_app, <- Hbytes, HlenT. unfold ok. lia. }
assert (HokS : 0 <= ok /\ ok + (Z.of_nat (length T) + 1) <= 12 * Z.of_nat (length ids) + 1).
{ pose proof (sc_dec_list_prefix_len ids (S k) HIDR ltac:(lia)) as HL.
  rewrite Hpiece in HL. unfold ok in *. lia. }
assert (T1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_sup_chain + 0x158))) by (rewrite Q1; reflexivity).
assert (Traw : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite T1; apply ret_ok_codeptr_v; [unfold AF_sup_chain; lia | reflexivity]).
assert (Tsp : spZ (ms_regs ms) = sp0 + (-112))
  by (unfold spZ in *; rewrite Q2, (EE 2%nat 2%bv eq_refl); lia).
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4).
assert (T10 : getr (ms_regs ms) 10 = w64 (lst + ok)).
{ rewrite Q10, (EE 20%nat 20%bv eq_refl), (EE 25%nat 25%bv eq_refl), R20, R25. unfold w64.
  apply scl_add64. }
assert (T11 : getr (ms_regs ms) 11 = w64 (scl_fmtv k)) by (rewrite Q11, (EE 11%nat 11%bv eq_refl); exact H11).
(* the block's bounds *)
destruct (al_blocks _ _ LAWS lyL SL WL (ms_mem ms) mdv1 lst (12 * Z.of_nat (length ids) + 1) HARm HBLK)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbmax).
assert (Hreq : req_size (12 * Z.of_nat (length ids) + 1) = 12 * Z.of_nat (length ids) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (12 * Z.of_nat (length ids) + 1) 0); lia).
rewrite Hreq in Hbceil, Hbapp, Hbpres.
(* the text block is apart from the image, and below the wrapper's stack window *)
pose proof (scl_blk_off_img lyL SL WL (ms_mem ms) mdv1 lst (12 * Z.of_nat (length ids) + 1) HARm HBLK
  ltac:(rewrite Hreq; lia)) as Hoff.
rewrite Hreq in Hoff.
assert (HspK : 0x606000 <= spZ (ms_regs ms) - 3 * ESTACK)
  by (pose proof alloc_ceiling_val; unfold ESTACK in *; lia).
assert (HbK : lst + (12 * Z.of_nat (length ids) + 1) <= spZ (ms_regs ms) - 3 * ESTACK) by (unfold ESTACK in *; lia).
(* the shared sprintf contract's premises (RtPFCmd.sh_asprintf_realizes) *)
destruct (scl_text_facts k vk ps T Hparse Htext) as (HTR & HPP).
destruct (cmd_rec_cells lyL SL WL (ms_mem ms) mdv1 HARm) as (_ & (HG1 & cval & HG2) & _).
destruct (ecall_pre_stk_at SEGS B (3 * ESTACK) STK sp0 FP ly SE W0 mem0 md0 own lyL SL WL (ms_mem ms)
  mdv1 kL (ms_regs ms) (-112) HJ Tsp ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia)
  ltac:(unfold ESTACK in *; lia) Traw T3 T4) as (HEC & HSLO & HSCR).
pose proof (CmdRecImg.cmd_consts_view_sp SEGS B LAWS HB IMG RLO RHI WL (ms_mem ms) HRODm) as HCV.
destruct (scl_cr_ok (3 * ESTACK) (spZ (ms_regs ms)) (lst + ok) (Z.of_nat (length T) + 1) lst
  (12 * Z.of_nat (length ids) + 1) Hoff ltac:(lia) ltac:(lia) HspK ltac:(unfold ESTACK; lia)) as [HCRB HCRD].
pose proof (scl_img_disj (3 * ESTACK) (spZ (ms_regs ms)) (lst + ok) (Z.of_nat (length T) + 1) lst
  (12 * Z.of_nat (length ids) + 1) 0xa7098 8 Hoff ltac:(lia) ltac:(lia) HspK ltac:(unfold ESTACK; lia)
  ltac:(lia) ltac:(lia) ltac:(lia)) as HGCD.
pose proof (scl_img_disj (3 * ESTACK) (spZ (ms_regs ms)) (lst + ok) (Z.of_nat (length T) + 1) lst
  (12 * Z.of_nat (length ids) + 1) 0x6045d8 8 Hoff ltac:(lia) ltac:(lia) HspK ltac:(unfold ESTACK; lia)
  ltac:(lia) ltac:(lia) ltac:(lia)) as HGVD.
destruct (scl_sp_side (3 * ESTACK) (spZ (ms_regs ms)) (lst + ok) (Z.of_nat (length T) + 1) lst
  (12 * Z.of_nat (length ids) + 1) ltac:(lia) ltac:(lia) HbK ltac:(unfold ESTACK; lia)) as [HXSD HPW].
pose proof (scl_dog (lst + ok) (Z.of_nat (length T) + 1) lst (12 * Z.of_nat (length ids) + 1) Hoff
  ltac:(lia) ltac:(lia)) as HDOG.
assert (HVA : RtPFCmd.va_words2 (ms_regs ms) (rdW WL (ms_mem ms)) (spZ (ms_regs ms)) []
  (map (argZ (ms_regs ms)) [2; 3; 4; 5; 6; 7] ++ [])).
{ split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia. }
assert (HFMT : RtPFShared.fmt_at (rdW WL (ms_mem ms))
  (RtPFShared.snp_out (3 * ESTACK) (spZ (ms_regs ms)) (lst + ok) (Z.of_nat (length T) + 1))
  (scl_fmtv k) (scl_fmt k)).
{ apply (scl_fmt_at lyL SL WL (ms_mem ms) mdv1 k _ HARm HRODm).
  apply (scl_img_disj _ _ _ _ lst (12 * Z.of_nat (length ids) + 1));
  [exact Hoff | lia | lia | exact HspK | unfold ESTACK; lia
  | unfold scl_fmtv; destruct (Nat.eqb k 0); lia
  | unfold scl_fmtv, scl_fmt; destruct (Nat.eqb k 0); cbn [length sc_fmt0 sc_fmt1]; lia | lia]. }
assert (HFF : RtPFCmd.FR_cmd (rdW WL (ms_mem ms))
  (RtPFShared.snp_out (3 * ESTACK) (spZ (ms_regs ms)) (lst + ok) (Z.of_nat (length T) + 1))
  (scl_fmtv k) (map (argZ (ms_regs ms)) [2; 3; 4; 5; 6; 7] ++ []) T).
{ apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ (scl_fmt k) ps [PF.AInt vk] HFMT Hparse);
    [| exact Htext | exact HPP | unfold scl_fmtv, scl_fmt; destruct (Nat.eqb k 0); vm_compute; reflexivity].
  cbn [map app RtPFCmd.arg_of RtPFShared.pf_args_asan RtPFShared.pf_arg_asan]. split; [|exact I].
  split; [exact Hvk|]. rewrite scl_argZ2, Q12, E32, scl_lw_mod. apply Z.mod_mod. lia. }
(* the window the entry writes is inside the list text block *)
assert (HDOK : dest_ok SEGS B lyL SL WL (ms_regs ms) (ms_mem ms) (lst + ok) (Z.of_nat (length T) + 1)).
{ intros a Ha. split; [apply (apresent_writable SEGS); exact (proj1 (Hbpres a ltac:(lia)))|].
  split; [exact (proj2 (Hbpres a ltac:(lia)))|]. unfold ESTACK in *. lia. }
pose proof (amem_range_of_block SEGS B LAWS lyL SL WL (ms_mem ms) mdv1 lst
  (12 * Z.of_nat (length ids) + 1) (lst + ok) (Z.of_nat (length T) + 1) HARm HBLK ltac:(lia) ltac:(lia)) as HAMR.
pose proof (range_addressable_of_block SEGS B LAWS lyL SL WL (ms_mem ms) mdv1 lst
  (12 * Z.of_nat (length ids) + 1) (lst + ok) (Z.of_nat (length T) + 1) HARm HBLK ltac:(lia) ltac:(lia)) as HRAD.
pose proof (shadow_hull_vis_of_block SEGS B LAWS lyL SL WL (ms_mem ms) mdv1 lst
  (12 * Z.of_nat (length ids) + 1) (lst + ok) (Z.of_nat (length T) + 1) HARm HBLK ltac:(lia) ltac:(lia)
  ltac:(lia)) as HHULL.
assert (HTL31 : Z.of_nat (length T) < 2 ^ 31 - 1) by lia.
assert (Hd0 : 0 < lst + ok) by lia.
assert (Hd63 : lst + ok + (Z.of_nat (length T) + 1) <= 2 ^ 63) by lia.
assert (HXS : spZ (ms_regs ms) + 8 * Z.of_nat (length (@nil Z)) < 2 ^ 63) by (cbn [length]; lia).
(* the band premises: no argument slot on the stack (xs = []), and the destination's slack
   word, which reads up to 8 bytes past the text; the text ends at or before the block's last byte and the + 8 is a
   band bound only, which the block's own band gives (PaLibH.amem8_of_block) *)
assert (HV47 : spZ (ms_regs ms) + 8 * Z.of_nat (length (@nil Z)) <= 2 ^ 47).
{ apply (RtPFSx.va_slots_below_47_AR SEGS B lyL SL WL (ms_regs ms) (ms_mem ms) mdv1 [] HEC).
  pose proof HEC as (_ & _ & _ & _ & Hhi & _). cbn [length]. lia. }
assert (HAM8 : amem_range (lst + ok) (Z.of_nat (length T) + 1 + 8)).
{ pose proof (req_size_pos (12 * Z.of_nat (length ids) + 1) ltac:(lia)) as [_ Hrq].
  exact (amem8_of_block SEGS B LAWS lyL SL WL (ms_mem ms) mdv1 lst (12 * Z.of_nat (length ids) + 1)
           (lst + ok) (Z.of_nat (length T) + 1) HARm HBLK ltac:(lia) ltac:(lia) ltac:(lia)). }
(* 0x8c408: sprintf(lst + o, fmt, v) writes the member's text and returns at some FP state fx1 *)
eapply SRr_bind.
{ eapply (scl_art_blkF fxk (3 * ESTACK) (fun a => lst + ok <= a < lst + ok + (Z.of_nat (length T) + 1))
    (SIG CS___interceptor_trampoline_sprintf) WL (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly SE W0 mem0 md0 own lyL SL mdv1 kL (-112)
    (Z_to_bv 64 (BASE + (AF_sup_chain + 0x158))) _ HJ Tsp ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(unfold ESTACK in *; lia) T1).
  - intros a Ha. apply HWR. lia.
  - apply (srr_art_postF_of_pf (fx := fxk) SEGS B (3 * ESTACK) lyL SL WL (ms_regs ms) (ms_mem ms) mdv1 _
      (lst + ok) (Z.of_nat (length T) + 1) (T ++ [0]) (Z.of_nat (length T)) HSCR).
    exact (ASPRINTF fxk lyL SL WL (ms_regs ms) (ms_mem ms) mdv1 (lst + ok) (scl_fmtv k) []
      (map (argZ (ms_regs ms)) [2; 3; 4; 5; 6; 7] ++ []) T cval HEC HSLO HSCR T10 T11 HCV HCRB HCRD HG1 HG2
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HGCD HGVD HVA HXS HXSD HFF HTL31 Hd0 Hd63 HPW HDOK HAMR HRAD
      HHULL HDOG HFRMk HV47 HAM8). }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & HQ2 & HK2).
destruct HQ2 as (HR10 & HBYZ).
pose proof (scl_bytes_of_Z (rdW WL mem2) (lst + ok) T HTR HBYZ) as HBYT.
clear HBYZ HEC HSLO HSCR HCV HCRB HCRD HG1 HG2 HGCD HGVD HVA HXS HXSD HFF HFMT HPW HDOK HAMR HRAD HHULL HDOG.
(* back at 0x8c40c at the FP state fx1: the call site's symbolic state taken to fx1 (PaFx.v's st_ok_restrict_xfx),
   the runs at fx1, with the list text block's bytes kept outside the window the entry wrote *)
pose proof (PaFx.st_ok_restrict_xfx fxk fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
pose proof (paj_run (fx := fx1) B LAWS) as RUN1.
pose proof (paj_run_to (fx := fx1) B LAWS) as RUNTO1.
pose proof (paj_branch (fx := fx1) (PI := PI)) as BR1.
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H WL) mem2) HP2 (@nil nat) HS2.
lazymatch type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex _ _ =>
   assert (HEI2 : img_env VAL A_LIM Ex)
     by (apply img_env_havoc; [assumption | rewrite length_map; cbv; lia]);
   assert (SHOK2 : sh_ok SEGS scl_Bx scl_SH Ex (mrestrict (w_H WL) mem2))
     by (unfold sh_ok, scl_SH; apply Forall_nil)
end.
(* what the call changed: its scratch window, inside this walk's stack window, and the text it wrote *)
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (lst <= a < lst + 12 * Z.of_nat (length ids) + 1) ->
  ~ (sp0 - STK <= a < sp0) -> rdW WL mem2 a = rdW WL mem a).
{ intros a Ha Hb Hs.
  rewrite (HK2 a Ha ltac:(unfold ESTACK in *; lia) ltac:(cbv beta; lia)). exact (KEEP1 a Ha). }
assert (KEEPB : forall a, lst <= a < lst + ok -> rdW WL mem2 a = rdW WL mem a).
{ intros a Ha.
  rewrite (HK2 a ltac:(lia) ltac:(unfold ESTACK in *; lia) ltac:(cbv beta; lia)). apply KEEP1. lia. }
assert (KEEPF : forall a, sp0 - 112 <= a < sp0 -> rdW WL mem2 a = rdW WL mem a).
{ intros a Ha.
  rewrite (HK2 a ltac:(lia) ltac:(unfold ESTACK in *; lia)
                  ltac:(cbv beta; unfold ESTACK in *; lia)). apply KEEP1. lia. }
assert (HBapp : PF.pf_bytes (T ++ [0]) = PF.pf_bytes T ++ [Z_to_bv 8 0])
  by (unfold PF.pf_bytes; rewrite map_app; reflexivity).
(* the invariant at the next pass, for any state whose memory is the one the call left *)
assert (MKINV : forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  ajournal SEGS B STK sp0 FP ly SE W0 mem0 md0 own lyL SL WL mem' md' kL ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW WL mem' a = rdW WL mem2 a) ->
  spZ regs' = sp0 - 112 ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
  getr regs' 8 = w64 c -> getr regs' 9 = w64 (Z.of_nat (length ids)) ->
  getr regs' 19 = w64 (c + 4) -> getr regs' 20 = w64 lst ->
  getr regs' 22 = w64 SB -> getr regs' 23 = w64 ((c + 4) / 8 + SB) ->
  getr regs' 26 = w64 0x21ee0 -> getr regs' 27 = w64 0x21f00 ->
  getr regs' 24 = w64 (Z.of_nat (S k)) ->
  getr regs' 25 = w64 (Z.of_nat (length (dec_list (firstn (S k) ids)))) ->
  getr regs' 18 = w64 (pids + 4 * Z.of_nat (S k)) ->
  getr regs' 21 = w64 (pids + 4 * Z.of_nat (S k)) ->
  scl_inv (S k) regs' mem' md').
{ intros regs' mem' md' HJ' KEEP' S2 S3 S4 S8 S9 S19 S20 S22 S23 S26 S27 S24 S25 S18 S21.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (lst <= a < lst + 12 * Z.of_nat (length ids) + 1) ->
    ~ (sp0 - STK <= a < sp0) -> rdW WL mem' a = rdW WL mem a)
    by (intros a Ha Hb Hs; rewrite (KEEP' a Ha); exact (KEEPC a Ha Hb Hs)).
  assert (KB : forall a, lst <= a < lst + ok -> rdW WL mem' a = rdW WL mem a)
    by (intros a Ha; rewrite (KEEP' a ltac:(lia)); exact (KEEPB a Ha)).
  split; [lia|]. split; [exact HJ'|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
  split; [exact S8|]. split; [exact S9|]. split; [exact S19|]. split; [exact S20|]. split; [exact S22|].
  split; [exact S23|]. split; [exact S26|]. split; [exact S27|]. split; [exact S24|]. split; [exact S25|].
  split; [exact S18|]. split; [exact S21|].
  assert (KF : forall a, sp0 - 112 <= a < sp0 -> rdW WL mem' a = rdW WL mem a)
    by (intros a Ha; rewrite (KEEP' a ltac:(lia)); exact (KEEPF a Ha)).
  split.
  { (* the frame the prologue wrote is above the wrapper's scratch window *)
    intros j r Hj.
    assert (Hj13 : (j < 13)%nat).
    { assert (HL : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      change (length sc_saved) with 13%nat in HL. exact HL. }
    apply (scl_val_keep WL mem mem' (sp0 - 8 - 8 * Z.of_nat j) 8 _); [|exact (HFR j r Hj)].
    intros x Hx. cbn [Z.of_nat] in Hx. apply KF. lia. }
  split.
  { (* the text: the bytes before the window are kept, the window holds the member's text *)
    rewrite (sc_dec_list_step ids k vk Hnth), <- Hbytes, <- app_assoc.
    intros i Hi. rewrite !length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length (dec_list (firstn k ids)))) as [Hlt | Hge].
    - rewrite app_nth1 by lia.
      rewrite (KB (lst + Z.of_nat i) ltac:(unfold ok in *; lia)).
      pose proof (HTXT i ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
      rewrite app_nth1 in Hb by lia. exact Hb.
    - rewrite app_nth2 by lia.
      pose proof (HBYT (i - length (dec_list (firstn k ids)))%nat) as Hb.
      rewrite HBapp in Hb.
      replace (lst + ok + Z.of_nat (i - length (dec_list (firstn k ids)))) with (lst + Z.of_nat i) in Hb
        by (unfold ok; rewrite Nat2Z.inj_sub by lia; lia).
      rewrite (KEEP' (lst + Z.of_nat i) ltac:(unfold ok in *; lia)).
      apply Hb. rewrite length_app, HlenT. cbn [length]. lia. }
  split.
  { (* the member array: apart from the text block and below the stack *)
    intros i Hi. pose proof Hi as Hi'. rewrite scl_concat_len in Hi'.
    rewrite (KA (pids + Z.of_nat i)); [exact (HARR i Hi) | | |].
    - unfold ESTACK in *. lia.
    - unfold iv_apart in HAPART. lia.
    - unfold ESTACK in *. lia. }
  split.
  { (* its shadow: a shadow byte is no byte of the text block and lies below the stack *)
    apply (range_addressable_agree (rdW WL mem) (rdW WL mem')); [|exact HRADDR].
    intros x Hx. apply KA.
    - unfold shadow_of_addr, SHADOW_OFF.
      pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 44)
        ltac:(lia) ltac:(lia)). lia.
    - intros Hin. apply (scl_shadow_apart lyL SL WL mem2 md2 lst (12 * Z.of_nat (length ids) + 1) x
        (proj1 HJ2) HBLK ltac:(unfold kHighMemEnd; lia)). rewrite Hreq. lia.
    - unfold shadow_of_addr, SHADOW_OFF.
      pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 44)
        ltac:(lia) ltac:(lia)). lia. }
  split.
  { (* the read-only image *)
    apply (scl_aro_keep lyL SL WL mem mem' md lst (12 * Z.of_nat (length ids) + 1) (sp0 - STK) sp0);
    [exact HARc | | unfold kLowMemEnd; lia | | exact HROD].
    - (* the block is live at the memory the loop started from *)
      exact HBLK.
    - intros a Ha Hs Hbk. apply KA; [exact Ha | rewrite Hreq in Hbk; lia | exact Hs]. }
  (* what the pass left alone *)
  intros a Ha Hb Hs. rewrite (KA a Ha Hb Hs). exact (HAG a Ha Hb Hs). }
(* 0x8c40c .. 0x8c41c: the loop's counters move on, then the back-edge branch *)
paj_run_tok RUN1 HS HJ2 SHOK2 SC_Bspan.
{ apply awr_ok_nil. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv2 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv2 end).
assert (KEEPE : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms0) a = rdW WL mem2 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
  [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
clear HF HFr HG.
psrr_branch_tok RUN1 BR1 HS SHOK2 SC_Bspan.
- (* the back edge: one more member remains *)
  paj_run_to_tok RUNTO1 HS HJ2 SHOK2 SC_Bspan SCL_HEAD.
  { apply awr_ok_nil. }
  assert (KEEPD : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms1) a = rdW WL mem2 a).
  { intros a Ha. rewrite <- (KEEPE a Ha).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.
  apply (KH fx1 (ms_regs ms1) (ms_mem ms1) _ Hfx).
  + apply MKINV.
    * exact HJ2.
    * exact KEEPD.
    * unfold spZ in *. rewrite P2, (EE 2%nat 2%bv eq_refl). lia.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact R3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact R4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact R8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact R9.
    * rewrite P19, (EE 19%nat 19%bv eq_refl). exact R19.
    * rewrite P20, (EE 20%nat 20%bv eq_refl). exact R20.
    * rewrite P22, (EE 22%nat 22%bv eq_refl). exact R22.
    * rewrite P23, (EE 23%nat 23%bv eq_refl). exact R23.
    * rewrite P26, (EE 26%nat 26%bv eq_refl). exact R26.
    * rewrite P27, (EE 27%nat 27%bv eq_refl). exact R27.
    * rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P25. cbv [CLOB] in *. cbn [map nth] in *.
      rewrite (EE 25%nat 25%bv eq_refl), R25, HR10. unfold w64. rewrite scl_add64. f_equal.
      rewrite Hpiece. reflexivity.
    * rewrite P18, (EE 18%nat 18%bv eq_refl), R18. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P21, (EE 21%nat 21%bv eq_refl), R21. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia.
  + (* the branch says the member count is not reached yet *)
    rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite !U_SOff in Hc. prreg_norm Hc.
    rewrite (EE 9%nat 9%bv eq_refl), (EE 24%nat 24%bv eq_refl), R9, R24 in Hc.
    unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite !Z.mod_small in Hc by lia. lia.
- (* the fall-through: this was the last member *)
  paj_run_to_tok RUNTO1 HS HJ2 SHOK2 SC_Bspan SCL_EXIT.
  { apply awr_ok_nil. }
  assert (KEEPD : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms1) a = rdW WL mem2 a).
  { intros a Ha. rewrite <- (KEEPE a Ha).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.
  apply (KE fx1 (ms_regs ms1) (ms_mem ms1) _ Hfx).
  + apply MKINV.
    * exact HJ2.
    * exact KEEPD.
    * unfold spZ in *. rewrite P2, (EE 2%nat 2%bv eq_refl). lia.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact R3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact R4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact R8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact R9.
    * rewrite P19, (EE 19%nat 19%bv eq_refl). exact R19.
    * rewrite P20, (EE 20%nat 20%bv eq_refl). exact R20.
    * rewrite P22, (EE 22%nat 22%bv eq_refl). exact R22.
    * rewrite P23, (EE 23%nat 23%bv eq_refl). exact R23.
    * rewrite P26, (EE 26%nat 26%bv eq_refl). exact R26.
    * rewrite P27, (EE 27%nat 27%bv eq_refl). exact R27.
    * rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P25. cbv [CLOB] in *. cbn [map nth] in *.
      rewrite (EE 25%nat 25%bv eq_refl), R25, HR10. unfold w64. rewrite scl_add64. f_equal.
      rewrite Hpiece. reflexivity.
    * rewrite P18, (EE 18%nat 18%bv eq_refl), R18. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P21, (EE 21%nat 21%bv eq_refl), R21. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia.
  + (* the branch says this member was the last *)
    rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    rewrite !U_SOff in Hc. prreg_norm Hc.
    rewrite (EE 9%nat 9%bv eq_refl), (EE 24%nat 24%bv eq_refl), R9, R24 in Hc.
    unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite !Z.mod_small in Hc by lia. lia.
Qed.

(* the invariant at a state the walk reaches without writing and without touching the registers it keeps *)
Lemma scl_inv_move : forall (k : nat) (regs regs' : bvmap 5 word) mem md mem' md',
scl_inv k regs mem md ->
ajournal SEGS B STK sp0 FP ly SE W0 mem0 md0 own lyL SL WL mem' md' kL ->
(forall a, 0 <= a < 2 ^ 64 -> rdW WL mem' a = rdW WL mem a) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
   getr regs' r = getr regs r) ->
scl_inv k regs' mem' md'.
Proof.
intros k regs regs' mem md mem' md' HINV HJ' K KR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HINV as (Hkle & HJ & Hsp & R3 & R4 & R8 & R9 & R19 & R20 & R22 & R23 & R26 & R27 & R24 & R25 & R18 &
  R21 & HFR & HTXT & HARR & HRADDR & HROD & HAG).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkok & _).
pose proof Hstkok as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS lyL SL WL mem md lst (12 * Z.of_nat (length ids) + 1) HARc HBLK)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbmax).
assert (Hreq : req_size (12 * Z.of_nat (length ids) + 1) = 12 * Z.of_nat (length ids) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (12 * Z.of_nat (length ids) + 1) 0); lia).
rewrite Hreq in Hbceil.
assert (HTLn : Z.of_nat (length (dec_list (firstn k ids))) <= 12 * Z.of_nat (length ids))
  by (pose proof (sc_dec_list_prefix_len ids k HIDR ltac:(lia)); lia).
split; [exact Hkle|]. split; [exact HJ'|].
split; [unfold spZ in *; rewrite (KR 2%bv ltac:(cbn [In]; tauto)); exact Hsp|].
split; [rewrite (KR 3%bv ltac:(cbn [In]; tauto)); exact R3|].
split; [rewrite (KR 4%bv ltac:(cbn [In]; tauto)); exact R4|].
split; [rewrite (KR 8%bv ltac:(cbn [In]; tauto)); exact R8|].
split; [rewrite (KR 9%bv ltac:(cbn [In]; tauto)); exact R9|].
split; [rewrite (KR 19%bv ltac:(cbn [In]; tauto)); exact R19|].
split; [rewrite (KR 20%bv ltac:(cbn [In]; tauto)); exact R20|].
split; [rewrite (KR 22%bv ltac:(cbn [In]; tauto)); exact R22|].
split; [rewrite (KR 23%bv ltac:(cbn [In]; tauto)); exact R23|].
split; [rewrite (KR 26%bv ltac:(cbn [In]; tauto)); exact R26|].
split; [rewrite (KR 27%bv ltac:(cbn [In]; tauto)); exact R27|].
split; [rewrite (KR 24%bv ltac:(cbn [In]; tauto)); exact R24|].
split; [rewrite (KR 25%bv ltac:(cbn [In]; tauto)); exact R25|].
split; [rewrite (KR 18%bv ltac:(cbn [In]; tauto)); exact R18|].
split; [rewrite (KR 21%bv ltac:(cbn [In]; tauto)); exact R21|].
split; [exact (scl_frame_keep WL mem mem' sp0 regs0 K ltac:(lia) ltac:(lia) HFR)|].
split.
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (K (lst + Z.of_nat i) ltac:(lia)). exact (HTXT i ltac:(rewrite length_app; cbn [length]; lia)). }
split.
{ intros i Hi. pose proof Hi as Hi'. rewrite scl_concat_len in Hi'.
  rewrite (K (pids + Z.of_nat i) ltac:(pose proof HPIDS0; pose proof HPIDC; lia)). exact (HARR i Hi). }
split.
{ apply (range_addressable_agree (rdW WL mem) (rdW WL mem')); [|exact HRADDR].
  intros x Hx. apply K. unfold shadow_of_addr, SHADOW_OFF.
  pose proof HPIDS0. pose proof HPIDC.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
split; [exact (scl_aro_move WL mem mem' K HROD)|].
intros a Ha Hb Hs. rewrite (K a Ha). exact (HAG a Ha Hb Hs).
Qed.


(* the body of the loop: from its head to the back edge, at the FP state fxk of the pass *)
Lemma sc_loop_body : forall (fxk : YK11.FPState) (k : nat) regs mem md (Q : world SEGS -> config -> Prop),
frm0 fxk ->
(k < length ids)%nat ->
scl_inv k regs mem md ->
(forall (fx' : YK11.FPState) regs' mem' md', fxrel fxk fx' -> scl_inv (S k) regs' mem' md' ->
 (S k < length ids)%nat -> SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCL_HEAD) regs' mem' md') Q) ->
(forall (fx' : YK11.FPState) regs' mem' md', fxrel fxk fx' -> scl_inv (S k) regs' mem' md' ->
 S k = length ids -> SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCL_EXIT) regs' mem' md') Q) ->
SRr SEGS WL (@cfg_at fxk SEGS (BASE + SCL_HEAD) regs mem md) Q.
Proof.
intros fxk k regs mem md Q HFRMk Hk HINV KH KE.
pose proof (paj_run (fx := fxk) B LAWS) as RUNk.
pose proof (paj_run_to (fx := fxk) B LAWS) as RUNTOk.
pose proof (paj_branch (fx := fxk) (PI := PI)) as BRk.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HINV as (Hkle & HJ & Hsp & R3 & R4 & R8 & R9 & R19 & R20 & R22 & R23 & R26 & R27 & R24 & R25 & R18 &
  R21 & HFR & HTXT & HARR & HRADDR & HROD & HAG).
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
  by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
destruct (scl_seed_nomem fxk WL regs mem 0 SCL_HEAD R22) as [HS SHOK].
set (E := scl_E regs 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply scl_E_img).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; unfold E; apply (scl_E_reg regs 0 m r Hm)).
(* the member the pass prints *)
assert (Hex : exists v, nth_error ids k = Some v).
{ destruct (nth_error ids k) as [v|] eqn:Ev; [exists v; reflexivity|].
  apply nth_error_None in Ev. lia. }
destruct Hex as [vk Hnth].
unfold cfg_at, w64.
(* 0x8c3e4 .. 0x8c3e8: a1 takes "%d", then the test for the first member *)
paj_run_tok RUNk HS HJ SHOK SC_Bspan.
{ apply awr_ok_nil. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv1 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv1 end).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms) a = rdW WL mem a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
  [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
clear HF HFr HG.
psrr_branch_tok RUNk BRk HS SHOK SC_Bspan.
- (* the first member: the format stays "%d" *)
  assert (Hk0 : k = 0%nat).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. apply Z.eqb_eq in Hc.
    rewrite (EE 24%nat 24%bv eq_refl), R24 in Hc. unfold w64 in Hc.
    rewrite unsigned_lit_small in Hc by lia. rewrite !ZC in Hc by lia. lia. }
  paj_run_to_tok RUNTOk HS HJ SHOK SC_Bspan SCL_CHK.
  { apply awr_ok_nil. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms0) a = rdW WL mem a).
  { intros a Ha. rewrite <- (KEEP1 a Ha).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs (scl_xs 0)
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (scl_E_agree regs 0)
    ltac:(vm_compute; reflexivity)) as KEPT.
  pmkst HS. prreg HS (11%bv : bv 5) P11.
  apply (scl_pass fxk k vk (ms_regs ms0) (ms_mem ms0) _ Q HFRMk Hk Hnth).
  + exact (scl_inv_move k regs (ms_regs ms0) mem md (ms_mem ms0) _ HINV HJ KEEP2 KEPT).
  + rewrite P11, (EE 27%nat 27%bv eq_refl), R27. unfold scl_fmtv. rewrite Hk0. reflexivity.
  + exact KH.
  + exact KE.
- (* a later member: a1 takes " %d" *)
  assert (Hkn0 : k <> 0%nat).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. apply Z.eqb_neq in Hc.
    rewrite (EE 24%nat 24%bv eq_refl), R24 in Hc. unfold w64 in Hc.
    rewrite unsigned_lit_small in Hc by lia. rewrite !ZC in Hc by lia. lia. }
  paj_run_to_tok RUNTOk HS HJ SHOK SC_Bspan SCL_CHK.
  { apply awr_ok_nil. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms0) a = rdW WL mem a).
  { intros a Ha. rewrite <- (KEEP1 a Ha).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs (scl_xs 0)
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (scl_E_agree regs 0)
    ltac:(vm_compute; reflexivity)) as KEPT.
  pmkst HS. prreg HS (11%bv : bv 5) P11.
  apply (scl_pass fxk k vk (ms_regs ms0) (ms_mem ms0) _ Q HFRMk Hk Hnth).
  + exact (scl_inv_move k regs (ms_regs ms0) mem md (ms_mem ms0) _ HINV HJ KEEP2 KEPT).
  + rewrite P11, (EE 26%nat 26%bv eq_refl), R26. unfold scl_fmtv.
    destruct (Nat.eqb_spec k 0) as [Hq | Hq]; [exfalso; exact (Hkn0 Hq) | reflexivity].
  + exact KH.
  + exact KE.
Qed.

(* the whole loop, by induction on the number of passes left (at most 62; no unrolling); each pass starts at the
   FP state the one before it returned *)
Lemma scl_loop_from : forall (j : nat) (fxk : YK11.FPState) (k : nat) regs mem md (Q : world SEGS -> config -> Prop),
frm0 fxk ->
(k + j = length ids)%nat -> (0 < j)%nat ->
scl_inv k regs mem md ->
(forall (fx' : YK11.FPState) regs' mem' md', fxrel fxk fx' -> scl_inv (length ids) regs' mem' md' ->
 SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCL_EXIT) regs' mem' md') Q) ->
SRr SEGS WL (@cfg_at fxk SEGS (BASE + SCL_HEAD) regs mem md) Q.
Proof.
induction j as [|j IH]; intros fxk k regs mem md Q HFRMk Hkj Hj HINV KE; [lia|].
apply (sc_loop_body fxk k regs mem md Q HFRMk ltac:(lia) HINV).
- (* the back edge: one more pass remains, from the FP state this pass returned *)
  intros fx' regs' mem' md' Hfx HINV' Hlt.
  apply (IH fx' (S k) regs' mem' md' Q (fxrel_frm0 fxk fx' HFRMk Hfx) ltac:(lia) ltac:(lia) HINV').
  intros fx'' regs'' mem'' md'' Hfx' HINV''.
  exact (KE fx'' regs'' mem'' md'' (fxrel_trans fxk fx' fx'' Hfx Hfx') HINV'').
- (* the fall-through: the loop is done *)
  intros fx' regs' mem' md' Hfx HINV' Heq. apply (KE fx' regs' mem' md' Hfx). rewrite <- Heq. exact HINV'.
Qed.

(* the loop, from the loop-skip test to the exit; it runs from the memory memL the segment before it leaves *)
Lemma sc_loop : forall regs md (Q : world SEGS -> config -> Prop),
frm0 fx ->
ajournal SEGS B STK sp0 FP ly SE W0 mem0 md0 own lyL SL WL memL md kL ->
spZ regs = sp0 - 112 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 8 = w64 c -> getr regs 9 = w64 (Z.of_nat (length ids)) ->
getr regs 18 = w64 pids -> getr regs 19 = w64 (c + 4) -> getr regs 20 = w64 lst ->
getr regs 22 = w64 SB -> getr regs 23 = w64 ((c + 4) / 8 + SB) ->
sc_frame_at (mrestrict (w_H WL) memL) sp0 regs0 ->
rdW WL memL lst = Some 0 ->
abytes_atR (rdW WL memL) pids (concat (map le32 ids)) ->
range_addressable (rdW WL memL) SHADOW_OFF pids (4 * Z.of_nat (length ids)) ->
arodata_okP SEGS RLO RHI B (rdW WL memL) ->
(forall (fx' : YK11.FPState) regs' mem' md', fxrel fx fx' -> scl_inv (length ids) regs' mem' md' ->
 SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCL_EXIT) regs' mem' md') Q) ->
SRr SEGS WL (cfg_at SEGS (BASE + SCL_LOOP) regs memL md) Q.
Proof.
intros regs md Q HFRM HJ Hsp R3 R4 R8 R9 R18 R19 R20 R22 R23 HFR Hlst HARR HRADDR HROD KE.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
  by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
destruct (scl_seed_nomem fx WL regs memL 0 SCL_LOOP R22) as [HS SHOK].
set (E := scl_E regs 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply scl_E_img).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm; unfold E; apply (scl_E_reg regs 0 m r Hm)).
pose proof (proj1 HJ) as HARL.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkok & _).
pose proof Hstkok as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS lyL SL WL memL md lst (12 * Z.of_nat (length ids) + 1) HARL HBLK)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbmax).
assert (Hreq : req_size (12 * Z.of_nat (length ids) + 1) = 12 * Z.of_nat (length ids) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (12 * Z.of_nat (length ids) + 1) 0); lia).
rewrite Hreq in Hbceil.
unfold cfg_at, w64.
(* 0x8c3c4: blez s1 skips the loop when there is no member *)
paj_run_tok RUN HS HJ SHOK SC_Bspan.
{ apply awr_ok_nil. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv1 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv1 end).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms) a = rdW WL memL a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
  [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
clear HF HFr HG.
assert (D9 : sv_denot E (SOff 9 0) = Z_to_bv 64 (Z.of_nat (length ids))).
{ cbn [sv_denot]. rewrite (EE 9%nat 9%bv eq_refl), R9. unfold w64.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
psrr_branch_tok RUN BR HS SHOK SC_Bspan.
- (* the skip: there is at least one member *)
  exfalso.
  change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc. rewrite D9 in Hc.
  rewrite brz_ge in Hc by lia.
  rewrite (YO0b.s64_small 0), (YO0b.s64_small (Z.of_nat (length ids))) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc. lia.
- (* 0x8c3c8 .. 0x8c3e0: the counters, the two formats, s5 = the member array *)
  paj_run_to_tok RUNTO HS HJ SHOK SC_Bspan SCL_HEAD.
  { apply awr_ok_nil. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW WL (ms_mem ms0) a = rdW WL memL a).
  { intros a Ha. rewrite <- (KEEP1 a Ha).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros b wlo whi x Hin Hrr; destruct Hin | exact Ha | intros [] ]. }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs (scl_xs 0)
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23]%bv HS (scl_E_agree regs 0)
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  prreg HS (21%bv : bv 5) P21. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HV71 : VAL 312%nat = 0x21ee0).
  { change 312%nat with (A_OBJ 71). rewrite (VOBJS 71%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
  assert (HV56 : VAL 297%nat = 0x21f00).
  { change 297%nat with (A_OBJ 56). rewrite (VOBJS 56%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
  apply (scl_loop_from (length ids) fx 0 (ms_regs ms0) (ms_mem ms0) _ Q HFRM ltac:(lia) ltac:(lia)); [|exact KE].
  split; [lia|]. split; [exact HJ|].
  split; [unfold spZ in *; rewrite (KR 2%bv ltac:(cbn [In]; tauto)); exact Hsp|].
  split; [rewrite (KR 3%bv ltac:(cbn [In]; tauto)); exact R3|].
  split; [rewrite (KR 4%bv ltac:(cbn [In]; tauto)); exact R4|].
  split; [rewrite (KR 8%bv ltac:(cbn [In]; tauto)); exact R8|].
  split; [rewrite (KR 9%bv ltac:(cbn [In]; tauto)); exact R9|].
  split; [rewrite (KR 19%bv ltac:(cbn [In]; tauto)); exact R19|].
  split; [rewrite (KR 20%bv ltac:(cbn [In]; tauto)); exact R20|].
  split; [rewrite (KR 22%bv ltac:(cbn [In]; tauto)); exact R22|].
  split; [rewrite (KR 23%bv ltac:(cbn [In]; tauto)); exact R23|].
  split; [rewrite P26, (img_env_atomP E 312%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)), HV71; reflexivity|].
  split; [rewrite P27, (img_env_atomP E 297%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)), HV56; reflexivity|].
  split; [rewrite P24; reflexivity|].
  split; [rewrite P25; reflexivity|].
  split; [rewrite (KR 18%bv ltac:(cbn [In]; tauto)), R18; f_equal; lia|].
  split; [rewrite P21, (EE 18%nat 18%bv eq_refl), R18; f_equal; lia|].
  split; [exact (scl_frame_keep WL memL (ms_mem ms0) sp0 regs0 KEEP2 ltac:(lia) ltac:(lia) HFR)|].
  split.
  { intros i Hi.
    assert (HL1 : length (dec_list (firstn 0 ids) ++ [Z_to_bv 8 0]) = 1%nat) by reflexivity.
    rewrite HL1 in Hi.
    destruct i as [|i]; [|lia]. replace (lst + Z.of_nat 0) with lst by lia.
    rewrite (KEEP2 lst ltac:(lia)). exact Hlst. }
  split.
  { intros i Hi. pose proof Hi as Hi'. rewrite scl_concat_len in Hi'.
    rewrite (KEEP2 (pids + Z.of_nat i) ltac:(pose proof HPIDS0; pose proof HPIDC; lia)). exact (HARR i Hi). }
  split.
  { apply (range_addressable_agree (rdW WL memL) (rdW WL (ms_mem ms0))); [|exact HRADDR].
    intros x Hx. apply KEEP2. unfold shadow_of_addr, SHADOW_OFF.
    pose proof HPIDS0. pose proof HPIDC.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  split; [exact (scl_aro_move WL memL (ms_mem ms0) KEEP2 HROD)|].
  intros a Ha _ _. exact (KEEP2 a Ha).
Qed.

End loop.



End e.
End f.
End d.
