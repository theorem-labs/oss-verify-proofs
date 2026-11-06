(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:136-141;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC93.v:83-84. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/put_dec_epi.v, with its module paths, module names and numbers changed; 434 of its 474 lines of code are new or changed and 347 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_chain_s5.v, with its module paths and module names changed; 122 of its 158 lines of code are new or changed and 438 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/check_words_chain_s2h.v for fuzz_command.asan-ubsan:
   module paths; the shadow address of w + 16 (the A loop's s7) is gone, the B loop computes the metadata byte of
   each word itself. *)
(* The facts stage 2 of check_words_chain's walk hands to the loop and the tail stages about the strings and the
   word array the statement names at the entry: the statement gives them over the entry's memory
   (cwc_sblk, in_blockA, aval_mem); the stages take them over the memory where they start
   (check_words_chain_iv.v's cwc_strk, cwc_wordk).

   Every string the statement names lies in a live block (cwc_sblk). It keeps its bytes by the journal's block
   clause (FP = []), and the block stays live (the abstract blocks are unchanged). Its shadow is the allocator
   record's block shadow in every state, the block bounds its length below MALLOC_MAX, and the record fact
   cr_heap_tail gives the bytes after its terminator; so cwc_strk holds at the later state. The word slot w + 8j
   lies in a live block of the harness, so its shadow byte is the block's: 0 for every granule the block covers
   whole. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YI04 YI00 YO0a YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaArt PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_chain_c check_words_chain_s0 check_words_chain_iv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HR : CwcRec B RLO RHI.
Hypothesis LAWS : AR_laws SEGS B.

(* the shadow byte of the granule that holds an 8-byte word inside a live block is 0 *)
Lemma cwc_word_shadow0 : forall ly S (W : world SEGS) mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a -> a + 8 <= p + req_size n ->
rdW W mem (SHADOW_OFF + a / 8) = Some 0.
Proof.
intros ly S W mem md p n a HAR Hin Hpa Han.
destruct (al_shadow _ _ LAWS _ _ _ _ _ p n HAR Hin) as [(Hp8 & Hn0 & Hc) _].
assert (Hi0 : 0 <= (a - p) / 8) by (apply Z.div_pos; lia).
assert (Hi1 : (a - p) / 8 < req_size n / 8).
{ assert (H1 : (a - p) / 8 <= (req_size n + (-1) * 8) / 8) by (apply Z.div_le_mono; lia).
  rewrite Z.div_add in H1 by lia. lia. }
assert (Hi2 : (a - p) / 8 < (req_size n + 7) / 8).
{ assert (req_size n / 8 <= (req_size n + 7) / 8) by (apply Z.div_le_mono; lia). lia. }
specialize (Hc ((a - p) / 8) (conj Hi0 Hi2)).
apply Z.ltb_lt in Hi1. rewrite Hi1 in Hc.
assert (Ea : a / 8 = p / 8 + (a - p) / 8).
{ pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. rewrite Hp8, Z.add_0_r in Dp.
  replace a with ((a - p) + (p / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
unfold shadow_of_addr in Hc. rewrite Ea, Z.add_assoc. exact Hc.
Qed.

(* a string in a live block over the entry's memory holds again over a later memory of the walk: the journal's
   block clause keeps its bytes, and the block stays live *)
Lemma cwc_sblk_now : forall STK sp0 ly S W mem md own S2 mem' md' k p x,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 [] ly S W mem md own ly S2 W mem' md' k ->
ablocks B ly S2 = ablocks B ly S ->
cwc_sblk B ly S (rdW W mem) p x -> cwc_sblk B ly S2 (rdW W mem') p x.
Proof.
intros STK sp0 ly S W mem md own S2 mem' md' k p x HAR0 HJ Eab (Hp & Hblk & [Hb Hnz]).
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof Hblk as (q & kq & Hin & Hq1 & Hq2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q kq HAR0 Hin) as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (req_size_pos kq ltac:(lia)) as [Hr1 Hr2].
split; [exact Hp|]. split; [rewrite Eab; exact Hblk|]. split; [|exact Hnz].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
replace (p + Z.of_nat i) with (q + (p + Z.of_nat i - q)) by lia.
rewrite (F2 q kq (p + Z.of_nat i - q) Hin ltac:(rewrite Eab; exact Hin) ltac:(lia)
  ltac:(intros X; exact (inFP_nil _ X))).
replace (q + (p + Z.of_nat i - q)) with (p + Z.of_nat i) by lia.
apply Hb. rewrite length_app. cbn [length]. lia.
Qed.

(* the string facts the wrapper contracts take, for a string in a live block: the block bounds its length below
   MALLOC_MAX, so below 2 ^ 32, and gives its bytes' presence and shadow; the record gives the bytes after its
   terminator *)
Lemma cwc_strk_of_sblk : forall ly S (W : world SEGS) mem md p x,
AR SEGS B ly S W mem md ->
cwc_sblk B ly S (rdW W mem) p x -> cwc_strk W mem p x.
Proof.
intros ly S W mem md p x HAR HSB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cr_heap_tail B RLO RHI HR ly S W mem md p x HAR HSB) as Htail.
destruct HSB as (Hp & (q & kq & Hin & Hq1 & Hq2) & HstrR).
assert (HS : astr_at SEGS W mem p x) by (apply astr_atR_view; exact HstrR).
assert (Hvis : forall a, p <= a < p + (astr_len x + 1) -> rdW W mem a <> None).
{ intros a Ha. destruct HstrR as [Hbytes _].
  specialize (Hbytes (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; unfold astr_len in Ha; lia)).
  replace (p + Z.of_nat (Z.to_nat (a - p))) with a in Hbytes by lia. rewrite Hbytes. discriminate. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ q kq HAR Hin) as (H16 & H4096 & Hceil & Hia & Hpres & Hnd & Hk).
pose proof (req_size_pos kq ltac:(lia)) as [Hr1 Hr2].
assert (Hrq : req_size kq <= Z.max kq 1) by (unfold req_size; destruct (Z.eqb_spec kq 0); lia).
unfold MALLOC_MAX in Hk. unfold astr_len in *.
split; [lia|]. split; [exact HS|]. split; [|exact Htail]. unfold cwc_rd, astr_len.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hvis|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md q kq p (Z.of_nat (length x) + 1) HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md q kq p (Z.of_nat (length x) + 1) HAR Hin ltac:(lia) ltac:(lia))|].
intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md q kq p (Z.of_nat (length x) + 1) HAR Hin ltac:(lia) ltac:(lia) Hpos).
Qed.

(* slot j of the harness's word array, over a later memory of the walk *)
Lemma cwc_wordk_now : forall STK sp0 ly S W mem md own S2 mem' md' k wp j v,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 [] ly S W mem md own ly S2 W mem' md' k ->
ablocks B ly S2 = ablocks B ly S ->
in_blockA (ablocks B ly S) (wp + 8 * j) 8 ->
aval_mem (rdW W mem) (wp + 8 * j) 8 v ->
cwc_wordk W mem' wp j v.
Proof.
intros STK sp0 ly S W mem md own S2 mem' md' k wp j v HAR0 HJ Eab (q & kq & Hin & Hq1 & Hq2) Hv.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q kq HAR0 Hin) as (H16 & H4096 & Hceil & Hia & Hpres & Hnd & Hk).
pose proof (req_size_pos kq ltac:(lia)) as [Hr1 Hr2].
split; [lia|]. split; [lia|]. split.
- intros i Hi. replace (wp + 8 * j + Z.of_nat i) with (q + (wp + 8 * j + Z.of_nat i - q)) by lia.
  rewrite (F2 q kq (wp + 8 * j + Z.of_nat i - q) Hin ltac:(rewrite Eab; exact Hin) ltac:(lia)
    ltac:(intros X; exact (inFP_nil _ X))).
  replace (q + (wp + 8 * j + Z.of_nat i - q)) with (wp + 8 * j + Z.of_nat i) by lia. exact (Hv i Hi).
- apply (cwc_word_shadow0 ly S2 W mem' md' q kq); [exact HAR' | rewrite Eab; exact Hin | lia | lia].
Qed.

(* the thirteen saved registers as the prologue leaves them in the stack region (check_words_chain_s1.v's
   ss_cwc_sm, region 2) *)
Definition cwc_ch2 : list YP09.chunk :=
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Lemma cwc_frame_of_region2 : forall E m sp0 (regs : bvmap 5 word) wlo whi cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-104) 0 wlo whi cs) ->
incl cwc_ch2 cs ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
cwc_frame m sp0 regs.
Proof.
intros E m sp0 regs wlo whi cs HRg Hinc Hsp HE j rr Hj.
assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some cwc_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 rr))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
do 13 (destruct j as [|j];
[ cbn in Hj; injection Hj as <-;
  lazymatch goal with |- val_mem _ _ (_ + ?odx) _ (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
  let od' := eval vm_compute in odx in change odx with od';
  let nn := eval vm_compute in (Z.to_nat R) in
  eapply field_of_region with (cs := cs) (od := od') (w := 8%N) (e := SOff nn 0);
  [ exact HRg | exact Hsp | apply Hinc; cbn; tauto
  | cbn [sv_denot]; rewrite (HE nn (Z_to_bv 5 R) ltac:(lia) eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
  | exact HRr | cbn; lia ] end
| ]). cbn in Hj13. lia.
Qed.

(* a signed compare of two small words is the compare of their values *)
Lemma cwc_blt_small : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. rewrite branch_lt, !unsigned_lit_small by lia. rewrite !s64_small by lia. reflexivity.
Qed.

(* the loop head's registers s8 = s9 = w + 16, as the set-up computes them (0x89298 s8 := w + 16, 0x892ac
   s9 := s8) *)
Lemma cwc_word16 : forall (E : env) wp, bv_unsigned (ew E 11) = wp ->
Z_to_bv 64 (bv_unsigned (ew E 11) + 16) = w64 (wp + 8 * 2).
Proof. intros E wp H11. rewrite H11. unfold w64. f_equal; lia. Qed.

End e.
End c.
End b.
