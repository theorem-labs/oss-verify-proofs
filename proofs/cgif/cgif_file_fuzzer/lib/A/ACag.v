(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACai.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma U_mulw_hw : forall E nh nw h w, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w ->
0 <= h < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> h * w < 2 ^ 31 ->
U E (SMdw M_MUL (SOff nh 0) (SOff nw 0)) = h * w.
Proof.
intros E nh nw h w Hh Hw Rh Rw Hp.
assert (Hp0 : 0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite (U_atom E nh h Hh), (U_atom E nw w Hw) by lia.
rewrite (Z.mod_small h), (Z.mod_small w) by lia.
rewrite swrap32_small by lia. apply wrap64_small. lia.
Qed.
Lemma denot_mulw_hw : forall E nh nw h w, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w ->
0 <= h < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> h * w < 2 ^ 31 ->
sv_denot E (SMdw M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (h * w).
Proof. intros. rewrite denot_lit_U. f_equal. apply U_mulw_hw; assumption. Qed.
Lemma val_mem_mod4 : forall m a v, val_mem SEGS m a 4 v -> val_mem SEGS m a 4 (v mod 2 ^ 32).
Proof.
intros m a v H k Hk. rewrite (H k Hk). do 2 f_equal. unfold YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Section K.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma region_kept_tlzw_stack : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs,
tlzw_kept SEGS B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> alloc_ceiling <= b + lo -> b + hi <= 2 ^ 64 -> sp <= b + lo ->
(b + hi <= pR \/ pR + 12 <= b + lo) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs (K1 & _) Hn Hceil H64 Hsp HpR Hp2.
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply K1; [lia | unfold LZW_TSTK, ASTACK; lia | lia].
- intros _. apply (apresent_writable SEGS). apply Hp2. lia.
Qed.
Lemma region_kept_tlzw_frame : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs cid pos,
tlzw_kept SEGS B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(b + hi <= pR \/ pR + 12 <= b + lo) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs cid pos (_ & _ & _ & K4 & _) Hn Hin Hlo Hhi HpR Hp2.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | lia].
- intros _. apply (apresent_writable SEGS). apply Hp2. lia.
Qed.
Lemma region_kept_tlzw_fshadow : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs cid pos,
tlzw_kept SEGS B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
shadow_addr (frame_addr lyc cid pos) <= b + lo -> b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
(b + hi <= pR \/ pR + 12 <= b + lo) -> whi <= wlo ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs cid pos (_ & _ & _ & K4 & _) Hn Hin Hlo Hhi HpR Hro.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview SEGS). apply (K4 cid pos a Hin); [right; unfold in_zr; cbn [fst snd]; lia | lia].
Qed.
Lemma region_kept_tlzw_block : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs m,
tlzw_kept SEGS B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs m (_ & K2 & _) Hn Hin Hlo Hhi HnE Hp2.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp2. lia.
Qed.
End K.
End e.
End d.
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
Ltac keptLZW HK AG Hp4 Hfin3 HfinS3 EFA3 F HFp4 Hraw3 Hing3 Hrp4 ErR ErG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
let Bv := rnB in
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | unbox; lia | unbox; lia | unbox; lia | first [left; lia | right; lia] | intros a Ha; apply Hp4; lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ HK);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; lia
| left; lia | intros a Ha; apply (fun H => proj1 (HFp4 a H)); lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_fshadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ HK);
[ evalE AG | exact Hfin3
| unfold shadow_addr; rewrite <- SB_SHADOW_OFF, EFA3; fold F; unfold SB; lia
| unfold shadow_addr; rewrite <- SB_SHADOW_OFF, EFA3; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; lia
| left; unfold SB; lia | lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | left; lia | intros a Ha; lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | ErR | intros a Ha; apply (fun H => proj1 (Hrp4 a H)); lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; lia | ErG | intros a Ha; lia ]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 55%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 55%nat (as_uar_cell Bv) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 250%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 9) (pa_val (A_OBJ 9)) 8 (pa_val A_TEXT + AF_asan3_cgif_raw_addframe));
[exact (H (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
end.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
End g.
End f.
