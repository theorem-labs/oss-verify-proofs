(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YCfy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw YCgl YChb YChi.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ctx_lzw1 : forall l, In l CTX_cgif_raw_addframe -> In (0x89a24 :: l) CTX_LZW_GenerateStream.
Proof. intros l Hl. cbn in Hl. repeat (destruct Hl as [<- | Hl]; [cbn; tauto|]); destruct Hl. Qed.
Lemma ctx_lzw2 : forall l, In l CTX_cgif_raw_addframe -> In (0x89dac :: l) CTX_LZW_GenerateStream.
Proof. intros l Hl. cbn in Hl. repeat (destruct Hl as [<- | Hl]; [cbn; tauto|]); destruct Hl. Qed.
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
Lemma val_mem_mod4 : forall m a v, val_mem trbsegs m a 4 v -> val_mem trbsegs m a 4 (v mod 2 ^ 32).
Proof.
intros m a v H k Hk. rewrite (H k Hk). do 2 f_equal. unfold YP0g.le_byte.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Section K.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Lemma region_kept_tlzw_stack : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs,
tlzw_kept B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> alloc_ceiling <= b + lo -> b + hi <= 2 ^ 64 -> sp <= b + lo ->
(b + hi <= pR \/ pR + 12 <= b + lo) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs (K1 & _) Hn Hceil H64 Hsp HpR Hp2.
pose proof asan_consts as (C1 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply K1; [lia | unfold LZW_TSTK, ASTACK; lia | lia].
- intros _. apply (apresent_writable trbsegs). apply Hp2. lia.
Qed.
Lemma region_kept_tlzw_frame : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs cid pos,
tlzw_kept B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(b + hi <= pR \/ pR + 12 <= b + lo) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs cid pos (_ & _ & _ & K4 & _) Hn Hin Hlo Hhi HpR Hp2.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | lia].
- intros _. apply (apresent_writable trbsegs). apply Hp2. lia.
Qed.
Lemma region_kept_tlzw_fshadow : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs cid pos,
tlzw_kept B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
shadow_addr (frame_addr lyc cid pos) <= b + lo -> b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
(b + hi <= pR \/ pR + 12 <= b + lo) -> whi <= wlo ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs cid pos (_ & _ & _ & K4 & _) Hn Hin Hlo Hhi HpR Hro.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview trbsegs). apply (K4 cid pos a Hin); [right; unfold in_zr; cbn [fst snd]; lia | lia].
Qed.
Lemma region_kept_tlzw_block : forall E lyc Sc W memc W2 mem2 sp pR (Er : Z -> Prop) n b lo hi wlo whi cs m,
tlzw_kept B lyc Sc W memc W2 mem2 sp pR Er ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept trbsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 sp pR Er n b lo hi wlo whi cs m (_ & K2 & _) Hn Hin Hlo Hhi HnE Hp2.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable trbsegs). apply Hp2. lia.
Qed.
End K.
End d.
Definition chunk_in (lo hi : Z) (c : YQ0b.chunk) : bool :=
Z.leb lo (YQ0b.c_off c) && Z.leb (YQ0b.c_off c + YQ0b.c_len c) hi.
Definition trim_region (r : YQ0b.region) (lo hi : Z) : YQ0b.region :=
YQ0b.mkRegion (YQ0b.r_base r) lo hi (Z.max (YQ0b.r_wlo r) lo) (Z.min (YQ0b.r_whi r) hi)
(filter (chunk_in lo hi) (YQ0b.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YQ0b.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
Ltac keptLZW HK AG Hp4 Hfin3 HfinS3 EFA3 F HFp4 Hraw3 Hing3 Hrp4 ErR ErG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | unbox; lia | unbox; lia | unbox; lia | first [left; lia | right; lia] | intros a Ha; apply Hp4; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 57%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ HK);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; lia
| left; lia | intros a Ha; apply (fun H => proj1 (HFp4 a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_fshadow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ HK);
[ evalE AG | exact Hfin3
| unfold shadow_addr; rewrite <- SB_SHADOW_OFF, EFA3; fold F; unfold SB; lia
| unfold shadow_addr; rewrite <- SB_SHADOW_OFF, EFA3; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; lia
| left; unfold SB; lia | lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | left; lia | intros a Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | ErR | intros a Ha; apply (fun H => proj1 (Hrp4 a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_tlzw_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK);
[ evalE AG | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; lia | ErG | intros a Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_rawadd _ _ _ _) => apply (region_kept_val trbsegs _ _ _ A_GOT_rawadd 8 A_cgif_raw_addframe); [exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_rawadd ];
keptLZW HK AG Hp4 Hfin3 HfinS3 EFA3 F HFp4 Hraw3 Hing3 Hrp4 ErR ErG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ra_trace_in : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX_cgif_raw_addframe -> raZ regsT = ra ->
((pcf = 0x53508 /\ ra = 0x89db8) \/ (pcf = 0x53508 /\ ra = 0x8a0a0) \/ (pcf = 0x53668 /\ ra = 0x89a34)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) Trb_universe.
Proof.
intros pcf ra regsT regs ch Hctx Hra Hpc.
rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). rewrite Hra.
cbn [CTX_cgif_raw_addframe In] in Hctx.
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]];
(repeat (destruct Hctx as [H | Hctx]; [rewrite <- H; apply TRACES_cgif_raw_addframe_U; vm_compute; repeat (first [left; reflexivity | right])|]); destruct Hctx).
Qed.
End e.
