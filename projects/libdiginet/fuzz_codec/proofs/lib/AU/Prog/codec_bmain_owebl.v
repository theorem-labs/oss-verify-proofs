(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 636 of its 666 lines of code are new or changed and 219 lines of the source are left out. *)
(* The owe() segments of the image-B walk of LLVMFuzzerTestOneInput that call owe_sysex (lib/AU/Prog/codec_bmain_inv.v
   seg_owe 9 and 11; image A inlines owe_sysex, image B calls it at 0x82f70 / 0x8308c): the cut facts with the
   frame's shadow map as a parameter, and the call of owe_sysex through its image-B contract.
   - mcom_sh g pos sp1 sh s9v: codec_bmain_inv.v's mcommon with the frame's 60 shadow bytes the list sh and s9
     the value s9v; mcommon .. kv is mcom_sh .. (shm kv) (F + 448) (mcom_sh_of / mcommon_of_sh). SCRIBBLE (OWE9)
     calls owe_sysex while the shadow bytes 6, 7 of its 10-byte payload at F + 48 read 00 02 (marked usable) and s9
     holds the shadow address of desk + 10 (0x82958; s9 is reloaded at 0x82dd0), so that state is no mcommon.
   - bm_facts_sh, bm_base_ok_sh, bm_entry_sh, bm_exit_sh, bm_call_kept_sh: codec_bmain_st.v's bm_facts, bm_base_ok,
     bm_entry, bm_exit and codec_bmain_headl.v's bm_call_kept_x over mcom_sh, with the same proofs (none of them reads
     the shadow clause except to carry it). The entry state's register file is bm_sregs9 (s9 an atom of its own,
     bm_ss9); the exit checks the eleven other fixed registers (bm_keep_ok9) and takes s9's value as a premise.
   - bm_owe_sysex_at: from the cut facts at owe_sysex's entry, cdcU_owe_sysex_specX at BM_owe_sysex and a
     continuation from the return state: k with want, want_len and want_display owe_sysex's answer, the frame off
     [F + 336, F + 376) kept. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgSatU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_headl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ================================ the cut facts with a shadow map ================================ *)
Definition mcom_sh (g : ectx) (pos sp1 : Z) (sh : list Z) (s9v : Z) (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
e_pre B MT K XM_LIB g /\
(* the machine frame: 0x8099c addi sp,sp,-320; 0x809dc andi sp,sp,-32; 0x809e0 mv s1,sp; 0x809d8 addi s0,sp,320 *)
sp1 = 32 * ((e_sp0 g - 320) / 32) /\
getr regs2 2 = w64 sp1 /\ getr regs2 9 = w64 sp1 /\ getr regs2 8 = w64 (e_sp0 g) /\
getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
(* 0x809fc s5 = the shadow offset; 0x80a50 + 0x80a7c s2 = shadow_addr F; 0x80a54 s11 = -8; 0x80b94 s7 = k;
   0x80bac s9 = the dots byte; 0x80c10 s3 = sp1 + 216; 0x80bf0 s10 = 1 *)
getr regs2 21 = w64 SHADOW_OFF /\ getr regs2 18 = w64 (shadow_addr (FA g pos)) /\ getr regs2 27 = w64 (-8) /\
getr regs2 23 = w64 (FA g pos + 192) /\ getr regs2 25 = w64 s9v /\
getr regs2 19 = w64 (sp1 + 216) /\ getr regs2 26 = w64 1 /\
(* the frame is 64-aligned (lib/AU/YCem.v frame_al64) *)
FA g pos mod 64 = 0 /\
(* the spills, 0x80b80-0x80c2c (k = F + 192) *)
val_mem tfibsegs (rd W2 mem2) (sp1 + 16) 8 (FA g pos + 192 + 47) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 24) 8 (FA g pos + 192 + 144) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 32) 8 (FA g pos + 50) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 40) 8 (FA g pos + 192 + 148) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 48) 8 0x990 /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 56) 8 0x5cb0 /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 64) 8 (FA g pos + 48) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 72) 8 (FA g pos) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 80) 8 (FA g pos) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 88) 8 (FA g pos + 34) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 96) 8 (FA g pos + 33) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 104) 8 (FA g pos + 80) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 112) 8 (FA g pos + 32) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 120) 8 (FA g pos + 192 + 40) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 128) 8 (FA g pos + 448) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 136) 8 (FA g pos + 192 + 168) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 144) 8 (FA g pos + 192 + 108) /\
val_mem tfibsegs (rd W2 mem2) (sp1 + 152) 8 (FA g pos + 192 + 76) /\
(* the thirteen saved words, which the epilogue restores (0x809a4-0x809d4, 0x8367c-0x836ac) *)
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 8) 8 (raZ (e_regs g)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 16) 8 (bv_unsigned (getr (e_regs g) 8)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
val_mem tfibsegs (rd W2 mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)) /\
(* the flag address the frame request wrote at F + 504, which the release reads (0x83578) *)
val_mem tfibsegs (rd W2 mem2) (FA g pos + 504) 8 (flag_addr (e_ly g) 3 pos) /\
(* the frame's 60 shadow bytes *)
(forall i, 0 <= i < 60 ->
 aview tfibsegs (w_H W2) mem2 (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) sh 0)) /\
(* the input bytes (the journal keeps them: this walk's footprint is empty) and the heap blocks *)
garr8 tfibsegs (rd W2 mem2) (e_p g) (map (fun b : byte => bv_unsigned b) (e_pl g)) /\
Permutation (ablocks B ly2 S2) (ablocks B (e_ly g) (e_S g)).

Lemma mcom_sh_of : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2,
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 -> mcom_sh g pos sp1 (shm kv) (FA g pos + 448) ly2 S2 W2 regs2 mem2 md2.
Proof. intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 H. exact H. Qed.
Lemma mcommon_of_sh : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2,
mcom_sh g pos sp1 (shm kv) (FA g pos + 448) ly2 S2 W2 regs2 mem2 md2 -> mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2.
Proof. intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 H. exact H. Qed.

(* the entry state's registers with s9 an atom of its own, and the exit's fixed registers without s9 *)
Definition bm_sregs9 : list sv := sr_set bm_sregs 25%bv (SOff 25 0).
Definition bm_ss9 (pc : Z) (rs : smem) (AF : list (nat * afact)) : sstate :=
mkSS pc bm_sregs9 (bm_regs ++ rs) None (mkFacts (bm_atoms ++ AF) [] []).
Definition BM_KEEPR9 : list (bv 5) := [2; 9; 8; 3; 4; 21; 18; 27; 23; 19; 26]%bv.
Definition bm_keep_ok9 (sr : list sv) : bool :=
forallb (fun r => sv_eqb (sr_get sr r) (sr_get bm_sregs r)) BM_KEEPR9.

(* ================================ the bridges over mcom_sh ================================ *)
Lemma bm_facts_sh : forall g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcom_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 ->
frame_addr ly2 3 pos = FA g pos /\ FA g pos mod 64 = 0 /\ 4096 <= FA g pos /\
FA g pos + fs_frame_bytes 3 <= alloc_ceiling /\ 480 <= fs_frame_bytes 3 /\ alloc_ceiling <= BM_HI /\
0x7fff7f800000 <= alloc_ceiling /\
sp1 mod 32 = 0 /\ e_sp0 g - 352 < sp1 <= e_sp0 g - 320 /\ alloc_ceiling + LLVMF_STK <= e_sp0 g /\
e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\
(forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W2) mem2 a) /\
0 <= e_n g < 2 ^ 26 /\ 4096 <= e_p g /\ e_p g + e_n g <= BM_HI /\
(0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2) /\ In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g))).
Proof.
intros g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK & Hceil & Hslo & Hshi & H47 & _).
pose proof HC as (Hpre & Hsp1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (EFA : frame_addr ly2 3 pos = FA g pos).
{ unfold FA, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). lia. }
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (Hf4096 & Hfceil & _).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (Hf64 & _).
assert (FS3 : 480 <= fs_frame_bytes 3) by (apply Z.leb_le; vm_compute; reflexivity).
rewrite EFA in Hf4096, Hfceil, Hf64.
unfold e_pre, codec_lib_pre_x in Hpre.
destruct Hpre as (HFN & _ & _ & _ & Hpn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HFN as (HAR0 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hblk : 0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2) /\ In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g))).
{ intros Hn. destruct Hpn as [[Hn0 _] | [_ Hb]]; [lia|]. split; [|exact Hb].
  pose proof HC as HPerm. do 49 (destruct HPerm as (_ & HPerm)).
  eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]. }
assert (Hinput : 0 <= e_n g < 2 ^ 26 /\ 4096 <= e_p g /\ e_p g + e_n g <= BM_HI).
{ destruct Hpn as [[-> ->] | [Hn Hb]]; [unfold A_EMPTY, BM_HI; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hb) as (_ & H4096 & Hbc & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq). unfold BM_HI. lia. }
assert (Hsp : e_sp0 g - 352 < sp1 <= e_sp0 g - 320 /\ sp1 mod 32 = 0).
{ rewrite Hsp1. pose proof (Z.div_mod (e_sp0 g - 320) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (e_sp0 g - 320) 32 ltac:(lia)) as M.
  split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
destruct Hinput as (Hn & Hp & Hpn'). destruct Hsp as ((Hsp1a & Hsp1b) & Hsp32).
unfold BM_HI in *.
split; [exact EFA|]. split; [exact Hf64|]. split; [lia|]. split; [lia|]. split; [exact FS3|].
split; [lia|]. split; [lia|]. split; [exact Hsp32|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [exact Hal16|]. split; [exact Hpres|]. split; [lia|]. split; [lia|]. split; [lia|].
exact Hblk.
Qed.

Lemma bm_base_ok_sh : forall g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k c ys,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcom_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 ->
0 <= c <= e_n g ->
regs_ok (bm_env g pos c regs2 ys) bm_sregs9 regs2 /\
Forall (region_ok tfibsegs (bm_env g pos c regs2 ys) (mrestrict (w_H W2) mem2)) bm_regs0 /\
pairwise_disjoint (bm_env g pos c regs2 ys) bm_regs /\
atoms_ok (bm_env g pos c regs2 ys) bm_atoms.
Proof.
intros g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k c ys HJ Hfr HC Hc.
destruct (bm_facts_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
pose proof HJ as (HAR & _). unfold BM_HI in Hchi, Hpn.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R21 & R18 & R27 & R23 & R25 & R19 & R26 & HF64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 & V128 & V136 & V144 & V152 & _).
set (F := FA g pos) in *.
set (E := bm_env g pos c regs2 ys).
assert (EF : ew E 33 = Z_to_bv 64 F) by exact (bm_ew_F g pos c regs2 ys).
assert (ESH : ew E 34 = Z_to_bv 64 (shadow_addr F)) by exact (bm_ew_SH g pos c regs2 ys).
assert (ECP : ew E 35 = Z_to_bv 64 (e_p g + c)) by exact (bm_ew_CP g pos c regs2 ys).
assert (ECN : ew E 36 = Z_to_bv 64 (e_n g - c)) by exact (bm_ew_CN g pos c regs2 ys).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (bm_ew_SB g pos c regs2 ys).
assert (E2 : ew E 2 = getr regs2 2) by exact (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (E2' : ew E 2 = Z_to_bv 64 sp1) by (rewrite E2, R2; reflexivity).
assert (Hsh : SB + 512 <= shadow_addr F <= SB + 2 ^ 44 /\ shadow_addr F mod 8 = 0).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF.
  pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite Hf64, Z.add_0_r in D.
  assert (E8 : F / 8 = 8 * (F / 64)).
  { rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  rewrite E8. unfold SB, BM_HI in *. split; [lia|].
  replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia. apply Z.mod_mul. lia. }
split; [|split; [|split]].
- (* the registers *)
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  assert (O9 : getr regs2 9 = sv_denot E (SOff 2 0)) by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E2, R9, R2; reflexivity).
  assert (O18 : getr regs2 18 = sv_denot E (SOff 34 0)) by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ESH, R18; reflexivity).
  assert (O19 : getr regs2 19 = sv_denot E (SOff 2 216)) by (rewrite (bm_den_off E 2 sp1 216 E2') by lia; rewrite R19; reflexivity).
  assert (O21 : getr regs2 21 = sv_denot E (SOff 32 0)) by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32, R21; reflexivity).
  assert (O23 : getr regs2 23 = sv_denot E (SOff 33 192)) by (rewrite (bm_den_off E 33 F 192 EF) by lia; rewrite R23; reflexivity).
  assert (O26 : getr regs2 26 = sv_denot E (SLit 1)) by (cbn [sv_denot]; rewrite R26; reflexivity).
  assert (O27 : getr regs2 27 = sv_denot E (SLit 18446744073709551608)).
  { cbn [sv_denot]. rewrite R27. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
  repeat (destruct Hr as [<-|Hr];
  [ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
      let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    first [ exact O9 | exact O18 | exact O19 | exact O21 | exact O23 | exact O26 | exact O27
          | cbn [sv_denot];
            first [ rewrite getr_zero; reflexivity
                  | subst E; unfold bm_env; rewrite Z.add_0_r, ew_Ereg_lt by lia;
                    match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr _ ?x)) =>
                      let y := eval vm_compute in x in change x with y end;
                    rewrite Z_to_bv_bv_unsigned; reflexivity ] ]
  | ]).
  destruct Hr.
- (* the base regions *)
  apply Forall_app. split.
  + apply (cw_regs_ok B TL LAWS 0 (bm_xs g pos c ++ ys) ly2 S2 W2 regs2 mem2 md2 HAR ltac:(lia)).
    * unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    * intros a Ha. lia.
  + constructor; [|constructor].
    unfold bm_spill_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold bm_spill_chunks.
    assert (DF : forall o, 0 <= o < 512 -> sv_denot E (SOff 33 o) = Z_to_bv 64 (F + o))
      by (intros o Ho; apply (bm_den_off E 33 F o EF); lia).
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val tfibsegs E _ sp1 16 8 (SOff 33 239) (F + 192 + 47)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V16].
    * apply (chunk_ok_val tfibsegs E _ sp1 24 8 (SOff 33 336) (F + 192 + 144)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V24].
    * apply (chunk_ok_val tfibsegs E _ sp1 32 8 (SOff 33 50) (F + 50)); [rewrite DF by lia; reflexivity | zside | zside | exact V32].
    * apply (chunk_ok_val tfibsegs E _ sp1 40 8 (SOff 33 340) (F + 192 + 148)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V40].
    * apply (chunk_ok_val tfibsegs E _ sp1 48 8 (SLit 0x990) 0x990); [reflexivity | zside | zside | exact V48].
    * apply (chunk_ok_val tfibsegs E _ sp1 56 8 (SLit 0x5cb0) 0x5cb0); [reflexivity | zside | zside | exact V56].
    * apply (chunk_ok_val tfibsegs E _ sp1 64 8 (SOff 33 48) (F + 48)); [rewrite DF by lia; reflexivity | zside | zside | exact V64].
    * apply (chunk_ok_val tfibsegs E _ sp1 72 8 (SOff 33 0) F); [rewrite DF by lia; f_equal; lia | zside | zside | exact V72].
    * apply (chunk_ok_val tfibsegs E _ sp1 80 8 (SOff 33 0) F); [rewrite DF by lia; f_equal; lia | zside | zside | exact V80].
    * apply (chunk_ok_val tfibsegs E _ sp1 88 8 (SOff 33 34) (F + 34)); [rewrite DF by lia; reflexivity | zside | zside | exact V88].
    * apply (chunk_ok_val tfibsegs E _ sp1 96 8 (SOff 33 33) (F + 33)); [rewrite DF by lia; reflexivity | zside | zside | exact V96].
    * apply (chunk_ok_val tfibsegs E _ sp1 104 8 (SOff 33 80) (F + 80)); [rewrite DF by lia; reflexivity | zside | zside | exact V104].
    * apply (chunk_ok_val tfibsegs E _ sp1 112 8 (SOff 33 32) (F + 32)); [rewrite DF by lia; reflexivity | zside | zside | exact V112].
    * apply (chunk_ok_val tfibsegs E _ sp1 120 8 (SOff 33 232) (F + 192 + 40)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V120].
    * apply (chunk_ok_val tfibsegs E _ sp1 128 8 (SOff 33 448) (F + 448)); [rewrite DF by lia; reflexivity | zside | zside | exact V128].
    * apply (chunk_ok_val tfibsegs E _ sp1 136 8 (SOff 33 360) (F + 192 + 168)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V136].
    * apply (chunk_ok_val tfibsegs E _ sp1 144 8 (SOff 33 300) (F + 192 + 108)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V144].
    * apply (chunk_ok_val tfibsegs E _ sp1 152 8 (SOff 33 268) (F + 192 + 76)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V152].
- (* the base regions are pairwise disjoint *)
  apply pairwise_disjoint_of_extents.
  unfold bm_regs, bm_regs0, cw_regs, bm_spill_region, bm_cur_region, stack_region, got_region, bcell_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U2.
  unfold A_GOT_shadow, A_shadow_glob.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- (* the atom facts *)
  unfold bm_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U2, E32, EF, ESH, ECP, ECN.
  rewrite !unsigned_lit_small by (unfold SB, BM_HI in *; lia).
  change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, BM_HI in *. repeat split; lia.
Qed.

Lemma bm_entry_sh : forall g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k c pc ys (rs : smem) (AF : list (nat * afact)),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcom_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
regions_wf rs = true ->
Forall (region_ok tfibsegs (bm_env g pos c regs2 ys) (mrestrict (w_H W2) mem2)) rs ->
pairwise_disjoint (bm_env g pos c regs2 ys) rs ->
Forall (fun r => all_disjoint (bm_env g pos c regs2 ys) r bm_regs) rs ->
atoms_ok (bm_env g pos c regs2 ys) AF ->
st_ok tfibsegs (bm_env g pos c regs2 ys) (bm_ss9 pc rs AF)
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k c pc ys rs AF HJ Hfr HC Hcur Hwf Hrs Hpd Hap HAF.
pose proof Hcur as (Hc & C184 & C192).
destruct (bm_base_ok_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k c ys HJ Hfr HC Hc) as (Hregs & Hbase & Hbpd & Hat).
destruct (bm_facts_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & Hchi & Hclo & _ & Hsp & Hsp0c & Hsp047 & _ & Hpres & Hn & Hp & Hpn & _).
pose proof HC as (_ & _ & R2 & _).
unfold BM_HI in Hchi, Hpn.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (E2 : ew (bm_env g pos c regs2 ys) 2 = getr regs2 2) by exact (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl).
assert (U2 : bv_unsigned (ew (bm_env g pos c regs2 ys) 2) = sp1) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold bm_ss9. apply (entry_st_ok_full tfibsegs).
all: change (Ereg regs2 (cw_extra (bm_xs g pos c ++ ys))) with (bm_env g pos c regs2 ys).
- exact Hregs.
- rewrite regions_wf_app, Hwf. reflexivity.
- apply Forall_app. split; [|exact Hrs]. unfold bm_regs. apply Forall_app. split; [exact Hbase|].
  constructor; [|constructor].
  unfold bm_cur_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
  split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
  + constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val tfibsegs (bm_env g pos c regs2 ys) _ sp1 184 8 (SOff 35 0) (e_p g + c));
      [rewrite (bm_den_off (bm_env g pos c regs2 ys) 35 (e_p g + c) 0 (bm_ew_CP g pos c regs2 ys)) by (unfold BM_HI in *; lia); f_equal; lia
      | unfold BM_HI in *; zside | zside | exact C184].
    * apply (chunk_ok_val tfibsegs (bm_env g pos c regs2 ys) _ sp1 192 8 (SOff 36 0) (e_n g - c));
      [rewrite (bm_den_off (bm_env g pos c regs2 ys) 36 (e_n g - c) 0 (bm_ew_CN g pos c regs2 ys)) by lia; f_equal; lia
      | zside | zside | exact C192].
- apply bm_pd_app; [exact Hbpd | exact Hpd | exact Hap].
- split; [apply bm_atoms_ok_app; [exact Hat | exact HAF]|]. split; exact I.
Qed.

Lemma bm_exit_sh : forall g pos sp1 sh s9v sh' s9v' c ys ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3 pcv ss E,
mcom_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
env_agree 35 (bm_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W3) (mkst regs3 pcv mem3 (seg_rom tfibsegs))) ->
bm_keep_ok9 (ss_regs ss) = true -> getr regs3 25 = w64 s9v' ->
(forall a, bm_keepzone g pos sp1 a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
(forall i, 0 <= i < 60 ->
 aview tfibsegs (w_H W3) mem3 (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) sh' 0)) ->
Permutation (ablocks B ly3 S3) (ablocks B (e_ly g) (e_S g)) ->
mcom_sh g pos sp1 sh' s9v' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros g pos sp1 sh s9v sh' s9v' c ys ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3 pcv ss E
  HC HJ3 HAE HS Hkeep H25 KE HSH HPerm.
pose proof (proj1 HAE) as AG.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R21 & R18 & R27 & R23 & R25 & R19 & R26 & HF64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 & V128 & V136 & V144 & V152 &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & SFL & _ & Hga & _).
pose proof Hpre as HPRE0. unfold e_pre, codec_lib_pre_x in HPRE0.
destruct HPRE0 as (HFN & _ & _ & _ & Hpn & Hnpl & HPL & Hfr0 & _).
pose proof HFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK & Hceil0 & Hslo0 & Hshi0 & H470 & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hfr3 : frames S3 = [(3, pos)]) by (rewrite Hfrs3, Hfr0; reflexivity).
assert (Hin3 : In (3, pos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (EFA3 : frame_addr ly3 3 pos = FA g pos).
{ unfold FA, frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). lia. }
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 mem3 md3 3 pos HAR3 Hin3) as (Hf4096 & Hfceil & _).
rewrite EFA3 in Hf4096, Hfceil.
assert (FS3 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity). rewrite FS3 in Hfceil.
assert (Hsp : e_sp0 g - 352 < sp1 <= e_sp0 g - 320).
{ rewrite Hsp1. pose proof (Z.div_mod (e_sp0 g - 320) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (e_sp0 g - 320) 32 ltac:(lia)) as M. lia. }
assert (Hsp0 : alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g <= 2 ^ 47) by (unfold e_sp0 in *; lia).
destruct Hsp0 as (Hsp0a & Hsp0b).
assert (Hinp : 0 <= e_n g < 2 ^ 26 /\ 4096 <= e_p g /\ e_p g + e_n g <= 0x7fffff800000).
{ destruct Hpn as [[-> ->] | [Hn Hb]]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hb) as (_ & H4096 & Hbc & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq). lia. }
destruct Hinp as (Hng & Hpg & Hpng).
assert (RR : forall (r : bv 5), In r BM_KEEPR9 -> getr regs3 r = sv_denot E (sr_get bm_sregs r)).
{ intros r Hr. pose proof (proj1 (forallb_forall _ _) Hkeep r Hr) as Hb.
  apply sv_eqb_eq in Hb. rewrite <- Hb.
  exact (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regs3 pcv mem3 (seg_rom tfibsegs)) r HS). }
assert (EF : ew E 33 = Z_to_bv 64 (FA g pos))
  by (rewrite (AG 33%nat ltac:(lia)); exact (bm_ew_F g pos c regs2 ys)).
assert (ESH : ew E 34 = Z_to_bv 64 (shadow_addr (FA g pos)))
  by (rewrite (AG 34%nat ltac:(lia)); exact (bm_ew_SH g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (rewrite (AG 32%nat ltac:(lia)); exact (bm_ew_SB g pos c regs2 ys)).
assert (E2 : ew E 2 = Z_to_bv 64 sp1)
  by (rewrite (AG 2%nat ltac:(lia)), (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2; reflexivity).
assert (DOF : forall o, 0 <= o <= 512 -> sv_denot E (SOff 33 o) = w64 (FA g pos + o)).
{ intros o Ho. unfold w64. apply (bm_den_off _ 33 (FA g pos) o EF); lia. }
assert (DAT : forall n (r : bv 5), (n < 35)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot E (SOff n 0) = getr regs2 r).
{ intros n r Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (AG n Hn). apply bm_ew_reg. exact Hr. }
assert (VM : forall a m v, (forall i, 0 <= i < Z.of_nat m -> bm_keepzone g pos sp1 (a + i)) ->
  0 <= a -> a + Z.of_nat m <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a m v -> val_mem tfibsegs (mrestrict (w_H W3) mem3) a m v).
{ intros a m v Hin Ha Ham Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE. replace x with (a + (x - a)) by lia. apply Hin. lia. }
assert (SPZ : forall o, 16 <= o <= 152 -> forall i, 0 <= i < Z.of_nat 8 -> bm_keepzone g pos sp1 (sp1 + o + i))
  by (intros o Ho i Hi; left; cbn in Hi; lia).
assert (SVZ : forall o, 8 <= o <= 104 -> forall i, 0 <= i < Z.of_nat 8 -> bm_keepzone g pos sp1 (e_sp0 g - o + i))
  by (intros o Ho i Hi; right; left; cbn in Hi; lia).
assert (G2 : sr_get bm_sregs 2%bv = SOff 2 0) by (vm_compute; reflexivity).
assert (G9 : sr_get bm_sregs 9%bv = SOff 2 0) by (vm_compute; reflexivity).
assert (G8 : sr_get bm_sregs 8%bv = SOff 8 0) by (vm_compute; reflexivity).
assert (G3 : sr_get bm_sregs 3%bv = SOff 3 0) by (vm_compute; reflexivity).
assert (G4 : sr_get bm_sregs 4%bv = SOff 4 0) by (vm_compute; reflexivity).
assert (G21 : sr_get bm_sregs 21%bv = SOff 32 0) by (vm_compute; reflexivity).
assert (G18 : sr_get bm_sregs 18%bv = SOff 34 0) by (vm_compute; reflexivity).
assert (G27 : sr_get bm_sregs 27%bv = SLit 18446744073709551608) by (vm_compute; reflexivity).
assert (G23 : sr_get bm_sregs 23%bv = SOff 33 192) by (vm_compute; reflexivity).
assert (G25 : sr_get bm_sregs 25%bv = SOff 33 448) by (vm_compute; reflexivity).
assert (G19 : sr_get bm_sregs 19%bv = SOff 2 216) by (vm_compute; reflexivity).
assert (G26 : sr_get bm_sregs 26%bv = SLit 1) by (vm_compute; reflexivity).
unfold mcom_sh.
split; [exact Hpre|]. split; [exact Hsp1|].
split; [rewrite (RR 2%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G2, (DAT 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
split; [rewrite (RR 9%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G9, (DAT 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
split; [rewrite (RR 8%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G8, (DAT 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
split; [rewrite (RR 3%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G3, (DAT 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
split; [rewrite (RR 4%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G4, (DAT 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
split; [rewrite (RR 21%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RR 18%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G18; cbn [sv_denot]; rewrite ESH, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RR 27%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G27; cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
split; [rewrite (RR 23%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G23, (DOF 192 ltac:(lia)); reflexivity|].
split; [exact H25|].
split; [rewrite (RR 19%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G19, (bm_den_off E 2 sp1 216 E2) by lia; reflexivity|].
split; [rewrite (RR 26%bv ltac:(unfold BM_KEEPR9; cbn [In]; tauto)), G26; cbn [sv_denot]; reflexivity|].
split; [exact HF64|].
split; [apply (VM _ 8%nat); [apply (SPZ 16); lia | lia | cbn; lia | exact V16]|].
split; [apply (VM _ 8%nat); [apply (SPZ 24); lia | lia | cbn; lia | exact V24]|].
split; [apply (VM _ 8%nat); [apply (SPZ 32); lia | lia | cbn; lia | exact V32]|].
split; [apply (VM _ 8%nat); [apply (SPZ 40); lia | lia | cbn; lia | exact V40]|].
split; [apply (VM _ 8%nat); [apply (SPZ 48); lia | lia | cbn; lia | exact V48]|].
split; [apply (VM _ 8%nat); [apply (SPZ 56); lia | lia | cbn; lia | exact V56]|].
split; [apply (VM _ 8%nat); [apply (SPZ 64); lia | lia | cbn; lia | exact V64]|].
split; [apply (VM _ 8%nat); [apply (SPZ 72); lia | lia | cbn; lia | exact V72]|].
split; [apply (VM _ 8%nat); [apply (SPZ 80); lia | lia | cbn; lia | exact V80]|].
split; [apply (VM _ 8%nat); [apply (SPZ 88); lia | lia | cbn; lia | exact V88]|].
split; [apply (VM _ 8%nat); [apply (SPZ 96); lia | lia | cbn; lia | exact V96]|].
split; [apply (VM _ 8%nat); [apply (SPZ 104); lia | lia | cbn; lia | exact V104]|].
split; [apply (VM _ 8%nat); [apply (SPZ 112); lia | lia | cbn; lia | exact V112]|].
split; [apply (VM _ 8%nat); [apply (SPZ 120); lia | lia | cbn; lia | exact V120]|].
split; [apply (VM _ 8%nat); [apply (SPZ 128); lia | lia | cbn; lia | exact V128]|].
split; [apply (VM _ 8%nat); [apply (SPZ 136); lia | lia | cbn; lia | exact V136]|].
split; [apply (VM _ 8%nat); [apply (SPZ 144); lia | lia | cbn; lia | exact V144]|].
split; [apply (VM _ 8%nat); [apply (SPZ 152); lia | lia | cbn; lia | exact V152]|].
split; [apply (VM _ 8%nat); [apply (SVZ 8); lia | lia | cbn; lia | exact S8]|].
split; [apply (VM _ 8%nat); [apply (SVZ 16); lia | lia | cbn; lia | exact S16]|].
split; [apply (VM _ 8%nat); [apply (SVZ 24); lia | lia | cbn; lia | exact S24]|].
split; [apply (VM _ 8%nat); [apply (SVZ 32); lia | lia | cbn; lia | exact S32]|].
split; [apply (VM _ 8%nat); [apply (SVZ 40); lia | lia | cbn; lia | exact S40]|].
split; [apply (VM _ 8%nat); [apply (SVZ 48); lia | lia | cbn; lia | exact S48]|].
split; [apply (VM _ 8%nat); [apply (SVZ 56); lia | lia | cbn; lia | exact S56]|].
split; [apply (VM _ 8%nat); [apply (SVZ 64); lia | lia | cbn; lia | exact S64]|].
split; [apply (VM _ 8%nat); [apply (SVZ 72); lia | lia | cbn; lia | exact S72]|].
split; [apply (VM _ 8%nat); [apply (SVZ 80); lia | lia | cbn; lia | exact S80]|].
split; [apply (VM _ 8%nat); [apply (SVZ 88); lia | lia | cbn; lia | exact S88]|].
split; [apply (VM _ 8%nat); [apply (SVZ 96); lia | lia | cbn; lia | exact S96]|].
split; [apply (VM _ 8%nat); [apply (SVZ 104); lia | lia | cbn; lia | exact S104]|].
split; [apply (VM _ 8%nat); [intros i Hi; right; right; cbn in Hi; lia | lia | cbn; lia | exact SFL]|].
split; [exact HSH|].
split.
- (* the input bytes: the journal keeps them (its footprint is empty) *)
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  intros j Hj. pose proof Hj as Hj'. rewrite length_map in Hj'.
  destruct (HPL j Hj) as (Hv & Hr). split; [|exact Hr].
  assert (Hn0 : 0 < e_n g) by lia.
  assert (Hin0 : In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)))
    by (destruct Hpn as [[Hz _] | [_ Hb]]; [lia | exact Hb]).
  assert (Hinb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hin0]).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
  apply (cw_val_mem_kept (w_H (e_W g)) (w_H W3) (e_mem g) mem3); [|exact Hv].
  intros x Hx. cbn [Z.of_nat] in Hx.
  replace x with (e_p g + (x - e_p g)) by lia.
  apply (F2 (e_p g) (e_n g) (x - e_p g) Hin0 Hinb3); [lia | apply inFP_nil].
- exact HPerm.
Qed.

Lemma bm_call_kept_sh : forall g pos sp1 sh s9v ly2 S2 W2 regsc mem2 md2 kev c T (Ef : Z -> Prop)
ly3 S3 W3 regs3 mem3 md3 k3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcom_sh g pos sp1 sh s9v ly2 S2 W2 regsc mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
(forall a, Ef a -> FA g pos + 192 <= a < FA g pos + 376) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
aregs_preserved regsc regs3 ->
Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
tcj_kept tfibsegs B T ly2 S2 W2 mem2 W3 mem3 (spZ regsc) Ef ->
mcom_sh g pos sp1 sh s9v ly3 S3 W3 regs3 mem3 md3 /\ cur_at g sp1 c W3 mem3 /\
(forall a, FA g pos <= a < FA g pos + 512 -> ~ Ef a ->
 aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
Proof.
intros g pos sp1 sh s9v ly2 S2 W2 regsc mem2 md2 kev c T Ef ly3 S3 W3 regs3 mem3 md3 k3 HJ Hfr HC Hcur HEf HJ3 HPR HPerm HK.
destruct (bm_facts_sh g pos sp1 sh s9v ly2 S2 W2 regsc mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite EFA, E512 in Happ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R21 & R18 & R27 & R23 & R25 & R19 & R26 & H64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 & V128 & V136 & V144 & V152 &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & VFL & SHM & GIN & PERM).
assert (Usp : spZ regsc = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold BM_HI in *; lia).
rewrite Usp in HK. destruct HK as (K1 & _ & _ & K4 & _ & _).
set (F := FA g pos) in *.
(* the machine stack at or above sp1: kept by clause 1 *)
assert (KS : forall a, sp1 <= a < e_sp0 g -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply K1; [lia | lia | intros He; pose proof (HEf a He); unfold BM_HI in *; lia]. }
(* the frame and its shadow: kept by clause 4 off E *)
assert (KF : forall a, F <= a < F + 512 -> ~ Ef a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha He. apply (K4 3 pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, E512; lia | exact He]. }
assert (KSH : forall i, 0 <= i < 60 ->
  aview tfibsegs (w_H W3) mem3 (shadow_addr F + i) = aview tfibsegs (w_H W2) mem2 (shadow_addr F + i)).
{ intros i Hi. apply (K4 3 pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA, E512. change (512 / 8) with 64. lia.
  - intros He. pose proof (HEf _ He) as Hr. unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
assert (VK : forall a n v, sp1 <= a -> a + Z.of_nat n <= e_sp0 g ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W3) mem3) a n v).
{ intros a n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KS. lia. }
assert (P2 : getr regs3 2 = getr regsc 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs3 3 = getr regsc 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs3 4 = getr regsc 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs3 8 = getr regsc 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs3 9 = getr regsc 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs3 18 = getr regsc 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs3 19 = getr regsc 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs3 21 = getr regsc 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs3 23 = getr regsc 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs3 25 = getr regsc 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs3 26 = getr regsc 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs3 27 = getr regsc 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
pose proof Hcur as (Hc & C184 & C192).
split; [|split].
- refine (conj Hpre (conj Hsp1 _)).
  rewrite P2, P9, P8, P3, P4, P21, P18, P27, P23, P25, P19, P26.
  refine (conj R2 (conj R9 (conj R8 (conj R3 (conj R4 (conj R21 (conj R18 (conj R27 (conj R23 (conj R25
    (conj R19 (conj R26 (conj H64 _))))))))))))).
  split; [apply VK; [lia | cbn; lia | exact V16]|].
  split; [apply VK; [lia | cbn; lia | exact V24]|].
  split; [apply VK; [lia | cbn; lia | exact V32]|].
  split; [apply VK; [lia | cbn; lia | exact V40]|].
  split; [apply VK; [lia | cbn; lia | exact V48]|].
  split; [apply VK; [lia | cbn; lia | exact V56]|].
  split; [apply VK; [lia | cbn; lia | exact V64]|].
  split; [apply VK; [lia | cbn; lia | exact V72]|].
  split; [apply VK; [lia | cbn; lia | exact V80]|].
  split; [apply VK; [lia | cbn; lia | exact V88]|].
  split; [apply VK; [lia | cbn; lia | exact V96]|].
  split; [apply VK; [lia | cbn; lia | exact V104]|].
  split; [apply VK; [lia | cbn; lia | exact V112]|].
  split; [apply VK; [lia | cbn; lia | exact V120]|].
  split; [apply VK; [lia | cbn; lia | exact V128]|].
  split; [apply VK; [lia | cbn; lia | exact V136]|].
  split; [apply VK; [lia | cbn; lia | exact V144]|].
  split; [apply VK; [lia | cbn; lia | exact V152]|].
  split; [apply VK; [lia | cbn; lia | exact S8]|].
  split; [apply VK; [lia | cbn; lia | exact S16]|].
  split; [apply VK; [lia | cbn; lia | exact S24]|].
  split; [apply VK; [lia | cbn; lia | exact S32]|].
  split; [apply VK; [lia | cbn; lia | exact S40]|].
  split; [apply VK; [lia | cbn; lia | exact S48]|].
  split; [apply VK; [lia | cbn; lia | exact S56]|].
  split; [apply VK; [lia | cbn; lia | exact S64]|].
  split; [apply VK; [lia | cbn; lia | exact S72]|].
  split; [apply VK; [lia | cbn; lia | exact S80]|].
  split; [apply VK; [lia | cbn; lia | exact S88]|].
  split; [apply VK; [lia | cbn; lia | exact S96]|].
  split; [apply VK; [lia | cbn; lia | exact S104]|].
  split.
  { apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact VFL].
    intros x Hx. cbn in Hx. apply KF; [lia|]. intros He. pose proof (HEf x He). lia. }
  pose proof Hpre as Hpre'. unfold e_pre, codec_lib_pre_x in Hpre'.
  destruct Hpre' as (_ & _ & _ & _ & _ & Hnpl & _).
  split; [intros i Hi; etransitivity; [exact (KSH i Hi) | exact (SHM i Hi)]|].
  split; [|exact (Permutation_trans HPerm PERM)].
  destruct (Z.eq_dec (e_n g) 0) as [Hn0 | Hn0].
  + intros j Hj. exfalso. rewrite length_map in Hj. lia.
  + destruct (Hblk ltac:(lia)) as (Hb2 & Hb0).
    assert (Hb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb2]).
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J2 & _).
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J3 & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
    apply (bm_garr8_kept_x (w_H W2) (w_H W3) mem2 mem3); [|exact GIN].
    intros x Hx. rewrite length_map in Hx.
    replace x with (e_p g + (x - e_p g)) by lia.
    rewrite (J3 (e_p g) (e_n g) (x - e_p g) Hb0 Hb3 ltac:(lia) (inFP_nil _)).
    rewrite (J2 (e_p g) (e_n g) (x - e_p g) Hb0 Hb2 ltac:(lia) (inFP_nil _)). reflexivity.
- split; [exact Hc|]. split; [apply VK; [lia | cbn; lia | exact C184] | apply VK; [lia | cbn; lia | exact C192]].
- exact KF.
Qed.

(* ================================ the call of owe_sysex (OWE9 0x82f70, OWE11 0x8308c) ================================
   From the cut facts at owe_sysex's entry (mcom_sh with any shadow map sh that marks k's 23 shadow bytes usable,
   the cursor, k, the arguments a0 = k, a1 = device, a2 = fn, a3 = the payload, a4 = its length, ra = the return
   address) and image B's contract cdcU_owe_sysex_specX, the same facts at the return address: k with want,
   want_len and want_display what owe_sysex writes, every byte of the frame off [F + 336, F + 376) kept. *)
Hypothesis MTL : ameter_laws MT.
Hypothesis OSX : cdcU_owe_sysex_specX tfibsegs B MT BM_owe_sysex.
Lemma bm_owe_sysex_at : forall (Q : world tfibsegs -> config -> Prop) g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 c kc
dev fn pl bs retpc,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0 ->
frames S2 = [(3, pos)] -> mo_le MT (e_S g) S2 0 ->
mcom_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 -> cur_at g sp1 c W2 mem2 -> k_at g pos kc W2 mem2 ->
(forall i, (24 <= i < 47)%nat -> nth i sh 0 = 0) ->
getr regs2 10 = w64 (FA g pos + 192) ->
arg_zxA 8 (getr regs2 11) dev -> arg_zxA 8 (getr regs2 12) fn ->
getr regs2 13 = w64 pl -> getr regs2 14 = w64 (Z.of_nat (length bs)) -> (length bs <= 19)%nat ->
crd_ok tfibsegs W2 mem2 sp1 TB_owe_sysex pl (Z.of_nat (length bs)) ->
(0 < Z.of_nat (length bs) -> 0 < pl /\ garr8 tfibsegs (rd W2 mem2) pl bs /\
  (pl + Z.of_nat (length bs) <= FA g pos + 192 + 144 \/ FA g pos + 192 + 184 <= pl)) ->
getr regs2 1 = w64 retpc -> YK0s.ret_ok (w64 retpc) -> 4096 <= retpc < 2 ^ 64 ->
(forall (W3 : world tfibsegs) ly3 S3 regs3 mem3 md3,
 ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 0 ->
 frames S3 = [(3, pos)] -> mo_le MT (e_S g) S3 0 ->
 mcom_sh g pos sp1 sh s9v ly3 S3 W3 regs3 mem3 md3 -> cur_at g sp1 c W3 mem3 -> aregs_preserved regs2 regs3 ->
 (let '(w, dp) := owe_sx dev fn bs in
  k_at g pos (set_wantZ kc (w ++ skipn (length w) (kz_want kc)) (Z.of_nat (length w)) dp) W3 mem3) ->
 (forall a, FA g pos <= a < FA g pos + 512 -> ~ (FA g pos + 336 <= a < FA g pos + 376) ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
 SRr tfibsegs W3 (cfg_at tfibsegs retpc regs3 mem3 md3) Q) ->
SRr tfibsegs W2 (cfg_at tfibsegs BM_owe_sysex regs2 mem2 md2) Q.
Proof using MTL LAWS OSX.
intros Q g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 c kc dev fn pl bs retpc HJ Hfr Hmo HC Hcur Hkat Hsh24 H10 Hdev Hfn
  H13 H14 Hbs Hcrd Hpl H1 Hret Hretr CONT.
destruct (bm_facts_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold BM_HI in Hchi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof satU_T_main_owe_sysex as HT1. pose proof satU_T_main_fits as HT2.
assert (HT0 : 0 <= TB_owe_sysex) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HTE : ESTACK <= TB_owe_sysex) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HC as (Hpre & _ & R2 & _ & _ & R3 & R4 & _).
pose proof HC as HPerm0. do 49 (destruct HPerm0 as (_ & HPerm0)).
assert (Usp : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hal16 : spZ regs2 mod 16 = 0).
{ rewrite Usp. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D.
  replace sp1 with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & _).
assert (HENT : cdc_entry tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(3, pos)] ly2 S2 W2 mem2 md2 0 regs2 TB_owe_sysex).
{ eapply (cpw_entry B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    (e_ly g) (e_S g) ly2 S2 W2 mem2 md2 0 regs2 TB_owe_sysex HJ).
  - rewrite H1. exact Hret.
  - unfold raZ. rewrite H1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - exact Hal16.
  - rewrite Usp. lia.
  - rewrite Usp. lia.
  - unfold EV_CDC. unfold EV_LIB in Hev. lia.
  - exact HPerm0.
  - unfold LIVE_CDC. unfold LIVE_LIB in Hlive. lia. }
(* k's 184 bytes are marked usable: its 23 shadow bytes are 0 in sh *)
assert (HBS : block_shadow (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 192) 184).
{ pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
  apply bm_block_shadow; [exact Hf64 | lia | reflexivity | lia |].
  intros i Hi. change ((184 + 7) / 8) with 23 in Hi. change (184 / 8) with 23. change (192 / 8) with 24.
  rewrite (proj2 (Z.ltb_lt i 23) ltac:(lia)).
  rewrite (HSH' (24 + i) ltac:(lia)). f_equal. apply Hsh24. lia. }
assert (HCRD : crd_ok tfibsegs W2 mem2 (spZ regs2) TB_owe_sysex (FA g pos + 192) 184).
{ rewrite Usp. exact (satU_main_k_rd tfibsegs B LAWS ly2 S2 W2 mem2 md2 sp1 TB_owe_sysex pos (FA g pos)
    LLVMF_STK (e_sp0 g) HAR Hin EFA Hf64 HBS ltac:(lia) ltac:(lia)). }
assert (HDST : cdst_ok tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(3, pos)] W2 mem2 (spZ regs2)
  TB_owe_sysex (FA g pos + 192 + 144) 40).
{ rewrite Usp. replace (FA g pos + 192 + 144) with (FA g pos + 336) by lia.
  exact (satU_main_want_dst tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(3, pos)] ly2 S2 W2 mem2 md2 0 sp1 TB_owe_sysex pos (FA g pos) HJ ltac:(left; reflexivity) Hin EFA Hf64 HBS
    HT0 ltac:(lia) ltac:(lia)). }
assert (Hq8 : (FA g pos + 192) mod 8 = 0).
{ pose proof (Z.div_mod (FA g pos) 64 ltac:(lia)) as D. rewrite Hf64, Z.add_0_r in D.
  replace (FA g pos + 192) with ((8 * (FA g pos / 64) + 24) * 8) by lia. apply Z_mod_mult. }
pose proof Hkat as (HKA & HKW).
unfold cfg_at. change (w64 BM_owe_sysex) with (Z_to_bv 64 BM_owe_sysex).
eapply SRr_bind.
{ change (Z_to_bv 64 BM_owe_sysex) with (w64 BM_owe_sysex).
  exact (OSX LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0
    regs2 (FA g pos + 192) dev fn pl (Z.of_nat (length bs)) kc bs HENT H10 Hq8 HKA HKW HCRD HDST Hdev Hfn H13 H14
    eq_refl Hbs ltac:(rewrite Usp; exact Hcrd) Hpl). }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HPR & Hfrs3 & HPerm3 & Hio3 & Hmo3 & KTc & HRc).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
rewrite H1 in *.
assert (Hfr3 : frames S3 = [(3, pos)]) by (rewrite Hfrs3; exact Hfr).
destruct (bm_call_kept_sh g pos sp1 sh s9v ly2 S2 W2 regs2 mem2 md2 0 c TB_owe_sysex
  (fun x => FA g pos + 192 + 144 <= x < FA g pos + 192 + 184) ly3 S3 W3 regs3 mem3 md3 0 HJ Hfr HC Hcur
  ltac:(intros a Ha; cbv beta in Ha; lia) HJ3 HPR HPerm3 KTc) as (HC3 & Hcur3 & KF).
assert (Hmo3' : mo_le MT (e_S g) S3 0)
  by (pose proof (mle_station _ _ _ _ 0 0 MTL Hmo Hmo3) as X; rewrite Z.add_0_r in X; exact X).
change (mkCfg (mkst regs3 (w64 retpc) mem3 (seg_rom tfibsegs)) md3)
  with (cfg_at tfibsegs retpc regs3 mem3 md3).
apply (CONT W3 ly3 S3 regs3 mem3 md3 HJ3 Hfr3 Hmo3' HC3 Hcur3 HPR).
- destruct (owe_sx dev fn bs) as [w dp] eqn:Ew.
  assert (Lw : (length w <= 24)%nat /\ 0 <= dp <= 1).
  { unfold owe_sx in Ew. injection Ew as Ew1 Ew2. subst w dp. split.
    - cbn [length app]. rewrite length_app. cbn [length]. lia.
    - destruct ((u8 fn =? 0x40) || (u8 fn =? 0x30))%bool; cbn [bit_or_0]; lia. }
  destruct Lw as (Lw & Rdp).
  split; [exact HRc|].
  destruct HKW as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17).
  unfold kcall_wfZ, set_wantZ.
  cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want
    kz_want_len kz_want_key kz_want_display].
  repeat split; try assumption; try lia.
  rewrite length_app, length_skipn, K17. lia.
- intros a Ha Hna. apply KF; [exact Ha | cbv beta; intros Hx; apply Hna; lia].
Qed.
End b.
End a.
