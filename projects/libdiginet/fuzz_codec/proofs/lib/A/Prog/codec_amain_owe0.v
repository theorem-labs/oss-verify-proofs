(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its addresses and numbers changed; 214 of its 347 lines of code are new or changed and 133 lines of the source are left out. *)
(* Segment OWE0 of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_owe 0): owe()'s
   FADER case (fuzz_codec.c:139-148), 0x82268-0x822d0, its slow check block 0x82b08-0x82b0c, the E_RANGE tail
   0x82730-0x82734 and 0x82738, to CHK 0x8273c.
     0x82268 the check of the strips byte's shadow (k.desk + 9; slow block 0x82b08); lw a,24(s6); lbu strips;
     bgeu a,strips -> E_RANGE; lw b,28(s6); bltu 1023,b -> E_RANGE; want = 0xb0, a, b >> 3, a + 0x20, (b & 7) << 4,
     want_len = 5, want_key = a | 0x10000; 0x82730 want_rc = -11; 0x82738 s11 = 10.
   The state: k's fields a, b read-only (atoms 37, 38), want_rc and want[0..5) writable (want[0..5) kept as atoms
   39-43 on the E_RANGE paths), want_len .. want_display writable (0 at the cut), the desk's four bytes read-only
   (atoms 44-47, region 8). The strips byte's check takes two fresh atoms (48, 49). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_lem codec_amain_st codec_amain_owel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the state at OWE0 ================================ *)
Definition o0_k : YP09.region := am_frame_region 200 208 200 200
[YP09.mkChunk 200 (CVal 4 (SOff 37 0)); YP09.mkChunk 204 (CVal 4 (SOff 38 0))].
Definition o0_w : YP09.region := am_frame_region 316 325 316 325
[YP09.mkChunk 316 (CVal 4 (SLit 0)); YP09.mkChunk 320 (CVal 1 (SOff 39 0)); YP09.mkChunk 321 (CVal 1 (SOff 40 0));
 YP09.mkChunk 322 (CVal 1 (SOff 41 0)); YP09.mkChunk 323 (CVal 1 (SOff 42 0)); YP09.mkChunk 324 (CVal 1 (SOff 43 0))].
Definition o0_l : YP09.region := am_frame_region 344 360 344 360
[YP09.mkChunk 344 (CVal 8 (SLit 0)); YP09.mkChunk 352 (CVal 4 (SLit 0)); YP09.mkChunk 356 (CVal 4 (SLit 0))].
Definition o0_d : YP09.region := owe_desk_region [SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0].
Definition o0_rs : smem := [o0_k; o0_w; o0_l; o0_d].
Definition o0_AF : list (nat * afact) :=
[(23%nat, mkAF 0x9d6a0 0x9d6c0 5); (44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 255 0);
 (47%nat, mkAF 0 255 0)].
Definition o0_ys (kc : kcallZ) (d : desk) : list Z :=
[kz_a kc; kz_b kc; nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0; nth 3 (kz_want kc) 0;
 nth 4 (kz_want kc) 0; d_dev d; d_strips d; d_chars d; d_counter d].

(* ================================ owe()'s FADER case ================================
   owe0_spec_ok, owe0_spec_rng and key0 are lib/Prog/codec_main_owe0.v:14-34 of the plain
   walk. *)
Lemma owe0_spec_ok : forall d a b c delta bytes n, a < d_strips d -> b <= 1023 ->
  owe_spec 0 (Some d) a b c delta bytes n =
  (0, ([0xb0; u8 a; u8 (b / 8); u8 (0x20 + a); u8 ((b mod 8) * 16)], KEY 1 a, 0)).
Proof.
  intros d a b c delta bytes n Ha Hb. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [lia|]. destruct (Z.ltb_spec 1023 b); [lia|]. reflexivity.
Qed.
Lemma owe0_spec_rng : forall d a b c delta bytes n, d_strips d <= a \/ 1023 < b ->
  fst (owe_spec 0 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); destruct (Z.ltb_spec 1023 b); try reflexivity; lia.
Qed.
Lemma key0 : forall a, 0 <= a < 65536 -> Z.lor a 65536 = KEY 1 a.
Proof.
  intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small a) by lia. rewrite Z.lor_comm. reflexivity.
Qed.

(* five bytes read back as a byte array *)
Lemma o0_garr5 : forall m a x0 x1 x2 x3 x4, val_mem tfibsegs m a 1 x0 -> val_mem tfibsegs m (a + 1) 1 x1 ->
val_mem tfibsegs m (a + 2) 1 x2 -> val_mem tfibsegs m (a + 3) 1 x3 -> val_mem tfibsegs m (a + 4) 1 x4 ->
0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> 0 <= x4 < 256 ->
garr8 tfibsegs m a [x0; x1; x2; x3; x4].
Proof.
intros m a x0 x1 x2 x3 x4 V0 V1 V2 V3 V4 R0 R1 R2 R3 R4 j Hj. cbn [length] in Hj.
destruct j as [|[|[|[|[|j]]]]]; cbn [nth].
- rewrite Z.add_0_r. split; assumption.
- change (Z.of_nat 1) with 1. split; assumption.
- change (Z.of_nat 2) with 2. split; assumption.
- change (Z.of_nat 3) with 3. split; assumption.
- change (Z.of_nat 4) with 4. split; assumption.
- lia.
Qed.
(* the values the FADER case stores, from a and b *)
Lemma o0_srl3 : forall E x b, U E x = b -> 0 <= b < 2 ^ 64 -> U E (SAlu ALU_SRL x (SLit 3)) = b / 8.
Proof.
intros E x b Hx Hb. rewrite U_SAlu, Hx, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64. apply Z.mod_small.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma o0_add32 : forall E x a, U E x = a -> 0 <= a < 2 ^ 63 -> U E (SAlu ALU_ADD x (SLit 32)) = a + 32.
Proof.
intros E x a Hx Ha. rewrite U_SAlu, Hx, U_SLit. cbn [zalu_raw]. change (zcanon 32) with 32.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma o0_low3 : forall E x b, U E x = b -> 0 <= b < 2 ^ 64 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL x (SLit 61)) (SLit 57)) = (b mod 8) * 16.
Proof.
intros E x b Hx Hb. rewrite !U_SAlu, Hx, !U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 61) 63) with 61. change (Z.land (zcanon 57) 63) with 57.
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as Hm.
assert (E1 : (b * 2 ^ 61) mod 2 ^ 64 = (b mod 8) * 2 ^ 61).
{ rewrite (Z.div_mod b 8) at 1 by lia.
  replace ((8 * (b / 8) + b mod 8) * 2 ^ 61) with ((b mod 8) * 2 ^ 61 + (b / 8) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite E1, Z.shiftr_div_pow2 by lia.
replace ((b mod 8) * 2 ^ 61) with ((b mod 8 * 16) * 2 ^ 57) by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. lia.
Qed.
Lemma o0_or : forall E x a, U E x = a -> 0 <= a < 65536 -> U E (SAlu ALU_OR x (SLit 65536)) = KEY 1 a.
Proof.
intros E x a Hx Ha. rewrite U_SAlu, Hx, U_SLit. cbn [zalu_raw]. change (zcanon 65536) with 65536.
pose proof (lor_lt_pow2 a 65536 17 ltac:(lia) ltac:(lia)) as L.
unfold zcanon, M64. rewrite Z.mod_small by lia. apply key0. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

Theorem seg_owe0_holds : seg_owe B MT K XM_LIB 0.
Proof using TL LAWS ROB GM IV.
unfold seg_owe. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & _ & c & kc & od & Hcur & Hkat & Hrec & Hkind & Hnd & Hrc & Hw0 & Hwl0 & Hwk0 & Hwd0 & R23).
destruct od as [d|]; [| destruct (Hnd eq_refl) as [H|[H|H]]; lia].
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hkat as (HK & HW).
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbef & Gout & Vwrc & Gwant & Vwl & Vwk & Vwd).
destruct HW as (Wkind & Wp & Wdesk & Wa & Wb & Wc & Wdelta & Wn & Wrc & Wwrc & Wwl & Wwk & Wwd & Lbytes & Lbef & Lout & Lwant).
pose proof (Gwant 0%nat ltac:(lia)) as (G0 & Q0).
pose proof (Gwant 1%nat ltac:(lia)) as (G1 & Q1).
pose proof (Gwant 2%nat ltac:(lia)) as (G2 & Q2).
pose proof (Gwant 3%nat ltac:(lia)) as (G3 & Q3).
pose proof (Gwant 4%nat ltac:(lia)) as (G4 & Q4).
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hrec as (_ & Hpd & _).
pose proof (pd_range_A _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rch & Rcnt).
pose proof (owe_desk_range _ _ _ Hpd) as Hdr.
assert (Hdal : kz_desk kc mod 32 = 0) by (destruct Hdv as [-> | ->]; reflexivity).
pose proof HJ as (HAR & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
set (ys := o0_ys kc d).
set (E := am_env g pos c regs2 ys).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_a kc)) by exact (am_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (kz_b kc)) by exact (am_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (nth 3 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 5).
assert (X43 : ew E 43 = Z_to_bv 64 (nth 4 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 6).
assert (X44 : ew E 44 = Z_to_bv 64 (d_dev d)) by exact (am_ew_y g pos c regs2 ys 7).
assert (X45 : ew E 45 = Z_to_bv 64 (d_strips d)) by exact (am_ew_y g pos c regs2 ys 8).
assert (X46 : ew E 46 = Z_to_bv 64 (d_chars d)) by exact (am_ew_y g pos c regs2 ys 9).
assert (X47 : ew E 47 = Z_to_bv 64 (d_counter d)) by exact (am_ew_y g pos c regs2 ys 10).
assert (DX : forall n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 (kz_desk kc)).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 23 23%bv eq_refl), R23. reflexivity. }
assert (U23 : bv_unsigned (ew E 23) = kz_desk kc) by (rewrite E23; apply unsigned_lit_small; lia).
(* the desk is off the frame *)
pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk kc + 8) 4 200 360 HAR
  ltac:(rewrite Hfr; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(change (fs_frame_bytes 3) with 512; lia)) as GAP.
rewrite EFA in GAP.
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o0_rs).
{ unfold o0_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: { apply (owe_desk_region_ok B TL E W2 mem2 (kz_p kc) (kz_desk kc) d _ HRO Hpd U23).
       intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ];
       [exact (DX _ _ X44) | exact (DX _ _ X45) | exact (DX _ _ X46) | exact (DX _ _ X47) | lia]. }
  all: unfold o0_k, o0_w, o0_l;
  (apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]);
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 200 4 (SOff 37 0) (kz_a kc)); [exact (DX 37%nat _ X37) | zside | zside |].
    replace (FA g pos + 200) with (FA g pos + 176 + 24) by lia. exact Va.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 204 4 (SOff 38 0) (kz_b kc)); [exact (DX 38%nat _ X38) | zside | zside |].
    replace (FA g pos + 204) with (FA g pos + 176 + 28) by lia. exact Vb.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 316 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia. rewrite <- Hw0. exact Vwrc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 320 1 (SOff 39 0) (nth 0 (kz_want kc) 0));
    [exact (DX 39%nat _ X39) | zside | zside |].
    replace (FA g pos + 320) with (FA g pos + 176 + 144 + Z.of_nat 0) by lia. exact G0.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 321 1 (SOff 40 0) (nth 1 (kz_want kc) 0));
    [exact (DX 40%nat _ X40) | zside | zside |].
    replace (FA g pos + 321) with (FA g pos + 176 + 144 + Z.of_nat 1) by lia. exact G1.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 322 1 (SOff 41 0) (nth 2 (kz_want kc) 0));
    [exact (DX 41%nat _ X41) | zside | zside |].
    replace (FA g pos + 322) with (FA g pos + 176 + 144 + Z.of_nat 2) by lia. exact G2.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 323 1 (SOff 42 0) (nth 3 (kz_want kc) 0));
    [exact (DX 42%nat _ X42) | zside | zside |].
    replace (FA g pos + 323) with (FA g pos + 176 + 144 + Z.of_nat 3) by lia. exact G3.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 324 1 (SOff 43 0) (nth 4 (kz_want kc) 0));
    [exact (DX 43%nat _ X43) | zside | zside |].
    replace (FA g pos + 324) with (FA g pos + 176 + 144 + Z.of_nat 4) by lia. exact G4.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 344 8 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. rewrite <- Hwl0. exact Vwl.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 352 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. rewrite <- Hwk0. exact Vwk.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 356 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
assert (Hpd2 : pairwise_disjoint E o0_rs).
{ unfold o0_rs, o0_k, o0_w, o0_l, o0_d, owe_desk_region, am_frame_region. cbn [pairwise_disjoint all_disjoint nth].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U23. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r am_regs) o0_rs).
{ unfold o0_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: exact (owe_desk_apart_base E _ (kz_desk kc) sp1 U23 Hdr U2 ltac:(lia)).
  all: unfold o0_k, o0_w, o0_l;
  (apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia]). }
assert (HAF : atoms_ok E o0_AF).
{ unfold o0_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U23, X44, X45, X46, X47. rewrite !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 0) ys o0_rs o0_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd2 Hap HAF) as HS.
fold E in HS. change (owe_pc 0) with 0x82268 in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk; owe_desk_SH] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC).
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p kc) (kz_desk kc) d GM IV HAR Hpd E23
      (am_ew_SB g pos c regs2 ys)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 5 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE : env_agree 37 (am_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (owe_U_sx32 E 37 (kz_a kc) X37 ltac:(lia)) as Ua.
pose proof (owe_U_sx32 E 38 (kz_b kc) X38 ltac:(lia)) as Ub.
assert (OK : owe_kZ kc (Some d) =
  owe_spec 0 (Some d) (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
unfold cfg_at. change (w64 (owe_pc 0)) with (Z_to_bv 64 0x82268).
(* 0x82268 the check of the strips byte's shadow, lw a, lbu strips, to bgeu a,strips *)
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
(* the run took two fresh atoms (48: the shadow byte, 49: the slow check's low bits); E1 agrees with E below 48 *)
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => set (E1 := Ev) in * end.
assert (HA1 : env_agree 48 E E1) by (subst E1; apply env_agree_ewset2).
assert (HAE1 : env_agree 37 (am_env g pos c regs2 ys) E1) by (subst E1; env_agree_chain HAE).
assert (U2_1 : bv_unsigned (ew E1 2) = sp1) by (rewrite (proj1 HA1 2%nat ltac:(lia)); exact U2).
assert (UF1 : bv_unsigned (ew E1 33) = FA g pos) by (rewrite (proj1 HA1 33%nat ltac:(lia)); exact UF).
assert (DX1 : forall n v, ew E1 n = Z_to_bv 64 v -> sv_denot E1 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (X39_1 : ew E1 39 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by (rewrite (proj1 HA1 39%nat ltac:(lia)); exact X39).
assert (X40_1 : ew E1 40 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by (rewrite (proj1 HA1 40%nat ltac:(lia)); exact X40).
assert (X41_1 : ew E1 41 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by (rewrite (proj1 HA1 41%nat ltac:(lia)); exact X41).
assert (X42_1 : ew E1 42 = Z_to_bv 64 (nth 3 (kz_want kc) 0)) by (rewrite (proj1 HA1 42%nat ltac:(lia)); exact X42).
assert (X43_1 : ew E1 43 = Z_to_bv 64 (nth 4 (kz_want kc) 0)) by (rewrite (proj1 HA1 43%nat ltac:(lia)); exact X43).
cw_branch Hb1.
all: rewrite branch_geu_U, !(YCbn.U_agree 48 E E1 _ HA1) in Hb1 by reflexivity.
all: rewrite Ua, (U_atom E 45 (d_strips d) X45) in Hb1 by lia.
- (* strips <= a: the E_RANGE tail, to CHK *)
  apply negb_true_iff, Z.ltb_ge in Hb1.
  assert (Ha : d_strips d <= kz_a kc) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x8273c. cw_keep ltac:(owe_kwr U2_1 UF1).
  owe_fields HS UF1 Hrw Hrl. owe_fld Hrw UF1 320 1%N V320. owe_fld Hrw UF1 321 1%N V321.
  owe_fld Hrw UF1 322 1%N V322. owe_fld Hrw UF1 323 1%N V323. owe_fld Hrw UF1 324 1%N V324.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 5
    m3 r3 md3 E1 _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0;
    nth 3 (kz_want kc) 0; nth 4 (kz_want kc) 0] 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
  + apply o0_garr5; [owe_byte V320 DX1 X39_1 | owe_byte V321 DX1 X40_1 | owe_byte V322 DX1 X41_1
      | owe_byte V323 DX1 X42_1 | owe_byte V324 DX1 X43_1 | exact Q0 | exact Q1 | exact Q2 | exact Q3 | exact Q4].
  + apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V352). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe0_spec_rng. lia.
- (* a < strips *)
  apply negb_false_iff, Z.ltb_lt in Hb1.
  assert (Ha : kz_a kc < d_strips d /\ kz_a kc < 2 ^ 31) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  assert (Ua1 : bv_unsigned (sv_denot E1 (SExt true 32 (SOff 37 0))) = kz_a kc).
  { change (U E1 (SExt true 32 (SOff 37 0)) = kz_a kc). rewrite (YCbn.U_agree 48 E E1 _ HA1) by reflexivity.
    rewrite Ua. destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia. }
  (* 0x82288 lw b, li 1023, to bltu 1023,b *)
  cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA). cw_keep ltac:(owe_kwr U2_1 UF1).
  cw_branch Hb2.
  all: rewrite branch_ltu_U, U_lit, (YCbn.U_agree 48 E E1 _ HA1), Ub in Hb2 by first [reflexivity | lia].
  + (* 1023 < b: the E_RANGE tail *)
    apply Z.ltb_lt in Hb2.
    assert (Hb : 1023 < kz_b kc) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x8273c. cw_keep ltac:(owe_kwr U2_1 UF1).
    owe_fields HS UF1 Hrw Hrl. owe_fld Hrw UF1 320 1%N V320. owe_fld Hrw UF1 321 1%N V321.
    owe_fld Hrw UF1 322 1%N V322. owe_fld Hrw UF1 323 1%N V323. owe_fld Hrw UF1 324 1%N V324.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 5
      m3 r3 md3 E1 _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0;
      nth 3 (kz_want kc) 0; nth 4 (kz_want kc) 0] 0 0 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
    * apply o0_garr5; [owe_byte V320 DX1 X39_1 | owe_byte V321 DX1 X40_1 | owe_byte V322 DX1 X41_1
        | owe_byte V323 DX1 X42_1 | owe_byte V324 DX1 X43_1 | exact Q0 | exact Q1 | exact Q2 | exact Q3 | exact Q4].
    * apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V352). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
    * apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe0_spec_rng. lia.
  + (* b <= 1023: the command, to CHK *)
    apply Z.ltb_ge in Hb2.
    assert (Hb : kz_b kc <= 1023) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
    assert (Ub1 : U E1 (SExt true 32 (SOff 38 0)) = kz_b kc).
    { rewrite (YCbn.U_agree 48 E E1 _ HA1) by reflexivity. rewrite Ub. destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia. }
    assert (Ua1' : U E1 (SExt true 32 (SOff 37 0)) = kz_a kc) by exact Ua1.
    assert (U322 : bv_unsigned (sv_denot E1 (SAlu ALU_SRL (SExt true 32 (SOff 38 0)) (SLit 3))) = kz_b kc / 8)
      by exact (o0_srl3 E1 _ _ Ub1 ltac:(lia)).
    assert (U323 : bv_unsigned (sv_denot E1 (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 32))) = kz_a kc + 32)
      by exact (o0_add32 E1 _ _ Ua1' ltac:(lia)).
    assert (U324 : bv_unsigned (sv_denot E1 (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 38 0)) (SLit 61))
      (SLit 57))) = (kz_b kc mod 8) * 16) by exact (o0_low3 E1 _ _ Ub1 ltac:(lia)).
    assert (U352 : bv_unsigned (sv_denot E1 (SAlu ALU_OR (SExt true 32 (SOff 37 0)) (SLit 65536))) = KEY 1 (kz_a kc))
      by exact (o0_or E1 _ _ Ua1' ltac:(lia)).
    assert (Kr : 0 <= KEY 1 (kz_a kc) < 2 ^ 32).
    { rewrite <- key0 by lia. pose proof (lor_lt_pow2 (kz_a kc) 65536 17 ltac:(lia) ltac:(lia)). lia. }
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x8273c. cw_keep ltac:(owe_kwr U2_1 UF1).
    owe_fields HS UF1 Hrw Hrl. owe_fld Hrw UF1 320 1%N V320. owe_fld Hrw UF1 321 1%N V321.
    owe_fld Hrw UF1 322 1%N V322. owe_fld Hrw UF1 323 1%N V323. owe_fld Hrw UF1 324 1%N V324.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 5
      m3 r3 md3 E1 _ 0 [176; u8 (kz_a kc); u8 (kz_b kc / 8); u8 (0x20 + kz_a kc); u8 ((kz_b kc mod 8) * 16)] 5
      (KEY 1 (kz_a kc)) 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
    * apply o0_garr5;
      [ apply (owe_vm _ _ 1 _ _ V320); vm_compute; reflexivity
      | replace (FA g pos + 320 + 1) with (FA g pos + 321) by lia; apply (owe_vm _ _ 1 _ _ V321); rewrite Ua1
      | replace (FA g pos + 320 + 2) with (FA g pos + 322) by lia; apply (owe_vm _ _ 1 _ _ V322); rewrite U322
      | replace (FA g pos + 320 + 3) with (FA g pos + 323) by lia; apply (owe_vm _ _ 1 _ _ V323); rewrite U323
      | replace (FA g pos + 320 + 4) with (FA g pos + 324) by lia; apply (owe_vm _ _ 1 _ _ V324); rewrite U324
      | lia | apply owe_u8_range | apply owe_u8_range | apply owe_u8_range | apply owe_u8_range ];
      unfold u8; change (2 ^ (8 * Z.of_N 1)) with 256; change (2 ^ (8 * Z.of_nat 1)) with 256;
      rewrite !Z.mod_mod by lia; f_equal; lia.
    * apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V352). rewrite U352. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
      change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
    * apply (owe_want_ok_succ kc (Some d) _ [0xb0; u8 (kz_a kc); u8 (kz_b kc / 8); u8 (0x20 + kz_a kc);
        u8 ((kz_b kc mod 8) * 16)] (KEY 1 (kz_a kc)) 0).
      { rewrite OK. apply owe0_spec_ok; lia. }
      cbn [length firstn app map]. unfold u8. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
End b.
End a.
