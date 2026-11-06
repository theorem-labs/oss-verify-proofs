(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 253 of its 272 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_owe1.v, with its addresses and numbers changed; 157 of its 268 lines of code are new or changed and 161 lines of the source are left out. *)
(* Segment OWE2 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_owe 2): owe()'s
   TOUCH case (fuzz_codec.c:158-161), 0x829b8-0x829f4, its slow check block 0x830bc-0x830c0, the tail 0x829f8-0x82a10
   it shares with VPOT and JOG, the E_RANGE tail 0x82dc8-0x82dcc and the reload of s9 at 0x82dd0, to CHK 0x82dd4.
   It is the image-A segment (lib/A/Prog/codec_amain_owe2.v) at image B (k = F + 192 in s7, the desk in s6).
     0x829b8 / 0x829c0 the UBSan checks of the desk pointer d = s6 (NULL, or not 8-aligned: bm_trap_taken), not
     taken: d is SPEC_C24 or SPEC_PC (pd_okB), 32-aligned, an atom fact of the state; 0x829c4 the check of the
     strips byte's shadow (d + 9; slow block 0x830bc); lw a,24(s7); lbu strips; bgeu a,strips -> E_RANGE;
     lw c,32(s7); want[0..2) = 0x90 0x09 (sh of the spill 48(sp1)), want[2] = (c ? 0x40 : 0) | a, want_len = 3,
     want_key = 0x80000; 0x82dc8 want_rc = -11; 0x82dd0 s9 = F + 448.
   The state: k's fields a, c read-only (atoms 37, 38), want_rc and want[0..3) writable (want[0..3) kept as atoms
   39-41 on the E_RANGE path), want_len .. want_display writable (0 at the cut), the desk's four bytes read-only
   (atoms 42-45, region 8). The strips byte's check takes two fresh atoms (46, 47). owe2_spec_ok, owe2_spec_rng
   and o2_touch_byte are the image-A segment's (lib/A/Prog/codec_amain_owe2.v:55-87). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_lem codec_bmain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_owel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the trap edges inside the segment's ranges are the two desk checks at its root *)
Lemma o2_traps :
  List.filter (fun a => ((0x829b8 <=? a) && (a <? 0x82a14)) || ((0x830bc <=? a) && (a <? 0x830c8)) ||
                        ((0x82dc8 <=? a) && (a <? 0x82dd4)))
    (bm_trap_taken ++ bm_trap_fall) = [0x829b8; 0x829c0].
Proof. vm_compute. reflexivity. Qed.

(* ================================ the state at OWE2 ================================ *)
Definition o2_k : YP09.region := bm_frame_region 216 228 216 216
[YP09.mkChunk 216 (CVal 4 (SOff 37 0)); YP09.mkChunk 224 (CVal 4 (SOff 38 0))].
Definition o2_w : YP09.region := bm_frame_region 332 339 332 339
[YP09.mkChunk 332 (CVal 4 (SLit 0)); YP09.mkChunk 336 (CVal 1 (SOff 39 0)); YP09.mkChunk 337 (CVal 1 (SOff 40 0));
 YP09.mkChunk 338 (CVal 1 (SOff 41 0))].
Definition o2_l : YP09.region := bm_frame_region 360 376 360 376
[YP09.mkChunk 360 (CVal 8 (SLit 0)); YP09.mkChunk 368 (CVal 4 (SLit 0)); YP09.mkChunk 372 (CVal 4 (SLit 0))].
Definition o2_d : YP09.region := owe_desk_region [SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0].
Definition o2_rs : smem := [o2_k; o2_w; o2_l; o2_d].
Definition o2_AF : list (nat * afact) :=
[(22%nat, mkAF 0x9dfc0 0x9dfe0 5); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0);
 (45%nat, mkAF 0 255 0)].
Definition o2_ys (kc : kcallZ) (d : desk) : list Z :=
[kz_a kc; kz_c kc; nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0;
 d_dev d; d_strips d; d_chars d; d_counter d].

(* ================================ owe()'s TOUCH case ================================ *)
Lemma owe2_spec_ok : forall d a b c delta bytes n, a < d_strips d ->
  owe_spec 2 (Some d) a b c delta bytes n =
  (0, ([0x90; 0x09; u8 (Z.lor (bit_or_0 (negb (c =? 0)) 0x40) a)], KEY 8 0, 0)).
Proof.
  intros d a b c delta bytes n Ha. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [lia|]. reflexivity.
Qed.
Lemma owe2_spec_rng : forall d a b c delta bytes n, d_strips d <= a ->
  fst (owe_spec 2 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [reflexivity | lia].
Qed.

(* want[2] = (c ? 0x40 : 0) | a, from snez / slli / or over the sign-extended c and a *)
Lemma o2_touch_byte : forall E xc xa c a, U E xc = (if c <? 2 ^ 31 then c else c + (2 ^ 64 - 2 ^ 32)) ->
  0 <= c < 2 ^ 32 -> U E xa = a -> 0 <= a < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) xc) (SLit 6)) xa) = Z.lor (bit_or_0 (negb (c =? 0)) 0x40) a.
Proof.
intros E xc xa c a Uc Hc Ua Ha.
assert (Hlt : U E (SAlu ALU_SLTU (SLit 0) xc) = if c =? 0 then 0 else 1).
{ rewrite U_SAlu, Uc, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0.
  destruct (Z.eqb_spec c 0) as [H0|H0].
  - rewrite H0. reflexivity.
  - destruct (Z.ltb_spec c (2 ^ 31)); cbv beta iota; rewrite (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity. }
assert (Hsl : U E (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) xc) (SLit 6)) = if c =? 0 then 0 else 64).
{ rewrite U_SAlu, Hlt, U_SLit. cbn [zalu_raw]. destruct (c =? 0); reflexivity. }
rewrite U_SAlu, Hsl, Ua. cbn [zalu_raw].
destruct (c =? 0); cbn [negb bit_or_0]; unfold zcanon, M64; apply Z.mod_small;
pose proof (lor_lt_pow2 64 a 8 ltac:(lia) ltac:(lia));
pose proof (lor_lt_pow2 0 a 8 ltac:(lia) ltac:(lia));
lia.
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
Context {ROB : YCeh.ro_tfa_below_ofl}.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

Theorem seg_owe2_holds : seg_owe B MT K XM_LIB 2.
Proof using TL LAWS ROB GM IV.
unfold seg_owe. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & _ & c & kc & od & Hcur & Hkat & Hrec & Hkind & Hnd & Hrc & Hw0 & Hwl0 & Hwk0 & Hwd0 & R22).
destruct od as [d|]; [| destruct (Hnd eq_refl) as [H|[H|H]]; lia].
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold BM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hkat as (HK & HW).
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbef & Gout & Vwrc & Gwant & Vwl & Vwk & Vwd).
destruct HW as (Wkind & Wp & Wdesk & Wa & Wb & Wc & Wdelta & Wn & Wrc & Wwrc & Wwl & Wwk & Wwd & Lbytes & Lbef & Lout & Lwant).
pose proof (Gwant 0%nat ltac:(lia)) as (G0 & Q0).
pose proof (Gwant 1%nat ltac:(lia)) as (G1 & Q1).
pose proof (Gwant 2%nat ltac:(lia)) as (G2 & Q2).
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hrec as (_ & Hpd & _).
pose proof (pd_range_B _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rch & Rcnt).
pose proof (owe_desk_range _ _ _ Hpd) as Hdr.
assert (Hdal : kz_desk kc mod 32 = 0) by (destruct Hdv as [-> | ->]; reflexivity).
pose proof HJ as (HAR & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
set (ys := o2_ys kc d).
set (E := bm_env g pos c regs2 ys).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_a kc)) by exact (bm_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (kz_c kc)) by exact (bm_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (d_dev d)) by exact (bm_ew_y g pos c regs2 ys 5).
assert (X43 : ew E 43 = Z_to_bv 64 (d_strips d)) by exact (bm_ew_y g pos c regs2 ys 6).
assert (X44 : ew E 44 = Z_to_bv 64 (d_chars d)) by exact (bm_ew_y g pos c regs2 ys 7).
assert (X45 : ew E 45 = Z_to_bv 64 (d_counter d)) by exact (bm_ew_y g pos c regs2 ys 8).
assert (DX : forall n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
assert (E22 : ew E 22 = Z_to_bv 64 (kz_desk kc)).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 22 22%bv eq_refl), R22. reflexivity. }
assert (U22 : bv_unsigned (ew E 22) = kz_desk kc) by (rewrite E22; apply unsigned_lit_small; lia).
(* the desk is off the frame *)
pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk kc + 8) 4 216 376 HAR
  ltac:(rewrite Hfr; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(change (fs_frame_bytes 3) with 512; lia)) as GAP.
rewrite EFA in GAP.
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o2_rs).
{ unfold o2_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: { apply (owe_desk_region_ok B TL E W2 mem2 (kz_p kc) (kz_desk kc) d _ HRO Hpd U22).
       intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ];
       [exact (DX _ _ X42) | exact (DX _ _ X43) | exact (DX _ _ X44) | exact (DX _ _ X45) | lia]. }
  all: unfold o2_k, o2_w, o2_l;
  (apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]);
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 216 4 (SOff 37 0) (kz_a kc)); [exact (DX 37%nat _ X37) | zside | zside |].
    replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact Va.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 224 4 (SOff 38 0) (kz_c kc)); [exact (DX 38%nat _ X38) | zside | zside |].
    replace (FA g pos + 224) with (FA g pos + 192 + 32) by lia. exact Vc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. rewrite <- Hw0. exact Vwrc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 336 1 (SOff 39 0) (nth 0 (kz_want kc) 0));
    [exact (DX 39%nat _ X39) | zside | zside |].
    replace (FA g pos + 336) with (FA g pos + 192 + 144 + Z.of_nat 0) by lia. exact G0.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 337 1 (SOff 40 0) (nth 1 (kz_want kc) 0));
    [exact (DX 40%nat _ X40) | zside | zside |].
    replace (FA g pos + 337) with (FA g pos + 192 + 144 + Z.of_nat 1) by lia. exact G1.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 338 1 (SOff 41 0) (nth 2 (kz_want kc) 0));
    [exact (DX 41%nat _ X41) | zside | zside |].
    replace (FA g pos + 338) with (FA g pos + 192 + 144 + Z.of_nat 2) by lia. exact G2.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 360 8 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 360) with (FA g pos + 192 + 168) by lia. rewrite <- Hwl0. exact Vwl.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 368 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 368) with (FA g pos + 192 + 176) by lia. rewrite <- Hwk0. exact Vwk.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 372 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 372) with (FA g pos + 192 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
assert (Hpd2 : pairwise_disjoint E o2_rs).
{ unfold o2_rs, o2_k, o2_w, o2_l, o2_d, owe_desk_region, bm_frame_region. cbn [pairwise_disjoint all_disjoint nth].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U22. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r bm_regs) o2_rs).
{ unfold o2_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: exact (owe_desk_apart_base E _ (kz_desk kc) sp1 U22 Hdr U2 ltac:(lia)).
  all: unfold o2_k, o2_w, o2_l;
  (apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia]). }
assert (HAF : atoms_ok E o2_AF).
{ unfold o2_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U22, X42, X43, X44, X45. rewrite !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 2) ys o2_rs o2_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd2 Hap HAF) as HS.
fold E in HS. change (owe_pc 2) with 0x829b8 in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk; owe_desk_SH] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC).
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p kc) (kz_desk kc) d GM IV HAR Hpd E22
      (bm_ew_SB g pos c regs2 ys)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 3 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE : env_agree 37 (bm_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (owe_U_sx32 E 37 (kz_a kc) X37 ltac:(lia)) as Ua.
pose proof (owe_U_sx32 E 38 (kz_c kc) X38 ltac:(lia)) as Uc.
assert (OK : owe_kZ kc (Some d) =
  owe_spec 2 (Some d) (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
unfold cfg_at. change (w64 (owe_pc 2)) with (Z_to_bv 64 0x829b8).
(* 0x829b8 the desk checks (decided by the desk's atom fact), the check of the strips byte's shadow, lw a, lbu strips, to bgeu a,strips *)
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
(* the run took two fresh atoms (46: the shadow byte, 47: the slow check's low bits); E1 agrees with E below 46 *)
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => set (E1 := Ev) in * end.
assert (HA1 : env_agree 46 E E1) by (subst E1; apply env_agree_ewset2).
assert (HAE1 : env_agree 37 (bm_env g pos c regs2 ys) E1) by (subst E1; env_agree_chain HAE).
assert (U2_1 : bv_unsigned (ew E1 2) = sp1) by (rewrite (proj1 HA1 2%nat ltac:(lia)); exact U2).
assert (UF1 : bv_unsigned (ew E1 33) = FA g pos) by (rewrite (proj1 HA1 33%nat ltac:(lia)); exact UF).
assert (DX1 : forall n v, ew E1 n = Z_to_bv 64 v -> sv_denot E1 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (X39_1 : ew E1 39 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by (rewrite (proj1 HA1 39%nat ltac:(lia)); exact X39).
assert (X40_1 : ew E1 40 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by (rewrite (proj1 HA1 40%nat ltac:(lia)); exact X40).
assert (X41_1 : ew E1 41 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by (rewrite (proj1 HA1 41%nat ltac:(lia)); exact X41).
cw_branch Hb1.
all: rewrite branch_geu_U, !(YCbn.U_agree 46 E E1 _ HA1) in Hb1 by reflexivity.
all: rewrite Ua, (U_atom E 43 (d_strips d) X43) in Hb1 by lia.
- (* strips <= a: the E_RANGE tail, to CHK *)
  apply negb_true_iff, Z.ltb_ge in Hb1.
  assert (Ha : d_strips d <= kz_a kc) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2_1 UF1).
  owe_fields HS UF1 Hrw Hrl. owe_fld Hrw UF1 336 1%N V336. owe_fld Hrw UF1 337 1%N V337. owe_fld Hrw UF1 338 1%N V338.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 3
    m3 r3 md3 E1 _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0] 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
  + owe_old3 V336 V337 V338 DX1 X39_1 X40_1 X41_1 Q0 Q1 Q2.
  + apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe2_spec_rng. lia.
- (* a < strips: the command, to CHK *)
  apply negb_false_iff, Z.ltb_lt in Hb1.
  assert (Ha : kz_a kc < d_strips d /\ kz_a kc < 2 ^ 31) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  assert (U338 : bv_unsigned (sv_denot E1 (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0)
    (SExt true 32 (SOff 38 0))) (SLit 6)) (SExt true 32 (SOff 37 0)))) =
    Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_a kc)).
  { change (U E1 (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0)
      (SExt true 32 (SOff 38 0))) (SLit 6)) (SExt true 32 (SOff 37 0))) =
      Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_a kc)).
    rewrite (YCbn.U_agree 46 E E1 _ HA1) by reflexivity.
    apply o2_touch_byte; [exact Uc | lia | | lia].
    rewrite Ua. destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia. }
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2_1 UF1).
  owe_fields HS UF1 Hrw Hrl.
  owe_fld Hrw UF1 336 2%N V336. owe_fld Hrw UF1 338 1%N V338.
  destruct (owe_split2 _ _ _ 2448 V336 ltac:(vm_compute; reflexivity) ltac:(lia)) as (V336a & V337a).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 3
    m3 r3 md3 E1 _ 0 [144; 9; u8 (Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_a kc))] 3 (KEY 8 0) 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | change (KEY 8 0) with 524288; lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
  + apply owe_garr3; [ exact V336a | exact V337a
                     | replace (FA g pos + 336 + 2) with (FA g pos + 338) by lia; apply (owe_vm _ _ 1 _ _ V338);
                       rewrite U338; unfold u8; change (2 ^ (8 * Z.of_N 1)) with 256;
                       change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite !Z.mod_mod by lia; reflexivity
                     | lia | lia | apply owe_u8_range ].
  + apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
  + apply (owe_want_ok_succ kc (Some d) _ [0x90; 0x09; u8 (Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_a kc))]
      (KEY 8 0) 0).
    { rewrite OK. apply owe2_spec_ok; lia. }
    cbn [length firstn app map]. unfold u8. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
End b.
End a.
