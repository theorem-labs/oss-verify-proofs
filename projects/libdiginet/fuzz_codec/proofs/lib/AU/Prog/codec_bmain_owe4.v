(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 253 of its 272 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_owe1.v, with its addresses and numbers changed; 120 of its 242 lines of code are new or changed and 150 lines of the source are left out. *)
(* Segment OWE4 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_owe 4): owe()'s
   JOG case (fuzz_codec.c:166-169), 0x82920-0x82938, the tail 0x829f8-0x82a10 (shared with OWE2 / OWE3), the
   E_RANGE tail 0x82dc8-0x82dcc and the reload of s9 at 0x82dd0, to CHK 0x82dd4. It is the image-A segment
   (lib/A/Prog/codec_amain_owe4.v) at image B (k = F + 192 in s7).
     0x82920 lw a0,36(s7) (delta); addiw a1,a0,-64; li a2,-128; bltu a1,a2 -> E_RANGE (delta outside [-64, 63]);
     a0 = delta + 64; ld a1,56(s1) (the spill 0x5cb0); 0x829f8 sh a1,144(s7) (want[0..2) = b0 5c);
     sb a0,146(s7) (want[2] = delta + 64); want_len = 3; want_key = 0x80000 = KEY 8 0; 0x82dd0 s9 = F + 448.
   No instrumented check and no trap edge in the segment's ranges. The state: k.delta read-only (atom 37 = delta
   mod 2^32), want_rc and want[0..3) writable (want[0..3) kept as atoms 38-40 on the E_RANGE path), want_len ..
   want_display writable (0 at the cut). *)
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

(* no trap edge of the function lies in the segment's ranges *)
Lemma o4_no_trap :
  forallb (fun a => negb (((0x82920 <=? a) && (a <? 0x8293c)) || ((0x829f8 <=? a) && (a <? 0x82a14)) ||
                          ((0x82dc8 <=? a) && (a <? 0x82dd4))))
    (bm_trap_taken ++ bm_trap_fall) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================ the state at OWE4 ================================ *)
Definition o4_k : YP09.region := bm_frame_region 228 232 228 228 [YP09.mkChunk 228 (CVal 4 (SOff 37 0))].
Definition o4_w : YP09.region := bm_frame_region 332 339 332 339
[YP09.mkChunk 332 (CVal 4 (SLit 0)); YP09.mkChunk 336 (CVal 1 (SOff 38 0)); YP09.mkChunk 337 (CVal 1 (SOff 39 0));
 YP09.mkChunk 338 (CVal 1 (SOff 40 0))].
Definition o4_l : YP09.region := bm_frame_region 360 376 360 376
[YP09.mkChunk 360 (CVal 8 (SLit 0)); YP09.mkChunk 368 (CVal 4 (SLit 0)); YP09.mkChunk 372 (CVal 4 (SLit 0))].
Definition o4_rs : smem := [o4_k; o4_w; o4_l].
Definition o4_ys (kc : kcallZ) : list Z :=
[kz_delta kc mod 2 ^ 32; nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0].

(* ================================ owe()'s JOG case ================================
   owe4_spec_ok, owe4_spec_rng and the executor's values are the image-A segment's
   (lib/A/Prog/codec_amain_owe4.v:46-117). *)
Lemma owe4_spec_ok : forall od a b c delta bytes n, -64 <= delta <= 63 ->
  owe_spec 4 od a b c delta bytes n = (0, ([0xb0; 0x5c; u8 (delta + 64)], KEY 8 0, 0)).
Proof.
  intros od a b c delta bytes n Hd. unfold owe_spec. destruct od; cbv beta iota zeta;
    (destruct (Z.ltb_spec delta (-64)); [lia|]); (destruct (Z.ltb_spec 63 delta); [lia|]); reflexivity.
Qed.
Lemma owe4_spec_rng : forall od a b c delta bytes n, delta < -64 \/ 63 < delta ->
  fst (owe_spec 4 od a b c delta bytes n) = E_RANGE.
Proof.
  intros od a b c delta bytes n H. unfold owe_spec. destruct od; cbv beta iota zeta;
    destruct (Z.ltb_spec delta (-64)); destruct (Z.ltb_spec 63 delta); try reflexivity; lia.
Qed.

Lemma o4_mod_eq : forall x m q, 0 < m -> q * m <= x < (q + 1) * m -> x mod m = x - q * m.
Proof. intros x m q Hm Hx. symmetry. apply (Z.mod_unique x m q); lia. Qed.
(* the sign-extended int delta (atom value delta mod 2 ^ 32) *)
Lemma o4_U_sx : forall E n d, ew E n = Z_to_bv 64 (d mod 2 ^ 32) -> - 2 ^ 31 <= d < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = d mod 2 ^ 64.
Proof.
intros E n d Hn Hd. rewrite (owe_U_sx32 E n (d mod 2 ^ 32) Hn) by (apply Z.mod_pos_bound; lia).
destruct (Z.le_gt_cases 0 d) as [H0|H0].
- rewrite (Z.mod_small d (2 ^ 32)) by lia. rewrite (Z.mod_small d (2 ^ 64)) by lia.
  destruct (Z.ltb_spec d (2 ^ 31)); lia.
- rewrite (o4_mod_eq d (2 ^ 32) (-1)) by lia. rewrite (o4_mod_eq d (2 ^ 64) (-1)) by lia.
  destruct (Z.ltb_spec (d - -1 * 2 ^ 32) (2 ^ 31)); lia.
Qed.
(* addiw a1,a0,-64 compared with -128 (bltu): taken exactly when delta is outside [-64, 63] *)
Lemma o4_br : forall E d, ew E 37 = Z_to_bv 64 (d mod 2 ^ 32) -> - 2 ^ 31 <= d < 2 ^ 31 ->
(U E (SAluw ALU_ADD (SExt true 32 (SOff 37 0)) (SLit (-64))) <? U E (SLit 18446744073709551488)) =
((d <? -64) || (63 <? d)).
Proof.
intros E d H37 Hd. rewrite U_lit by lia.
rewrite U_of_S, S_SAluw. rewrite (o4_U_sx E 37 d H37 Hd), U_SLit. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
replace ((-64) mod 2 ^ 64 mod 2 ^ 32) with (2 ^ 32 - 64) by reflexivity.
assert (Dm : (d mod 2 ^ 64) mod 2 ^ 32 = d mod 2 ^ 32).
{ destruct (Z.le_gt_cases 0 d) as [H0|H0].
  - rewrite (Z.mod_small d (2 ^ 64)) by lia. reflexivity.
  - rewrite (o4_mod_eq d (2 ^ 64) (-1)) by lia. rewrite (o4_mod_eq d (2 ^ 32) (-1)) by lia.
    rewrite (o4_mod_eq (d - -1 * 2 ^ 64) (2 ^ 32) (2 ^ 32 - 1)) by lia. lia. }
rewrite Dm.
assert (Ex : d mod 2 ^ 32 + (2 ^ 32 - 64) + 2 ^ 31 = (d - 64 + 2 ^ 31) + (1 - d / 2 ^ 32) * 2 ^ 32)
  by (pose proof (Z.div_mod d (2 ^ 32) ltac:(lia)); lia).
rewrite Ex, Z.mod_add by lia.
destruct (Z.le_gt_cases 0 (d - 64 + 2 ^ 31)) as [H0|H0].
- rewrite (Z.mod_small (d - 64 + 2 ^ 31)) by lia. replace (d - 64 + 2 ^ 31 - 2 ^ 31) with (d - 64) by lia.
  destruct (Z.le_gt_cases 0 (d - 64)) as [H1|H1].
  + rewrite (Z.mod_small (d - 64) (2 ^ 64)) by lia.
    destruct (Z.ltb_spec (d - 64) 18446744073709551488); destruct (Z.ltb_spec d (-64));
    destruct (Z.ltb_spec 63 d); cbn; first [reflexivity | exfalso; lia].
  + rewrite (o4_mod_eq (d - 64) (2 ^ 64) (-1)) by lia.
    destruct (Z.ltb_spec (d - 64 - -1 * 2 ^ 64) 18446744073709551488); destruct (Z.ltb_spec d (-64));
    destruct (Z.ltb_spec 63 d); cbn; first [reflexivity | exfalso; lia].
- rewrite (o4_mod_eq (d - 64 + 2 ^ 31) (2 ^ 32) (-1)) by lia.
  rewrite (Z.mod_small (d - 64 + 2 ^ 31 - -1 * 2 ^ 32 - 2 ^ 31) (2 ^ 64)) by lia.
  destruct (Z.ltb_spec (d - 64 + 2 ^ 31 - -1 * 2 ^ 32 - 2 ^ 31) 18446744073709551488); destruct (Z.ltb_spec d (-64));
  destruct (Z.ltb_spec 63 d); cbn; first [reflexivity | exfalso; lia].
Qed.
(* want[2] = delta + 64 *)
Lemma o4_U_add : forall E d, ew E 37 = Z_to_bv 64 (d mod 2 ^ 32) -> -64 <= d <= 63 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 64))) = d + 64.
Proof.
intros E d H37 Hd. change (U E (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 64)) = d + 64).
rewrite U_SAlu, (o4_U_sx E 37 d H37 ltac:(lia)), U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
change (64 mod 2 ^ 64) with 64.
destruct (Z.le_gt_cases 0 d) as [H0|H0].
- rewrite (Z.mod_small d) by lia. apply Z.mod_small. lia.
- rewrite (o4_mod_eq d (2 ^ 64) (-1)) by lia. rewrite (o4_mod_eq (d - -1 * 2 ^ 64 + 64) (2 ^ 64) 1) by lia. lia.
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

Theorem seg_owe4_holds : seg_owe B MT K XM_LIB 4.
Proof using TL LAWS.
unfold seg_owe. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & _ & c & kc & od & Hcur & Hkat & Hrec & Hkind & _ & Hrc & Hw0 & Hwl0 & Hwk0 & Hwd0 & R22).
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
pose proof HC as (_ & _ & R2 & _).
pose proof (Z.mod_pos_bound (kz_delta kc) (2 ^ 32) ltac:(lia)) as Md.
set (ys := o4_ys kc).
set (E := bm_env g pos c regs2 ys).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_delta kc mod 2 ^ 32)) by exact (bm_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 3).
assert (DX : forall n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o4_rs).
{ unfold o4_rs, o4_k, o4_w, o4_l. repeat apply Forall_cons; try apply Forall_nil;
  (apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]);
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 228 4 (SOff 37 0) (kz_delta kc mod 2 ^ 32));
    [exact (DX 37%nat _ X37) | zside | zside |].
    replace (FA g pos + 228) with (FA g pos + 192 + 36) by lia.
    exact (cw_val_mem_mod _ _ 4 _ Vdelta).
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. rewrite <- Hw0. exact Vwrc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 336 1 (SOff 38 0) (nth 0 (kz_want kc) 0));
    [exact (DX 38%nat _ X38) | zside | zside |].
    replace (FA g pos + 336) with (FA g pos + 192 + 144 + Z.of_nat 0) by lia. exact G0.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 337 1 (SOff 39 0) (nth 1 (kz_want kc) 0));
    [exact (DX 39%nat _ X39) | zside | zside |].
    replace (FA g pos + 337) with (FA g pos + 192 + 144 + Z.of_nat 1) by lia. exact G1.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 338 1 (SOff 40 0) (nth 2 (kz_want kc) 0));
    [exact (DX 40%nat _ X40) | zside | zside |].
    replace (FA g pos + 338) with (FA g pos + 192 + 144 + Z.of_nat 2) by lia. exact G2.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 360 8 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 360) with (FA g pos + 192 + 168) by lia. rewrite <- Hwl0. exact Vwl.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 368 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 368) with (FA g pos + 192 + 176) by lia. rewrite <- Hwk0. exact Vwk.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 372 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 372) with (FA g pos + 192 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
assert (Hpd : pairwise_disjoint E o4_rs).
{ unfold o4_rs, o4_k, o4_w, o4_l, bm_frame_region. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r bm_regs) o4_rs).
{ unfold o4_rs, o4_k, o4_w, o4_l. repeat apply Forall_cons; try apply Forall_nil;
  (apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia]). }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 4) ys o4_rs []
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd Hap I) as HS.
fold E in HS. change (owe_pc 4) with 0x82920 in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 3 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE : env_agree 37 (bm_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
assert (OK : owe_kZ kc od = owe_spec 4 od (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
unfold cfg_at. change (w64 (owe_pc 4)) with (Z_to_bv 64 0x82920).
(* 0x82920 lw delta, addiw -64, li -128, to bltu *)
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
cw_branch Hb1.
all: rewrite branch_ltu_U, (o4_br E (kz_delta kc) X37 Wdelta) in Hb1.
- (* delta outside [-64, 63]: the E_RANGE tail, to CHK *)
  assert (Hd : kz_delta kc < -64 \/ 63 < kz_delta kc)
    by (destruct (Z.ltb_spec (kz_delta kc) (-64)); destruct (Z.ltb_spec 63 (kz_delta kc)); cbn in Hb1; first [discriminate | lia]).
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
  owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 1%N V336. owe_fld Hrw UF 337 1%N V337. owe_fld Hrw UF 338 1%N V338.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od 3
    m3 r3 md3 E _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0] 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
  + owe_old3 V336 V337 V338 DX X38 X39 X40 Q0 Q1 Q2.
  + apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe4_spec_rng. exact Hd.
- (* -64 <= delta <= 63: the command (0x829f8, shared with OWE2 / OWE3), to CHK *)
  assert (Hd : -64 <= kz_delta kc <= 63)
    by (destruct (Z.ltb_spec (kz_delta kc) (-64)); destruct (Z.ltb_spec 63 (kz_delta kc)); cbn in Hb1; first [discriminate | lia]).
  pose proof (o4_U_add E (kz_delta kc) X37 Hd) as U338.
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
  owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 2%N V336. owe_fld Hrw UF 338 1%N V338.
  destruct (owe_split2 _ _ _ 23728 V336 ltac:(vm_compute; reflexivity) ltac:(lia)) as (V336a & V337a).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od 3
    m3 r3 md3 E _ 0 [176; 92; u8 (kz_delta kc + 64)] 3 (KEY 8 0) 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | change (KEY 8 0) with 524288; lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
  + apply owe_garr3; [ exact V336a
                    | exact V337a
                    | replace (FA g pos + 336 + 2) with (FA g pos + 338) by lia; apply (owe_vm _ _ 1 _ _ V338);
                      rewrite U338; unfold u8; change (2 ^ (8 * Z.of_N 1)) with 256;
                      change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite !Z.mod_mod by lia; reflexivity
                    | lia | lia | apply owe_u8_range ].
  + apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
  + apply (owe_want_ok_succ kc od _ [0xb0; 0x5c; u8 (kz_delta kc + 64)] (KEY 8 0) 0).
    { rewrite OK. apply owe4_spec_ok; lia. }
    cbn [length firstn app map]. unfold u8. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
End b.
End a.
