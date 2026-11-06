(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 253 of its 272 lines of code are new or changed and 574 lines of the source are left out. *)
(* Segment OWE1 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_owe 1): owe()'s
   BUTTON case (fuzz_codec.c:151-155), 0x82a98-0x82aec, the E_RANGE tail 0x82dc8-0x82dcc and the reload of s9 at
   0x82dd0, to CHK 0x82dd4. It is the image-A segment (lib/A/Prog/codec_amain_owe1.v) at image B (k = F + 192 in s7).
     0x82a98 lw a0,24(s7) (a); bltu 127,a0 -> E_RANGE; lw a1,28(s7) (b); bltu 63,a1 -> E_RANGE; lw a2,32(s7) (c);
     want[0] = 0x90, want[1] = a, want[2] = (c ? 0x40 : 0) | b, want_len = 3, want_key = a << 8 | b | 0x20000;
     0x82dc8 want_rc = -11; 0x82dd0 s9 = F + 448 (the spill 128(sp1)).
   No instrumented check and no UBSan check (k's fields are at constant offsets of the frame; the segment's range
   holds no trap edge). The state: k's three fields read-only (atoms 37-39), want_rc and want[0..3) writable
   (want[0..3) kept as atoms 40-42 on the E_RANGE path), want_len .. want_display writable (0 at the cut). *)
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
Lemma o1_no_trap :
  forallb (fun a => negb (((0x82a98 <=? a) && (a <? 0x82af0)) || ((0x82dc8 <=? a) && (a <? 0x82dd4))))
    (bm_trap_taken ++ bm_trap_fall) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================ the state at OWE1 ================================ *)
Definition o1_k : YP09.region := bm_frame_region 216 228 216 216
[YP09.mkChunk 216 (CVal 4 (SOff 37 0)); YP09.mkChunk 220 (CVal 4 (SOff 38 0)); YP09.mkChunk 224 (CVal 4 (SOff 39 0))].
Definition o1_w : YP09.region := bm_frame_region 332 339 332 339
[YP09.mkChunk 332 (CVal 4 (SLit 0)); YP09.mkChunk 336 (CVal 1 (SOff 40 0)); YP09.mkChunk 337 (CVal 1 (SOff 41 0));
 YP09.mkChunk 338 (CVal 1 (SOff 42 0))].
Definition o1_l : YP09.region := bm_frame_region 360 376 360 376
[YP09.mkChunk 360 (CVal 8 (SLit 0)); YP09.mkChunk 368 (CVal 4 (SLit 0)); YP09.mkChunk 372 (CVal 4 (SLit 0))].
Definition o1_rs : smem := [o1_k; o1_w; o1_l].
Definition o1_ys (kc : kcallZ) : list Z :=
[kz_a kc; kz_b kc; kz_c kc; nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0].

(* ================================ owe()'s BUTTON case ================================
   owe1_spec_ok, owe1_spec_rng and key1 are the image-A segment's (lib/A/Prog/codec_amain_owe1.v:49-72). *)
Lemma owe1_spec_ok : forall od a b c delta bytes n, 0 <= a <= 0x7f -> 0 <= b <= 0x3f ->
  owe_spec 1 od a b c delta bytes n =
  (0, ([0x90; u8 a; u8 (Z.lor (bit_or_0 (negb (c =? 0)) 0x40) b)], KEY 2 (Z.lor ((a * 256) mod 2 ^ 32) b), 0)).
Proof.
  intros od a b c delta bytes n Ha Hb. unfold owe_spec. destruct od; cbv beta iota zeta;
    (destruct (Z.ltb_spec 0x7f a); [lia|]); (destruct (Z.ltb_spec 0x3f b); [lia|]); reflexivity.
Qed.
Lemma owe1_spec_rng : forall od a b c delta bytes n, 0x7f < a \/ 0x3f < b ->
  fst (owe_spec 1 od a b c delta bytes n) = E_RANGE.
Proof.
  intros od a b c delta bytes n H. unfold owe_spec. destruct od; cbv beta iota zeta;
    destruct (Z.ltb_spec 0x7f a); destruct (Z.ltb_spec 0x3f b); try reflexivity; lia.
Qed.
Lemma key1 : forall a b, 0 <= a <= 127 -> 0 <= b <= 63 ->
  Z.lor (Z.shiftl a 8 mod 2 ^ 64) (Z.lor b 131072) = KEY 2 (Z.lor ((a * 256) mod 2 ^ 32) b).
Proof.
  intros a b Ha Hb. unfold KEY. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (a * 2 ^ 8)) by lia. rewrite (Z.mod_small (a * 256)) by lia.
  change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  assert (L := lor_lt_pow2 (a * 256) b 16 ltac:(lia) ltac:(lia)).
  rewrite (Z.mod_small (Z.lor (a * 256) b)) by lia.
  replace (a * 2 ^ 8) with (a * 256) by lia.
  rewrite Z.lor_assoc, Z.lor_comm. reflexivity.
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

Theorem seg_owe1_holds : seg_owe B MT K XM_LIB 1.
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
set (ys := o1_ys kc).
set (E := bm_env g pos c regs2 ys).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_a kc)) by exact (bm_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (kz_b kc)) by exact (bm_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (kz_c kc)) by exact (bm_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 5).
assert (DX : forall n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o1_rs).
{ unfold o1_rs, o1_k, o1_w, o1_l. repeat apply Forall_cons; try apply Forall_nil;
  (apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]);
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 216 4 (SOff 37 0) (kz_a kc)); [exact (DX 37%nat _ X37) | zside | zside |].
    replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact Va.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 220 4 (SOff 38 0) (kz_b kc)); [exact (DX 38%nat _ X38) | zside | zside |].
    replace (FA g pos + 220) with (FA g pos + 192 + 28) by lia. exact Vb.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 224 4 (SOff 39 0) (kz_c kc)); [exact (DX 39%nat _ X39) | zside | zside |].
    replace (FA g pos + 224) with (FA g pos + 192 + 32) by lia. exact Vc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. rewrite <- Hw0. exact Vwrc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 336 1 (SOff 40 0) (nth 0 (kz_want kc) 0));
    [exact (DX 40%nat _ X40) | zside | zside |].
    replace (FA g pos + 336) with (FA g pos + 192 + 144 + Z.of_nat 0) by lia. exact G0.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 337 1 (SOff 41 0) (nth 1 (kz_want kc) 0));
    [exact (DX 41%nat _ X41) | zside | zside |].
    replace (FA g pos + 337) with (FA g pos + 192 + 144 + Z.of_nat 1) by lia. exact G1.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 338 1 (SOff 42 0) (nth 2 (kz_want kc) 0));
    [exact (DX 42%nat _ X42) | zside | zside |].
    replace (FA g pos + 338) with (FA g pos + 192 + 144 + Z.of_nat 2) by lia. exact G2.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 360 8 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 360) with (FA g pos + 192 + 168) by lia. rewrite <- Hwl0. exact Vwl.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 368 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 368) with (FA g pos + 192 + 176) by lia. rewrite <- Hwk0. exact Vwk.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 372 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 372) with (FA g pos + 192 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
assert (Hpd : pairwise_disjoint E o1_rs).
{ unfold o1_rs, o1_k, o1_w, o1_l, bm_frame_region. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r bm_regs) o1_rs).
{ unfold o1_rs, o1_k, o1_w, o1_l. repeat apply Forall_cons; try apply Forall_nil;
  (apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia]). }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 1) ys o1_rs []
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd Hap I) as HS.
fold E in HS. change (owe_pc 1) with 0x82a98 in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 3 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE : env_agree 37 (bm_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (owe_U_sx32 E 37 (kz_a kc) X37 ltac:(lia)) as Ua.
pose proof (owe_U_sx32 E 38 (kz_b kc) X38 ltac:(lia)) as Ub.
pose proof (owe_U_sx32 E 39 (kz_c kc) X39 ltac:(lia)) as Uc.
(* the record's result codes *)
assert (OK : owe_kZ kc od = owe_spec 1 od (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
unfold cfg_at. change (w64 (owe_pc 1)) with (Z_to_bv 64 0x82a98).
(* 0x82a98 lw a, li 127, to bltu 127,a *)
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
cw_branch Hb1.
all: rewrite branch_ltu_U, U_lit, Ua in Hb1 by lia.
- (* a > 127: the E_RANGE tail, to CHK *)
  apply Z.ltb_lt in Hb1.
  assert (Ha : 127 < kz_a kc) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
  owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 1%N V336. owe_fld Hrw UF 337 1%N V337. owe_fld Hrw UF 338 1%N V338.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od 3
    m3 r3 md3 E _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0] 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
  + owe_old3 V336 V337 V338 DX X40 X41 X42 Q0 Q1 Q2.
  + apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe1_spec_rng. lia.
- (* a <= 127 *)
  apply Z.ltb_ge in Hb1.
  assert (Ha : kz_a kc <= 127) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  assert (Ua' : bv_unsigned (sv_denot E (SExt true 32 (SOff 37 0))) = kz_a kc).
  { change (U E (SExt true 32 (SOff 37 0)) = kz_a kc). rewrite Ua.
    destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia. }
  (* 0x82aa4 lw b, li 63, to bltu 63,b *)
  cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
  cw_branch Hb2.
  all: rewrite branch_ltu_U, U_lit, Ub in Hb2 by lia.
  + (* b > 63: the E_RANGE tail *)
    apply Z.ltb_lt in Hb2.
    assert (Hb : 63 < kz_b kc) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
    owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 1%N V336. owe_fld Hrw UF 337 1%N V337. owe_fld Hrw UF 338 1%N V338.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od 3
      m3 r3 md3 E _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0] 0 0 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
    * owe_old3 V336 V337 V338 DX X40 X41 X42 Q0 Q1 Q2.
    * apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V368). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
    * apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe1_spec_rng. lia.
  + (* b <= 63: the command, to CHK *)
    apply Z.ltb_ge in Hb2.
    assert (Hb : kz_b kc <= 63) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
    assert (Ub' : U E (SExt true 32 (SOff 38 0)) = kz_b kc).
    { rewrite Ub. destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia. }
    assert (U338 : bv_unsigned (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0)
      (SExt true 32 (SOff 39 0))) (SLit 6)) (SExt true 32 (SOff 38 0)))) =
      Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_b kc)).
    { change (U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0)
        (SExt true 32 (SOff 39 0))) (SLit 6)) (SExt true 32 (SOff 38 0))) =
        Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_b kc)).
      assert (Hlt : U E (SAlu ALU_SLTU (SLit 0) (SExt true 32 (SOff 39 0))) = if kz_c kc =? 0 then 0 else 1).
      { rewrite U_SAlu, Uc, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0.
        destruct (Z.eqb_spec (kz_c kc) 0) as [H0|H0].
        - rewrite H0. reflexivity.
        - destruct (Z.ltb_spec (kz_c kc) (2 ^ 31)); cbv beta iota;
          rewrite (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity. }
      assert (Hsl : U E (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SExt true 32 (SOff 39 0))) (SLit 6)) =
        if kz_c kc =? 0 then 0 else 64).
      { rewrite U_SAlu, Hlt, U_SLit. cbn [zalu_raw]. destruct (kz_c kc =? 0); reflexivity. }
      rewrite U_SAlu, Hsl, Ub'. cbn [zalu_raw].
      destruct (kz_c kc =? 0); cbn [negb bit_or_0]; unfold zcanon, M64; apply Z.mod_small;
      pose proof (lor_lt_pow2 64 (kz_b kc) 7 ltac:(lia) ltac:(lia));
      pose proof (lor_lt_pow2 0 (kz_b kc) 7 ltac:(lia) ltac:(lia));
      lia. }
    assert (Kr : 0 <= KEY 2 (Z.lor ((kz_a kc * 256) mod 2 ^ 32) (kz_b kc)) < 2 ^ 32).
    { unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (Z.lor ((kz_a kc * 256) mod 2 ^ 32) (kz_b kc)) (2 ^ 16) ltac:(lia)) as L1.
      pose proof (lor_lt_pow2 (2 * 65536) (Z.lor ((kz_a kc * 256) mod 2 ^ 32) (kz_b kc) mod 2 ^ 16) 32
        ltac:(lia) ltac:(lia)). lia. }
    assert (U368 : bv_unsigned (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 8))
      (SAlu ALU_OR (SExt true 32 (SOff 38 0)) (SLit 131072)))) = KEY 2 (Z.lor ((kz_a kc * 256) mod 2 ^ 32) (kz_b kc))).
    { change (U E (SAlu ALU_OR (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 8))
        (SAlu ALU_OR (SExt true 32 (SOff 38 0)) (SLit 131072))) = KEY 2 (Z.lor ((kz_a kc * 256) mod 2 ^ 32) (kz_b kc))).
      rewrite !U_SAlu, !U_SLit. change (U E (SExt true 32 (SOff 37 0))) with (bv_unsigned (sv_denot E (SExt true 32 (SOff 37 0)))).
      rewrite Ua', Ub'. cbn [zalu_raw]. change (zcanon 8) with 8. change (zcanon 131072) with 131072.
      change (Z.land 8 63) with 8.
      assert (L3 : 0 <= Z.lor (kz_b kc) 131072 < 2 ^ 64)
        by (pose proof (lor_lt_pow2 (kz_b kc) 131072 18 ltac:(lia) ltac:(lia)); lia).
      unfold zcanon, M64. rewrite (Z.mod_small (Z.lor (kz_b kc) 131072)) by lia.
      rewrite key1 by lia. apply Z.mod_small. lia. }
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
    owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 1%N V336. owe_fld Hrw UF 337 1%N V337. owe_fld Hrw UF 338 1%N V338.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc od 3
      m3 r3 md3 E _ 0 [144; u8 (kz_a kc); u8 (Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_b kc))] 3
      (KEY 2 (Z.lor ((kz_a kc * 256) mod 2 ^ 32) (kz_b kc))) 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V332). vm_compute. reflexivity.
    * apply owe_garr3; [ apply (owe_vm _ _ 1 _ _ V336); vm_compute; reflexivity
                      | replace (FA g pos + 336 + 1) with (FA g pos + 337) by lia; apply (owe_vm _ _ 1 _ _ V337);
                        rewrite Ua'; unfold u8; change (2 ^ (8 * Z.of_N 1)) with 256;
                        change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite !Z.mod_mod by lia; reflexivity
                      | replace (FA g pos + 336 + 2) with (FA g pos + 338) by lia; apply (owe_vm _ _ 1 _ _ V338);
                        rewrite U338; unfold u8; change (2 ^ (8 * Z.of_N 1)) with 256;
                        change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite !Z.mod_mod by lia; reflexivity
                      | lia | apply owe_u8_range | apply owe_u8_range ].
    * apply (owe_vm _ _ 8 _ _ V360). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V368). rewrite U368. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
      change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V372). vm_compute. reflexivity.
    * apply (owe_want_ok_succ kc od _ [0x90; u8 (kz_a kc); u8 (Z.lor (bit_or_0 (negb (kz_c kc =? 0)) 0x40) (kz_b kc))]
        (KEY 2 (Z.lor ((kz_a kc * 256) mod 2 ^ 32) (kz_b kc))) 0).
      { rewrite OK. apply owe1_spec_ok; lia. }
      cbn [length firstn app map]. unfold u8. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
End b.
End a.
