(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its addresses and numbers changed; 182 of its 303 lines of code are new or changed and 145 lines of the source are left out. *)
(* Segment OWE3 of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_owe 3): owe()'s
   VPOT case (fuzz_codec.c:163-167), 0x823cc-0x82410, its slow check block 0x82b20-0x82b24, the tail 0x823b4-0x823c8
   it shares with TOUCH and JOG, the E_RANGE tail 0x82730-0x82734 and 0x82738, to CHK 0x8273c.
     0x823cc the check of the strips byte's shadow (k.desk + 9; slow block 0x82b20); lw a,24(s6); lbu strips;
     bgeu a,strips -> E_RANGE; lw delta,36(s6); addiw t,delta,-64; bltu t,-128 -> E_RANGE; want = 0xb0, a | 0x40,
     delta + 64, want_len = 3, want_key = 0x80000; 0x82730 want_rc = -11; 0x82738 s11 = 10.
   The state: k's fields a and delta (as its 4 bytes, delta mod 2^32) read-only (atoms 37, 38), want_rc and
   want[0..3) writable (want[0..3) kept as atoms 39-41 on the E_RANGE paths), want_len .. want_display writable (0 at
   the cut), the desk's four bytes read-only (atoms 42-45, region 8). The strips byte's check takes two fresh atoms
   (46, 47). owe3_spec_ok and owe3_spec_rng are lib/Prog/codec_main_owe34_lib.v:32-47 of the plain
   walk. *)
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

(* ================================ the state at OWE3 ================================ *)
Definition o3_k : YP09.region := am_frame_region 200 216 200 200
[YP09.mkChunk 200 (CVal 4 (SOff 37 0)); YP09.mkChunk 212 (CVal 4 (SOff 38 0))].
Definition o3_w : YP09.region := am_frame_region 316 323 316 323
[YP09.mkChunk 316 (CVal 4 (SLit 0)); YP09.mkChunk 320 (CVal 1 (SOff 39 0)); YP09.mkChunk 321 (CVal 1 (SOff 40 0));
 YP09.mkChunk 322 (CVal 1 (SOff 41 0))].
Definition o3_l : YP09.region := am_frame_region 344 360 344 360
[YP09.mkChunk 344 (CVal 8 (SLit 0)); YP09.mkChunk 352 (CVal 4 (SLit 0)); YP09.mkChunk 356 (CVal 4 (SLit 0))].
Definition o3_d : YP09.region := owe_desk_region [SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0].
Definition o3_rs : smem := [o3_k; o3_w; o3_l; o3_d].
Definition o3_AF : list (nat * afact) :=
[(23%nat, mkAF 0x9d6a0 0x9d6c0 5); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0);
 (45%nat, mkAF 0 255 0)].
Definition o3_ys (kc : kcallZ) (d : desk) : list Z :=
[kz_a kc; kz_delta kc mod 2 ^ 32; nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0;
 d_dev d; d_strips d; d_chars d; d_counter d].

(* ================================ owe()'s VPOT case ================================ *)
Lemma owe3_spec_ok : forall d a b c delta bytes n, a < d_strips d -> -64 <= delta <= 63 ->
  owe_spec 3 (Some d) a b c delta bytes n = (0, ([0xb0; u8 (Z.lor 0x40 a); u8 (delta + 64)], KEY 8 0, 0)).
Proof.
  intros d a b c delta bytes n Ha Hd. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [lia|].
  destruct (Z.ltb_spec delta (-64)); [lia|]. destruct (Z.ltb_spec 63 delta); [lia|]. reflexivity.
Qed.
Lemma owe3_spec_rng : forall d a b c delta bytes n, d_strips d <= a \/ delta < -64 \/ 63 < delta ->
  fst (owe_spec 3 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); destruct (Z.ltb_spec delta (-64)); destruct (Z.ltb_spec 63 delta);
    try reflexivity; lia.
Qed.

(* the sign-extended 4 bytes of an int delta, as a 64-bit value *)
Lemma o3_sx_small : forall delta, - 2 ^ 31 <= delta < 2 ^ 31 ->
  (if delta mod 2 ^ 32 <? 2 ^ 31 then delta mod 2 ^ 32 else delta mod 2 ^ 32 + (2 ^ 64 - 2 ^ 32)) = delta mod 2 ^ 64.
Proof.
intros delta H. destruct (Z.ltb_spec (delta mod 2 ^ 32) (2 ^ 31)); cbv beta iota; Z.div_mod_to_equations; lia.
Qed.
(* 0x823f0 addiw t,delta,-64 and 0x823f8 bltu t,-128: taken exactly when delta is outside [-64, 63] *)
Lemma o3_delta_U : forall E x delta, U E x mod 2 ^ 32 = delta mod 2 ^ 32 -> - 2 ^ 31 <= delta < 2 ^ 31 ->
  (U E (SAluw ALU_ADD x (SLit (-64))) <? 18446744073709551488) = negb ((-64 <=? delta) && (delta <=? 63)).
Proof.
intros E x delta Hx Hd. rewrite U_of_S, S_SAluw, Hx, U_SLit.
change (zcanon (-64) mod 2 ^ 32) with 4294967232. cbn [zalu_raw].
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
destruct (Z.leb_spec (-64) delta); destruct (Z.leb_spec delta 63); cbn [andb negb];
[apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.
(* want[1] = a | 0x40 and want[2] = delta + 64 *)
Lemma o3_or64 : forall E x a, U E x = a -> 0 <= a < 256 -> U E (SAlu ALU_OR x (SLit 64)) = Z.lor 64 a.
Proof.
intros E x a Hx Ha. rewrite U_SAlu, Hx, U_SLit. cbn [zalu_raw]. change (zcanon 64) with 64.
pose proof (lor_lt_pow2 64 a 8 ltac:(lia) ltac:(lia)) as L.
unfold zcanon, M64. rewrite Z.lor_comm. apply Z.mod_small. lia.
Qed.
Lemma o3_add64 : forall E x delta, U E x = delta mod 2 ^ 64 -> -64 <= delta <= 63 ->
  U E (SAlu ALU_ADD x (SLit 64)) = delta + 64.
Proof.
intros E x delta Hx Hd. rewrite U_SAlu, Hx, U_SLit. cbn [zalu_raw]. change (zcanon 64) with 64.
unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
Lemma o3_mod64_32 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof. intros z. Z.div_mod_to_equations. lia. Qed.

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

Theorem seg_owe3_holds : seg_owe B MT K XM_LIB 3.
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
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hrec as (_ & Hpd & _).
pose proof (pd_range_A _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rch & Rcnt).
pose proof (owe_desk_range _ _ _ Hpd) as Hdr.
assert (Hdal : kz_desk kc mod 32 = 0) by (destruct Hdv as [-> | ->]; reflexivity).
pose proof (Z.mod_pos_bound (kz_delta kc) (2 ^ 32) ltac:(lia)) as Mdl.
pose proof HJ as (HAR & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
set (ys := o3_ys kc d).
set (E := am_env g pos c regs2 ys).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_a kc)) by exact (am_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (kz_delta kc mod 2 ^ 32)) by exact (am_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (d_dev d)) by exact (am_ew_y g pos c regs2 ys 5).
assert (X43 : ew E 43 = Z_to_bv 64 (d_strips d)) by exact (am_ew_y g pos c regs2 ys 6).
assert (X44 : ew E 44 = Z_to_bv 64 (d_chars d)) by exact (am_ew_y g pos c regs2 ys 7).
assert (X45 : ew E 45 = Z_to_bv 64 (d_counter d)) by exact (am_ew_y g pos c regs2 ys 8).
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
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o3_rs).
{ unfold o3_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: { apply (owe_desk_region_ok B TL E W2 mem2 (kz_p kc) (kz_desk kc) d _ HRO Hpd U23).
       intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ];
       [exact (DX _ _ X42) | exact (DX _ _ X43) | exact (DX _ _ X44) | exact (DX _ _ X45) | lia]. }
  all: unfold o3_k, o3_w, o3_l;
  (apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]);
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 200 4 (SOff 37 0) (kz_a kc)); [exact (DX 37%nat _ X37) | zside | zside |].
    replace (FA g pos + 200) with (FA g pos + 176 + 24) by lia. exact Va.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 212 4 (SOff 38 0) (kz_delta kc mod 2 ^ 32));
    [exact (DX 38%nat _ X38) | zside | zside |].
    replace (FA g pos + 212) with (FA g pos + 176 + 36) by lia. exact (cw_val_mem_mod _ _ 4 _ Vdelta).
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
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 344 8 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. rewrite <- Hwl0. exact Vwl.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 352 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. rewrite <- Hwk0. exact Vwk.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 356 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
assert (Hpd2 : pairwise_disjoint E o3_rs).
{ unfold o3_rs, o3_k, o3_w, o3_l, o3_d, owe_desk_region, am_frame_region. cbn [pairwise_disjoint all_disjoint nth].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U23. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r am_regs) o3_rs).
{ unfold o3_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: exact (owe_desk_apart_base E _ (kz_desk kc) sp1 U23 Hdr U2 ltac:(lia)).
  all: unfold o3_k, o3_w, o3_l;
  (apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia]). }
assert (HAF : atoms_ok E o3_AF).
{ unfold o3_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U23, X42, X43, X44, X45. rewrite !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 3) ys o3_rs o3_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd2 Hap HAF) as HS.
fold E in HS. change (owe_pc 3) with 0x823cc in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk; owe_desk_SH] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC).
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p kc) (kz_desk kc) d GM IV HAR Hpd E23
      (am_ew_SB g pos c regs2 ys)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 3 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE : env_agree 37 (am_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (owe_U_sx32 E 37 (kz_a kc) X37 ltac:(lia)) as Ua.
pose proof (owe_U_sx32 E 38 (kz_delta kc mod 2 ^ 32) X38 ltac:(lia)) as Ud.
assert (OK : owe_kZ kc (Some d) =
  owe_spec 3 (Some d) (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
unfold cfg_at. change (w64 (owe_pc 3)) with (Z_to_bv 64 0x823cc).
(* 0x823cc the check of the strips byte's shadow, lw a, lbu strips, to bgeu a,strips *)
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
(* the run took two fresh atoms (46: the shadow byte, 47: the slow check's low bits); E1 agrees with E below 46 *)
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => set (E1 := Ev) in * end.
assert (HA1 : env_agree 46 E E1) by (subst E1; apply env_agree_ewset2).
assert (HAE1 : env_agree 37 (am_env g pos c regs2 ys) E1) by (subst E1; env_agree_chain HAE).
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
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x8273c. cw_keep ltac:(owe_kwr U2_1 UF1).
  owe_fields HS UF1 Hrw Hrl. owe_fld Hrw UF1 320 1%N V320. owe_fld Hrw UF1 321 1%N V321. owe_fld Hrw UF1 322 1%N V322.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 3
    m3 r3 md3 E1 _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0] 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
  + owe_old3 V320 V321 V322 DX1 X39_1 X40_1 X41_1 Q0 Q1 Q2.
  + apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V352). vm_compute. reflexivity.
  + apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe3_spec_rng. lia.
- (* a < strips *)
  apply negb_false_iff, Z.ltb_lt in Hb1.
  assert (Ha : kz_a kc < d_strips d /\ kz_a kc < 2 ^ 31) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  (* 0x823ec lw delta, addiw t,delta,-64, li -128, to bltu t,-128 *)
  cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA). cw_keep ltac:(owe_kwr U2_1 UF1).
  assert (Hdx : U E (SExt true 32 (SOff 38 0)) = kz_delta kc mod 2 ^ 64).
  { rewrite Ud. apply o3_sx_small. lia. }
  assert (Hdx32 : U E (SExt true 32 (SOff 38 0)) mod 2 ^ 32 = kz_delta kc mod 2 ^ 32)
    by (rewrite Hdx; apply o3_mod64_32).
  cw_branch Hb2.
  all: rewrite branch_ltu_U, U_lit, (YCbn.U_agree 46 E E1 _ HA1) in Hb2 by first [reflexivity | lia].
  all: rewrite (o3_delta_U E _ (kz_delta kc) Hdx32 ltac:(lia)) in Hb2.
  + (* delta outside [-64, 63]: the E_RANGE tail *)
    apply negb_true_iff, andb_false_iff in Hb2.
    assert (Hd : kz_delta kc < -64 \/ 63 < kz_delta kc) by (destruct Hb2 as [H|H]; apply Z.leb_gt in H; lia).
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x8273c. cw_keep ltac:(owe_kwr U2_1 UF1).
    owe_fields HS UF1 Hrw Hrl. owe_fld Hrw UF1 320 1%N V320. owe_fld Hrw UF1 321 1%N V321.
    owe_fld Hrw UF1 322 1%N V322.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 3
      m3 r3 md3 E1 _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0] 0 0 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
    * owe_old3 V320 V321 V322 DX1 X39_1 X40_1 X41_1 Q0 Q1 Q2.
    * apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V352). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
    * apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe3_spec_rng. lia.
  + (* -64 <= delta <= 63: the command, to CHK *)
    apply negb_false_iff, andb_true_iff in Hb2. destruct Hb2 as [Hd1 Hd2].
    apply Z.leb_le in Hd1. apply Z.leb_le in Hd2.
    assert (U321 : bv_unsigned (sv_denot E1 (SAlu ALU_OR (SExt true 32 (SOff 37 0)) (SLit 64))) = Z.lor 64 (kz_a kc)).
    { change (U E1 (SAlu ALU_OR (SExt true 32 (SOff 37 0)) (SLit 64)) = Z.lor 64 (kz_a kc)).
      rewrite (YCbn.U_agree 46 E E1 _ HA1) by reflexivity. apply o3_or64; [|lia].
      rewrite Ua. destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia. }
    assert (U322 : bv_unsigned (sv_denot E1 (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 64))) = kz_delta kc + 64).
    { change (U E1 (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 64)) = kz_delta kc + 64).
      rewrite (YCbn.U_agree 46 E E1 _ HA1) by reflexivity. apply o3_add64; [exact Hdx | lia]. }
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2_1 UF1 EFA) 0x8273c. cw_keep ltac:(owe_kwr U2_1 UF1).
    owe_fields HS UF1 Hrw Hrl. owe_fld Hrw UF1 320 1%N V320. owe_fld Hrw UF1 321 1%N V321.
    owe_fld Hrw UF1 322 1%N V322.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 3
      m3 r3 md3 E1 _ 0 [176; u8 (Z.lor 64 (kz_a kc)); u8 (kz_delta kc + 64)] 3 (KEY 8 0) 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE1 HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | change (KEY 8 0) with 524288; lia | lia | ].
    * apply (owe_vm _ _ 4 _ _ V316). vm_compute. reflexivity.
    * apply owe_garr3;
      [ apply (owe_vm _ _ 1 _ _ V320); vm_compute; reflexivity
      | replace (FA g pos + 320 + 1) with (FA g pos + 321) by lia; apply (owe_vm _ _ 1 _ _ V321); rewrite U321
      | replace (FA g pos + 320 + 2) with (FA g pos + 322) by lia; apply (owe_vm _ _ 1 _ _ V322); rewrite U322
      | lia | apply owe_u8_range | apply owe_u8_range ];
      unfold u8; change (2 ^ (8 * Z.of_N 1)) with 256; change (2 ^ (8 * Z.of_nat 1)) with 256;
      rewrite !Z.mod_mod by lia; reflexivity.
    * apply (owe_vm _ _ 8 _ _ V344). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V352). vm_compute. reflexivity.
    * apply (owe_vm _ _ 4 _ _ V356). vm_compute. reflexivity.
    * apply (owe_want_ok_succ kc (Some d) _ [0xb0; u8 (Z.lor 0x40 (kz_a kc)); u8 (kz_delta kc + 64)] (KEY 8 0) 0).
      { rewrite OK. apply owe3_spec_ok; lia. }
      cbn [length firstn app map]. unfold u8. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
End b.
End a.
