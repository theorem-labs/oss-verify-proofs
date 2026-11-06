(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 253 of its 272 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_owe1.v, with its addresses and numbers changed; 249 of its 355 lines of code are new or changed and 166 lines of the source are left out. *)
(* Segment OWE7 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_owe 7): owe()'s
   STRIP_LEDS case (fuzz_codec.c:199-208), 0x82a68-0x82a94, the code it shares with COUNTER_LEDS 0x82dbc-0x82dc4 and
   0x82e78-0x82ed8, the E_RANGE tail 0x82dc8-0x82dcc and the reload of s9 (0x82dd0), to CHK 0x82dd4. It is the
   image-A segment (lib/A/Prog/codec_amain_owe7.v) at image B.
     0x82a68 / 0x82a70 the UBSan tests of the desk pointer s6 (NULL, not 8-aligned) and 0x82e7c (not 8-aligned): trap
     edges of codec_bmain_inv.v bm_trap_taken, which the engine decides from the desk's atom fact; 0x82a74 the
     instrumented check of the desk byte at s6 + 9 (lb of its shadow byte; lw a1 = a; bnez to 0x830d4, which goes back
     to 0x82a8c when (a mod 8) < k); lbu a0 = strips; bltu a1,a0 -> 0x82dbc, else j E_RANGE; 0x82dbc lw a2 = b;
     bgeu 127,a2 -> 0x82e78, else E_RANGE; 0x82e80 the check of the desk byte at s6 + 8 (slow part 0x83104);
     lbu a0 = device; want_display = 0; key = a | 0x50000; want = F0 13 dev 20 a b F7; 0x82ed0 want_len = 7,
     want_key; j 0x82dd0; 0x82dc8 want_rc = -11; 0x82dd0 s9 = 128(s1).
   The state: k's fields a, b read-only (atoms 37, 38), want_rc and want[0..7) writable (want[0..7) kept as atoms
   39-45 on the E_RANGE paths), want_len .. want_display writable (0 at the cut), the desk's four bytes read-only
   (atoms 46-49, base atom 22 = k.desk, with its atom fact: SPEC_C24 or SPEC_PC, 32-aligned). The engine checks both
   desk bytes against the shadow entry owe_desk_SH (codec_bmain_owel.v owe_desk_shent); each check adds two atoms to
   the environment, which agrees with the start one below atom 50.
   owe7_spec_ok, owe7_spec_rng and key5 are lib/Prog/codec_main_owe7.v:16-35 of the plain walk. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_lem codec_bmain_st codec_bmain_owel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the state at OWE7 ================================ *)
Definition o7_k : YP09.region := bm_frame_region 216 224 216 216
[YP09.mkChunk 216 (CVal 4 (SOff 37 0)); YP09.mkChunk 220 (CVal 4 (SOff 38 0))].
Definition o7_w : YP09.region := bm_frame_region 332 343 332 343
[YP09.mkChunk 332 (CVal 4 (SLit 0)); YP09.mkChunk 336 (CVal 1 (SOff 39 0)); YP09.mkChunk 337 (CVal 1 (SOff 40 0));
 YP09.mkChunk 338 (CVal 1 (SOff 41 0)); YP09.mkChunk 339 (CVal 1 (SOff 42 0)); YP09.mkChunk 340 (CVal 1 (SOff 43 0));
 YP09.mkChunk 341 (CVal 1 (SOff 44 0)); YP09.mkChunk 342 (CVal 1 (SOff 45 0))].
Definition o7_l : YP09.region := bm_frame_region 360 376 360 376
[YP09.mkChunk 360 (CVal 8 (SLit 0)); YP09.mkChunk 368 (CVal 4 (SLit 0)); YP09.mkChunk 372 (CVal 4 (SLit 0))].
Definition o7_d : YP09.region := owe_desk_region [SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0].
Definition o7_rs : smem := [o7_k; o7_w; o7_l; o7_d].
(* k.desk (s6, atom 22) is SPEC_C24 or SPEC_PC *)
Definition o7_AF : list (nat * afact) := [(22%nat, mkAF 0x9dfc0 0x9dfe0 5)].
Definition o7_ys (kc : kcallZ) (d : desk) : list Z :=
[kz_a kc; kz_b kc; nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0; nth 3 (kz_want kc) 0;
 nth 4 (kz_want kc) 0; nth 5 (kz_want kc) 0; nth 6 (kz_want kc) 0; d_dev d; d_strips d; d_chars d; d_counter d].

(* ================================ owe()'s STRIP_LEDS case ================================ *)
Lemma owe7_spec_ok : forall d a b c delta bytes n, a < d_strips d -> b <= 0x7f ->
  owe_spec 7 (Some d) a b c delta bytes n =
  (0, ([0xf0; 0x13; u8 (d_dev d); 0x20; u8 a; u8 b; 0xf7], KEY 5 a, 0)).
Proof.
  intros d a b c delta bytes n Ha Hb. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [lia|]. destruct (Z.ltb_spec 0x7f b); [lia|]. reflexivity.
Qed.
Lemma owe7_spec_rng : forall d a b c delta bytes n, d_strips d <= a \/ 0x7f < b ->
  fst (owe_spec 7 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); destruct (Z.ltb_spec 0x7f b); try reflexivity; lia.
Qed.
Lemma key5 : forall a, 0 <= a < 65536 -> Z.lor a 327680 = KEY 5 a.
Proof.
  intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small a) by lia. rewrite Z.lor_comm. reflexivity.
Qed.

(* ================================ the executor's values ================================ *)
Lemma o7_dx : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* `lbu` of a byte atom *)
Lemma o7_zx8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the key a | 0x50000 *)
Lemma o7_key_U : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_OR (SExt true 32 (SOff n 0)) (SLit 327680)) = KEY 5 v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu, (owe_U_sx32 E n v Hn ltac:(lia)), U_SLit.
destruct (Z.ltb_spec v (2 ^ 31)); [|lia]. cbn [zalu_raw].
change (zcanon 327680) with 327680.
assert (L : 0 <= Z.lor v 327680 < 2 ^ 19) by (pose proof (lor_lt_pow2 v 327680 19 ltac:(lia) ltac:(lia)); lia).
rewrite zcanon_id by (unfold M64; lia). apply key5. lia.
Qed.
(* a field the state holds, read back in the final memory *)
Lemma o7_vmw : forall m a b (w : N) E x v,
val_mem tfibsegs m a (N.to_nat w) (bv_unsigned (sv_denot E x) mod 2 ^ (8 * Z.of_N w)) -> a = b ->
U E x mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w) -> val_mem tfibsegs m b (N.to_nat w) v.
Proof.
intros m a b w E x v H <- Hv. apply (owe_vm _ _ _ _ _ H). rewrite N_nat_Z.
rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). exact Hv.
Qed.
Lemma o7_lit : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (sv_denot E (SLit z)) = z.
Proof. intros E z Hz. exact (U_lit E z Hz). Qed.
Lemma o7_at : forall m a b n v, val_mem tfibsegs m a n v -> a = b -> val_mem tfibsegs m b n v.
Proof. intros m a b n v H <-. exact H. Qed.
Lemma o7_gcons : forall m a x l, val_mem tfibsegs m a 1 x -> 0 <= x < 256 -> garr8 tfibsegs m (a + 1) l ->
garr8 tfibsegs m a (x :: l).
Proof.
intros m a x l V R G [|j] Hj.
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact V | exact R].
- cbn [nth]. destruct (G j ltac:(cbn in Hj; lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. exact Hv.
Qed.

(* the environment after a run agrees with the start one below atom NK: HA, HAE (below 37, for owe_chk_end) and
   U2 / UF (atoms 2 and 33) for it *)
Ltac o7_sync E0 NK HAE0 U2o UFo HA HAE U2 UF :=
  lazymatch goal with HS : st_ok _ ?E1 _ _ |- _ =>
    try clear HA; try clear HAE; try clear U2; try clear UF;
    assert (HA : env_agree NK E0 E1) by env_agree_chain HAE0;
    assert (HAE : env_agree 37 E0 E1) by
      (split; [intros nn Hnn; apply (proj1 HA); exact (Nat.lt_le_trans nn 37 NK Hnn ltac:(apply Nat.leb_le; reflexivity))
              | exact (proj2 HA)]);
    pose proof U2o as U2; try rewrite <- (proj1 HA 2%nat ltac:(apply Nat.ltb_lt; reflexivity)) in U2;
    pose proof UFo as UF; try rewrite <- (proj1 HA 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) in UF
  end.
(* an atom's value in the current environment *)
(* (the agreement HA is named: a failing lia on another one costs tens of seconds in this context) *)
Ltac o7_xa HA X := lazymatch type of X with ew _ ?n = _ =>
  exact (eq_trans (proj1 HA n ltac:(apply Nat.ltb_lt; reflexivity)) X) end.
(* a byte the state holds as an atom (old want bytes) *)
Ltac o7_old HA V X :=
  apply (o7_vmw _ _ _ 1%N _ _ _ V); [lia|]; rewrite (U_atom _ _ _ ltac:(o7_xa HA X)) by lia; reflexivity.
(* a literal field *)
Ltac o7_litf V w := apply (o7_vmw _ _ _ w _ _ _ V); [lia | unfold U; rewrite o7_lit by lia; reflexivity].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

Theorem seg_owe7_holds : seg_owe B MT K XM_LIB 7.
Proof using TL LAWS GM IV ROB.
unfold seg_owe. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & _ & c & kc & od & Hcur & Hkat & Hrec & Hkind & Hod & Hrc & Hw0 & Hwl0 & Hwk0 & Hwd0 & R22).
destruct od as [d|]; [|exfalso; destruct (Hod eq_refl) as [X | [X | X]]; discriminate X].
pose proof Hrec as (_ & Hpd & _ & _).
destruct (pd_range_B _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rchr & Rcnt).
unfold CM_SPEC_C24, CM_SPEC_PC in Hdv.
assert (Hdal : kz_desk kc mod 32 = 0) by (destruct Hdv as [Hd | Hd]; rewrite Hd; reflexivity).
assert (Hdr : 0x9dfc0 <= kz_desk kc <= 0x9dfe0) by (destruct Hdv as [Hd | Hd]; rewrite Hd; lia).

clear Hdv.
pose proof HC as (Hpre & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold BM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof Hkat as (HK & HW).
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbef & Gout & Vwrc & Gwant & Vwl & Vwk & Vwd).
destruct HW as (Wkind & Wp & Wdesk & Wa & Wb & Wc & Wdelta & Wn & Wrc & Wwrc & Wwl & Wwk & Wwd & Lbytes & Lbef & Lout & Lwant).
pose proof (Gwant 0%nat ltac:(lia)) as (G0 & Q0).
pose proof (Gwant 1%nat ltac:(lia)) as (G1 & Q1).
pose proof (Gwant 2%nat ltac:(lia)) as (G2 & Q2).
pose proof (Gwant 3%nat ltac:(lia)) as (G3 & Q3).
pose proof (Gwant 4%nat ltac:(lia)) as (G4 & Q4).
pose proof (Gwant 5%nat ltac:(lia)) as (G5 & Q5).
pose proof (Gwant 6%nat ltac:(lia)) as (G6 & Q6).
pose proof HC as (_ & _ & R2 & _).
set (ys := o7_ys kc d).
set (E := bm_env g pos c regs2 ys).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_a kc)) by exact (bm_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (kz_b kc)) by exact (bm_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (nth 3 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 5).
assert (X43 : ew E 43 = Z_to_bv 64 (nth 4 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 6).
assert (X44 : ew E 44 = Z_to_bv 64 (nth 5 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 7).
assert (X45 : ew E 45 = Z_to_bv 64 (nth 6 (kz_want kc) 0)) by exact (bm_ew_y g pos c regs2 ys 8).
assert (X46 : ew E 46 = Z_to_bv 64 (d_dev d)) by exact (bm_ew_y g pos c regs2 ys 9).
assert (X47 : ew E 47 = Z_to_bv 64 (d_strips d)) by exact (bm_ew_y g pos c regs2 ys 10).
assert (X48 : ew E 48 = Z_to_bv 64 (d_chars d)) by exact (bm_ew_y g pos c regs2 ys 11).
assert (X49 : ew E 49 = Z_to_bv 64 (d_counter d)) by exact (bm_ew_y g pos c regs2 ys 12).
assert (U2o : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UFo : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
assert (E22 : ew E 22 = Z_to_bv 64 (kz_desk kc)).
{ subst E. rewrite (bm_ew_reg g pos c regs2 ys 22 22%bv eq_refl), R22. reflexivity. }
assert (U22 : bv_unsigned (ew E 22) = kz_desk kc) by (rewrite E22; apply unsigned_lit_small; lia).
pose proof U2o as U2. pose proof UFo as UF.
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o7_rs).
{ unfold o7_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: { apply (owe_desk_region_ok B TL E W2 mem2 (kz_p kc) (kz_desk kc) d _ HRO Hpd U22).
       intros i Hi. destruct i as [|[|[|[|i]]]];
       [exact (o7_dx E _ _ X46) | exact (o7_dx E _ _ X47) | exact (o7_dx E _ _ X48) | exact (o7_dx E _ _ X49) | lia]. }
  all: unfold o7_k, o7_w, o7_l;
  (apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]);
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 216 4 (SOff 37 0) (kz_a kc)); [exact (o7_dx E 37%nat _ X37) | zside | zside |].
    replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact Va.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 220 4 (SOff 38 0) (kz_b kc)); [exact (o7_dx E 38%nat _ X38) | zside | zside |].
    replace (FA g pos + 220) with (FA g pos + 192 + 28) by lia. exact Vb.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. rewrite <- Hw0. exact Vwrc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 336 1 (SOff 39 0) (nth 0 (kz_want kc) 0));
    [exact (o7_dx E 39%nat _ X39) | zside | zside |].
    replace (FA g pos + 336) with (FA g pos + 192 + 144 + Z.of_nat 0) by lia. exact G0.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 337 1 (SOff 40 0) (nth 1 (kz_want kc) 0));
    [exact (o7_dx E 40%nat _ X40) | zside | zside |].
    replace (FA g pos + 337) with (FA g pos + 192 + 144 + Z.of_nat 1) by lia. exact G1.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 338 1 (SOff 41 0) (nth 2 (kz_want kc) 0));
    [exact (o7_dx E 41%nat _ X41) | zside | zside |].
    replace (FA g pos + 338) with (FA g pos + 192 + 144 + Z.of_nat 2) by lia. exact G2.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 339 1 (SOff 42 0) (nth 3 (kz_want kc) 0));
    [exact (o7_dx E 42%nat _ X42) | zside | zside |].
    replace (FA g pos + 339) with (FA g pos + 192 + 144 + Z.of_nat 3) by lia. exact G3.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 340 1 (SOff 43 0) (nth 4 (kz_want kc) 0));
    [exact (o7_dx E 43%nat _ X43) | zside | zside |].
    replace (FA g pos + 340) with (FA g pos + 192 + 144 + Z.of_nat 4) by lia. exact G4.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 341 1 (SOff 44 0) (nth 5 (kz_want kc) 0));
    [exact (o7_dx E 44%nat _ X44) | zside | zside |].
    replace (FA g pos + 341) with (FA g pos + 192 + 144 + Z.of_nat 5) by lia. exact G5.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 342 1 (SOff 45 0) (nth 6 (kz_want kc) 0));
    [exact (o7_dx E 45%nat _ X45) | zside | zside |].
    replace (FA g pos + 342) with (FA g pos + 192 + 144 + Z.of_nat 6) by lia. exact G6.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 360 8 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 360) with (FA g pos + 192 + 168) by lia. rewrite <- Hwl0. exact Vwl.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 368 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 368) with (FA g pos + 192 + 176) by lia. rewrite <- Hwk0. exact Vwk.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 372 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 372) with (FA g pos + 192 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
assert (Hpd7 : pairwise_disjoint E o7_rs).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk kc + 8) 4 216 376 HAR Hin3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as AP.
  rewrite EFA in AP.
  unfold o7_rs, o7_k, o7_w, o7_l, o7_d, owe_desk_region, bm_frame_region. cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U22. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r bm_regs) o7_rs).
{ unfold o7_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: { unfold o7_d. apply (owe_desk_apart_base E _ (kz_desk kc) sp1 U22 Hdr U2 ltac:(lia)). }
  all: unfold o7_k, o7_w, o7_l;
  apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
  [exact HJ | exact Hfr | exact HC | lia | lia]. }
assert (HAF : atoms_ok E o7_AF).
{ unfold o7_AF. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22.
  change (2 ^ 5) with 32. lia. }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 7) ys o7_rs o7_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd7 Hap HAF) as HS.
fold E in HS. change (owe_pc 7) with 0x82a68 in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk; owe_desk_SH] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC).
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p kc) (kz_desk kc) d GM IV HAR Hpd E22
      (bm_ew_SB g pos c regs2 ys)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 7 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE0 : env_agree 50 E E) by apply env_agree_refl.
assert (OK : owe_kZ kc (Some d) =
  owe_spec 7 (Some d) (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at. change (w64 (owe_pc 7)) with (Z_to_bv 64 0x82a68).
(* 0x82a68 the UBSan tests of the desk pointer (decided by the engine from its atom fact), the check of the strips
   byte, lw a, lbu strips, to bltu a,strips *)
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
o7_sync E 50%nat HAE0 U2o UFo HA HAE U2 UF.
cw_branch Hb1.
all: rewrite branch_ltu_U, (owe_U_sx32 _ 37 (kz_a kc) ltac:(o7_xa HA X37) ltac:(lia)),
  (o7_zx8 _ 47 (d_strips d) ltac:(o7_xa HA X47) Rstr) in Hb1.
- (* a < strips *)
  apply Z.ltb_lt in Hb1.
  assert (Ha : kz_a kc < d_strips d /\ kz_a kc < 2 ^ 31) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  (* 0x82dbc lw b, li 127, to bgeu 127,b *)
  cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
  o7_sync E 50%nat HAE0 U2o UFo HA HAE U2 UF.
  cw_branch Hb2.
  all: rewrite branch_geu_U, U_lit, (owe_U_sx32 _ 38 (kz_b kc) ltac:(o7_xa HA X38) ltac:(lia)) in Hb2 by lia.
  + (* b <= 127: the command, to CHK *)
    apply negb_true_iff, Z.ltb_ge in Hb2.
    assert (Hb : kz_b kc <= 127) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
    (* 0x82e78 the alignment test of the desk (decided), the check of the device byte, the stores, to CHK *)
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
    o7_sync E 50%nat HAE0 U2o UFo HA HAE U2 UF.
    owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 2%N V336. owe_fld Hrw UF 338 1%N V338.
    owe_fld Hrw UF 339 1%N V339. owe_fld Hrw UF 340 1%N V340. owe_fld Hrw UF 341 1%N V341. owe_fld Hrw UF 342 1%N V342.
    destruct (owe_split2 _ _ _ 5104 V336 ltac:(rewrite o7_lit by lia; reflexivity) ltac:(lia)) as (V336a & V336b).
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 7
      m3 r3 md3 _ _ 0 [0xf0; 0x13; d_dev d; 0x20; kz_a kc; kz_b kc; 0xf7] 7 (KEY 5 (kz_a kc)) 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | | lia | ].
    * o7_litf V332 4%N.
    * apply o7_gcons; [apply (o7_at _ _ _ _ _ V336a); lia | lia|].
      apply o7_gcons; [apply (o7_at _ _ _ _ _ V336b); lia | lia|].
      apply o7_gcons; [|lia|].
      { apply (o7_vmw _ _ _ 1%N _ _ _ V338); [lia|]. rewrite (o7_zx8 _ 46 (d_dev d) ltac:(o7_xa HA X46) Rdev).
        reflexivity. }
      apply o7_gcons; [o7_litf V339 1%N | lia |].
      apply o7_gcons; [|lia|].
      { apply (o7_vmw _ _ _ 1%N _ _ _ V340); [lia|]. rewrite (owe_U_sx32 _ 37 (kz_a kc) ltac:(o7_xa HA X37) ltac:(lia)).
        destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); [reflexivity | lia]. }
      apply o7_gcons; [|lia|].
      { apply (o7_vmw _ _ _ 1%N _ _ _ V341); [lia|]. rewrite (owe_U_sx32 _ 38 (kz_b kc) ltac:(o7_xa HA X38) ltac:(lia)).
        destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); [reflexivity | lia]. }
      apply o7_gcons; [o7_litf V342 1%N | lia | apply garr8_nil].
    * o7_litf V360 8%N.
    * apply (o7_vmw _ _ _ 4%N _ _ _ V368); [lia|]. rewrite (o7_key_U _ 37 (kz_a kc) ltac:(o7_xa HA X37) ltac:(lia)).
      reflexivity.
    * o7_litf V372 4%N.
    * rewrite <- key5 by lia. pose proof (lor_lt_pow2 (kz_a kc) 327680 19 ltac:(lia) ltac:(lia)). lia.
    * apply (owe_want_ok_succ kc (Some d) _ [0xf0; 0x13; u8 (d_dev d); 0x20; u8 (kz_a kc); u8 (kz_b kc); 0xf7]
        (KEY 5 (kz_a kc)) 0).
      { rewrite OK. apply owe7_spec_ok; lia. }
      assert (U8a : u8 (d_dev d) = d_dev d) by (apply u8_smallZ; lia).
      assert (U8b : u8 (kz_a kc) = kz_a kc) by (apply u8_smallZ; lia).
      assert (U8c : u8 (kz_b kc) = kz_b kc) by (apply u8_smallZ; lia).
      cbn [length firstn app map]. rewrite ?U8a, ?U8b, ?U8c. reflexivity.
  + (* b > 127: the E_RANGE tail, to CHK *)
    apply negb_false_iff, Z.ltb_lt in Hb2.
    assert (Hb : 127 < kz_b kc) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
    cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
    o7_sync E 50%nat HAE0 U2o UFo HA HAE U2 UF.
    owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 1%N V336. owe_fld Hrw UF 337 1%N V337. owe_fld Hrw UF 338 1%N V338.
    owe_fld Hrw UF 339 1%N V339. owe_fld Hrw UF 340 1%N V340. owe_fld Hrw UF 341 1%N V341. owe_fld Hrw UF 342 1%N V342.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 7
      m3 r3 md3 _ _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0; nth 3 (kz_want kc) 0;
                           nth 4 (kz_want kc) 0; nth 5 (kz_want kc) 0; nth 6 (kz_want kc) 0] 0 0 0
      HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
    [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
    | exact KE | | | | | | lia | lia | lia | lia | ].
    * o7_litf V332 4%N.
    * apply o7_gcons; [o7_old HA V336 X39 | exact Q0 |].
      apply o7_gcons; [o7_old HA V337 X40 | exact Q1 |].
      apply o7_gcons; [o7_old HA V338 X41 | exact Q2 |].
      apply o7_gcons; [o7_old HA V339 X42 | exact Q3 |].
      apply o7_gcons; [o7_old HA V340 X43 | exact Q4 |].
      apply o7_gcons; [o7_old HA V341 X44 | exact Q5 |].
      apply o7_gcons; [o7_old HA V342 X45 | exact Q6 | apply garr8_nil].
    * o7_litf V360 8%N.
    * o7_litf V368 4%N.
    * o7_litf V372 4%N.
    * apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe7_spec_rng. lia.
- (* strips <= a: the E_RANGE tail, to CHK *)
  apply Z.ltb_ge in Hb1.
  assert (Ha : d_strips d <= kz_a kc) by (destruct (Z.ltb_spec (kz_a kc) (2 ^ 31)); lia).
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82dd4. cw_keep ltac:(owe_kwr U2 UF).
  o7_sync E 50%nat HAE0 U2o UFo HA HAE U2 UF.
  owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 336 1%N V336. owe_fld Hrw UF 337 1%N V337. owe_fld Hrw UF 338 1%N V338.
  owe_fld Hrw UF 339 1%N V339. owe_fld Hrw UF 340 1%N V340. owe_fld Hrw UF 341 1%N V341. owe_fld Hrw UF 342 1%N V342.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 7
    m3 r3 md3 _ _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0; nth 3 (kz_want kc) 0;
                         nth 4 (kz_want kc) 0; nth 5 (kz_want kc) 0; nth 6 (kz_want kc) 0] 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + o7_litf V332 4%N.
  + apply o7_gcons; [o7_old HA V336 X39 | exact Q0 |].
    apply o7_gcons; [o7_old HA V337 X40 | exact Q1 |].
    apply o7_gcons; [o7_old HA V338 X41 | exact Q2 |].
    apply o7_gcons; [o7_old HA V339 X42 | exact Q3 |].
    apply o7_gcons; [o7_old HA V340 X43 | exact Q4 |].
    apply o7_gcons; [o7_old HA V341 X44 | exact Q5 |].
    apply o7_gcons; [o7_old HA V342 X45 | exact Q6 | apply garr8_nil].
  + o7_litf V360 8%N.
  + o7_litf V368 4%N.
  + o7_litf V372 4%N.
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe7_spec_rng. lia.
Qed.
End b.
End a.
