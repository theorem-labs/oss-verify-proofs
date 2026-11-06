(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its addresses and numbers changed; 216 of its 309 lines of code are new or changed and 173 lines of the source are left out. *)
(* Segment OWE8 of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_owe 8): owe()'s
   COUNTER_LEDS case (fuzz_codec.c:200-208), 0x8270c-0x82720, the code it shares with STRIP_LEDS 0x82724-0x8272c and
   0x827e0-0x82834, the E_RANGE tail 0x82730-0x82734 and 0x82738, to CHK 0x8273c.
     0x8270c the instrumented check of the desk byte at s7 + 11 (lb of its shadow byte; bnez to 0x82b44, which goes
     back to 0x82720 when (a mod 8) < k); lbu a1 = counter; 0x82724 lw a2 = b; bgeu 127,a2 -> 0x827e0, else E_RANGE;
     0x827e0 the check of the desk byte at s7 + 8 (slow part 0x82b5c); lbu a0 = device; want_display = 0;
     key = counter | 0x50000; want = F0 13 dev 20 counter b F7 (F0 13 from the spill 80(s1)); 0x8282c want_len = 7,
     want_key; 0x82730 want_rc = -11; 0x82738 s11 = 10.
   The state: k's field b read-only (atom 37), want_rc and want[0..7) writable (want[0..7) kept as atoms 38-44 on the
   E_RANGE path), want_len .. want_display writable (0 at the cut), the desk's four bytes read-only (atoms 45-48, base
   atom 23 = k.desk, with its atom fact: SPEC_C24 or SPEC_PC, 32-aligned). The engine checks both desk bytes against
   the shadow entry owe_desk_SH (both are marked usable: codec_amain_owel.v owe_desk_shent); each check adds two atoms
   (the shadow byte and the slow path's andi) to the environment, which agrees with the start one below atom 49.
   owe8_spec_ok, owe8_spec_rng and key5 are lib/Prog/codec_main_owe8.v:15-34 of the plain
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

(* ================================ the state at OWE8 ================================ *)
Definition o8_k : YP09.region := am_frame_region 204 208 204 204 [YP09.mkChunk 204 (CVal 4 (SOff 37 0))].
Definition o8_w : YP09.region := am_frame_region 316 327 316 327
[YP09.mkChunk 316 (CVal 4 (SLit 0)); YP09.mkChunk 320 (CVal 1 (SOff 38 0)); YP09.mkChunk 321 (CVal 1 (SOff 39 0));
 YP09.mkChunk 322 (CVal 1 (SOff 40 0)); YP09.mkChunk 323 (CVal 1 (SOff 41 0)); YP09.mkChunk 324 (CVal 1 (SOff 42 0));
 YP09.mkChunk 325 (CVal 1 (SOff 43 0)); YP09.mkChunk 326 (CVal 1 (SOff 44 0))].
Definition o8_l : YP09.region := am_frame_region 344 360 344 360
[YP09.mkChunk 344 (CVal 8 (SLit 0)); YP09.mkChunk 352 (CVal 4 (SLit 0)); YP09.mkChunk 356 (CVal 4 (SLit 0))].
Definition o8_d : YP09.region := owe_desk_region [SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0].
Definition o8_rs : smem := [o8_k; o8_w; o8_l; o8_d].
(* k.desk (s7, atom 23) is SPEC_C24 or SPEC_PC *)
Definition o8_AF : list (nat * afact) := [(23%nat, mkAF 0x9d6a0 0x9d6c0 5)].
Definition o8_ys (kc : kcallZ) (d : desk) : list Z :=
[kz_b kc; nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0; nth 3 (kz_want kc) 0;
 nth 4 (kz_want kc) 0; nth 5 (kz_want kc) 0; nth 6 (kz_want kc) 0; d_dev d; d_strips d; d_chars d; d_counter d].

(* ================================ owe()'s COUNTER_LEDS case ================================ *)
Lemma owe8_spec_ok : forall d a b c delta bytes n, b <= 0x7f ->
  owe_spec 8 (Some d) a b c delta bytes n =
  (0, ([0xf0; 0x13; u8 (d_dev d); 0x20; u8 (d_counter d); u8 b; 0xf7], KEY 5 (d_counter d), 0)).
Proof.
  intros d a b c delta bytes n Hb. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.ltb_spec 0x7f b); [lia|]. reflexivity.
Qed.
Lemma owe8_spec_rng : forall d a b c delta bytes n, 0x7f < b ->
  fst (owe_spec 8 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.ltb_spec 0x7f b); [reflexivity | lia].
Qed.
Lemma key5 : forall a, 0 <= a < 65536 -> Z.lor a 327680 = KEY 5 a.
Proof.
  intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small a) by lia. rewrite Z.lor_comm. reflexivity.
Qed.

(* ================================ the executor's values ================================ *)
Lemma o8_dx : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* `lbu` of a byte atom *)
Lemma o8_zx8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the key counter | 0x50000 *)
Lemma o8_key_U : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_OR (SExt false 8 (SOff n 0)) (SLit 327680)) = KEY 5 v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu, (o8_zx8 E n v Hn Hv), U_SLit. cbn [zalu_raw].
change (zcanon 327680) with 327680.
assert (L : 0 <= Z.lor v 327680 < 2 ^ 19) by (pose proof (lor_lt_pow2 v 327680 19 ltac:(lia) ltac:(lia)); lia).
rewrite zcanon_id by (unfold M64; lia). apply key5. lia.
Qed.
(* a field the state holds, read back in the final memory *)
Lemma o8_vmw : forall m a b (w : N) E x v,
val_mem tfibsegs m a (N.to_nat w) (bv_unsigned (sv_denot E x) mod 2 ^ (8 * Z.of_N w)) -> a = b ->
U E x mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w) -> val_mem tfibsegs m b (N.to_nat w) v.
Proof.
intros m a b w E x v H <- Hv. apply (owe_vm _ _ _ _ _ H). rewrite N_nat_Z.
rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). exact Hv.
Qed.
Lemma o8_lit : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (sv_denot E (SLit z)) = z.
Proof. intros E z Hz. exact (U_lit E z Hz). Qed.
Lemma o8_at : forall m a b n v, val_mem tfibsegs m a n v -> a = b -> val_mem tfibsegs m b n v.
Proof. intros m a b n v H <-. exact H. Qed.
Lemma o8_gcons : forall m a x l, val_mem tfibsegs m a 1 x -> 0 <= x < 256 -> garr8 tfibsegs m (a + 1) l ->
garr8 tfibsegs m a (x :: l).
Proof.
intros m a x l V R G [|j] Hj.
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact V | exact R].
- cbn [nth]. destruct (G j ltac:(cbn in Hj; lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. exact Hv.
Qed.

(* the environment after a run agrees with the start one below atom NK: HA, HAE (below 37, for owe_chk_end) and
   U2 / UF (atoms 2 and 33) for it *)
Ltac o8_sync E0 NK HAE0 U2o UFo HA HAE U2 UF :=
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
Ltac o8_xa HA X := lazymatch type of X with ew _ ?n = _ =>
  exact (eq_trans (proj1 HA n ltac:(apply Nat.ltb_lt; reflexivity)) X) end.
(* a byte the state holds as an atom (old want bytes) *)
Ltac o8_old HA V X Q :=
  apply (o8_vmw _ _ _ 1%N _ _ _ V); [lia|]; rewrite (U_atom _ _ _ ltac:(o8_xa HA X)) by lia; reflexivity.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

Theorem seg_owe8_holds : seg_owe B MT K XM_LIB 8.
Proof using TL LAWS GM IV ROB.
unfold seg_owe. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & _ & c & kc & od & Hcur & Hkat & Hrec & Hkind & Hod & Hrc & Hw0 & Hwl0 & Hwk0 & Hwd0 & R23).
destruct od as [d|]; [|exfalso; destruct (Hod eq_refl) as [X | [X | X]]; discriminate X].
pose proof Hrec as (_ & Hpd & _ & _).
destruct (pd_range_A _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rchr & Rcnt).
unfold CM_SPEC_C24, CM_SPEC_PC in Hdv.
assert (Hdal : kz_desk kc mod 32 = 0) by (destruct Hdv as [Hd | Hd]; rewrite Hd; reflexivity).
assert (Hdr : 0x9d6a0 <= kz_desk kc <= 0x9d6c0) by (destruct Hdv as [Hd | Hd]; rewrite Hd; lia).
clear Hdv.
pose proof HC as (Hpre & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
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
set (ys := o8_ys kc d).
set (E := am_env g pos c regs2 ys).
assert (X37 : ew E 37 = Z_to_bv 64 (kz_b kc)) by exact (am_ew_y g pos c regs2 ys 0).
assert (X38 : ew E 38 = Z_to_bv 64 (nth 0 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 1).
assert (X39 : ew E 39 = Z_to_bv 64 (nth 1 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 2).
assert (X40 : ew E 40 = Z_to_bv 64 (nth 2 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 3).
assert (X41 : ew E 41 = Z_to_bv 64 (nth 3 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 4).
assert (X42 : ew E 42 = Z_to_bv 64 (nth 4 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 5).
assert (X43 : ew E 43 = Z_to_bv 64 (nth 5 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 6).
assert (X44 : ew E 44 = Z_to_bv 64 (nth 6 (kz_want kc) 0)) by exact (am_ew_y g pos c regs2 ys 7).
assert (X45 : ew E 45 = Z_to_bv 64 (d_dev d)) by exact (am_ew_y g pos c regs2 ys 8).
assert (X46 : ew E 46 = Z_to_bv 64 (d_strips d)) by exact (am_ew_y g pos c regs2 ys 9).
assert (X47 : ew E 47 = Z_to_bv 64 (d_chars d)) by exact (am_ew_y g pos c regs2 ys 10).
assert (X48 : ew E 48 = Z_to_bv 64 (d_counter d)) by exact (am_ew_y g pos c regs2 ys 11).
assert (U2o : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UFo : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 (kz_desk kc)).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 23 23%bv eq_refl), R23. reflexivity. }
assert (U23 : bv_unsigned (ew E 23) = kz_desk kc) by (rewrite E23; apply unsigned_lit_small; lia).
pose proof U2o as U2. pose proof UFo as UF.
(* the entry state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o8_rs).
{ unfold o8_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: { apply (owe_desk_region_ok B TL E W2 mem2 (kz_p kc) (kz_desk kc) d _ HRO Hpd U23).
       intros i Hi. destruct i as [|[|[|[|i]]]];
       [exact (o8_dx E _ _ X45) | exact (o8_dx E _ _ X46) | exact (o8_dx E _ _ X47) | exact (o8_dx E _ _ X48) | lia]. }
  all: unfold o8_k, o8_w, o8_l;
  (apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
   [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | ]);
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 204 4 (SOff 37 0) (kz_b kc)); [exact (o8_dx E 37%nat _ X37) | zside | zside |].
    replace (FA g pos + 204) with (FA g pos + 176 + 28) by lia. exact Vb.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 316 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia. rewrite <- Hw0. exact Vwrc.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 320 1 (SOff 38 0) (nth 0 (kz_want kc) 0)); [exact (o8_dx E 38%nat _ X38) | zside | zside |].
    replace (FA g pos + 320) with (FA g pos + 176 + 144 + Z.of_nat 0) by lia. exact G0.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 321 1 (SOff 39 0) (nth 1 (kz_want kc) 0)); [exact (o8_dx E 39%nat _ X39) | zside | zside |].
    replace (FA g pos + 321) with (FA g pos + 176 + 144 + Z.of_nat 1) by lia. exact G1.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 322 1 (SOff 40 0) (nth 2 (kz_want kc) 0)); [exact (o8_dx E 40%nat _ X40) | zside | zside |].
    replace (FA g pos + 322) with (FA g pos + 176 + 144 + Z.of_nat 2) by lia. exact G2.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 323 1 (SOff 41 0) (nth 3 (kz_want kc) 0)); [exact (o8_dx E 41%nat _ X41) | zside | zside |].
    replace (FA g pos + 323) with (FA g pos + 176 + 144 + Z.of_nat 3) by lia. exact G3.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 324 1 (SOff 42 0) (nth 4 (kz_want kc) 0)); [exact (o8_dx E 42%nat _ X42) | zside | zside |].
    replace (FA g pos + 324) with (FA g pos + 176 + 144 + Z.of_nat 4) by lia. exact G4.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 325 1 (SOff 43 0) (nth 5 (kz_want kc) 0)); [exact (o8_dx E 43%nat _ X43) | zside | zside |].
    replace (FA g pos + 325) with (FA g pos + 176 + 144 + Z.of_nat 5) by lia. exact G5.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 326 1 (SOff 44 0) (nth 6 (kz_want kc) 0)); [exact (o8_dx E 44%nat _ X44) | zside | zside |].
    replace (FA g pos + 326) with (FA g pos + 176 + 144 + Z.of_nat 6) by lia. exact G6.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 344 8 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. rewrite <- Hwl0. exact Vwl.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 352 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. rewrite <- Hwk0. exact Vwk.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 356 4 (SLit 0) 0); [reflexivity | zside | zside |].
    replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. rewrite <- Hwd0. exact Vwd. }
assert (Hpd8 : pairwise_disjoint E o8_rs).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk kc + 8) 4 0 448 HAR Hin3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as AP.
  rewrite EFA in AP.
  unfold o8_rs, o8_k, o8_w, o8_l, o8_d, owe_desk_region, am_frame_region. cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UF, U23. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r am_regs) o8_rs).
{ unfold o8_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  4: { unfold o8_d. apply (owe_desk_apart_base E _ (kz_desk kc) sp1 U23 Hdr U2 ltac:(lia)). }
  all: unfold o8_k, o8_w, o8_l;
  apply (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys);
  [exact HJ | exact Hfr | exact HC | lia | lia]. }
assert (HAF : atoms_ok E o8_AF).
{ unfold o8_AF. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23.
  change (2 ^ 5) with 32. lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c (owe_pc 8) ys o8_rs o8_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd8 Hap HAF) as HS.
fold E in HS. change (owe_pc 8) with 0x8270c in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk; owe_desk_SH] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC).
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p kc) (kz_desk kc) d GM IV HAR Hpd E23
      (am_ew_SB g pos c regs2 ys)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 7 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HAE0 : env_agree 49 E E) by apply env_agree_refl.
assert (OK : owe_kZ kc (Some d) =
  owe_spec 8 (Some d) (kz_a kc) (kz_b kc) (kz_c kc) (kz_delta kc) (kz_bytes kc) (kz_n kc))
  by (unfold owe_kZ; rewrite Hkind; reflexivity).
pose proof HJ as HJR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at. change (w64 (owe_pc 8)) with (Z_to_bv 64 0x8270c).
(* 0x8270c the check of the counter byte, lbu, lw b, li 127, to bgeu 127,b *)
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA). cw_keep ltac:(owe_kwr U2 UF).
o8_sync E 49%nat HAE0 U2o UFo HA HAE U2 UF.
cw_branch Hb1.
all: rewrite branch_geu_U, U_lit, (owe_U_sx32 _ 37 (kz_b kc) ltac:(o8_xa HA X37) ltac:(lia)) in Hb1 by lia.
- (* b <= 127: the command, to CHK *)
  apply negb_true_iff, Z.ltb_ge in Hb1.
  assert (Hb : kz_b kc <= 127) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
  (* 0x827e0 the check of the device byte, the stores, to CHK *)
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x8273c. cw_keep ltac:(owe_kwr U2 UF).
  o8_sync E 49%nat HAE0 U2o UFo HA HAE U2 UF.
  owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 320 2%N V320. owe_fld Hrw UF 322 1%N V322.
  owe_fld Hrw UF 323 1%N V323. owe_fld Hrw UF 324 1%N V324. owe_fld Hrw UF 325 1%N V325. owe_fld Hrw UF 326 1%N V326.
  destruct (owe_split2 _ _ _ 5104 V320 ltac:(rewrite o8_lit by lia; reflexivity) ltac:(lia)) as (V320a & V320b).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 7
    m3 r3 md3 _ _ 0 [0xf0; 0x13; d_dev d; 0x20; d_counter d; kz_b kc; 0xf7] 7 (KEY 5 (d_counter d)) 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | | lia | ].
  + apply (o8_vmw _ _ _ 4%N _ _ _ V316); [lia | unfold U; rewrite o8_lit by lia; reflexivity].
  + apply o8_gcons; [apply (o8_at _ _ _ _ _ V320a); lia | lia|].
    apply o8_gcons; [apply (o8_at _ _ _ _ _ V320b); lia | lia|].
    apply o8_gcons; [|lia|].
    { apply (o8_vmw _ _ _ 1%N _ _ _ V322); [lia|]. rewrite (o8_zx8 _ 45 (d_dev d) ltac:(o8_xa HA X45) Rdev).
      reflexivity. }
    apply o8_gcons; [|lia|].
    { apply (o8_vmw _ _ _ 1%N _ _ _ V323); [lia|]. unfold U. rewrite o8_lit by lia. reflexivity. }
    apply o8_gcons; [|lia|].
    { apply (o8_vmw _ _ _ 1%N _ _ _ V324); [lia|]. rewrite (o8_zx8 _ 48 (d_counter d) ltac:(o8_xa HA X48) Rcnt).
      reflexivity. }
    apply o8_gcons; [|lia|].
    { apply (o8_vmw _ _ _ 1%N _ _ _ V325); [lia|]. rewrite (owe_U_sx32 _ 37 (kz_b kc) ltac:(o8_xa HA X37) ltac:(lia)).
      destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); [reflexivity | lia]. }
    apply o8_gcons; [|lia|apply garr8_nil].
    { apply (o8_vmw _ _ _ 1%N _ _ _ V326); [lia|]. unfold U. rewrite o8_lit by lia. reflexivity. }
  + apply (o8_vmw _ _ _ 8%N _ _ _ V344); [lia | unfold U; rewrite o8_lit by lia; reflexivity].
  + apply (o8_vmw _ _ _ 4%N _ _ _ V352); [lia|]. rewrite (o8_key_U _ 48 (d_counter d) ltac:(o8_xa HA X48) Rcnt).
    reflexivity.
  + apply (o8_vmw _ _ _ 4%N _ _ _ V356); [lia | unfold U; rewrite o8_lit by lia; reflexivity].
  + rewrite <- key5 by lia. pose proof (lor_lt_pow2 (d_counter d) 327680 19 ltac:(lia) ltac:(lia)). lia.
  + apply (owe_want_ok_succ kc (Some d) _ [0xf0; 0x13; u8 (d_dev d); 0x20; u8 (d_counter d); u8 (kz_b kc); 0xf7]
      (KEY 5 (d_counter d)) 0).
    { rewrite OK. apply owe8_spec_ok. lia. }
    assert (U8a : u8 (d_dev d) = d_dev d) by (apply u8_smallZ; lia).
    assert (U8b : u8 (d_counter d) = d_counter d) by (apply u8_smallZ; lia).
    assert (U8c : u8 (kz_b kc) = kz_b kc) by (apply u8_smallZ; lia).
    cbn [length firstn app map]. rewrite ?U8a, ?U8b, ?U8c. reflexivity.
- (* b > 127: the E_RANGE tail, to CHK *)
  apply negb_false_iff, Z.ltb_lt in Hb1.
  assert (Hb : 127 < kz_b kc) by (destruct (Z.ltb_spec (kz_b kc) (2 ^ 31)); lia).
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x8273c. cw_keep ltac:(owe_kwr U2 UF).
  o8_sync E 49%nat HAE0 U2o UFo HA HAE U2 UF.
  owe_fields HS UF Hrw Hrl. owe_fld Hrw UF 320 1%N V320. owe_fld Hrw UF 321 1%N V321. owe_fld Hrw UF 322 1%N V322.
  owe_fld Hrw UF 323 1%N V323. owe_fld Hrw UF 324 1%N V324. owe_fld Hrw UF 325 1%N V325. owe_fld Hrw UF 326 1%N V326.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys kc (Some d) 7
    m3 r3 md3 _ _ (-11) [nth 0 (kz_want kc) 0; nth 1 (kz_want kc) 0; nth 2 (kz_want kc) 0; nth 3 (kz_want kc) 0;
                         nth 4 (kz_want kc) 0; nth 5 (kz_want kc) 0; nth 6 (kz_want kc) 0] 0 0 0
    HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HJR HAE HS) end;
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia
  | exact KE | | | | | | lia | lia | lia | lia | ].
  + apply (o8_vmw _ _ _ 4%N _ _ _ V316); [lia | unfold U; rewrite o8_lit by lia; reflexivity].
  + apply o8_gcons; [o8_old HA V320 X38 Q0 | exact Q0 |].
    apply o8_gcons; [o8_old HA V321 X39 Q1 | exact Q1 |].
    apply o8_gcons; [o8_old HA V322 X40 Q2 | exact Q2 |].
    apply o8_gcons; [o8_old HA V323 X41 Q3 | exact Q3 |].
    apply o8_gcons; [o8_old HA V324 X42 Q4 | exact Q4 |].
    apply o8_gcons; [o8_old HA V325 X43 Q5 | exact Q5 |].
    apply o8_gcons; [o8_old HA V326 X44 Q6 | exact Q6 | apply garr8_nil].
  + apply (o8_vmw _ _ _ 8%N _ _ _ V344); [lia | unfold U; rewrite o8_lit by lia; reflexivity].
  + apply (o8_vmw _ _ _ 4%N _ _ _ V352); [lia | unfold U; rewrite o8_lit by lia; reflexivity].
  + apply (o8_vmw _ _ _ 4%N _ _ _ V356); [lia | unfold U; rewrite o8_lit by lia; reflexivity].
  + apply owe_want_ok_fail; [|discriminate]. rewrite OK. apply owe8_spec_rng. lia.
Qed.
End b.
End a.
