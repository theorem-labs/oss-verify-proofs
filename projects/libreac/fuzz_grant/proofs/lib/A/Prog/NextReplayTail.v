(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextReplayTail), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC93.v. *)
(* The re-assert tail of reac_headamp_tx_next on the ASan build (fuzz_grant.asan 0x85374,
   the slot lib/A/Prog/HeadampTxNext.v names RSWP), proved as the cut nx_resweep_spec of
   lib/A/Prog/NextReplayDefs.v.

   The tail reads the period (452), the remembered width (450) and the silence counter
   (456), adds one to the counter and stores it, and either goes to the re-arm block
   REARM (0x85404), whose cut nx_rearm_spec it takes as a hypothesis, or returns 0 with
   the table as Pau Aliagas's resweep (lib/Prog/NextModel.v) gives it. Each of its three
   instrumented accesses loads the shadow byte at (a >> 3) + 0x7fff8000 and branches to the
   error path (a call of __asan_report_* ), which the proof shows is not reached: the shadow
   entry mkSHE 10 0 460 (the 460-byte table) decides the three checks inside the engine.
   The period's and the width's shadow bytes cover only table bytes (marked usable), so the
   engine reads them as 0; the counter's granule holds the table's last four bytes, so the
   engine follows the check's slow path and finds the access inside the table. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase YC1g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SegSetModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
NextArith HeadampTxEffective HeadampTxNext NextReplayDefs NextRearmDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------- *)
(* 32-bit values sign-extended to 64 bits (lw, addiw).               *)

Lemma rt_mod32_zcanon : forall z, zcanon z mod 4294967296 = z mod 4294967296.
Proof.
  intros z. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
  apply Z.mod_mod_divide. exists 4294967296. reflexivity.
Qed.

Lemma rt_swrap_mod : forall z, bv_swrap 32 z mod 4294967296 = z mod 4294967296.
Proof.
  intros z. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma rt_swrap_modin : forall z, bv_swrap 32 z = bv_swrap 32 (z mod 4294967296).
Proof.
  intros z. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma rt_sx : forall x, 0 <= x < 4294967296 ->
  zcanon (bv_swrap 32 x) = if x <? 2147483648 then x else x + 18446744069414584320.
Proof.
  intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap.
  change (2 ^ 64) with 18446744073709551616.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  destruct (Z.ltb_spec x 2147483648) as [Hl|Hl].
  - rewrite (Z.mod_small (x + 2147483648) 4294967296) by lia.
    replace (x + 2147483648 - 2147483648) with x by lia. apply Z.mod_small. lia.
  - assert (Hm : (x + 2147483648) mod 4294967296 = x - 2147483648)
      by (first [apply (Z.mod_unique _ _ 1) | symmetry; apply (Z.mod_unique _ _ 1)]; lia).
    rewrite Hm.
    first [apply (Z.mod_unique _ _ (-1)) | symmetry; apply (Z.mod_unique _ _ (-1))]; lia.
Qed.

Lemma rt_sx_lt : forall x y, 0 <= x < 4294967296 -> 0 <= y < 4294967296 ->
  (zcanon (bv_swrap 32 x) <? zcanon (bv_swrap 32 y)) = (x <? y).
Proof.
  intros x y Hx Hy. rewrite (rt_sx x Hx), (rt_sx y Hy).
  destruct (Z.ltb_spec x 2147483648) as [H1|H1]; destruct (Z.ltb_spec y 2147483648) as [H2|H2];
    cbv iota; destruct (Z.ltb_spec x y) as [H3|H3];
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Lemma rt_sx_eq0 : forall x, 0 <= x < 4294967296 -> (zcanon (bv_swrap 32 x) =? 0) = (x =? 0).
Proof.
  intros x Hx. rewrite (rt_sx x Hx).
  destruct (Z.ltb_spec x 2147483648) as [H1|H1]; cbv iota; destruct (Z.eqb_spec x 0) as [H2|H2];
    first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.

Lemma rt_U_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 4294967296 ->
  U E (SExt true 32 (SOff n 0)) = zcanon (bv_swrap 32 v).
Proof.
  intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia.
  change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small v) by lia. reflexivity.
Qed.

(* The value the tail stores into the silence counter: its low 32 bits. *)
Definition RT_TICK : sv := SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1).

Lemma rt_tick_U : forall E v, ew E 35 = Z_to_bv 64 v -> 0 <= v < 4294967296 ->
  U E RT_TICK = zcanon (bv_swrap 32 ((v + 1) mod 4294967296)).
Proof.
  intros E v H35 Hv. unfold RT_TICK. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
  change (2 ^ 32) with 4294967296.
  rewrite (rt_U_sext E 35 v H35 Hv), U_SLit, rt_mod32_zcanon, rt_swrap_mod.
  rewrite (Z.mod_small v) by lia. change (zcanon 1 mod 4294967296) with 1.
  rewrite <- zcanon_wrap. rewrite <- rt_swrap_modin. reflexivity.
Qed.

Lemma rt_tick_mod : forall E v, ew E 35 = Z_to_bv 64 v -> 0 <= v < 4294967296 ->
  bv_unsigned (sv_denot E RT_TICK) mod 4294967296 = (v + 1) mod 4294967296.
Proof.
  intros E v H35 Hv. change (bv_unsigned (sv_denot E RT_TICK)) with (U E RT_TICK).
  rewrite (rt_tick_U E v H35 Hv), rt_mod32_zcanon, rt_swrap_mod. apply Z.mod_mod. lia.
Qed.

(* One byte of a word depends only on the word's low 32 bits when it is one of the low four. *)
Lemma rt_div_low : forall r q i, 0 <= i < 4 ->
  ((4294967296 * q + r) / 2 ^ (8 * i)) mod 256 = (r / 2 ^ (8 * i)) mod 256.
Proof.
  intros r q i Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia.
  - change (2 ^ (8 * 0)) with 1. rewrite !Z.div_1_r.
    replace (4294967296 * q + r) with (r + (16777216 * q) * 256) by ring. apply Z_mod_plus_full.
  - change (2 ^ (8 * 1)) with 256.
    replace (4294967296 * q + r) with (r + (16777216 * q) * 256) by ring. rewrite Z.div_add by lia.
    replace (r / 256 + 16777216 * q) with (r / 256 + (65536 * q) * 256) by ring. apply Z_mod_plus_full.
  - change (2 ^ (8 * 2)) with 65536.
    replace (4294967296 * q + r) with (r + (65536 * q) * 65536) by ring. rewrite Z.div_add by lia.
    replace (r / 65536 + 65536 * q) with (r / 65536 + (256 * q) * 256) by ring. apply Z_mod_plus_full.
  - change (2 ^ (8 * 3)) with 16777216.
    replace (4294967296 * q + r) with (r + (256 * q) * 16777216) by ring. rewrite Z.div_add by lia.
    replace (r / 16777216 + 256 * q) with (r / 16777216 + q * 256) by ring. apply Z_mod_plus_full.
Qed.

Lemma rt_byte_mod32 : forall (w1 w2 : word) i, 0 <= i < 4 ->
  bv_unsigned w1 mod 4294967296 = bv_unsigned w2 mod 4294967296 ->
  byte_of_word w1 i = byte_of_word w2 i.
Proof.
  intros w1 w2 i Hi H. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (Z.div_mod (bv_unsigned w1) 4294967296) by lia.
  rewrite (Z.div_mod (bv_unsigned w2) 4294967296) by lia.
  rewrite !rt_div_low by lia. rewrite H. reflexivity.
Qed.

Lemma rt_getrZ : forall (regs : bvmap 5 word) (r : bv 5) (z : Z), z = bv_unsigned r ->
  getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
  intros regs r z ->. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma rt_r5_nz : (5%bv : bv 5) <> 0%bv.
Proof. intros X. apply (f_equal (@bv_unsigned 5)) in X. vm_compute in X. discriminate X. Qed.

(* The callee-saved registers, each as the call left it. *)
Lemma rt_preserved : forall regs regs2 : bvmap 5 word,
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  getr regs2 18 = getr regs 18 -> getr regs2 19 = getr regs 19 -> getr regs2 20 = getr regs 20 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 23 = getr regs 23 ->
  getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 -> getr regs2 26 = getr regs 26 ->
  getr regs2 27 = getr regs 27 ->
  aregs_preserved regs regs2.
Proof.
  intros regs regs2 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
  unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - rewrite (rt_getrZ regs2 2%bv 2 eq_refl), (rt_getrZ regs 2%bv 2 eq_refl). exact H2.
  - rewrite (rt_getrZ regs2 3%bv 3 eq_refl), (rt_getrZ regs 3%bv 3 eq_refl). exact H3.
  - rewrite (rt_getrZ regs2 4%bv 4 eq_refl), (rt_getrZ regs 4%bv 4 eq_refl). exact H4.
  - rewrite (rt_getrZ regs2 8%bv 8 eq_refl), (rt_getrZ regs 8%bv 8 eq_refl). exact H8.
  - rewrite (rt_getrZ regs2 9%bv 9 eq_refl), (rt_getrZ regs 9%bv 9 eq_refl). exact H9.
  - rewrite (rt_getrZ regs2 18%bv 18 eq_refl), (rt_getrZ regs 18%bv 18 eq_refl). exact H18.
  - rewrite (rt_getrZ regs2 19%bv 19 eq_refl), (rt_getrZ regs 19%bv 19 eq_refl). exact H19.
  - rewrite (rt_getrZ regs2 20%bv 20 eq_refl), (rt_getrZ regs 20%bv 20 eq_refl). exact H20.
  - rewrite (rt_getrZ regs2 21%bv 21 eq_refl), (rt_getrZ regs 21%bv 21 eq_refl). exact H21.
  - rewrite (rt_getrZ regs2 22%bv 22 eq_refl), (rt_getrZ regs 22%bv 22 eq_refl). exact H22.
  - rewrite (rt_getrZ regs2 23%bv 23 eq_refl), (rt_getrZ regs 23%bv 23 eq_refl). exact H23.
  - rewrite (rt_getrZ regs2 24%bv 24 eq_refl), (rt_getrZ regs 24%bv 24 eq_refl). exact H24.
  - rewrite (rt_getrZ regs2 25%bv 25 eq_refl), (rt_getrZ regs 25%bv 25 eq_refl). exact H25.
  - rewrite (rt_getrZ regs2 26%bv 26 eq_refl), (rt_getrZ regs 26%bv 26 eq_refl). exact H26.
  - rewrite (rt_getrZ regs2 27%bv 27 eq_refl), (rt_getrZ regs 27%bv 27 eq_refl). exact H27.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* ---------------------------------------------------------------- *)
(* The symbolic state at RSWP.  Atom 2 is the machine's sp (the call's sp less 80),
   10 the table, 32 the shadow base, 33..35 the width, the period and the silence counter
   the tail reads, and 36..45 the ten registers the prologue saved (ra, s0..s8), which the
   epilogue reads back.  The machine stack and the two fields the tail only reads are
   read-only regions; RT_TXW (the counter, written) is added before the counter's access. *)
Definition RT_STK : YP09.region := YP09.mkRegion (Some 2%nat) 0 80 0 0
  [ YP09.mkChunk 72 (CVal 8 (SOff 36 0)); YP09.mkChunk 64 (CVal 8 (SOff 37 0));
    YP09.mkChunk 56 (CVal 8 (SOff 38 0)); YP09.mkChunk 48 (CVal 8 (SOff 39 0));
    YP09.mkChunk 40 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 41 0));
    YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 16 (CVal 8 (SOff 43 0));
    YP09.mkChunk 8 (CVal 8 (SOff 44 0)); YP09.mkChunk 0 (CVal 8 (SOff 45 0)) ].
Definition RT_TXR : YP09.region := YP09.mkRegion (Some 10%nat) 450 456 450 450
  [ YP09.mkChunk 450 (CVal 1 (SOff 33 0)); YP09.mkChunk 452 (CVal 4 (SOff 34 0)) ].
Definition RT_TXW : YP09.region := YP09.mkRegion (Some 10%nat) 456 460 456 460
  [ YP09.mkChunk 456 (CVal 4 (SOff 35 0)) ].
Definition rt_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46 - 80) (2 ^ 47 - 80) 4); (10%nat, PTRN 4); (32%nat, mkAF SB_NX SB_NX 0);
            (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 4294967295 0); (35%nat, mkAF 0 4294967295 0) ] [] [].
Definition rt_SH : list shent := [ mkSHE 10 0 460 ].
Definition rt_sr : list sv := sr_set sr_atoms (5%bv : bv 5) (SOff 32 0).
Definition ss_rt : sstate := mkSS RSWP rt_sr [ RT_STK; RT_TXR ] None rt_facts.

Definition rt_extra (regs : bvmap 5 word) (Tj : list byte) : list word :=
  map (Z_to_bv 64) [ SB_NX; tb Tj 450; u32at Tj 452; u32at Tj 456 ] ++
  [ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
    getr regs 21; getr regs 22; getr regs 23; getr regs 24 ].
Definition ERT (regsj regs : bvmap 5 word) (Tj : list byte) : env :=
  Eimg (Ereg regsj (rt_extra regs Tj)).

(* What the walk needs of an environment. *)
Definition rt_env_ok (E : env) (regs : bvmap 5 word) (tx : Z) (Tj : list byte) : Prop :=
  ew E 2 = Z_to_bv 64 (spZ regs - NEXT_STK) /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\
  ew E 6 = Z_to_bv 64 (SHADOW_OFF + (tx + 437) / 8) /\ ew E 10 = Z_to_bv 64 tx /\
  ew E 25 = getr regs 25 /\ ew E 26 = getr regs 26 /\ ew E 27 = getr regs 27 /\
  ew E 32 = Z_to_bv 64 SB_NX /\ ew E 33 = Z_to_bv 64 (tb Tj 450) /\
  ew E 34 = Z_to_bv 64 (u32at Tj 452) /\ ew E 35 = Z_to_bv 64 (u32at Tj 456) /\
  ew E 36 = getr regs 1 /\ ew E 37 = getr regs 8 /\ ew E 38 = getr regs 9 /\
  ew E 39 = getr regs 18 /\ ew E 40 = getr regs 19 /\ ew E 41 = getr regs 20 /\
  ew E 42 = getr regs 21 /\ ew E 43 = getr regs 22 /\ ew E 44 = getr regs 23 /\
  ew E 45 = getr regs 24.

Lemma rt_env_lift : forall E E' regs tx Tj,
  (forall n, (n < 46)%nat -> ew E' n = ew E n) -> rt_env_ok E regs tx Tj -> rt_env_ok E' regs tx Tj.
Proof.
  intros E E' regs tx Tj HA H. unfold rt_env_ok in *. rewrite !HA by lia. exact H.
Qed.

Lemma rt_env : forall (regs regsj : bvmap 5 word) (tx chp parp valp : Z) (Tj : list byte),
  nx_at_rswp regs regsj tx chp parp valp -> rt_env_ok (ERT regsj regs Tj) regs tx Tj.
Proof.
  intros regs regsj tx chp parp valp Tj (KG & R2 & R5 & R6 & R10 & R15).
  assert (EL : forall n, (n < A_TEXT)%nat ->
            ew (ERT regsj regs Tj) n = ew (Ereg regsj (rt_extra regs Tj)) n)
    by (intros n Hn; unfold ERT; apply Eimg_low; exact Hn).
  unfold rt_env_ok. repeat match goal with |- _ /\ _ => split end;
    rewrite EL by (unfold A_TEXT; lia).
  - rewrite (ew_Ereg_nat regsj _ 2 2%bv eq_refl). exact R2.
  - rewrite (ew_Ereg_nat regsj _ 3 3%bv eq_refl). apply KG. cbn [In]. auto 10.
  - rewrite (ew_Ereg_nat regsj _ 4 4%bv eq_refl). apply KG. cbn [In]. auto 10.
  - rewrite (ew_Ereg_nat regsj _ 6 6%bv eq_refl). exact R6.
  - rewrite (ew_Ereg_nat regsj _ 10 10%bv eq_refl). exact R10.
  - rewrite (ew_Ereg_nat regsj _ 25 25%bv eq_refl). apply KG. cbn [In]. auto 10.
  - rewrite (ew_Ereg_nat regsj _ 26 26%bv eq_refl). apply KG. cbn [In]. auto 10.
  - rewrite (ew_Ereg_nat regsj _ 27 27%bv eq_refl). apply KG. cbn [In]. auto 10.
  - exact (ew_Ereg_extra regsj _ 0).
  - exact (ew_Ereg_extra regsj _ 1).
  - exact (ew_Ereg_extra regsj _ 2).
  - exact (ew_Ereg_extra regsj _ 3).
  - exact (ew_Ereg_extra regsj _ 4).
  - exact (ew_Ereg_extra regsj _ 5).
  - exact (ew_Ereg_extra regsj _ 6).
  - exact (ew_Ereg_extra regsj _ 7).
  - exact (ew_Ereg_extra regsj _ 8).
  - exact (ew_Ereg_extra regsj _ 9).
  - exact (ew_Ereg_extra regsj _ 10).
  - exact (ew_Ereg_extra regsj _ 11).
  - exact (ew_Ereg_extra regsj _ 12).
  - exact (ew_Ereg_extra regsj _ 13).
Qed.

(* ---------------------------------------------------------------- *)
(* What a run leaves of the memory.                                   *)

Definition rt_meq (W : world SEGS) (m1 m2 : word -> option byte) : Prop :=
  forall x : word, mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x.

(* Every byte but the silence counter's four is kept. *)
Definition rt_agree (W : world SEGS) (m1 m2 : word -> option byte) (tx : Z) : Prop :=
  forall x : word, ~ (tx + 456 <= bv_unsigned x < tx + 460) ->
    mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x.

Lemma rt_meq_refl : forall W m, rt_meq W m m.
Proof. intros W m x. reflexivity. Qed.

Lemma rt_meq_trans : forall W m1 m2 m3, rt_meq W m1 m2 -> rt_meq W m2 m3 -> rt_meq W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x. rewrite (H2 x). exact (H1 x). Qed.

Lemma rt_meq_agree : forall W m1 m2 tx, rt_meq W m1 m2 -> rt_agree W m1 m2 tx.
Proof. intros W m1 m2 tx H x _. exact (H x). Qed.

Lemma rt_agree_trans : forall W m1 m2 m3 tx,
  rt_agree W m1 m2 tx -> rt_agree W m2 m3 tx -> rt_agree W m1 m3 tx.
Proof. intros W m1 m2 m3 tx H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Definition rt_rob (r : YP09.region) : bool := YP09.r_whi r <=? YP09.r_wlo r.
Definition rt_tkb (r : YP09.region) : bool :=
  rt_rob r ||
  match YP09.r_base r with
  | Some n => Nat.eqb n 10 && (456 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 460)
  | None => false
  end.

Lemma rt_ro_nowr : forall E rs a, forallb rt_rob rs = true -> ~ in_wrange E rs a.
Proof.
  intros E rs a Hb (r & Hin & Ha). pose proof (proj1 (forallb_forall _ _) Hb r Hin) as Hr.
  unfold rt_rob in Hr. apply Z.leb_le in Hr. lia.
Qed.

Lemma rt_tk_win : forall E rs a tx, bv_unsigned (ew E 10) = tx -> forallb rt_tkb rs = true ->
  in_wrange E rs a -> tx + 456 <= a < tx + 460.
Proof.
  intros E rs a tx H10 Hb (r & Hin & Ha). pose proof (proj1 (forallb_forall _ _) Hb r Hin) as Hr.
  unfold rt_tkb, rt_rob in Hr. apply orb_true_iff in Hr as [Hr | Hr]; [apply Z.leb_le in Hr; lia |].
  revert Hr Ha. destruct (YP09.r_base r) as [n|]; intros Hr Ha; [|discriminate Hr].
  apply andb_true_iff in Hr as [Hr H2]. apply andb_true_iff in Hr as [Hn H1].
  apply Nat.eqb_eq in Hn. subst n. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [base_val] in Ha. rewrite H10 in Ha. lia.
Qed.

Lemma rt_ro_awr : forall E rs STK sp0 FP bl0 blc lyy own,
  forallb rt_rob rs = true -> awr_ok E rs STK sp0 FP bl0 blc lyy own.
Proof. intros E rs STK sp0 FP bl0 blc lyy own Hb a Ha. exfalso. exact (rt_ro_nowr E rs a Hb Ha). Qed.

Lemma rt_tk_awr : forall E rs STK sp0 FP bl0 blc lyy own tx,
  bv_unsigned (ew E 10) = tx -> forallb rt_tkb rs = true ->
  (forall a, tx <= a < tx + TX_SIZE -> awr_byte STK sp0 FP bl0 blc lyy own a) ->
  awr_ok E rs STK sp0 FP bl0 blc lyy own.
Proof.
  intros E rs STK sp0 FP bl0 blc lyy own tx H10 Hb Hw a Ha. apply Hw.
  pose proof (rt_tk_win E rs a tx H10 Hb Ha). unfold TX_SIZE. lia.
Qed.

Lemma rt_ro_meq : forall E rs (W : world SEGS) m1 m2,
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> forallb rt_rob rs = true ->
  rt_meq W m1 m2.
Proof. intros E rs W m1 m2 HF Hb x. apply HF. exact (rt_ro_nowr E rs _ Hb). Qed.

Lemma rt_tk_agree : forall E rs (W : world SEGS) m1 m2 tx,
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> bv_unsigned (ew E 10) = tx ->
  forallb rt_tkb rs = true -> rt_agree W m1 m2 tx.
Proof.
  intros E rs W m1 m2 tx HF H10 Hb x Hx. apply HF. intros Hw. apply Hx.
  exact (rt_tk_win E rs _ tx H10 Hb Hw).
Qed.

Lemma rt_grows : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  assert (HN : mrestrict (w_H W) m1 (Z_to_bv 64 a) <> None)
    by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  pose proof (HG _ HN) as H2. unfold mrestrict in H2. rewrite Hh in H2.
  destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:Hb2; [exists b2; reflexivity | exfalso; exact (H2 eq_refl)].
Qed.

Lemma rt_meq_obj : forall W m1 m2 tx T, rt_meq W m1 m2 ->
  obj_at SEGS (mrestrict (w_H W) m1) tx LAY_TX (tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W) m2) tx LAY_TX (tx_vals T).
Proof.
  intros W m1 m2 tx T HQ HO. apply (proj2 (tx_obj_bytes SEGS _ _ _)). intros i Hi.
  rewrite <- (proj1 (tx_obj_bytes SEGS _ _ _) HO i Hi). unfold mbyte. rewrite HQ. reflexivity.
Qed.

Lemma rt_agree_same : forall W memc m1 m2 sp tx chp parp valp,
  nx_same W memc m1 sp tx chp parp valp (tx + 432) -> rt_agree W m1 m2 tx ->
  nx_same W memc m2 sp tx chp parp valp (tx + 432).
Proof.
  intros W memc m1 m2 sp tx chp parp valp HS HA x H1 H2.
  rewrite (HA x); [exact (HS x H1 H2) | intros H3; apply H2; unfold nx_touch2; lia].
Qed.

Lemma rt_agree_val : forall W m1 m2 tx a (n : nat) v, rt_agree W m1 m2 tx ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (tx + 460 <= a \/ a + Z.of_nat n <= tx + 456) ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof.
  intros W m1 m2 tx a n v HA H0 H1 H2 HV k Hk. pose proof (HV k Hk) as H. unfold mbyte in *.
  rewrite (HA (Z_to_bv 64 (a + Z.of_nat k))); [exact H|].
  rewrite unsigned_lit_small by lia. lia.
Qed.

Lemma rt_agree_saved : forall W m1 m2 tx regs sp, rt_agree W m1 m2 tx ->
  0 <= tx -> tx + 460 <= sp - 80 -> sp <= 2 ^ 64 ->
  nx_saved W m1 regs sp -> nx_saved W m2 regs sp.
Proof.
  intros W m1 m2 tx regs sp HA H0 H1 H2 (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  unfold nx_saved. repeat match goal with |- _ /\ _ => split end;
    (eapply rt_agree_val; [exact HA | lia | lia | lia | eassumption]).
Qed.

(* The table after the tail stored the ticked counter: the four counter bytes come from the
   region the store wrote, every other byte is the table at RSWP. *)
Lemma rt_tick_obj : forall (W : world SEGS) memj m (tx : Z) (Tj : list byte) (Ex : env) cs lo hi wlo whi,
  length Tj = 460%nat -> 0 <= tx -> tx + 460 <= 2 ^ 64 ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals Tj) ->
  rt_agree W memj m tx ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew Ex 10) = tx ->
  In (YP09.mkChunk 456 (CVal 4 RT_TICK)) cs ->
  bv_unsigned (sv_denot Ex RT_TICK) mod 4294967296 = (u32 Tj 456 + 1) mod 4294967296 ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals (set4 Tj 456 (u32 Tj 456 + 1))).
Proof.
  intros W memj m tx Tj Ex cs lo hi wlo whi HL Ht0 Ht1 HO HA HR H10 HIn Hmod.
  apply (proj2 (tx_obj_bytes SEGS _ tx _)). intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
  unfold set4. change (Z.to_nat 456) with 456%nat.
  rewrite (SegSetModel.nth_upd_bytes _ _ 456 (Z.to_nat i)) by (rewrite length_le4; lia).
  rewrite length_le4.
  destruct (Z_lt_le_dec i 456) as [Hlo | Hge].
  - replace ((456 <=? Z.to_nat i)%nat && (Z.to_nat i <? 456 + 4)%nat)%bool with false
      by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
    rewrite <- (proj1 (tx_obj_bytes SEGS _ tx Tj) HO i Hi). unfold mbyte.
    rewrite (HA (Z_to_bv 64 (tx + i))); [reflexivity|].
    rewrite unsigned_lit_small by lia. lia.
  - replace ((456 <=? Z.to_nat i)%nat && (Z.to_nat i <? 456 + 4)%nat)%bool with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    rewrite (le4_byte_of_word _ (Z.to_nat i - 456) ltac:(lia)).
    replace (Z.of_nat (Z.to_nat i - 456)) with (i - 456) by lia.
    replace (tx + i) with (tx + 456 + (i - 456)) by lia.
    rewrite (byte_of_region SEGS Ex _ 10%nat tx cs lo hi wlo whi 456 4 RT_TICK (i - 456) HR H10 HIn
               ltac:(cbn; lia)).
    f_equal. apply rt_byte_mod32; [lia|]. rewrite Hmod, Z_to_bv_unsigned.
    symmetry. exact (rt_mod32_zcanon (u32 Tj 456 + 1)).
Qed.

(* The counter's region, added before the counter's access. *)
Lemma rt_txw_ok : forall (W : world SEGS) (Ex : env) m tx (Tj : list byte),
  bv_unsigned (ew Ex 10) = tx -> ew Ex 35 = Z_to_bv 64 (u32at Tj 456) ->
  0 <= tx -> tx + 460 <= 2 ^ 64 ->
  (forall o, 456 <= o < 460 -> apresent (w_H W) m (tx + o)) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals Tj) ->
  region_ok SEGS Ex (mrestrict (w_H W) m) RT_TXW.
Proof.
  intros W Ex m tx Tj H10 H35 Ht0 Ht1 Hp HO.
  pose proof (u32at_range Tj 456) as R.
  unfold RT_TXW, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H10. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply Hp. lia.
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS Ex _ tx 456 4 (SOff 35 0) (u32at Tj 456)).
    + cbn [sv_denot]. rewrite H35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + apply (nx_val4 _ tx Tj 456 (proj1 (tx_obj_bytes SEGS _ _ _) HO)).
      intros d Hd. assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
        vm_compute; reflexivity.
Qed.

(* The register values the tail leaves at its return and at REARM, read off the
   symbolic registers. *)
Definition rt_ret_shape (sr : list sv) : bool :=
  sv_eqb (sr_get sr 1) (SOff 36 0) && sv_eqb (sr_get sr 2) (SOff 2 80) &&
  sv_eqb (sr_get sr 3) (SOff 3 0) && sv_eqb (sr_get sr 4) (SOff 4 0) &&
  sv_eqb (sr_get sr 8) (SOff 37 0) && sv_eqb (sr_get sr 9) (SOff 38 0) &&
  sv_eqb (sr_get sr 18) (SOff 39 0) && sv_eqb (sr_get sr 19) (SOff 40 0) &&
  sv_eqb (sr_get sr 20) (SOff 41 0) && sv_eqb (sr_get sr 21) (SOff 42 0) &&
  sv_eqb (sr_get sr 22) (SOff 43 0) && sv_eqb (sr_get sr 23) (SOff 44 0) &&
  sv_eqb (sr_get sr 24) (SOff 45 0) && sv_eqb (sr_get sr 25) (SOff 25 0) &&
  sv_eqb (sr_get sr 26) (SOff 26 0) && sv_eqb (sr_get sr 27) (SOff 27 0) &&
  sv_eqb (sr_get sr 10) (SLit 0).

Lemma rt_atom_reg : forall (Ex : env) (n : nat) (r : word),
  ew Ex n = r -> sv_denot Ex (SOff n 0) = r.
Proof. intros Ex n r H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma rt_ret_regs : forall (Ex : env) ss (Hh : word -> bool) ms (regs : bvmap 5 word) tx Tj,
  st_ok_pi SEGS VAL Ex ss (restrict Hh ms) -> rt_env_ok Ex regs tx Tj ->
  80 <= spZ regs ->
  rt_ret_shape (ss_regs ss) = true ->
  aregs_preserved regs (ms_regs ms) /\ getr (ms_regs ms) 1 = getr regs 1 /\
  getr (ms_regs ms) 10 = w64 0.
Proof.
  intros Ex ss Hh ms regs tx Tj HS HE Hsp Hsh.
  destruct HE as (A2 & A3 & A4 & A6 & A10 & A25 & A26 & A27 & A32 & A33 & A34 & A35 &
    A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45).
  pose proof (fun r => st_ok_pi_restrict_reg Hh Ex ss ms r HS) as HR.
  unfold rt_ret_shape in Hsh. repeat rewrite andb_true_iff in Hsh.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_eq in H end.
  split; [|split].
  - apply rt_preserved; rewrite HR;
      match goal with H : sr_get (ss_regs ss) ?r = _ |- context [sr_get (ss_regs ss) ?r] => rewrite H end.
    + cbn [sv_denot]. rewrite A2, unsigned_lit_small by (unfold NEXT_STK; pose proof (bv_unsigned_in_range 64 (getr regs 2)); unfold spZ in *; change (bv_modulus 64) with (2 ^ 64) in *; lia).
      replace (spZ regs - NEXT_STK + 80) with (spZ regs) by (unfold NEXT_STK; lia).
      apply Z_to_bv_bv_unsigned.
    + exact (rt_atom_reg Ex 3 _ A3).
    + exact (rt_atom_reg Ex 4 _ A4).
    + exact (rt_atom_reg Ex 37 _ A37).
    + exact (rt_atom_reg Ex 38 _ A38).
    + exact (rt_atom_reg Ex 39 _ A39).
    + exact (rt_atom_reg Ex 40 _ A40).
    + exact (rt_atom_reg Ex 41 _ A41).
    + exact (rt_atom_reg Ex 42 _ A42).
    + exact (rt_atom_reg Ex 43 _ A43).
    + exact (rt_atom_reg Ex 44 _ A44).
    + exact (rt_atom_reg Ex 45 _ A45).
    + exact (rt_atom_reg Ex 25 _ A25).
    + exact (rt_atom_reg Ex 26 _ A26).
    + exact (rt_atom_reg Ex 27 _ A27).
  - rewrite HR. match goal with H : sr_get (ss_regs ss) 1 = _ |- _ => rewrite H end.
    exact (rt_atom_reg Ex 36 _ A36).
  - rewrite HR. match goal with H : sr_get (ss_regs ss) 10 = _ |- _ => rewrite H end.
    reflexivity.
Qed.

Definition rt_rearm_shape (sr : list sv) : bool :=
  sv_eqb (sr_get sr 2) (SOff 2 0) && sv_eqb (sr_get sr 3) (SOff 3 0) &&
  sv_eqb (sr_get sr 4) (SOff 4 0) && sv_eqb (sr_get sr 5) (SOff 32 0) &&
  sv_eqb (sr_get sr 6) (SOff 6 0) && sv_eqb (sr_get sr 10) (SOff 10 0) &&
  sv_eqb (sr_get sr 11) (SOff 10 456) && sv_eqb (sr_get sr 12) (SOff 33 0) &&
  sv_eqb (sr_get sr 14) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 456) (SLit 3)) (SOff 32 0)) &&
  sv_eqb (sr_get sr 25) (SOff 25 0) && sv_eqb (sr_get sr 26) (SOff 26 0) &&
  sv_eqb (sr_get sr 27) (SOff 27 0).

Lemma rt_rearm_regs : forall (Ex : env) ss (Hh : word -> bool) ms (regs : bvmap 5 word) tx Tj,
  st_ok_pi SEGS VAL Ex ss (restrict Hh ms) -> rt_env_ok Ex regs tx Tj ->
  0 <= tx -> tx + 460 <= 2 ^ 47 -> 80 <= spZ regs ->
  rt_rearm_shape (ss_regs ss) = true ->
  nx_at_rearm regs (ms_regs ms) tx (tb Tj 450).
Proof.
  intros Ex ss Hh ms regs tx Tj HS HE Ht0 Ht1 Hsp Hsh.
  destruct HE as (A2 & A3 & A4 & A6 & A10 & A25 & A26 & A27 & A32 & A33 & A34 & A35 &
    A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45).
  pose proof (fun r => st_ok_pi_restrict_reg Hh Ex ss ms r HS) as HR.
  unfold rt_rearm_shape in Hsh. repeat rewrite andb_true_iff in Hsh.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_eq in H end.
  unfold nx_at_rearm, nx_keep_gp.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite HR; match goal with H : sr_get (ss_regs ss) ?r = _ |- context [sr_get (ss_regs ss) ?r] =>
                                       rewrite H end).
  - intros r Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; rewrite HR;
      match goal with H : sr_get (ss_regs ss) ?r = _ |- context [sr_get (ss_regs ss) ?r] => rewrite H end.
    + exact (rt_atom_reg Ex 3 _ A3).
    + exact (rt_atom_reg Ex 4 _ A4).
    + exact (rt_atom_reg Ex 25 _ A25).
    + exact (rt_atom_reg Ex 26 _ A26).
    + exact (rt_atom_reg Ex 27 _ A27).
  - exact (rt_atom_reg Ex 2 _ A2).
  - exact (rt_atom_reg Ex 32 _ A32).
  - exact (rt_atom_reg Ex 6 _ A6).
  - exact (rt_atom_reg Ex 10 _ A10).
  - cbn [sv_denot]. rewrite A10, unsigned_lit_small by lia. reflexivity.
  - exact (rt_atom_reg Ex 33 _ A33).
  - unfold w64. rewrite denot_lit_U. f_equal.
    rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, A10, unsigned_lit_small by lia.
    rewrite (U_atom Ex 32 SB_NX A32) by (unfold SB_NX; lia).
    change (Z.land (zcanon 3) 63) with 3.
    rewrite (zcanon_id (tx + 456)) by (unfold M64; lia).
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (Hq : 0 <= (tx + 456) / 8 < 2 ^ 47)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite (zcanon_id ((tx + 456) / 8)) by (unfold M64; lia).
    rewrite zcanon_id by (unfold M64, SB_NX; lia).
    unfold SB_NX, SHADOW_OFF. lia.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis RARM : nx_rearm_spec B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* After a run whose regions are all read-only: the memory is the one before it. *)
Ltac rt_ro_step :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    Q0 : rt_meq ?W ?m0 ?m1,
    P0 : forall a, apresent (w_H ?W) ?m0 a -> apresent (w_H ?W) ?m1 a |- _ =>
      let M := fresh "MQ" in let P := fresh "MP" in
      pose proof (rt_meq_trans _ _ _ _ Q0 (rt_ro_meq _ _ W m1 m2 HFr ltac:(vm_compute; reflexivity))) as M;
      pose proof (fun a H => rt_grows W m1 m2 a HG (P0 a H)) as P;
      clear Q0 P0 HFr HG; rename M into MQ; rename P into MP
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.

(* After a run whose one writable region is the silence counter: every other byte is kept. *)
Ltac rt_tk_step tx U :=
  lazymatch goal with
  | HFr : frame_of ?Ey _ (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    Q0 : rt_agree ?W ?m0 ?m1 _,
    P0 : forall a, apresent (w_H ?W) ?m0 a -> apresent (w_H ?W) ?m1 a |- _ =>
      let M := fresh "MA" in let P := fresh "MP" in
      pose proof (rt_agree_trans _ _ _ _ _ Q0 (rt_tk_agree Ey _ W m1 m2 tx HFr U ltac:(vm_compute; reflexivity))) as M;
      pose proof (fun a H => rt_grows W m1 m2 a HG (P0 a H)) as P;
      clear Q0 P0 HFr HG; rename M into MA; rename P into MP
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.

(* The symbolic state at RSWP, from the cut's premises. *)
Lemma rt_seat : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T Tj : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals Tj) ->
  nx_at_rswp regs regsj tx chp parp valp ->
  st_ok_pi SEGS VAL (ERT regsj regs Tj) ss_rt
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + RSWP)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN rt_SH (ERT regsj regs Tj) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T Tj HCTX HMID HSAV HOBJ HRS.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK).
  pose proof HRS as (KG & R2 & R5 & R6 & R10 & R15).
  pose proof (proj1 HJ) as HARj.
  pose proof alloc_ceiling_value as (Cv1 & Cv2).
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
    as (Hg16 & Hg4096 & Hgceil & _ & _ & _).
  change (req_size TX_SIZE) with 460 in Hgceil.
  pose proof (proj1 (tx_obj_bytes SEGS _ _ _) HOBJ) as HBY.
  pose proof (HeadampTxEffective.tb_range Tj 450) as R450.
  pose proof (u32at_range Tj 452) as R452. pose proof (u32at_range Tj 456) as R456.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp.
  change (bv_modulus 64) with 18446744073709551616 in Rsp. fold (spZ regs) in Rsp.
  pose proof (rt_env regs regsj tx chp parp valp Tj HRS) as HE.
  destruct HE as (A2 & A3 & A4 & A6 & A10 & A25 & A26 & A27 & A32 & A33 & A34 & A35 &
    A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45).
  assert (HRG : regs_ok (ERT regsj regs Tj) rt_sr regsj).
  { unfold rt_sr. apply regs_ok_pin; [exact (regs_ok_Eimg_Ereg regsj (rt_extra regs Tj)) | exact rt_r5_nz |].
    rewrite (rt_atom_reg _ 32 _ A32). exact R5. }
  set (E := ERT regsj regs Tj) in *.
  assert (U2 : bv_unsigned (ew E 2) = spZ regs - NEXT_STK)
    by (rewrite A2; apply unsigned_lit_small; unfold NEXT_STK; lia).
  assert (U10 : bv_unsigned (ew E 10) = tx) by (rewrite A10; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX) by (rewrite A32; apply unsigned_lit_small; unfold SB_NX; lia).
  assert (U33 : bv_unsigned (ew E 33) = tb Tj 450) by (rewrite A33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = u32at Tj 452) by (rewrite A34; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = u32at Tj 456) by (rewrite A35; apply unsigned_lit_small; lia).
  split.
  - rewrite restrict_mkst_fx. unfold ss_rt. apply pa_entry_st_ok_full.
    + exact HRG.
    + vm_compute. reflexivity.
    + unfold RT_STK, RT_TXR.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U2. unfold NEXT_STK in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ _ 72 8 (SOff 36 0) (bv_unsigned (getr regs 1)));
             [ rewrite (rt_atom_reg E 36 _ A36); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 72) with (spZ regs - 8) by lia; exact S1 ].
        -- apply (chunk_ok_val SEGS E _ _ 64 8 (SOff 37 0) (bv_unsigned (getr regs 8)));
             [ rewrite (rt_atom_reg E 37 _ A37); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 64) with (spZ regs - 16) by lia; exact S2 ].
        -- apply (chunk_ok_val SEGS E _ _ 56 8 (SOff 38 0) (bv_unsigned (getr regs 9)));
             [ rewrite (rt_atom_reg E 38 _ A38); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 56) with (spZ regs - 24) by lia; exact S3 ].
        -- apply (chunk_ok_val SEGS E _ _ 48 8 (SOff 39 0) (bv_unsigned (getr regs 18)));
             [ rewrite (rt_atom_reg E 39 _ A39); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 48) with (spZ regs - 32) by lia; exact S4 ].
        -- apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 40 0) (bv_unsigned (getr regs 19)));
             [ rewrite (rt_atom_reg E 40 _ A40); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 19)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 40) with (spZ regs - 40) by lia; exact S5 ].
        -- apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 41 0) (bv_unsigned (getr regs 20)));
             [ rewrite (rt_atom_reg E 41 _ A41); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 20)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 32) with (spZ regs - 48) by lia; exact S6 ].
        -- apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 42 0) (bv_unsigned (getr regs 21)));
             [ rewrite (rt_atom_reg E 42 _ A42); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 21)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 24) with (spZ regs - 56) by lia; exact S7 ].
        -- apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 43 0) (bv_unsigned (getr regs 22)));
             [ rewrite (rt_atom_reg E 43 _ A43); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 22)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 16) with (spZ regs - 64) by lia; exact S8 ].
        -- apply (chunk_ok_val SEGS E _ _ 8 8 (SOff 44 0) (bv_unsigned (getr regs 23)));
             [ rewrite (rt_atom_reg E 44 _ A44); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 23)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 8) with (spZ regs - 72) by lia; exact S9 ].
        -- apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 45 0) (bv_unsigned (getr regs 24)));
             [ rewrite (rt_atom_reg E 45 _ A45); symmetry; apply Z_to_bv_bv_unsigned
             | pose proof (bv_unsigned_in_range 64 (getr regs 24)) as Hr;
               change (bv_modulus 64) with 18446744073709551616 in Hr; cbn; lia
             | cbn; lia
             | replace (spZ regs - 80 + 0) with (spZ regs - 80) by lia; exact S10 ].
      * rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ tx 450 1 (SOff 33 0) (tb Tj 450));
             [ cbn [sv_denot]; rewrite A33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memj) tx Tj 450 HBY); vm_compute; reflexivity ].
        -- apply (chunk_ok_val SEGS E _ tx 452 4 (SOff 34 0) (u32at Tj 452));
             [ cbn [sv_denot]; rewrite A34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memj) tx Tj 452 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity ].
    + apply pairwise_disjoint_of_extents.
      unfold RT_STK, RT_TXR, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U10.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold NEXT_STK in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [rt_facts f_atoms atoms_ok]. unfold afact_ok, PTRN.
      cbn [af_lo af_hi af_al2].
      rewrite U2, U10, U32, U33, U34, U35.
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold NEXT_STK, SB_NX in *.
      repeat match goal with |- _ /\ _ => split end; try lia.
      replace (spZ regs - 80) with (spZ regs + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
  - unfold sh_ok, rt_SH. constructor; [|constructor].
    apply (shent_ok_of_block SEGS B LAWS lyc Sc W memj mdj E BxN 10 tx TX_SIZE 0 460 HARj Hg).
    + unfold U, BxN. rewrite (rt_atom_reg E 32 _ A32). apply unsigned_lit_small. unfold SB_NX, SHADOW_OFF. lia.
    + unfold U. rewrite (rt_atom_reg E 10 _ A10). apply unsigned_lit_small. lia.
    + lia.
    + change (req_size TX_SIZE) with 460. lia.
Qed.

(* Every return of the tail: silent, with the table the model gives. *)
Lemma rt_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regs2 : bvmap 5 word) memj mem2 md2 (tx chp parp valp : Z) (T T' : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_same W memc memj (spZ regs) tx chp parp valp (tx + 432) ->
  (forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) memj a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memj a) ->
  rt_agree W memj mem2 tx ->
  (forall a, apresent (w_H W) memj a -> apresent (w_H W) mem2 a) ->
  next_model T tx = silent T' ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  getr regs2 10 = w64 0 ->
  obj_at SEGS (mrestrict (w_H W) mem2) tx LAY_TX (tx_vals T') ->
  tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 memj mem2 md2
    tx chp parp valp T T' HCTX HSAME HpresS HpresK HA HP HM HJ2 HPR H10 HO.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    Hspr & Hceil & _).
  apply (nx_finish B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2
           tx chp parp valp (tx + 432) T T' 0 0 0 0);
    [ unfold TX_SIZE; lia | exact HAR | exact Hg | exact Hoc | exact Hop | exact Hov
    | exact Hspr | exact Hceil | exact HM | exact HJ2 | exact HPR
    | exact (rt_agree_same W memc memj mem2 (spZ regs) tx chp parp valp HSAME HA)
    | intros a Ha; exact (HP a (HpresS a Ha))
    | intros a Ha; exact (HP a (HpresK a Ha))
    | exact H10 | exact HO
    | intros Hr; discriminate Hr ].
Qed.

Theorem pb_nx_resweep : nx_resweep_spec B.
Proof.
  unfold nx_resweep_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T Tj HCTX HMID HSAV HOBJ HL HI H437 HLOW HMOD HRS.
  destruct (rt_seat STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
              tx chp parp valp T Tj HCTX HMID HSAV HOBJ HRS) as [HS SHOK].
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL & HI0 & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK).
  pose proof alloc_ceiling_value as (Cv1 & Cv2).
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE (proj1 HJ) Hg)
    as (Hg16 & Hg4096 & Hgceil & _ & HgpresJ & _).
  change (req_size TX_SIZE) with 460 in Hgceil, HgpresJ.
  pose proof (HeadampTxEffective.tb_range Tj 450) as R450.
  pose proof (u32at_range Tj 452) as R452. pose proof (u32at_range Tj 456) as R456.
  pose proof Hret as Hret'. unfold YK0s.ret_ok in Hret'.
  pose proof (rt_env regs regsj tx chp parp valp Tj HRS) as HENV.
  remember (ERT regsj regs Tj) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERT; apply Eimg_env).
  clear HEdef.
  pose proof HENV as (A2 & A3 & A4 & A6 & A10 & A25 & A26 & A27 & A32 & A33 & A34 & A35 &
    A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45).
  assert (U10 : bv_unsigned (ew E 10) = tx) by (rewrite A10; apply unsigned_lit_small; lia).
  assert (U2 : bv_unsigned (ew E 2) = spZ regs - NEXT_STK)
    by (rewrite A2; apply unsigned_lit_small; unfold NEXT_STK; lia).
  assert (MQ : rt_meq W memj memj) by apply rt_meq_refl.
  assert (MP : forall a, apresent (w_H W) memj a -> apresent (w_H W) memj a) by (intros a Ha; exact Ha).
  unfold cfg_at. change (w64 (BASE + RSWP)) with (Z_to_bv 64 (BASE + RSWP)).
  (* 0x85374 .. 0x8538c: the period's shadow check (decided inside the engine) and its load *)
  paj_run_tok RUN HS HJ SHOK BspanN; [apply rt_ro_awr; vm_compute; reflexivity |].
  rt_ro_step.
  psrr_branch_tok RUN BR HS SHOK BspanN.
  - (* the period is 0: the silent return at 0x853d0 *)
    rewrite branch_eq_U, (rt_U_sext E 34 (u32at Tj 452) A34 R452), U_SLit in Hc.
    change (zcanon 0) with 0 in Hc. rewrite (rt_sx_eq0 _ R452) in Hc.
    apply Z.eqb_eq in Hc. rewrite u32at_u32 in Hc. rename Hc into H452.
    assert (HM : next_model T tx = silent Tj)
      by (rewrite HMOD; unfold resweep; rewrite H452; reflexivity).
    paj_run_tok RUN HS HJ SHOK BspanN; [apply rt_ro_awr; vm_compute; reflexivity |].
    rt_ro_step.
    lazymatch goal with
    | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
      destruct (rt_ret_regs Ex ssx (w_H W) msx regs tx Tj HSx HENV ltac:(lia) ltac:(vm_compute; reflexivity))
        as (HPR & R1 & R10);
      eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
      intros mat9; rewrite R1, Hret';
      eapply (rt_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msx) memj (ms_mem msx) _
                tx chp parp valp T Tj HCTX HSAME HpresS HpresK (rt_meq_agree _ _ _ tx MQ) MP HM);
      [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | exact HPR | exact R10
      | exact (rt_meq_obj _ _ _ _ _ MQ HOBJ) ]
    end.
  - (* the period is not 0 *)
    rewrite branch_eq_U, (rt_U_sext E 34 (u32at Tj 452) A34 R452), U_SLit in Hc.
    change (zcanon 0) with 0 in Hc. rewrite (rt_sx_eq0 _ R452) in Hc.
    apply Z.eqb_neq in Hc. rewrite u32at_u32 in Hc. rename Hc into H452.
    (* 0x85390 .. 0x853a8: the width's shadow check (decided inside the engine) and its load *)
    paj_run_tok RUN HS HJ SHOK BspanN; [apply rt_ro_awr; vm_compute; reflexivity |].
    rt_ro_step.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    + (* the width is 0: the silent return *)
      rewrite branch_eq_U, (U_atom E 33 (tb Tj 450) A33) in Hc by lia. rewrite U_SLit in Hc.
      change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. rename Hc into H450.
      assert (HM : next_model T tx = silent Tj)
        by (rewrite HMOD; unfold resweep; rewrite (proj2 (Z.eqb_neq _ 0) H452), H450; reflexivity).
      paj_run_tok RUN HS HJ SHOK BspanN; [apply rt_ro_awr; vm_compute; reflexivity |].
      rt_ro_step.
      lazymatch goal with
      | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
        destruct (rt_ret_regs Ex ssx (w_H W) msx regs tx Tj HSx HENV ltac:(lia) ltac:(vm_compute; reflexivity))
          as (HPR & R1 & R10);
        eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
        intros mat9; rewrite R1, Hret';
        eapply (rt_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msx) memj (ms_mem msx) _
                  tx chp parp valp T Tj HCTX HSAME HpresS HpresK (rt_meq_agree _ _ _ tx MQ) MP HM);
        [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | exact HPR | exact R10
        | exact (rt_meq_obj _ _ _ _ _ MQ HOBJ) ]
      end.
    + (* the width is not 0: the counter is ticked *)
      rewrite branch_eq_U, (U_atom E 33 (tb Tj 450) A33) in Hc by lia. rewrite U_SLit in Hc.
      change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. rename Hc into H450.
      (* the counter's four bytes, the one region the tail writes *)
      lazymatch goal with
      | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) |- _ =>
        assert (HRW : region_ok SEGS Ex (ms_mem (restrict Hh msx)) RT_TXW)
          by (cbn [restrict ms_mem];
              exact (rt_txw_ok W Ex (ms_mem msx) tx Tj U10 A35 ltac:(lia) ltac:(lia)
                       (fun o Ho => MP (tx + o) (proj1 (HgpresJ (tx + o) ltac:(lia))))
                       (rt_meq_obj _ _ _ _ _ MQ HOBJ)));
        pose proof (st_ok_pi_add_region Ex ssx (restrict Hh msx) RT_TXW HSx ltac:(vm_compute; reflexivity) HRW
                      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
                              let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
                            unfold RT_TXW; cbn [all_disjoint]; unfold extent_disjoint;
                            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U2, U10;
                            unfold NEXT_STK in *; repeat split; lia)) as HS2;
        clear HSx HRW; rename HS2 into HS
      end.
      pose proof (rt_meq_agree _ _ _ tx MQ) as MA. clear MQ.
      (* 0x853ac .. 0x853cc: the counter's shadow check (its slow path decided inside the
         engine), its load, the add and the store *)
      paj_run_tok RUN HS HJ SHOK BspanN;
        [apply (rt_tk_awr _ _ _ _ _ _ _ _ _ tx U10); [vm_compute; reflexivity | exact Hwtab] |].
      rt_tk_step tx U10.
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E3 eqn:HE3 end.
      assert (HENV3 : rt_env_ok E3 regs tx Tj)
        by (apply (rt_env_lift E E3 regs tx Tj); [intros n Hn; rewrite HE3, !ew_ewset_other by lia; reflexivity
                                                 | exact HENV]).
      clear HE3.
      pose proof HENV3 as (G2 & G3 & G4 & G6 & G10 & G25 & G26 & G27 & G32 & G33 & G34 & G35 &
        G36 & G37 & G38 & G39 & G40 & G41 & G42 & G43 & G44 & G45).
      assert (U10' : bv_unsigned (ew E3 10) = tx) by (rewrite G10; apply unsigned_lit_small; lia).
      psrr_branch_tok RUN BR HS SHOK BspanN.
      * (* the period is reached: the re-arm block *)
        rewrite branch_geu_U in Hc.
        change (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1)) with RT_TICK in Hc.
        rewrite (rt_tick_U E3 (u32at Tj 456) G35 R456), (rt_U_sext E3 34 (u32at Tj 452) G34 R452) in Hc.
        rewrite rt_sx_lt in Hc by (first [apply Z.mod_pos_bound; lia | lia]).
        apply negb_true_iff, Z.ltb_ge in Hc. rewrite (u32at_u32 Tj 452), (u32at_u32 Tj 456) in Hc. rename Hc into Hge.
        assert (HM : next_model T tx = silent (rearm Tj))
          by (rewrite HMOD; unfold resweep;
              rewrite (proj2 (Z.eqb_neq _ 0) H452), (proj2 (Z.eqb_neq _ 0) H450), (proj2 (Z.leb_le _ _) Hge);
              reflexivity).
        paj_run_to_tok RUNTO HS HJ SHOK BspanN REARM;
          [apply (rt_tk_awr _ _ _ _ _ _ _ _ _ tx U10'); [vm_compute; reflexivity | exact Hwtab] |].
        rt_tk_step tx U10'.
        lazymatch goal with
        | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
          pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0
                        (YP09.mkRegion (Some 10%nat) 456 460 456 460 [YP09.mkChunk 456 (CVal 4 RT_TICK)])
                        HSx ltac:(vm_compute; reflexivity)) as HRT;
          cbn [restrict ms_mem] in HRT;
          pose proof (rt_rearm_regs Ex ssx (w_H W) msx regs tx Tj HSx HENV3 ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(vm_compute; reflexivity)) as HRR;
          pose proof (rt_tick_obj W memj (ms_mem msx) tx Tj Ex _ _ _ _ _ HL ltac:(lia) ltac:(lia) HOBJ MA HRT U10'
                        (or_introl eq_refl) (rt_tick_mod Ex (u32at Tj 456) G35 R456)) as HOT;
          pmkst HSx;
          refine (RARM STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msx) (ms_mem msx) _
                    tx chp parp valp T Tj HCTX _ _ HOT HL HM HRR);
          [ split; [exact HJ|]; split;
            [ exact (rt_agree_same W memc memj (ms_mem msx) (spZ regs) tx chp parp valp HSAME MA)
            | split; [intros a Ha; exact (MP a (HpresS a Ha)) | intros a Ha; exact (MP a (HpresK a Ha))] ]
          | exact (rt_agree_saved W memj (ms_mem msx) tx regs (spZ regs) MA ltac:(lia)
                     ltac:(unfold NEXT_STK in *; lia) ltac:(lia) HSAV) ]
        end.
      * (* the period is not reached: the silent return with the ticked counter *)
        rewrite branch_geu_U in Hc.
        change (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1)) with RT_TICK in Hc.
        rewrite (rt_tick_U E3 (u32at Tj 456) G35 R456), (rt_U_sext E3 34 (u32at Tj 452) G34 R452) in Hc.
        rewrite rt_sx_lt in Hc by (first [apply Z.mod_pos_bound; lia | lia]).
        apply negb_false_iff, Z.ltb_lt in Hc. rewrite (u32at_u32 Tj 452), (u32at_u32 Tj 456) in Hc. rename Hc into Hlt.
        assert (HM : next_model T tx = silent (set4 Tj 456 (u32 Tj 456 + 1)))
          by (rewrite HMOD; unfold resweep;
              rewrite (proj2 (Z.eqb_neq _ 0) H452), (proj2 (Z.eqb_neq _ 0) H450), (proj2 (Z.leb_gt _ _) Hlt);
              reflexivity).
        paj_run_tok RUN HS HJ SHOK BspanN;
          [apply (rt_tk_awr _ _ _ _ _ _ _ _ _ tx U10'); [vm_compute; reflexivity | exact Hwtab] |].
        rt_tk_step tx U10'.
        lazymatch goal with
        | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
          pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0
                        (YP09.mkRegion (Some 10%nat) 456 460 456 460 [YP09.mkChunk 456 (CVal 4 RT_TICK)])
                        HSx ltac:(vm_compute; reflexivity)) as HRT;
          cbn [restrict ms_mem] in HRT;
          pose proof (rt_tick_obj W memj (ms_mem msx) tx Tj Ex _ _ _ _ _ HL ltac:(lia) ltac:(lia) HOBJ MA HRT U10'
                        (or_introl eq_refl) (rt_tick_mod Ex (u32at Tj 456) G35 R456)) as HOT;
          destruct (rt_ret_regs Ex ssx (w_H W) msx regs tx Tj HSx HENV3 ltac:(lia) ltac:(vm_compute; reflexivity))
            as (HPR & R1 & R10);
          eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
          intros mat9; rewrite R1, Hret';
          eapply (rt_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msx) memj (ms_mem msx) _
                    tx chp parp valp T _ HCTX HSAME HpresS HpresK MA MP HM);
          [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | exact HPR | exact R10 | exact HOT ]
        end.
Qed.

End h.
End f.
End d.
