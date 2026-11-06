(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_free_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section IMS.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.

(* [comment removed for export] *)
Lemma ims_byte_loop : forall (k : nat) (cur : Z) m m0 (dst n : Z),
  Z.of_nat k = dst + n - cur -> dst <= cur < dst + n -> 0 <= dst -> dst + n < 2^64 ->
  mem_inv asegs m -> wr_at asegs m dst n -> bytes_at asegs m dst (repeat zb0 (Z.to_nat (cur - dst))) ->
  munch [(dst, dst + n)] m0 m -> wmono asegs m0 m ->
  (forall a j, dst <= a -> a + Z.of_nat j <= dst + n -> P (Z_to_bv 64 a, j)) ->
  (forall m' (a3' : word), mem_inv asegs m' -> wr_at asegs m' dst n -> bytes_at asegs m' dst (repeat zb0 (Z.to_nat n)) ->
     munch [(dst, dst + n)] m0 m' -> wmono asegs m0 m' ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (dst + n)) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x65478) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (dst + n)) (Z_to_bv 64 cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x65434) fc None m (seg_rom asegs)).
Proof. aceil.
  induction k as [|k IH]; intros cur m m0 dst n Hk RNG D0 DN MI WR BA MU WM PD CONT; [exfalso; lia|].
  pose proof (wr_at_store_ok asegs m dst n (cur - dst) 1 WR ltac:(lia) ltac:(cbn; lia)) as SOK.
  replace (dst + (cur - dst)) with cur in SOK by lia.
  zstepA.
  all: try (apply PD; lia).
  change (le1 (Z_to_bv 64 0)) with [zb0]. change (Z_to_bv 64 cur) with (wa cur) at 2.
  pose proof (mem_inv_store asegs m (wa cur) [zb0] MI SOK) as MI'.
  pose proof (wr_at_write asegs m dst n (wa cur) [zb0] WR) as WR'.
  pose proof (bytes_at_snoc0 m dst (Z.to_nat (cur - dst)) D0 ltac:(lia) BA) as BA'.
  replace (dst + Z.of_nat (Z.to_nat (cur - dst))) with cur in BA' by lia.
  assert (MU' : munch [(dst, dst + n)] m0 (write_to_mem m (wa cur) [zb0])).
  { apply munch_write; [exact MU| lia| cbn; lia| cbn; left; lia]. }
  assert (WM' : wmono asegs m0 (write_to_mem m (wa cur) [zb0])) by (apply wmono_write; exact WM).
  remember (write_to_mem m (wa cur) [zb0]) as m1 eqn:E1. clear E1 SOK MI WR BA MU WM m.
  zstepA. zstepA. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *) eapply (IH (cur + 1) m1 m0 dst n); try first [exact MI'| exact WR'| exact MU'| exact WM'| exact PD| exact CONT]; try lia.
    replace (Z.to_nat (cur + 1 - dst)) with (S (Z.to_nat (cur - dst))) by lia. exact BA'.
  - (* [comment removed for export] *) zstepA. eapply CONT; [exact MI'| exact WR'| | exact MU'| exact WM'].
    replace (Z.to_nat n) with (S (Z.to_nat (cur - dst))) by lia. exact BA'.
Qed.

(* [comment removed for export] *)
Lemma ims_sd_loop : forall (k : nat) (cur : Z) m m0 (dst n : Z),
  Z.of_nat k = (dst + n - cur) / 16 -> dst <= cur < dst + n -> (dst + n - cur) mod 16 = 0 -> cur mod 8 = 0 -> 0 <= dst -> dst + n < 2^64 ->
  mem_inv asegs m -> wr_at asegs m dst n -> bytes_at asegs m dst (repeat zb0 (Z.to_nat (cur - dst))) ->
  munch [(dst, dst + n)] m0 m -> wmono asegs m0 m ->
  (forall a j, dst <= a -> a + Z.of_nat j <= dst + n -> P (Z_to_bv 64 a, j)) ->
  (forall m' (a3' : word), mem_inv asegs m' -> wr_at asegs m' dst n -> bytes_at asegs m' dst (repeat zb0 (Z.to_nat n)) ->
     munch [(dst, dst + n)] m0 m' -> wmono asegs m0 m' ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (dst + n)) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x65478) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (dst + n)) (Z_to_bv 64 cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x65468) fc None m (seg_rom asegs)).
Proof. aceil.
  induction k as [|k IH]; intros cur m m0 dst n Hk RNG M16 C8 D0 DN MI WR BA MU WM PD CONT.
  { exfalso. Z.div_mod_to_equations. lia. }
  assert (R16 : cur + 16 <= dst + n) by (Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof (wr_at_store_ok asegs m dst n (cur - dst) 8 WR ltac:(lia) ltac:(cbn; lia)) as SOK.
  replace (dst + (cur - dst)) with cur in SOK by lia.
  zstepA.
  all: try (apply PD; lia).
  change (Z_to_le_bytes 8 0) with (repeat zb0 8). change (Z_to_bv 64 cur) with (wa cur) at 2.
  pose proof (mem_inv_store asegs m (wa cur) (repeat zb0 8) MI SOK) as MI'.
  pose proof (wr_at_write asegs m dst n (wa cur) (repeat zb0 8) WR) as WR'.
  pose proof (bytes_at_app0 m dst (Z.to_nat (cur - dst)) 8 D0 ltac:(lia) BA) as BA'.
  replace (dst + Z.of_nat (Z.to_nat (cur - dst))) with cur in BA' by lia.
  assert (MU' : munch [(dst, dst + n)] m0 (write_to_mem m (wa cur) (repeat zb0 8))).
  { apply munch_write; [exact MU| lia| cbn; lia| cbn; left; lia]. }
  assert (WM' : wmono asegs m0 (write_to_mem m (wa cur) (repeat zb0 8))) by (apply wmono_write; exact WM).
  remember (write_to_mem m (wa cur) (repeat zb0 8)) as m1 eqn:E1. clear E1 SOK MI WR BA MU WM m.
  (* [comment removed for export] *)
  pose proof (wr_at_store_ok asegs m1 dst n (cur + 8 - dst) 8 WR' ltac:(lia) ltac:(cbn; lia)) as SOK.
  replace (dst + (cur + 8 - dst)) with (cur + 8) in SOK by lia.
  zstepA.
  all: try (apply PD; lia).
  change (Z_to_le_bytes 8 0) with (repeat zb0 8). change (Z_to_bv 64 (cur + 8)) with (wa (cur + 8)).
  pose proof (mem_inv_store asegs m1 (wa (cur + 8)) (repeat zb0 8) MI' SOK) as MI2.
  pose proof (wr_at_write asegs m1 dst n (wa (cur + 8)) (repeat zb0 8) WR') as WR2.
  pose proof (bytes_at_app0 m1 dst (Z.to_nat (cur - dst) + 8) 8 D0 ltac:(lia) BA') as BA2.
  replace (dst + Z.of_nat (Z.to_nat (cur - dst) + 8)) with (cur + 8) in BA2 by lia.
  assert (MU2 : munch [(dst, dst + n)] m0 (write_to_mem m1 (wa (cur + 8)) (repeat zb0 8))).
  { apply munch_write; [exact MU'| lia| cbn; lia| cbn; left; lia]. }
  assert (WM2 : wmono asegs m0 (write_to_mem m1 (wa (cur + 8)) (repeat zb0 8))) by (apply wmono_write; exact WM').
  remember (write_to_mem m1 (wa (cur + 8)) (repeat zb0 8)) as m2 eqn:E2. clear E2 SOK MI' WR' BA' MU' WM' m1.
  zstepA. zstepA. if_cases K0; zify_cond K0.
  - eapply (IH (cur + 16) m2 m0 dst n); try first [exact MI2| exact WR2| exact MU2| exact WM2| exact PD| exact CONT]; try lia.
    replace (Z.to_nat (cur + 16 - dst)) with (Z.to_nat (cur - dst) + 8 + 8)%nat by lia. exact BA2.
  - eapply CONT; [exact MI2| exact WR2| | exact MU2| exact WM2].
    replace (Z.to_nat n) with (Z.to_nat (cur - dst) + 8 + 8)%nat by (Z.div_mod_to_equations; lia). exact BA2.
Qed.

(* [comment removed for export] *)
Lemma imemset0_walk : forall (a3 : word) m (dst n : Z),
  0 < n -> 0 <= dst -> dst + n < 2^64 ->
  mem_inv asegs m -> wr_at asegs m dst n ->
  (forall a j, dst <= a -> a + Z.of_nat j <= dst + n -> P (Z_to_bv 64 a, j)) ->
  (forall m' (a1' a2' a3' : word), mem_inv asegs m' -> wr_at asegs m' dst n -> bytes_at asegs m' dst (repeat zb0 (Z.to_nat n)) ->
     munch [(dst, dst + n)] m m' -> wmono asegs m m' ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x6541c) fc None m (seg_rom asegs)).
Proof. aceil.
  intros a3 m dst n N0 D0 DN MI WR PD CONT.
  assert (BA0 : bytes_at asegs m dst (repeat zb0 (Z.to_nat (dst - dst)))) by (rewrite Z.sub_diag; apply bytes_at_nil; lia).
  zstepA. zstepA. zstepA. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    assert (D16 : dst mod 16 = 0 /\ n mod 16 = 0).
    { change 15 with (Z.ones 4) in K0. rewrite Z.land_lor_distr_l, !Z.land_ones in K0 by lia.
      change (2^4) with 16 in K0. pose proof (Z.lor_nonneg (n mod 16) (dst mod 16)) as X.
      pose proof (Z.lor_eq_0_iff (n mod 16) (dst mod 16)) as Y. Z.div_mod_to_equations. lia. }
    zstepA. if_cases K1; zify_cond K1; [exfalso; lia|].
    do 7 zstepA. zstepA.
    eapply (ims_sd_loop (Z.to_nat (n / 16)) dst m m dst n); try first [exact MI| exact WR| exact BA0| exact PD| apply munch_refl| apply wmono_refl]; try lia.
    intros m' a3' MI' WR' BA' MU' WM'. zstepA. eapply CONT; eassumption.
  - zstepA. if_cases K1; zify_cond K1; [exfalso; lia|].
    zstepA. zstepA.
    eapply (ims_byte_loop (Z.to_nat n) dst m m dst n); try first [exact MI| exact WR| exact BA0| exact PD| apply munch_refl| apply wmono_refl]; try lia.
    intros m' a3' MI' WR' BA' MU' WM'. zstepA. eapply CONT; eassumption.
Qed.
End IMS.

(* [comment removed for export] *)
Lemma Z_to_bv8_mod : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.

Lemma ia_cells4 : forall (b0 b1 k : Z) (pad : word), 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= k < 2^32 ->
  cells_bytes [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 pad]
  = cells_bytes [C4 (Z_to_bv 64 (b0 + 256 * b1 + 65536 * (bv_unsigned pad mod 65536 + 65536 * k)))].
Proof.
  intros b0 b1 k pad Hb0 Hb1 Hk. pose proof (bv_unsigned_in_range 64 pad) as PR. change (bv_modulus 64) with (2^64) in PR.
  set (q := bv_unsigned pad mod 65536). assert (HQ : 0 <= q < 65536) by (subst q; apply Z.mod_pos_bound; lia).
  cbn [cells_bytes cbytes app]. unfold le4, le2. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Z.mod_small by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^(8+8)) with 65536. change (2^(8+8+8)) with 16777216.
  rewrite !app_nil_r.
  f_equal. { apply Z_to_bv8_mod. Z.div_mod_to_equations; nia. }
  f_equal. { apply Z_to_bv8_mod. Z.div_mod_to_equations; nia. }
  f_equal. { apply Z_to_bv8_mod. subst q. Z.div_mod_to_equations; nia. }
  f_equal. apply Z_to_bv8_mod. subst q. Z.div_mod_to_equations; nia.
Qed.

Lemma land_mul65536_small : forall k c, 0 <= k -> 0 <= c < 65536 -> Z.land (65536 * k) c = 0.
Proof.
  intros k c Hk Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 16).
  - replace (65536 * k) with (Z.shiftl k 16) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 c i); [apply andb_false_r| lia|].
    destruct (Z.eq_dec c 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^16)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma sx32_hi16 : forall q, 0 <= q < 65536 ->
  exists k, 0 <= k < 2^32 /\ bv_unsigned (sx32 (Z_to_bv 64 (65536 * q))) = 65536 * (q + 65536 * k).
Proof.
  intros q Hq. unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite (Z.mod_small (65536 * q) (2^64)) by lia.
  destruct (Z.lt_ge_cases q 32768).
  - exists 0. split; [lia|]. rewrite (Z.mod_small _ (2^32)) by lia. rewrite Z.mod_small by lia. lia.
  - exists (2^32 - 1). split; [lia|].
    replace ((65536 * q + 2 ^ 31) `mod` 2 ^ 32) with (65536 * q + 2^31 - 2^32) by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations; lia.
Qed.

Lemma land_ff00 : forall Y, 0 <= Y -> Z.land (65536 * Y + 256) 65280 = 256.
Proof.
  intros Y HY. replace (65536 * Y + 256) with (Z.shiftl (256 * Y + 1) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace 65280 with (Z.shiftl 255 8) by reflexivity. rewrite <- Z.shiftl_land.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  replace ((256 * Y + 1) mod 256) with 1 by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ia_lockword : forall Y, 0 <= Y -> Z.lxor (65536 * Y) (Z.land (Z.lxor (65536 * Y) 256) 65280) = 65536 * Y + 256.
Proof.
  intros Y HY.
  assert (E : 65536 * Y + 256 = Z.lxor (65536 * Y) 256) by (apply Z.add_nocarry_lxor; apply land_mul65536_small; lia).
  rewrite <- E, (land_ff00 Y HY). exact (eq_sym E).
Qed.

(* [comment removed for export] *)
Lemma ia_lockbyte : forall Y, 0 <= Y ->
  Z.land ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (65536 * Y)) 8)) mod 18446744073709551616) 255 = 0.
Proof.
  intros Y HY. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (65536 * 65536).
  rewrite Z.mul_mod_distr_l by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace (65536 * (Y mod 65536) / 256) with (256 * (Y mod 65536)) by (Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound Y 65536 ltac:(lia)) as HM.
  rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32 `div` 2) with (2^31); lia).
  rewrite Z.mod_small by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256. Z.div_mod_to_equations; lia.
Qed.

Section IA.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo : Z) (ii : bool).
Notation IA := 0xaed80.
Definition boolz (b : bool) : Z := if b then 1 else 0.
Hypothesis SK : stk asegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv asegs m.
Variable pad : word.                                                           (* [comment removed for export] *)
Hypothesis IAF : rw_cells asegs m 0x13d608 [C1 (Z_to_bv 8 (boolz ii)); C1 zb0; C2 pad].   (* [comment removed for export] *)
Hypothesis PSZ : rw_cells asegs m 0x13d620 [C8 (Z_to_bv 64 4096)].            (* [comment removed for export] *)
Hypothesis GOT : rw_cells asegs m 0xa4990 [C8 (Z_to_bv 64 0x13d620)].        (* [comment removed for export] *)
Hypothesis IWR : wr_at asegs m IA 0x81030.                                     (* [comment removed for export] *)
Variable izl : list byte.                                                      (* [comment removed for export] *)
Hypothesis IZ : u8arr asegs m (IA + 8) izl.
Hypothesis EZ : izl = repeat zb0 (Z.to_nat 0x40000).
Variables psz chk : word.                                                      (* [comment removed for export] *)
Hypothesis IPS : rw_cells asegs m (IA + 0x40dc0) [C8 psz; C8 chk].
Hypothesis IPV : ii = true -> psz = Z_to_bv 64 4096 /\ chk = Z_to_bv 64 (IA + 0x40dd0).
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Notation iaW usp := [(usp - 48, usp); (IA, IA + 0x81030); (0x13d608, 0x13d60c)].

Lemma ia_walk :
  (forall m' (a1' a2' a3' a4' a5' a6' : word), mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> wmono asegs m m' ->
     munch (iaW (bv_unsigned sp)) m m' ->
     rw_cells asegs m' 0x13d608 [C1 (Z_to_bv 8 1); C1 zb0; C2 pad] ->
     rw_cells asegs m' (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))] ->
     u8arr asegs m' (IA + 8) izl -> wr_at asegs m' IA 0x81030 ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IA) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x5f91c) fc None m (seg_rom asegs)).
Proof. aceil.
  intros CONT.
  assert (IZL : Z.of_nat (length izl) = 0x40000) by (rewrite EZ, repeat_length; lia).
  aceil. 
  assert (WM : wmono asegs m m) by apply wmono_refl.
  pose proof (bv_unsigned_in_range 64 pad) as PR. change (bv_modulus 64) with (2^64) in PR.
  set (q := bv_unsigned pad mod 65536). assert (HQ : 0 <= q < 65536) by (subst q; apply Z.mod_pos_bound; lia).
  destruct ii; cbn [boolz] in IAF, CONT.
  - (* [comment removed for export] *)
    destruct (IPV eq_refl) as [-> ->].
    assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m) by apply munch_refl.
    carve_frame 48%nat SK.
    do 6 zstepA.   (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    do 6 zstepA. (* [comment removed for export] *)
    release_frame FR SK (bv_unsigned sp).
    zstepA. (* [comment removed for export] *)
    eapply CONT; [exact MI| exact SK| exact WM| | exact IAF| exact IPS| exact IZ| exact IWR].
    eapply munch_weaken; [| exact MU]. intros x; cbn; lia.
  - (* [comment removed for export] *)
    clear IPV.
    assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xaed80, 0xaed80 + 0x81030); (0x13d608, 0x13d60c)] m m) by apply munch_refl.
    carve_frame 48%nat SK.
    do 6 zstepA.   (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match type of IAF with rw_cells _ ?mx _ _ =>
      assert (IAF4 : rw_cells asegs mx 0x13d608 [C4 (Z_to_bv 64 (65536 * q))])
        by (eapply rw_cells_reshape; [| | exact IAF]; [cbn; tauto| rewrite (ia_cells4 0 0 0 pad) by lia; subst q; do 5 f_equal; lia]) end.
    clear IAF.
    do 8 zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    destruct (sx32_hi16 q HQ) as (k & Hk & HX).
    do 4 zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    rewrite HX. rewrite (ia_lockbyte (q + 65536 * k)) by lia.
    cstep. (* [comment removed for export] *)
    rewrite HX, (ia_lockword (q + 65536 * k)) in IAF4 by lia.
    match type of IAF4 with rw_cells _ ?mx _ _ =>
      assert (IAF : rw_cells asegs mx 0x13d608 [C1 zb0; C1 (Z_to_bv 8 1); C2 pad])
        by (eapply rw_cells_reshape; [| | exact IAF4]; [cbn; tauto| rewrite (ia_cells4 0 1 k pad) by lia; subst q; do 5 f_equal; lia]) end.
    clear IAF4.
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    do 7 zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    eapply imemset0_walk; [lia| lia| lia| exact MI| eapply wr_at_sub; [exact IWR| lia| lia] | intros; apply PDAT; lia|].
    clear MI. intros m2 a1' a2' a3' MI WR2 Z1 MU2 WM2. clear WR2. after_call m1 m2 MU2 WM2.
    ret_pc_lit.
    pose proof (wr_at_store_ok asegs m2 0xaed80 0x81030 0 1 IWR ltac:(lia) ltac:(cbn; lia)) as SOK.
    zstepA. (* [comment removed for export] *)
    settle_store 0xaed80 [zb0] SOK. rename m0 into m3.
    do 4 zstepA. zstepA. (* [comment removed for export] *)
    clear IZ.
    eapply imemset0_walk; [lia| lia| lia| exact MI| eapply wr_at_sub; [exact IWR| lia| lia] | intros; apply PDAT; lia|].
    clear MI a1' a2' a3'. intros m4 a1' a2' a3' MI WR2 Z2 MU2 WM2.
    assert (IZ : u8arr asegs m4 (0xaed80 + 8) izl) by (rewrite EZ; split; [exact Z2| rewrite repeat_length; exact WR2]).
    clear WR2 Z2.
    after_call m3 m4 MU2 WM2. ret_pc_lit.
    do 5 zstepA. zstepA. (* [comment removed for export] *)
    eapply imemset0_walk; [lia| lia| lia| exact MI| eapply wr_at_sub; [exact IWR| lia| lia] | intros; apply PDAT; lia|].
    clear MI a1' a2' a3'. intros m5 a1' a2' a3' MI WR2 Z3 MU2 WM2. clear WR2. after_call m4 m5 MU2 WM2. ret_pc_lit.
    do 5 zstepA. zstepA. (* [comment removed for export] *)
    clear IPS.
    eapply imemset0_walk; [lia| lia| lia| exact MI| eapply wr_at_sub; [exact IWR| lia| lia] | intros; apply PDAT; lia|].
    clear MI a1' a2' a3'. intros m6 a1' a2' a3' MI WR2 Z4 MU2 WM2. clear WR2. after_call m5 m6 MU2 WM2. ret_pc_lit.
    zstepA. zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    do 4 zstepA. (* [comment removed for export] *)
    clear Z4 Z1 Z3.
    pose proof (wr_at_store_ok asegs m6 0xaed80 0x81030 0x40dc0 8 IWR ltac:(lia) ltac:(cbn; lia)) as SOK.
    zstepA. (* [comment removed for export] *)
    settle_store 0xefb40 (le8 (Z_to_bv 64 4096)) SOK. rename m0 into m7.
    pose proof (wr_at_store_ok asegs m7 0xaed80 0x81030 0x40dc8 8 IWR ltac:(lia) ltac:(cbn; lia)) as SOK.
    zstepA. (* [comment removed for export] *)
    settle_store 0xefb48 (le8 (Z_to_bv 64 0xefb50)) SOK. rename m0 into m8.
    assert (PSC : rw_cells asegs m8 0xefb40 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 0xefb50)]).
    { split; [split; [cbn; tauto|]|].
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (proj2 (bytes_at_app asegs _ _ _ _)). split; [exact BAw0|]. rewrite length_le8. exact BAw1.
      - eapply wr_at_sub; [exact IWR| lia| cbn; lia]. }
    clear BAw BAw0 BAw1.
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    do 6 zstepA. (* [comment removed for export] *)
    release_frame FR SK (bv_unsigned sp).
    zstepA. (* [comment removed for export] *)
    eapply CONT; [exact MI| exact SK| exact WM| exact MU| exact IAF| exact PSC| exact IZ| exact IWR].
Qed.
End IA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ia_rw_bytes_b_rom : forall bs A, InitMem.rw_bytes_b asegs A bs = true ->
  forall i b, nth_error bs i = Some b ->
    seg_rom asegs (wa (A + Z.of_nat i)) = Some b /\ wview asegs (fun _ => None) (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs as [|b0 bs IH]; intros A Hb i b Hn; [destruct i; discriminate|].
  cbn [InitMem.rw_bytes_b] in Hb.
  destruct (seg_rom asegs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview asegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [Hbe Hb]. unfold bv_eqb in Hbe. apply Z.eqb_eq in Hbe. apply bv_eq in Hbe. subst b'.
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. rewrite Z.add_0_r. split; [exact Er| rewrite Ew; discriminate].
  - cbn in Hn. replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia. exact (IH (A + 1)%Z Hb i b Hn).
Qed.

Lemma ia_pad_any : forall (m : mem), exists pad : word, rw_cells asegs m 0x13d60a [C2 pad].
Proof.
  intros m.
  assert (Hb : InitMem.rw_bytes_b asegs 0x13d60a [zb0; zb0] = true) by (vm_compute; reflexivity).
  set (rd := fun i : nat => match m (wa (0x13d60a + Z.of_nat i)) with Some b => b | None => zb0 end).
  assert (G : forall i, (i < 2)%nat -> mrd asegs m (wa (0x13d60a + Z.of_nat i)) = Some (rd i) /\ wview asegs m (wa (0x13d60a + Z.of_nat i)) <> None).
  { intros i Hi. assert (E : nth_error [zb0; zb0] i = Some zb0) by (destruct i as [|[|]]; [reflexivity|reflexivity|lia]).
    destruct (ia_rw_bytes_b_rom _ _ Hb i zb0 E) as [R W].
    unfold mrd, rd. unfold wview in *. destruct (m (wa (0x13d60a + Z.of_nat i))) as [b1|] eqn:Em.
    - split; [reflexivity| discriminate].
    - split; [rewrite R; reflexivity| exact W]. }
  exists (Z_to_bv 64 (bv_unsigned (rd 0%nat) + 256 * bv_unsigned (rd 1%nat))).
  pose proof (bv_unsigned_in_range 8 (rd 0%nat)) as R0. pose proof (bv_unsigned_in_range 8 (rd 1%nat)) as R1.
  change (bv_modulus 8) with 256 in R0, R1.
  assert (CB2 : cells_bytes [C2 (Z_to_bv 64 (bv_unsigned (rd 0%nat) + 256 * bv_unsigned (rd 1%nat)))] = [rd 0%nat; rd 1%nat]).
  { cbn [cells_bytes cbytes app]. unfold le2. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
    rewrite Z.mod_small by lia. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    rewrite app_nil_r.
    f_equal; [apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; Z.div_mod_to_equations; nia|].
    f_equal. apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; Z.div_mod_to_equations; nia. }
  split; [split|].
  - cbn. tauto.
  - rewrite CB2. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [length] in Hi.
    rewrite (proj1 (G i Hi)). destruct i as [|[|]]; [reflexivity|reflexivity|lia].
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    replace i with (Z.of_nat (Z.to_nat i)) by lia. exact (proj2 (G (Z.to_nat i) ltac:(lia))).
Qed.

Section IA2.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo : Z) (ii : bool).
Notation IA := 0xaed80.
Hypothesis SK : stk asegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis MI : mem_inv asegs m.
Hypothesis IAF : rw_cells asegs m 0x13d608 [C1 (Z_to_bv 8 (boolz ii)); C1 zb0].   (* [comment removed for export] *)
Hypothesis PSZ : rw_cells asegs m 0x13d620 [C8 (Z_to_bv 64 4096)].
Hypothesis GOT : rw_cells asegs m 0xa4990 [C8 (Z_to_bv 64 0x13d620)].
Hypothesis IWR : wr_at asegs m IA 0x81030.
Variable izl : list byte.
Hypothesis IZ : u8arr asegs m (IA + 8) izl.
Hypothesis EZ : izl = repeat zb0 (Z.to_nat 0x40000).
Variables psz chk : word.
Hypothesis IPS : rw_cells asegs m (IA + 0x40dc0) [C8 psz; C8 chk].
Hypothesis IPV : ii = true -> psz = Z_to_bv 64 4096 /\ chk = Z_to_bv 64 (IA + 0x40dd0).
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Notation iaW usp := [(usp - 48, usp); (IA, IA + 0x81030); (0x13d608, 0x13d60c)].

(* [comment removed for export] *)
Lemma ia_walk2 :
  (forall m' (a1' a2' a3' a4' a5' a6' : word), mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> wmono asegs m m' ->
     munch (iaW (bv_unsigned sp)) m m' ->
     rw_cells asegs m' 0x13d608 [C1 (Z_to_bv 8 1); C1 zb0] ->
     rw_cells asegs m' (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))] ->
     u8arr asegs m' (IA + 8) izl -> wr_at asegs m' IA 0x81030 ->
     evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IA) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x5f91c) fc None m (seg_rom asegs)).
Proof.
  intros CONT. destruct (ia_pad_any m) as [pad PAD].
  assert (IAF3 : rw_cells asegs m 0x13d608 [C1 (Z_to_bv 8 (boolz ii)); C1 zb0; C2 pad]).
  { change [C1 (Z_to_bv 8 (boolz ii)); C1 zb0; C2 pad] with ([C1 (Z_to_bv 8 (boolz ii)); C1 zb0] ++ [C2 pad]).
    eapply rwc_join_at; [exact IAF| exact PAD| reflexivity]. }
  eapply (ia_walk P ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Q m lo ii SK LOC LO SPH MI pad IAF3 PSZ GOT IWR izl IZ EZ psz chk IPS IPV PSTK PDAT).
  intros m' a1' a2' a3' a4' a5' a6' MI' SK' WM' MU' IAF' IPS' IZ' IWR'.
  eapply CONT; [exact MI'| exact SK'| exact WM'| exact MU'| | exact IPS'| exact IZ'| exact IWR'].
  change [C1 (Z_to_bv 8 1); C1 zb0; C2 pad] with ([C1 (Z_to_bv 8 1); C1 zb0] ++ [C2 pad]) in IAF'.
  exact (proj1 (rwc_split _ _ _ _ _ IAF')).
Qed.
End IA2.
End RC__1.
