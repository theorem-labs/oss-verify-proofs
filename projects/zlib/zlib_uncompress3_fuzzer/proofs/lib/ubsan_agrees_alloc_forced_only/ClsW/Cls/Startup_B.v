(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Lib Require Import StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Common Require Import StrFun STRW_tac Startup_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls Require Import CImg F_memset F_memcpy Startup_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := CImg.psegs.

Definition rmemsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Lemma rmemset_specZ : forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  (0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
  evt rsegs (rmemsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x11fc0) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST MI -> -> -> Hc Hn Hl.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
  intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.

Definition rmemcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' A [CB (Z.to_nat n) src]
    /\ bytes_at rsegs m' S src.

Lemma rmemcpy_specZ : forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at rsegs m S src ->
  length src = Z.to_nat n ->
  rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
  (S + n <= A \/ A + n <= S)%Z ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  (0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
  evt rsegs (rmemcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x11bbc) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed.

(* the classifier has no stack-protector guard and no GOT word for it (its __init_ssp at 0x11508 is a
   bare ret), so the checksum's RGOT_SSP / RGUARD cells, rinit_ssp_spec and its canary are not carried. *)


Section LeRoundtrip.
Local Open Scope Z_scope.
Lemma testbit_small_high : forall a k, 0 <= a < 2 ^ 8 -> 8 <= k -> Z.testbit a k = false.
Proof.
  intros a k Ha Hk. destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 8); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_byte_testbit : forall a r k, 0 <= a < 2 ^ 8 -> 0 <= r -> 0 <= k ->
  Z.testbit (Z.lor a (Z.shiftl r 8)) k = if k <? 8 then Z.testbit a k else Z.testbit r (k - 8).
Proof.
  intros a r k Ha Hr Hk. rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec0 k 8).
  - rewrite (Z.testbit_neg_r r (k - 8)) by lia. apply orb_false_r.
  - rewrite (testbit_small_high a k) by lia. reflexivity.
Qed.

Lemma lor_byte_low : forall (b : byte) r, 0 <= r -> Z_to_bv 8 (Z.lor (bv_unsigned b) (Z.shiftl r 8)) = b.
Proof.
  intros b r Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.ltb_spec0 k 8).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite lor_byte_testbit by lia.
    replace (k <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite (testbit_small_high (bv_unsigned b) k) by lia. reflexivity.
Qed.

Lemma lor_byte_high : forall a r, 0 <= a < 2 ^ 8 -> 0 <= r -> Z.shiftr (Z.lor a (Z.shiftl r 8)) 8 = r.
Proof.
  intros a r Ha Hr. apply Z.bits_inj'. intros k Hk.
  rewrite Z.shiftr_spec by lia. rewrite lor_byte_testbit by lia.
  replace (k + 8 <? 8) with false by (symmetry; apply Z.ltb_ge; lia). f_equal. lia.
Qed.

Lemma bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma Z_to_le_bytes_bytes_le_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bytes_le_to_Z_nonneg bs) as Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  rewrite lor_byte_low by exact Hr. rewrite lor_byte_high by lia. rewrite IH. reflexivity.
Qed.

Lemma bytes_le_to_Z_bound : forall bs : list byte, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs.
  pose proof (bytes_le_to_Z_to_le_bytes (length bs) (bytes_le_to_Z bs) (bytes_le_to_Z_nonneg bs)) as E.
  rewrite Z_to_le_bytes_bytes_le_to_Z in E. rewrite E at 1.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. pose proof (bytes_le_to_Z_nonneg bs) as N.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (cbn in B |- *; lia).
  rewrite <- L. apply Z_to_le_bytes_bytes_le_to_Z.
Qed.
End LeRoundtrip.

(* package 3's canary_bytes / canary_of / rinit_ssp_post / rinit_ssp_spec (lines 158-216 of the r23
   Plain/Startup_B.v) are not carried: the classifier's __init_ssp is a bare ret. *)



(* The auxv [StackLayout.auxv_entries] lays for this image: ARCH_DLINFO's ten
   entries, [create_elf_tables]' sixteen, the CONFIG_RSEQ pair when the
   launch's kernel has it, and AT_NULL.  Keys and the image's own PhdrInfo are
   literal; every other value is the launch's. *)
Definition pauxv (la : LaunchAuxv) (hw ent uid gid rnd efn : word) : list word :=
  [Z_to_bv 64 33; la_sysinfo_ehdr la;
   Z_to_bv 64 40; cw_l1i_size (la_cache la); Z_to_bv 64 41; cw_l1i_geom (la_cache la);
   Z_to_bv 64 42; cw_l1d_size (la_cache la); Z_to_bv 64 43; cw_l1d_geom (la_cache la);
   Z_to_bv 64 44; cw_l2_size (la_cache la); Z_to_bv 64 45; cw_l2_geom (la_cache la);
   Z_to_bv 64 46; cw_l3_size (la_cache la); Z_to_bv 64 47; cw_l3_geom (la_cache la);
   Z_to_bv 64 51; la_minsigstksz la;
   Z_to_bv 64 16; hw; Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 17; Z_to_bv 64 100;
   Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10;
   Z_to_bv 64 7; z64; Z_to_bv 64 8; z64; Z_to_bv 64 9; ent;
   Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 13; gid; Z_to_bv 64 14; gid;
   Z_to_bv 64 23; z64; Z_to_bv 64 25; rnd; Z_to_bv 64 31; efn]
  ++ (if la_rseq la then [Z_to_bv 64 27; Z_to_bv 64 28; Z_to_bv 64 28; Z_to_bv 64 32] else [])
  ++ [z64; z64].

Lemma pauxv_length : forall la hw ent uid gid rnd efn,
  length (pauxv la hw ent uid gid rnd efn) = (2 * auxv_count (la_rseq la))%nat.
Proof. intros. unfold pauxv. destruct (la_rseq la); reflexivity. Qed.

Lemma pauxv_auxv_words : forall la ent sp top argv envp execfn uid gid hw,
  auxv_words la CImg.p_phdrs ent sp top argv envp execfn uid gid hw
  = pauxv la hw ent uid gid (Z_to_bv 64 (rnd_addr (la_rseq la) sp argv envp)) (Z_to_bv 64 (xfn_base top argv envp execfn)).
Proof. intros. unfold auxv_words, auxv_entries, pauxv. destruct (la_rseq la); reflexivity. Qed.

Notation RENVIRON := 0x141b0%Z (only parsing).
Notation RPROGNAME := 0x342d0%Z (only parsing).
Notation RHWCAP := 0x34348%Z (only parsing).
Notation RGOT3 := 0x13118%Z (only parsing).

Lemma renvp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at rsegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x11550) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x11544) fc None m (seg_rom rsegs)).
Proof.
  induction ws as [|w ws IH]; intros until rest; intros NZ B HQ.
  - cbn [u64s app] in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite app_length, length_le8 in BB.
    pose proof (rd_u64 rsegs m A z64 rest (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    cbn [length Z.of_nat] in HQ. exact_evt HQ.
  - cbn [u64s app] in B. rewrite <- app_assoc in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite !app_length, !length_le8 in BB.
    apply Forall_cons_iff in NZ. destruct NZ as [NZw NZ].
    pose proof (rd_u64 rsegs m A w _ (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep. if_true.
    apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
    eapply (IH Q); [exact NZ | exact B |].
    cbn [length] in HQ. exact_evt HQ.
Qed.





Section RInitLibc.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (R : Z) (P : Z) (s : list byte)
            (pn0 pnf0 hw0 env0 uid hw : word)
            (la : LaunchAuxv) (ent gid efn : word).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x141b8); (0x141b8, 0x34288); (0x34290, 0x342c0);
                 (RPROGNAME, 0x342e0); (RLIBC, 0x34350)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition rinit_libc_post : Z -> machine_state -> Prop :=
    fun t ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x14230) (Z_to_bv 64 0x34318) (Z_to_bv 64 0x14290) z64)
    /\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
    /\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells rsegs m' RSYSINFO [C8 z64]
    /\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
    /\ rw_cells rsegs m' RHWCAP [C8 hw]
    /\ rw_cells rsegs m' RENVIRON [C8 (Z_to_bv 64 E)]
    /\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x342d8); C8 (Z_to_bv 64 RPROGNAME)]
    /\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
    /\ bytes_at rsegs m' E (u64s eps ++ le8 z64 ++ u64s (pauxv la hw ent uid gid (Z_to_bv 64 R) efn))
    /\ bytes_at rsegs m' P (s ++ [Z_to_bv 8 0])
    /\ (0 < t < 4194304)%Z.

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x35000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  Definition rpn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists pg m',
    ms' = MS (mkR (Z_to_bv 64 0x11538) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
                  (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
                  (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x11614) fc None m' (seg_rom rsegs)
    /\ munch [(RPROGNAME, 0x342d8)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  Lemma rpn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(RPROGNAME, 0x342d8)]%Z m0 mm -> wmono rsegs m0 mm -> mem_inv rsegs mm ->
    bytes_at rsegs mm P (s ++ [Z_to_bv 8 0]) ->
    rw_cells rsegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt rsegs (rpn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x11538) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x11608) fc None mm (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length s)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_false. zstep. if_false.
      replace (Z_to_bv 64 (P + j)) with (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) by (f_equal; lia).
      unfold rpn_post. finish2. all: eassumption.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      destruct (nth_error s (Z.to_nat (j - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
      pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ Hb)) as NZb. cbn in NZb.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      pose proof (u8ro_read rsegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_cases K.
      + lstep. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
      + zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
  Qed.

  Ltac rscan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  (* A key at or above AUX_CNT (the cache words, AT_MINSIGSTKSZ): [bgeu] skips
     the store and the loop loads the next key. *)
  Ltac skip_it AUXB ki :=
    lstep; if_true; ldaux AUXB ki; lstep; astep.

  Lemma rinit_libc_spec : forall tp a0 a1,
    stk rsegs m lo (bv_unsigned sp) ->
    bytes_at rsegs m E (u64s eps ++ le8 z64 ++ u64s (pauxv la hw ent uid gid (Z_to_bv 64 R) efn)) ->
    bytes_at rsegs m P (s ++ [Z_to_bv 8 0]) ->
    rw_cells rsegs m RPROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells rsegs m RHWCAP [C8 hw0] ->
    rw_cells rsegs m RENVIRON [C8 env0] ->
    rw_cells rsegs m RSYSINFO [C8 z64] ->
    rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
    rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
    rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells rsegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x342d8); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv rsegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost rinit_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1150c) fc None m (seg_rom rsegs)).
  Proof.
    (* The walk is the same for both kernels up to the CONFIG_RSEQ pair, which
       only a CONFIG_RSEQ kernel lays; the two cases are walked separately. *)
    destruct (la_rseq la) eqn:RS.
    - intros tp a0 a1 ST ENV STR G2 HW ENVC SI LC TDC MT DS GOT3 GD MI -> ->.
      unfold td_cells, libc_cells in *.
      pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. rewrite pauxv_length, RS in EB. cbn [auxv_count] in EB.
      pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
      pose proof (bv_unsigned_in_range 64 hw) as RHW. unfold bv_modulus in RHW. cbn in RHW.
      iprefix.
      carve_frame 384%nat ST.
      do 10 lstep.
      apply (rw_cells_split_CB rsegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
      change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
      replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
      replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
      lstep. call (rmemset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
      rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
      apply (rw_cells_recast rsegs _ _ _ (repeat (C8 z64) 38)) in AUX;
        [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
      lstep. lstep. lstep.
      eapply (renvp_count_loop eps); [exact EPS | exact ENV |].
      lstep. lstep. lstep.
      pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
      apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
      replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
      unfold pauxv in AUXB. rewrite RS in AUXB. cbn [app] in AUXB.
      ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
      rscan_it AUXB 1%nat 2%nat.
      skip_it AUXB 4%nat. skip_it AUXB 6%nat. skip_it AUXB 8%nat. skip_it AUXB 10%nat. skip_it AUXB 12%nat.
      skip_it AUXB 14%nat. skip_it AUXB 16%nat. skip_it AUXB 18%nat. skip_it AUXB 20%nat.
      rscan_it AUXB 21%nat 22%nat. rscan_it AUXB 23%nat 24%nat. rscan_it AUXB 25%nat 26%nat. rscan_it AUXB 27%nat 28%nat.
      rscan_it AUXB 29%nat 30%nat. rscan_it AUXB 31%nat 32%nat. rscan_it AUXB 33%nat 34%nat. rscan_it AUXB 35%nat 36%nat.
      rscan_it AUXB 37%nat 38%nat. rscan_it AUXB 39%nat 40%nat. rscan_it AUXB 41%nat 42%nat. rscan_it AUXB 43%nat 44%nat.
      rscan_it AUXB 45%nat 46%nat. rscan_it AUXB 47%nat 48%nat. rscan_it AUXB 49%nat 50%nat. rscan_it AUXB 51%nat 52%nat.
      (* The CONFIG_RSEQ pair: AT_RSEQ_FEATURE_SIZE and AT_RSEQ_ALIGN are below AUX_CNT. *)
      rscan_it AUXB 53%nat 54%nat. rscan_it AUXB 55%nat 56%nat.
      steps_to 0x115c8%Z.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
      steps_to 0x11608%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (rpn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
      rename POST into G2. try rename MI0 into MI.
      apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
      apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
      cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
      replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
      replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
      lstep. lstep.
      name_sp sp (-384)%Z. name_sp sp (-336)%Z.
      icallk (rinit_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
      all: lazymatch goal with
           | |- forall _, _ => ipost rsegs; unname_sp; unname_sp
           | |- _ => unname_sp; unname_sp;
                     first [ hyp_by_addr | reflexivity | lia
                           | lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
                               replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
           end.
      rename PC into ST. unfold td_cells, libc_cells in *.
      lstep. lstep.
      (* the classifier's __init_ssp (0x11508) is a bare ret; it writes nothing *)
      lstep.
      do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
      do 5 lstep.
      join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
      release_frame FRlo ST (bv_unsigned sp).
      lstep.
      unfold rinit_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
      all: hyp_by_addr.
    - intros tp a0 a1 ST ENV STR G2 HW ENVC SI LC TDC MT DS GOT3 GD MI -> ->.
      unfold td_cells, libc_cells in *.
      pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. rewrite pauxv_length, RS in EB. cbn [auxv_count] in EB.
      pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
      pose proof (bv_unsigned_in_range 64 hw) as RHW. unfold bv_modulus in RHW. cbn in RHW.
      iprefix.
      carve_frame 384%nat ST.
      do 10 lstep.
      apply (rw_cells_split_CB rsegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
      change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
      replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
      replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
      lstep. call (rmemset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
      rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
      apply (rw_cells_recast rsegs _ _ _ (repeat (C8 z64) 38)) in AUX;
        [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
      lstep. lstep. lstep.
      eapply (renvp_count_loop eps); [exact EPS | exact ENV |].
      lstep. lstep. lstep.
      pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
      apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
      replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
      unfold pauxv in AUXB. rewrite RS in AUXB. cbn [app] in AUXB.
      ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
      rscan_it AUXB 1%nat 2%nat.
      skip_it AUXB 4%nat. skip_it AUXB 6%nat. skip_it AUXB 8%nat. skip_it AUXB 10%nat. skip_it AUXB 12%nat.
      skip_it AUXB 14%nat. skip_it AUXB 16%nat. skip_it AUXB 18%nat. skip_it AUXB 20%nat.
      rscan_it AUXB 21%nat 22%nat. rscan_it AUXB 23%nat 24%nat. rscan_it AUXB 25%nat 26%nat. rscan_it AUXB 27%nat 28%nat.
      rscan_it AUXB 29%nat 30%nat. rscan_it AUXB 31%nat 32%nat. rscan_it AUXB 33%nat 34%nat. rscan_it AUXB 35%nat 36%nat.
      rscan_it AUXB 37%nat 38%nat. rscan_it AUXB 39%nat 40%nat. rscan_it AUXB 41%nat 42%nat. rscan_it AUXB 43%nat 44%nat.
      rscan_it AUXB 45%nat 46%nat. rscan_it AUXB 47%nat 48%nat. rscan_it AUXB 49%nat 50%nat. rscan_it AUXB 51%nat 52%nat.
      steps_to 0x115c8%Z.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
      steps_to 0x11608%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (rpn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
      rename POST into G2. try rename MI0 into MI.
      apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
      apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
      cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
      replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
      replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
      lstep. lstep.
      name_sp sp (-384)%Z. name_sp sp (-336)%Z.
      icallk (rinit_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
      all: lazymatch goal with
           | |- forall _, _ => ipost rsegs; unname_sp; unname_sp
           | |- _ => unname_sp; unname_sp;
                     first [ hyp_by_addr | reflexivity | lia
                           | lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
                               replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
           end.
      rename PC into ST. unfold td_cells, libc_cells in *.
      lstep. lstep.
      (* the classifier's __init_ssp (0x11508) is a bare ret; it writes nothing *)
      lstep.
      do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
      do 5 lstep.
      join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
      release_frame FRlo ST (bv_unsigned sp).
      lstep.
      unfold rinit_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
      all: hyp_by_addr.
  Qed.
End RInitLibc.

