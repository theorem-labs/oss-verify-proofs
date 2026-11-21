(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_adler32.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_dkit Z_ukit Z_adler32 Zg_adler32_iface Zg_adler32_loops.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum ZChkArith ZChkAdl AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition NB : nat := 347 * 16.
Definition az_frameN (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j : list byte) : list cell :=
  CB 8 j :: C8 (wz 5552) :: C8 (wz (-5552)) :: az_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

Lemma az_nmax : forall (K : nat) (d : list byte) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 q21 q22 q25 q26 q27 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b n : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frameN ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  bytes_at usegs m p d -> (1 <= K)%nat -> 5552 * Z.of_nat K <= n -> Z.of_nat (length d) = n -> n < 5552 * Z.of_nat K + 5552 ->
  0 <= p -> p + n < 2^63 -> n < 2^32 -> bv_unsigned sp < 2^63 -> 128 <= bv_unsigned sp ->
  0 <= a < 2^16 -> 0 <= b < 2^16 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a' b' (q1' q21' q22' q25' q26' q27' : word),
      a' mod ABASE = fst (adl_raw (bZ (firstn (K * NB) d)) a b) mod ABASE /\
      b' mod ABASE = snd (adl_raw (bZ (firstn (K * NB) d)) a b) mod ABASE /\
      0 <= a' < ABASE /\ 0 <= b' < ABASE /\
      ms' = MS (mkR q1' (wz (bv_unsigned sp + -128)) gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) (wz (p + 5552 * Z.of_nat K)) (wz (n - 5552 * Z.of_nat K))
                   (wz b') (wz a') (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) q21' q22' (wz 4223091239536077) (wz 65521) q25' q26' q27'
                   (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
               F (wz 0x1b0b0) fc None m (seg_rom usegs))
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) (wz p) (wz n)
             (wz b) (wz a) (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) q21 q22 (wz 4223091239536077) (wz 65521) q25 q26 q27
             (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
        F (wz PC_AZ_NMAX) fc None m (seg_rom usegs)).
Proof.
  induction K as [|K IH]; intros until j; intros FR BY HK Hlo Hn Hhi Hp Hl Hn32 SP63 SP128 Ha Hb MI; [lia|].
  rewrite Nat2Z.inj_succ in *. unfold az_frameN, az_saved in FR.
  assert (LEN : (NB <= length d)%nat) by (unfold NB; lia).
  pose proof BY as BY0. rewrite <- (firstn_skipn NB d) in BY. apply bytes_at_app in BY. destruct BY as [BY1 BY2].
  rewrite length_firstn in BY2. replace (Z.of_nat (Init.Nat.min NB (length d))) with 5552 in BY2 by (unfold NB in *; lia).
  unfold PC_AZ_NMAX. do 6 zs.
  eapply evt_cut.
  { eapply evt_eq; [| eapply (az_in16 347 d) with (p := p) (a := a) (b := b); [exact BY0 | lia | unfold NB in LEN; lia | lia | lia | exact MI]].
    zreg_eq. }
  intros ms' (q1' & q21' & q22' & q25' & ->). fold NB.
  destruct (adl_bnd (firstn NB d) a b (2^16) (2^16) 5552 ltac:(lia) ltac:(lia) ltac:(rewrite length_firstn; unfold NB; lia)) as [B1 B2].
  set (A1 := fst (adl_raw (bZ (firstn NB d)) a b)) in *. set (B1v := snd (adl_raw (bZ (firstn NB d)) a b)) in *.
  assert (R1 : 0 <= A1 < RLIM) by (unfold RLIM; lia). assert (R2 : 0 <= B1v < RLIM) by (unfold RLIM; lia).
  pose proof (RQ_bound A1 R1) as Qa. pose proof (RQ_bound B1v R2) as Qb.
  pose proof (RH_bound A1 R1) as Ha2. pose proof (RH_bound B1v R2) as Hb2.
  pose proof (RT_bound A1 R1) as Ta. pose proof (RT_bound B1v R2) as Tb.
  unfold RT, RH, RD, RQ, AMAGIC_IMAGE in Qa, Qb, Ha2, Hb2, Ta, Tb.
  change (983265 * 4294967296 + 221234637) with 4223091239536077 in Qa, Qb, Ha2, Hb2, Ta, Tb. unfold RLIM in R1, R2.
  do 16 zs. fold (azq A1) (azq B1v). rewrite ?az_red1, ?az_red2 by (unfold RLIM; lia).
  pose proof (Z.mod_pos_bound A1 ABASE ltac:(unfold ABASE; lia)) as Ma. pose proof (Z.mod_pos_bound B1v ABASE ltac:(unfold ABASE; lia)) as Mb.
  assert (AB : ABASE = 65521) by reflexivity.
  zs. if_cases Kc; br_norm Kc; rewrite Z.shiftr_div_pow2 in Kc by lia; change (2 ^ 4) with 16 in Kc.
  -
    destruct (Nat.eq_dec K 0) as [->|NZ]; [exfalso; lia|].
    eapply evt_mono.
    { eapply evt_eq; [| eapply (IH (skipn NB d)) with (p := p + 5552) (n := n - 5552) (a := A1 mod ABASE) (b := B1v mod ABASE);
        try first [exact FR | exact BY2 | exact MI | lia | rewrite length_skipn; unfold NB in *; lia] ].
      all: zreg_eq. }
    intros ms' (a'' & b'' & q1'' & q21'' & q22'' & q25'' & q26'' & q27'' & E1 & E2 & R3 & R4 & ->).
    exists a'', b''. do 6 eexists.
    change (S K * NB)%nat with (NB + K * NB)%nat. rewrite firstn_split, bZ_app, adl_raw_app'. subst A1 B1v.
    destruct (adl_raw_congr (bZ (firstn (K * NB) (skipn NB d)))
                (fst (adl_raw (bZ (firstn NB d)) a b) mod ABASE) (snd (adl_raw (bZ (firstn NB d)) a b) mod ABASE)
                (fst (adl_raw (bZ (firstn NB d)) a b)) (snd (adl_raw (bZ (firstn NB d)) a b))
                ltac:(apply Z.mod_mod; unfold ABASE; lia) ltac:(apply Z.mod_mod; unfold ABASE; lia)) as [C1 C2].
    split; [rewrite E1; exact C1|]. split; [rewrite E2; exact C2|]. split; [exact R3|]. split; [exact R4|].
    zreg_eq.
  -
    destruct (Nat.eq_dec K 0) as [->|NZ]; [|exfalso; lia].
    apply evt_done. exists (A1 mod ABASE), (B1v mod ABASE). do 6 eexists.
    rewrite Nat.mul_1_l. subst A1 B1v.
    split; [apply Z.mod_mod; unfold ABASE; lia|]. split; [apply Z.mod_mod; unfold ABASE; lia|].
    split; [exact Ma|]. split; [exact Mb|]. zreg_eq.
Qed.

Definition PC_AZ_SBYTES : Z := 0x1ae64.
Definition PC_AZ_SCOMB : Z := 0x1ae80.

Lemma az_sbytes : forall (d : list byte) (q1 sp' gp tp t0 t1 t2 q8 q9 x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p e a b : Z),
  bytes_at usegs m p d -> d <> [] -> 0 <= p -> p + Z.of_nat (length d) < 2^63 -> e = p + Z.of_nat (length d) -> mem_inv usegs m ->
  evt usegs (fun ms' => exists x15',
      ms' = MS (mkR q1 sp' gp tp t0 t1 t2 q8 q9 (wz e) (wz e) (wz (-1))
                   (wz (snd (adl_raw (bZ d) a b))) (wz (fst (adl_raw (bZ d) a b))) x15' (wz e) q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
               F (wz PC_AZ_SCOMB) fc None m (seg_rom usegs))
    (MS (mkR q1 sp' gp tp t0 t1 t2 q8 q9 (wz e) (wz p) (wz (-1)) (wz b) (wz a) x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_SBYTES) fc None m (seg_rom usegs)).
Proof.
  induction d as [|c d IH]; intros until b; intros BY NE Hp Hl He MI; [congruence|].
  cbn [length] in Hl, He, BY |- *. rewrite Nat2Z.inj_succ in *.
  pose proof (u8ro_read usegs m p (c :: d) 0 c (wa (p + 0)) BY eq_refl ltac:(lia) eq_refl) as RD.
  replace (p + 0) with p in RD by lia.
  pose proof (bv_unsigned_in_range 8 c) as RC. change (bv_modulus 8) with 256 in RC.
  assert (BY' : bytes_at usegs m (p + 1) d).
  { change (c :: d) with ([c] ++ d) in BY. apply bytes_at_app in BY. exact (proj2 BY). }
  unfold PC_AZ_SBYTES. ustep AZ_TRAP. do 5 zs.
  replace (wz (a + bv_unsigned c + b)) with (wz (b + (a + bv_unsigned c))) by (f_equal; lia).
  rewrite bZ_cons, adl_raw_cons.
  destruct d as [|c2 d2].
  - cbn [length] in *. zs. br_false.
    apply evt_done. eexists. cbn [bZ map adl_raw fst snd]. subst e. replace (Z.succ (Z.of_nat 0)) with 1 by reflexivity. reflexivity.
  - pose proof (Nat2Z.is_nonneg (length d2)) as L2. cbn [length] in *. rewrite !Nat2Z.inj_succ in *.
    zs. br_true.
    eapply evt_mono; [eapply evt_eq; [| eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (p + 1) e (a + bv_unsigned c) (b + (a + bv_unsigned c)));
                      [exact BY' | discriminate | lia | lia | lia | exact MI]]; zreg_eq |].
    intros ms' (x15' & ->). eexists. zreg_eq.
Qed.

Lemma az_scomb : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 t0 t1 t2 q8 q9 q10 q11 q12 x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (a b lo : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  stk usegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  0 <= a < 2 * ABASE -> 0 <= b < RLIM ->
  mem_inv usegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono usegs m0 m ->
  evt usegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.lor ((b mod ABASE) * 2 ^ 16) (a mod ABASE)) lo m0)
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 q8 q9 q10 q11 q12 (wz b) (wz a) x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_SCOMB) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros FR STK LO SP63 Ha Hb MI MU WM.
  unfold PC_AZ_SCOMB, RLIM, ABASE, az_frame, az_saved in *. az_magic MI.
  pose proof (RQ_bound b Hb) as Qb. pose proof (RH_bound b Hb) as Hb2. pose proof (RT_bound b Hb) as Tb.
  unfold RT, RH, RD, RQ, AMAGIC_IMAGE in Qb, Hb2, Tb.
  change (983265 * 4294967296 + 221234637) with 4223091239536077 in *.
  do 6 zs. do 4 zs. rewrite (csub_mask a) by lia.
  do 8 zs. fold (azq b). rewrite ?az_red1, ?az_red2 by (unfold RLIM; lia).
  change (DeflateLz.adler_csub a) with (csub a). rewrite csub_mod by (unfold ABASE; lia). unfold ABASE.
  pose proof (Z.mod_pos_bound a 65521 ltac:(lia)) as Ma. pose proof (Z.mod_pos_bound b 65521 ltac:(lia)) as Mb.
  do 2 zs. rewrite shl16_small by lia. zs.
  az_epilogue FR STK sp.
  apply evt_done. unfold az_post, adler32_postS. do 14 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact STK].
Qed.

Lemma az_short : forall (d : list byte) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 t0 t1 t2 q8 q9 x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (p a b lo : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  stk usegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  bytes_at usegs m p d -> Z.of_nat (length d) <= 15 -> 0 <= p -> p + Z.of_nat (length d) < 2^63 ->
  0 <= a < 2^16 -> 0 <= b < 2^16 ->
  mem_inv usegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono usegs m0 m ->
  evt usegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (Z.lor ((snd (adl_raw (bZ d) a b) mod ABASE) * 2 ^ 16) (fst (adl_raw (bZ d) a b) mod ABASE)) lo m0)
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 q8 q9 (wz 16) (wz p) (wz (Z.of_nat (length d))) (wz b) (wz a) x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_SHORT) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros FR STK LO SP63 BY LE Hp Hl Ha Hb MI MU WM.
  destruct (adl_bnd d a b (2^16) (2^16) 15 ltac:(lia) ltac:(lia) LE) as [B1 B2].
  unfold PC_AZ_SHORT. destruct d as [|c d].
  - cbn [length Z.of_nat]. zs. br_true. cbn [bZ map adl_raw fst snd].
    eapply az_scomb; first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold ABASE, RLIM; lia].
  - pose proof (Nat2Z.is_nonneg (length d)) as L2. cbn [length] in *. rewrite !Nat2Z.inj_succ in *.
    zs. br_false. zs. rewrite zb_lxor_ones by lia. zs. zs. br_false. do 4 zs.
    eapply evt_cut.
    { eapply evt_eq; [| eapply (az_sbytes (c :: d)) with (p := p) (e := p + Z.of_nat (length (c :: d))) (a := a) (b := b);
        [exact BY | discriminate | lia | cbn [length]; lia | reflexivity | exact MI]]. cbn [length]. rewrite Nat2Z.inj_succ. zreg_eq. }
    intros ms' (x15' & ->).
    eapply az_scomb; first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold ABASE, RLIM; cbn [length] in *; lia].
Qed.

Lemma adl_raw_split : forall k d u v,
  adl_raw (bZ d) u v = adl_raw (bZ (skipn k d)) (fst (adl_raw (bZ (firstn k d)) u v)) (snd (adl_raw (bZ (firstn k d)) u v)).
Proof. intros. rewrite <- (firstn_skipn k d) at 1. rewrite bZ_app. apply adl_raw_app'. Qed.

Lemma lor_congr : forall rest a' b' A Bs, a' mod ABASE = A mod ABASE -> b' mod ABASE = Bs mod ABASE ->
  Z.lor ((snd (adl_raw rest a' b') mod ABASE) * 65536) (fst (adl_raw rest a' b') mod ABASE)
  = Z.lor ((snd (adl_raw rest A Bs) mod ABASE) * 65536) (fst (adl_raw rest A Bs) mod ABASE).
Proof.
  intros rest a' b' A Bs E1 E2. destruct (adl_raw_congr rest a' b' A Bs E1 E2) as [C1 C2]. rewrite C1, C2. reflexivity.
Qed.

Definition PC_AZ_MID : Z := 0x1b0bc.

Lemma az_mid : forall (d : list byte) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 t0 t1 t2 q8 q9 q10 x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (p a b lo : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  stk usegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  bytes_at usegs m p d -> 16 <= Z.of_nat (length d) < 5552 -> 0 <= p -> p + Z.of_nat (length d) < 2^63 ->
  0 <= a < 2^16 -> 0 <= b < 2^16 ->
  mem_inv usegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono usegs m0 m ->
  evt usegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (Z.lor ((snd (adl_raw (bZ d) a b) mod ABASE) * 2 ^ 16) (fst (adl_raw (bZ d) a b) mod ABASE)) lo m0)
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 q8 q9 q10 (wz p) (wz (Z.of_nat (length d))) (wz b) (wz a) x15 x16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_MID) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros FR STK LO SP63 BY LE Hp Hl Ha Hb MI MU WM.
  set (n := Z.of_nat (length d)) in *. set (q := Z.to_nat (n / 16)).
  assert (Hq : Z.of_nat q = n / 16) by (subst q; rewrite Z2Nat.id; [reflexivity|]; apply Z.div_pos; lia).
  assert (Hq2 : 16 * Z.of_nat q <= n < 16 * Z.of_nat q + 16) by (rewrite Hq; lia).
  assert (Hq1 : (1 <= q)%nat) by lia.
  pose proof BY as BY0. rewrite <- (firstn_skipn (q * 16) d) in BY. apply bytes_at_app in BY. destruct BY as [_ BY2].
  rewrite length_firstn in BY2.
  assert (LR : Z.of_nat (length (skipn (q * 16) d)) = n - 16 * Z.of_nat q) by (rewrite length_skipn; lia).
  replace (Z.of_nat (Init.Nat.min (q * 16) (length d))) with (16 * Z.of_nat q) in BY2 by lia.
  destruct (adl_bnd (firstn (q * 16) d) a b (2^16) (2^16) 5552 ltac:(lia) ltac:(lia) ltac:(rewrite length_firstn; lia)) as [B1 B2].
  unfold PC_AZ_MID. do 17 zs.
  eapply evt_cut.
  { eapply (az_do16 q d) with (p := p) (a := a) (b := b); first [exact BY0 | exact MI | lia]. }
  intros ms' (q23' & q24' & q25' & ->).
  rewrite (adl_raw_split (q * 16) d a b). zs.
  eapply evt_eq; [| eapply (az_tail (skipn (q * 16) d)) with (p := p + 16 * Z.of_nat q);
                    first [exact FR | exact STK | exact BY2 | exact MI | exact MU | exact WM | lia ] ].
  zreg_eq.
Qed.

Lemma len1_spec_eq : forall adler B (c : byte), adler32_z_spec adler B [c] = DeflateLz.adler32_len1 adler (bv_unsigned c).
Proof. intros. reflexivity. Qed.

Lemma spec_gen : forall adler B d, Z.of_nat (length d) <> 1 -> B <> 0 ->
  adler32_z_spec adler B d
  = Z.lor ((snd (adl_raw (bZ d) (adler mod 65536) (adler mod 2 ^ 32 / 2 ^ 16)) mod ABASE) * 2 ^ 16)
          (fst (adl_raw (bZ d) (adler mod 65536) (adler mod 2 ^ 32 / 2 ^ 16)) mod ABASE).
Proof.
  intros adler B d H1 H2. unfold adler32_z_spec, lo16, hi16. change (2 ^ 16) with 65536 at 1.
  replace (Z.of_nat (length d) =? 1) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (B =? 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  destruct (adl_raw _ _ _); reflexivity.
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells usegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma adler32_z_g : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (adler B lo : Z) (d : list byte),
  0 <= adler < 2^64 -> 0 < B -> B + Z.of_nat (length d) < 2^63 -> Z.of_nat (length d) < 2^32 ->
  bytes_at usegs m B d -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  (B + Z.of_nat (length d) <= lo \/ bv_unsigned sp <= B) ->
  evt usegs (adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_z_spec adler B d) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz (Z.of_nat (length d))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32_Z) fc None m (seg_rom usegs)).
Proof.
  intros until d. intros HA HB HBL HL BY MI STK LO SP63 SEP.
  pose proof (proj1 STK) as LO0.
  assert (RA : 0 <= adler mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  pose proof (srliw16 adler HA) as ES.
  set (s2v := adler mod 2 ^ 32 / 2 ^ 16) in *.
  assert (RS2 : 0 <= s2v < 65536).
  { subst s2v. split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mod_pos_bound adler (2^32)); lia. }
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (LD : Z.of_nat (length d) = Z.of_nat (length d)) by reflexivity.
  unfold Z_ADLER32_Z. carve_frame 128%nat STK. do 14 zs.
  destruct (Nat.eq_dec (length d) 1) as [L1|NL1].
  {
    destruct d as [|c [|]]; try discriminate L1. rewrite len1_spec_eq. cbn [length] in *.
    pose proof (bv_unsigned_in_range 8 c) as RC. change (bv_modulus 8) with 256 in RC.
    pose proof (u8ro_read usegs _ B [c] 0 c (wa (B + 0)) BY eq_refl ltac:(lia) eq_refl) as RD.
    replace (B + 0) with B in RD by lia.
    zstep. rewrite ES. do 4 zstep. if_false. gF.
    do 6 zstep.
    do 5 zstep. rewrite (csub_mask (adler mod 65536 + bv_unsigned c)) by lia.
    set (a := DeflateLz.adler_csub (adler mod 65536 + bv_unsigned c)).
    assert (RAa : 0 <= a < 65792) by (subst a; unfold DeflateLz.adler_csub; destruct (Z.ltb_spec 65520 (adler mod 65536 + bv_unsigned c)); lia).
    do 9 zstep. rewrite (csub_mask16 (a + s2v)) by lia.
    az_epilogue FR STK sp.
    apply evt_done. unfold adler32_postS. do 14 eexists. eexists.
    split; [unfold DeflateLz.adler32_len1; fold s2v; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| exact STK]. }
  assert (LEN1 : Z.of_nat (length d) <> 1) by lia. clear NL1.
  rewrite (spec_gen adler B d LEN1) by lia. fold s2v.
  zstep. rewrite ES. do 3 zstep. zs. br_true. zs. br_false. zs. zs. br_cases K16.
  2:{
      eapply (az_short d); first [exact FR | exact STK | exact BY | eassumption | exact MU | exact WM | lia]. }
  do 2 zs. zs. if_cases K347; br_norm K347; rewrite Z.shiftr_div_pow2 in K347 by lia; change (2 ^ 4) with 16 in K347.
  {
    eapply (az_mid d); first [exact FR | exact STK | exact BY | eassumption | exact MU | exact WM | lia]. }
  do 19 zs.
  lazymatch goal with H : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => az_magic H end.
  do 7 zs.
  set (n := Z.of_nat (length d)) in *. set (K := Z.to_nat (n / 5552)).
  assert (HKq : Z.of_nat K = n / 5552) by (subst K; rewrite Z2Nat.id; [reflexivity|]; apply Z.div_pos; lia).
  assert (HK2 : 5552 * Z.of_nat K <= n < 5552 * Z.of_nat K + 5552) by (rewrite HKq; lia).
  assert (HK1 : (1 <= K)%nat) by lia.
  assert (AB : ABASE = 65521) by reflexivity.
  eapply evt_cut.
  { eapply (az_nmax K d ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (p := B) (n := n);
      first [unfold az_frameN, az_saved; close_cells FR | exact BY | eassumption | lia]. }
  intros ms' (a' & b' & q1' & q21' & q22' & q25' & q26' & q27' & E1 & E2 & R3 & R4 & ->).
  pose proof FR as FRW. destruct FRW as [[W1 _] _]. cbn [cells_wf cell_wf] in W1. destruct W1 as [LJ _].
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?J :: C8 ?u :: C8 ?v :: _) =>
    eapply (rw_cells_recast _ _ _ (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (J ++ le8 u ++ le8 v))) in FR;
    [ | unfold az_frame, az_saved; cbn [cells_wf cell_wf]; rewrite !length_app, !length_le8, LJ; repeat split; reflexivity
      | unfold az_frame, az_saved; cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity ] end.
  pose proof BY as BYr. rewrite <- (firstn_skipn (K * NB) d) in BYr. apply bytes_at_app in BYr. destruct BYr as [_ BYr].
  rewrite length_firstn in BYr.
  assert (LR : Z.of_nat (length (skipn (K * NB) d)) = n - 5552 * Z.of_nat K) by (rewrite length_skipn; unfold NB; lia).
  zs. br_cases Kz.
  -
    rewrite firstn_all2 in E1, E2 by (unfold NB; lia).
    rewrite <- E1, <- E2. rewrite (Z.mod_small a' ABASE), (Z.mod_small b' ABASE) by lia.
    eapply az_fin; first [exact FR | exact STK | eassumption | exact MU | exact WM | lia].
  - replace (Z.of_nat (Init.Nat.min (K * NB) (length d))) with (5552 * Z.of_nat K) in BYr by (unfold NB in *; lia).
    rewrite (adl_raw_split (K * NB) d). rewrite <- (lor_congr (bZ (skipn (K * NB) d)) a' b' _ _ E1 E2).
    zs. zs. br_cases K16b.
    +
      assert (NE : skipn (K * NB) d <> []) by (intros E0; rewrite E0 in LR; cbn in LR; lia).
      eapply evt_eq; [| eapply (az_tail1 (skipn (K * NB) d)) with (p := B + 5552 * Z.of_nat K);
                        first [exact FR | exact STK | exact BYr | exact NE | eassumption | exact MU | exact WM | lia] ].
      zreg_eq.
    +
      eapply evt_eq; [| eapply (az_mid (skipn (K * NB) d)) with (p := B + 5552 * Z.of_nat K);
                        first [exact FR | exact STK | exact BYr | eassumption | exact MU | exact WM | lia] ].
      zreg_eq.
Qed.

Lemma adler32_g : adler32_stmt.
Proof.
  unfold adler32_stmt. intros until d. intros HA HB HBL HL BY MI STK LO SP63 SEP.
  unfold Z_ADLER32. do 3 zstep. rewrite (Z.mod_small (Z.of_nat (length d)) 4294967296) by lia.
  eapply adler32_z_g; eassumption.
Qed.
