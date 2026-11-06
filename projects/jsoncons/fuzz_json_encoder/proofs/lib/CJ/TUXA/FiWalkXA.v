(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge FP Arr Frame Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrMem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TU Require Import G3Lem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TUXA Require Import DgWalkXA.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := DgWalkXA.rsegs.

(* [comment removed for export] *)
Definition FM1 : Z := 0xCCCCCCCCCCCCCCCD.
Lemma mulhu10 : forall x, (0 <= x < 2 ^ 64)%Z -> (((x * (FM1 mod 18446744073709551616)) ≫ 64 mod 18446744073709551616) ≫ 3 = x / 10)%Z.
Proof.
  intros x Hx. unfold FM1. rewrite (Z.mod_small 0xCCCCCCCCCCCCCCCD) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (Hq : (x * 0xCCCCCCCCCCCCCCCD / 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.div_lt_upper_bound; lia).
  rewrite (Z.mod_small (x * 0xCCCCCCCCCCCCCCCD / 2 ^ 64)) by (split; [apply Z.div_pos; lia | lia]).
  rewrite Z.div_div by lia.
  pose proof (Z.div_mod x 10 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hr.
  set (q := x / 10) in *. set (r := x mod 10) in *.
  symmetry. apply (Z.div_unique _ _ _ (2 * q + r * 0xCCCCCCCCCCCCCCCD)); [left; lia | lia].
Qed.

Ltac exs := repeat (lazymatch goal with |- ex _ => eexists end).

Section FIU.
(* [comment removed for export] *)
Variables sp gp tp s0 s1 s2 s3 : word.
Variables F SK v : Z.
Local Notation SB := 2147450880%Z.
Local Notation BUF := (F + 32)%Z.
Hypothesis FR : (0x6c0000 <= F /\ F + 512 <= 2 ^ 47)%Z.
Hypothesis SKR : (0 <= SK < 2 ^ 64)%Z.
Hypothesis VR : (0 <= v < 2 ^ 64)%Z.
Definition FI_W : list (Z * Z) := [(BUF, BUF + 255)]%Z.

(* [comment removed for export] *)
Definition fi_mem (m0 m : word -> option byte) (bsb : list byte) : Prop :=
  u8arr rsegs m BUF bsb /\ length bsb = 255%nat /\ munch FI_W m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

(* [comment removed for export] *)
Definition fiu_post (ra t0 t1 t2 t3 t4 t5 t6 : word) (FP : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0' a1' a2' a3' a4' a5' a6' a7' m' (c : Z) (bsb : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 (Z_to_bv 64 c) (Z_to_bv 64 SK) (Z_to_bv 64 (BUF + c - 1)) (Z_to_bv 64 (BUF + c - 1)) (Z_to_bv 64 F) (Z_to_bv 64 SB) (Z_to_bv 64 BUF) (Z_to_bv 64 (SK / 8 + SB)) t3 t4 t5 t6)
             FP (Z_to_bv 64 0xbb3a8) fc None m' (seg_rom rsegs)
    /\ (1 <= c <= 20)%Z /\ fi_mem m0 m' bsb.

(* [comment removed for export] *)
Lemma fiu_loop : forall (n : nat) (x i : Z) ra t0 t1 t2 a4 a5 a6 a7 s6i s11i t3 t4 t5 t6 (FP : bvmap 5 word) fc (m0 m : word -> option byte) (bsb : list byte),
  Z.to_nat (19 - i) = n -> (0 <= i <= 19)%Z -> (0 <= x < 10 ^ (20 - i))%Z -> (x < 2 ^ 64)%Z ->
  fi_mem m0 m bsb ->
  evt rsegs (fiu_post ra t0 t1 t2 t3 t4 t5 t6 FP fc m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- i)) (Z_to_bv 64 10) (Z_to_bv 64 FM1) (Z_to_bv 64 254) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 i) (Z_to_bv 64 SK) s6i (Z_to_bv 64 x) (Z_to_bv 64 F) (Z_to_bv 64 SB) (Z_to_bv 64 BUF) s11i t3 t4 t5 t6)
        FP (Z_to_bv 64 0xbb2a4) fc None m (seg_rom rsegs)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros x i ra t0 t1 t2 a4 a5 a6 a7 s6i s11i t3 t4 t5 t6 FP fc m0 m bsb Hn Hi Hx Hx64 (BB & BBL & MU & WM & MI).
  assert (P20 : (10 ^ (20 - i) <= 10 ^ 20)%Z) by (apply Z.pow_le_mono_r; lia).
  unfold FI_W in MU.
  do 6 zstep. rewrite !mulhu10 by lia.
  do 3 zstep.
  pose proof (u8arr_store_ok rsegs m BUF bsb i (Z_to_bv 64 (BUF + i)) BB ltac:(rewrite BBL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad (le1 (Z_to_bv 64 ?e))) _) =>
    replace (write_to_mem mm ad (le1 (Z_to_bv 64 e))) with (write_to_mem mm (wa (BUF + i)) [Z_to_bv 8 e]) by (f_equal; try (unfold wa; f_equal; lia); try (symmetry; apply le1_lit); try apply le1_lit);
    pose proof (u8arr_write rsegs mm BUF bsb i (Z_to_bv 8 e) BB ltac:(rewrite BBL; lia)) as BB' end.
  clear BB. store_done.
  lazymatch type of BB' with u8arr _ _ _ ?l => assert (BBL' : length l = 255%nat) by (rewrite upd_length; exact BBL) end.
  zstep. zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    assert (E : ((- i + -1) mod 18446744073709551616 = 18446744073709551616 - i - 1)%Z) by (symmetry; apply (Z.mod_unique _ _ (-1)); lia).
    assert (NOTI : (Z.lxor ((- i + -1) mod 18446744073709551616) 18446744073709551615 = i)%Z).
    { rewrite lnot_mod64 by lia. rewrite E. unfold Z.lnot. symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; rewrite E in K2; lia|].
    zstep. zstep. rewrite NOTI. zstep. if_cases K3; zify_cond K3.
    + do 4 zstep.
      replace (Z_to_bv 64 (F - (- i + -1) mod 18446744073709551616 + 31)) with (Z_to_bv 64 (BUF + (i + 1) - 1))
        by (apply Z_to_bv_eqm; rewrite E; replace (F - (18446744073709551616 - i - 1) + 31)%Z with (BUF + (i + 1) - 1 + (-1) * 18446744073709551616)%Z by lia; rewrite Z_mod_plus_full; reflexivity).
      replace (Z_to_bv 64 (i + BUF)) with (Z_to_bv 64 (BUF + (i + 1) - 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (Z.shiftr SK 3 + 2147450880)) with (Z_to_bv 64 (SK / 8 + 2147450880)) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      apply evt_done. unfold fiu_post. exs. split; [reflexivity|]. split; [lia|].
      exact (conj BB' (conj BBL' (conj MU (conj WM MI)))).
    + exfalso. lazymatch type of K3 with ?T => idtac "K3F"; idtac T end. lia.
  - (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; [|lia].
    assert (Hi1 : (i <= 18)%Z).
    { destruct (Z_le_gt_dec i 18) as [?|Hg]; [lia|]. replace (20 - i)%Z with 1%Z in Hx by lia. lia. }
    replace (Z_to_bv 64 (- i + -1)) with (Z_to_bv 64 (- (i + 1))) by (f_equal; lia).
    eapply (IH (Z.to_nat (19 - (i + 1))) ltac:(lia) (x / 10)%Z (i + 1)%Z); [lia | lia | | apply Z.div_lt_upper_bound; lia | ].
    + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      replace (20 - i)%Z with (1 + (20 - (i + 1)))%Z in Hx by lia. rewrite Z.pow_add_r in Hx by lia. lia.
    + exact (conj BB' (conj BBL' (conj MU (conj WM MI)))).
Qed.

(* [comment removed for export] *)
Lemma fiu_walk : forall ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s6i s11i t3 t4 t5 t6 (FP : bvmap 5 word) fc (m : word -> option byte) (bsb : list byte),
  u8arr rsegs m BUF bsb -> length bsb = 255%nat -> mem_inv rsegs m ->
  evt rsegs (fiu_post ra t0 t1 t2 t3 t4 t5 t6 FP fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 (Z_to_bv 64 FM1) a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 0) (Z_to_bv 64 SK) s6i (Z_to_bv 64 v) (Z_to_bv 64 F) (Z_to_bv 64 SB) (Z_to_bv 64 BUF) s11i t3 t4 t5 t6)
        FP (Z_to_bv 64 0xbb29c) fc None m (seg_rom rsegs)).
Proof.
  intros until bsb. intros BB BBL MI.
  pose proof (munch_refl FI_W m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep.
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (- 0)) at 1 by reflexivity.
  eapply (fiu_loop (Z.to_nat (19 - 0)) v 0); [reflexivity | lia | cbn -[Z.pow]; lia | lia | exact (conj BB (conj BBL (conj MU (conj WM MI))))].
Qed.
End FIU.

(* [comment removed for export] *)
Definition FM2 : Z := 0x6666666666666667.
Lemma magic10 : forall xs, (-2^63 <= xs <= -10)%Z -> ((xs * 7378697629483820647) / 2^64 / 4 + 1 = - ((- xs) / 10))%Z.
Proof.
  intros xs Hx. rewrite Z.div_div by lia.
  assert (Hd : (- xs = 10 * ((- xs) / 10) + (- xs) mod 10)%Z) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound (- xs) 10 ltac:(lia)) as Hr.
  set (k := ((- xs) / 10)%Z) in *. set (r := ((- xs) mod 10)%Z) in *.
  assert (Hk : (1 <= k)%Z) by lia.
  assert (Q : (xs * 7378697629483820647 / (2 ^ 64 * 4) = - k - 1)%Z).
  { symmetry. apply (Z.div_unique _ _ _ (xs * 7378697629483820647 + 2 ^ 66 * (k + 1))); [left; lia | lia]. }
  rewrite Q. lia.
Qed.
Lemma sgn_hi : forall w, (2 ^ 63 <= w < 2 ^ 64)%Z -> bv_signed (Z_to_bv 64 w) = (w - 2 ^ 64)%Z.
Proof.
  intros w Hw. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2)%Z with (2 ^ 63)%Z.
  rewrite (Z.mod_eq (w + 2 ^ 63) (2 ^ 64)) by lia. replace ((w + 2 ^ 63) / 2 ^ 64)%Z with 1%Z; [lia|]. apply (Z.div_unique_pos _ _ _ (w + 2 ^ 63 - 2 ^ 64)); lia.
Qed.
Lemma sgn_lo : forall w, (- 2 ^ 63 <= w < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 w) = w.
Proof.
  intros w Hw. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 64 / 2)%Z with (2 ^ 63)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma nq_val : forall w, (2 ^ 63 <= w <= 2 ^ 64 - 10)%Z ->
  Z_to_bv 64 (bv_signed (Z_to_bv 64 ((bv_signed (Z_to_bv 64 w) * bv_signed (Z_to_bv 64 FM2)) ≫ 64)) ≫ 2 +
              ((bv_signed (Z_to_bv 64 w) * bv_signed (Z_to_bv 64 FM2)) ≫ 64 mod 18446744073709551616) ≫ 63)
  = Z_to_bv 64 (2 ^ 64 - (2 ^ 64 - w) / 10).
Proof.
  intros w Hw. rewrite (sgn_hi w) by lia. unfold FM2. rewrite (sgn_lo 7378697629483820647) by lia.
  set (xs := (w - 2 ^ 64)%Z). pose proof (magic10 xs ltac:(unfold xs; lia)) as MG.
  rewrite !Z.shiftr_div_pow2 by lia.
  set (hz := (xs * 7378697629483820647 / 2 ^ 64)%Z) in *.
  assert (Hh : (-2^62 <= hz <= -1)%Z) by (unfold hz; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (sgn_lo hz) by lia.
  assert (Uh : (hz mod 18446744073709551616 = hz + 2 ^ 64)%Z).
  { change 18446744073709551616%Z with (2 ^ 64)%Z. symmetry. apply (Z.mod_unique hz (2 ^ 64) (-1) (hz + 2 ^ 64)); lia. }
  rewrite Uh.
  replace ((hz + 2 ^ 64) / 2 ^ 63)%Z with 1%Z by (apply (Z.div_unique_pos _ _ _ (hz + 2 ^ 64 - 2 ^ 63)); lia).
  change (2 ^ 2)%Z with 4%Z. apply Z_to_bv_eqm. rewrite MG. unfold xs. replace (- (w - 2 ^ 64))%Z with (2 ^ 64 - w)%Z by lia.
  replace (2 ^ 64 - (2 ^ 64 - w) / 10)%Z with (- ((2 ^ 64 - w) / 10) + 1 * 2 ^ 64)%Z by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Section FI64.
(* [comment removed for export] *)
Variables sp gp tp s0 s1 s2 s3 s4 s6 s7 s8 s11 : word.
Variables F v : Z.
Local Notation BUF := (F + 32)%Z.
Hypothesis FR : (0x6c0000 <= F /\ F + 512 <= 2 ^ 47)%Z.
Hypothesis VR : (0 <= v < 2 ^ 64)%Z.

Definition fi64_mem (m0 m : word -> option byte) (bsb : list byte) : Prop :=
  u8arr rsegs m BUF bsb /\ length bsb = 255%nat /\ munch (FI_W F) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

(* [comment removed for export] *)
Definition fi64_post (ra t1 t2 t3 t4 t5 t6 : word) (FP : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' a0' a1' a2' a3' a4' a5' a6' a7' m' (c : Z) (bsb : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 BUF) (Z_to_bv 64 c) s11 t3 t4 t5 t6)
             FP (Z_to_bv 64 0xbb98c) fc None m' (seg_rom rsegs)
    /\ (1 <= c <= 19)%Z /\ fi64_mem m0 m' bsb.

(* [comment removed for export] *)
Lemma fi64_ploop : forall (n : nat) (x i : Z) ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (FP : bvmap 5 word) fc (m0 m : word -> option byte) (bsb : list byte),
  Z.to_nat (18 - i) = n -> (0 <= i <= 18)%Z -> (0 <= x < 10 ^ (19 - i))%Z -> (x < 2 ^ 64)%Z ->
  fi64_mem m0 m bsb ->
  evt rsegs (fi64_post ra t1 t2 t3 t4 t5 t6 FP fc m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FM1) (Z_to_bv 64 10) (Z_to_bv 64 254) (Z_to_bv 64 x) a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 BUF) (Z_to_bv 64 i) s11 t3 t4 t5 t6)
        FP (Z_to_bv 64 0xbb904) fc None m (seg_rom rsegs)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros x i ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 FP fc m0 m bsb Hn Hi Hx Hx64 (BB & BBL & MU & WM & MI).
  assert (P19 : (10 ^ (19 - i) <= 10 ^ 19)%Z) by (apply Z.pow_le_mono_r; lia).
  unfold FI_W in MU.
  do 5 zstep. rewrite !mulhu10 by lia.
  do 4 zstep.
  pose proof (u8arr_store_ok rsegs m BUF bsb i (Z_to_bv 64 (BUF + i)) BB ltac:(rewrite BBL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad (le1 (Z_to_bv 64 ?e))) _) =>
    replace (write_to_mem mm ad (le1 (Z_to_bv 64 e))) with (write_to_mem mm (wa (BUF + i)) [Z_to_bv 8 e]) by (f_equal; try (unfold wa; f_equal; lia); try (symmetry; apply le1_lit); try apply le1_lit);
    pose proof (u8arr_write rsegs mm BUF bsb i (Z_to_bv 8 e) BB ltac:(rewrite BBL; lia)) as BB' end.
  clear BB. store_done.
  lazymatch type of BB' with u8arr _ _ _ ?l => assert (BBL' : length l = 255%nat) by (rewrite upd_length; exact BBL) end.
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    apply evt_done. unfold fi64_post. exs. split; [reflexivity|]. split; [lia|].
    exact (conj BB' (conj BBL' (conj MU (conj WM MI)))).
  - zstep. if_cases K2; zify_cond K2; [|lia].
    assert (Hi1 : (i <= 17)%Z).
    { destruct (Z_le_gt_dec i 17) as [?|Hg]; [lia|]. replace (19 - i)%Z with 1%Z in Hx by lia. lia. }
    eapply (IH (Z.to_nat (18 - (i + 1))) ltac:(lia) (x / 10)%Z (i + 1)%Z); [lia | lia | | apply Z.div_lt_upper_bound; lia | ].
    + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      replace (19 - i)%Z with (1 + (19 - (i + 1)))%Z in Hx by lia. rewrite Z.pow_add_r in Hx by lia. lia.
    + exact (conj BB' (conj BBL' (conj MU (conj WM MI)))).
Qed.

(* [comment removed for export] *)
Lemma fi64_nloop : forall (n : nat) (w i : Z) ra t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 (FP : bvmap 5 word) fc (m0 m : word -> option byte) (bsb : list byte),
  Z.to_nat (18 - i) = n -> (0 <= i <= 18)%Z -> (2 ^ 63 <= w < 2 ^ 64)%Z -> (2 ^ 64 - w < 10 ^ (19 - i))%Z ->
  fi64_mem m0 m bsb ->
  evt rsegs (fi64_post ra t1 t2 t3 t4 t5 t6 FP fc m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FM2) (Z_to_bv 64 10) (Z_to_bv 64 (-20)) (Z_to_bv 64 254) a4 (Z_to_bv 64 w) a6 a7
             s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 BUF) (Z_to_bv 64 i) s11 t3 t4 t5 t6)
        FP (Z_to_bv 64 0xbb950) fc None m (seg_rom rsegs)).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros w i ra t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 FP fc m0 m bsb Hn Hi Hw Hq (BB & BBL & MU & WM & MI).
  assert (P19 : (10 ^ (19 - i) <= 10 ^ 19)%Z) by (apply Z.pow_le_mono_r; lia).
  unfold FI_W in MU.
  do 12 zstep.
  pose proof (u8arr_store_ok rsegs m BUF bsb i (Z_to_bv 64 (BUF + i)) BB ltac:(rewrite BBL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad (le1 (Z_to_bv 64 ?e))) _) =>
    replace (write_to_mem mm ad (le1 (Z_to_bv 64 e))) with (write_to_mem mm (wa (BUF + i)) [Z_to_bv 8 e]) by (f_equal; try (unfold wa; f_equal; lia); try (symmetry; apply le1_lit); try apply le1_lit);
    pose proof (u8arr_write rsegs mm BUF bsb i (Z_to_bv 8 e) BB ltac:(rewrite BBL; lia)) as BB' end.
  clear BB. store_done.
  lazymatch type of BB' with u8arr _ _ _ ?l => assert (BBL' : length l = 255%nat) by (rewrite upd_length; exact BBL) end.
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    apply evt_done. unfold fi64_post. exs. split; [reflexivity|]. split; [lia|].
    exact (conj BB' (conj BBL' (conj MU (conj WM MI)))).
  - zstep. if_cases K2; zify_cond K2; [|lia].
    assert (Hw10 : (2 ^ 63 <= w <= 2 ^ 64 - 10)%Z) by lia.
    rewrite (nq_val w Hw10).
    assert (Hi1 : (i <= 17)%Z).
    { destruct (Z_le_gt_dec i 17) as [?|Hg]; [lia|]. replace (19 - i)%Z with 1%Z in Hq by lia. lia. }
    assert (D1 : (1 <= (2 ^ 64 - w) / 10)%Z) by (apply Z.div_le_lower_bound; lia).
    assert (D2 : ((2 ^ 64 - w) / 10 <= 2 ^ 63 / 10)%Z) by (apply Z.div_le_mono; lia).
    eapply (IH (Z.to_nat (18 - (i + 1))) ltac:(lia) (2 ^ 64 - (2 ^ 64 - w) / 10)%Z (i + 1)%Z); [lia | lia | lia | | ].
    + replace (2 ^ 64 - (2 ^ 64 - (2 ^ 64 - w) / 10))%Z with ((2 ^ 64 - w) / 10)%Z by lia. apply Z.div_lt_upper_bound; [lia|].
      replace (19 - i)%Z with (1 + (19 - (i + 1)))%Z in Hq by lia. rewrite Z.pow_add_r in Hq by lia. lia.
    + exact (conj BB' (conj BBL' (conj MU (conj WM MI)))).
Qed.

(* [comment removed for export] *)
Lemma fi64_pwalk : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (FP : bvmap 5 word) fc (m : word -> option byte) (bsb : list byte),
  (v < 2 ^ 63)%Z -> u8arr rsegs m BUF bsb -> length bsb = 255%nat -> mem_inv rsegs m ->
  evt rsegs (fi64_post ra t1 t2 t3 t4 t5 t6 FP fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FM1) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 BUF) (Z_to_bv 64 0) s11 t3 t4 t5 t6)
        FP (Z_to_bv 64 0xbb8f8) fc None m (seg_rom rsegs)).
Proof.
  intros until bsb. intros Hv BB BBL MI.
  pose proof (munch_refl (FI_W F) m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. zstep.
  eapply (fi64_ploop (Z.to_nat (18 - 0)) v 0); [reflexivity | lia | cbn -[Z.pow]; lia | lia | exact (conj BB (conj BBL (conj MU (conj WM MI))))].
Qed.
Lemma fi64_nwalk : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (FP : bvmap 5 word) fc (m : word -> option byte) (bsb : list byte),
  (2 ^ 63 <= v)%Z -> u8arr rsegs m BUF bsb -> length bsb = 255%nat -> mem_inv rsegs m ->
  evt rsegs (fi64_post ra t1 t2 t3 t4 t5 t6 FP fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FM2) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 BUF) (Z_to_bv 64 0) s11 t3 t4 t5 t6)
        FP (Z_to_bv 64 0xbb940) fc None m (seg_rom rsegs)).
Proof.
  intros until bsb. intros Hv BB BBL MI.
  pose proof (munch_refl (FI_W F) m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. zstep. zstep.
  eapply (fi64_nloop (Z.to_nat (18 - 0)) v 0); [reflexivity | lia | lia | cbn -[Z.pow]; lia | exact (conj BB (conj BBL (conj MU (conj WM MI))))].
Qed.
End FI64.
