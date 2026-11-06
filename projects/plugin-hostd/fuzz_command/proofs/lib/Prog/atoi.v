From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import CType CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import atoi_c.
Import ListNotations.
Open Scope Z_scope.

Lemma acc_step : forall (str : list byte) j b n, nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
  atoi_acc n (skipn j str) =
    if c_digit b then atoi_acc (bv_swrap 32 (10 * n - (bv_unsigned b - 48))) (skipn (S j) str) else n.
Proof.
  intros str j b n H HJ. destruct (txt_cases str j b H HJ) as [(L & E) | (L & -> & E)]; rewrite E; reflexivity.
Qed.

Lemma val_space : forall (str : list byte) j b, nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
  c_space b = true -> atoi_val (skipn j str) = atoi_val (skipn (S j) str).
Proof.
  intros str j b H HJ SP. destruct (txt_cases str j b H HJ) as [(L & E) | (L & -> & E)].
  - rewrite E. unfold atoi_val. cbn [skip_space]. rewrite SP. reflexivity.
  - exfalso. vm_compute in SP. discriminate.
Qed.

Lemma val_nonspace : forall (str : list byte) j b, nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
  c_space b = false ->
  atoi_val (skipn j str) =
    if bv_unsigned b =? 45 then atoi_acc 0 (skipn (S j) str)
    else if bv_unsigned b =? 43 then bv_swrap 32 (- atoi_acc 0 (skipn (S j) str))
    else bv_swrap 32 (- atoi_acc 0 (skipn j str)).
Proof.
  intros str j b H HJ SP. destruct (txt_cases str j b H HJ) as [(L & E) | (L & -> & E)].
  - rewrite E. unfold atoi_val. cbn [skip_space]. rewrite SP. reflexivity.
  - rewrite E. reflexivity.
Qed.

Definition fin (pos : bool) (v : Z) : Z := if pos then bv_swrap 32 (- v) else v.

Ltac fixw t := match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_eqm x t) by (Z.div_mod_to_equations; lia) end.
Ltac fixA t := match goal with |- context [Z_to_bv 64 ?e] => replace e with t by lia end.

Section Atoi.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (str : list byte).
  Hypothesis BY : bytes_at rsegs m A (str ++ [Z_to_bv 8 0]).
  Hypothesis MI : mem_inv rsegs m.
  Notation POST := (atoi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str m).
  Notation ST pc x10 x11 x12 x13 x14 x15 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  #[using="BY"] Lemma bnd : 0 <= A /\ A + Z.of_nat (length str) + 1 <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ BY) as H. rewrite length_app in H. cbn [length] in H. lia. Qed.

  #[using="BY"] Lemma rd : forall k b, nth_error (str ++ [Z_to_bv 8 0]) k = Some b ->
    ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 1 = Some [b].
  Proof. intros k b H. eapply (u8ro_read rsegs m A); [exact BY | rewrite Nat2Z.id; exact H | lia | reflexivity]. Qed.

  #[using="MI"] Lemma done : forall v (x11 x12 x13 x14 x15 : word), v = atoi_val str ->
    evt rsegs POST (ST 0x1fb50 (Z_to_bv 64 v) x11 x12 x13 x14 x15).
  Proof.
    intros v x11 x12 x13 x14 x15 ->.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. finish.
  Qed.

  #[using="BY MI"] Lemma digits : forall k j n d (pos : bool) (x15 : word),
    (length str - j < k)%nat -> (j <= length str)%nat -> 0 <= d <= 9 -> -2^31 <= n < 2^31 ->
    fin pos (atoi_acc (bv_swrap 32 (10 * n - d)) (skipn j str)) = atoi_val str ->
    evt rsegs POST (ST 0x1fb30 (Z_to_bv 64 n) (Z_to_bv 64 (A + Z.of_nat j)) (Z_to_bv 64 (if pos then 1 else 0))
                       (Z_to_bv 64 d) (Z_to_bv 64 10) x15).
  Proof.
    pose proof bnd as BD.
    induction k as [|k IH]; intros j n d pos x15 HK HJ Hd Hn HV; [lia|].
    destruct (nth_txt str j HJ) as [b Hb].
    pose proof (rd j b Hb) as RD. pose proof (byte_rng b) as Rb.
    rewrite (acc_step str j b _ Hb HJ) in HV.
    zstep. zstep. zstep. fixw (10 * n - d). zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - rewrite (digit_t b ltac:(Z.div_mod_to_equations; lia)) in HV.
      assert (NZ : bv_unsigned b <> 0) by (Z.div_mod_to_equations; lia).
      pose proof (txt_nz_lt str j b Hb HJ NZ) as LT.
     
      replace (A + Z.of_nat j + 1) with (A + Z.of_nat (S j)) by lia.
      replace (bv_unsigned b + -48) with (bv_unsigned b - 48) by lia.
      pose proof (swrap32_range (10 * n - d)). apply IH; try lia.
    - rewrite (digit_f b ltac:(Z.div_mod_to_equations; lia)) in HV.
      destruct pos; cbv beta iota; cbn [fin] in HV.
      + zstep. if_false. zstep. fixw (- bv_swrap 32 (10 * n - d)).
        eapply done. rewrite <- HV. reflexivity.
      + zstep. if_true. eapply done. rewrite <- HV. reflexivity.
  Qed.

  #[using="BY MI"] Lemma num : forall j (pos : bool) b (x13 x14 x15 : word),
    nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
    fin pos (atoi_acc 0 (skipn j str)) = atoi_val str ->
    evt rsegs POST (ST 0x1fb18 (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (A + Z.of_nat j)) (Z_to_bv 64 (if pos then 1 else 0))
                       x13 x14 x15).
  Proof.
    intros j pos b x13 x14 x15 Hb HJ HV. pose proof bnd as BD. pose proof (byte_rng b) as Rb.
    rewrite (acc_step str j b 0 Hb HJ) in HV.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - rewrite (digit_f b ltac:(Z.div_mod_to_equations; lia)) in HV.
      destruct pos; cbv beta iota; cbn [fin] in HV.
      + zstep. zstep. if_true. zstep. eapply done. rewrite <- HV. reflexivity.
      + zstep. zstep. if_false. zstep. eapply done. rewrite <- HV. reflexivity.
    - rewrite (digit_t b ltac:(Z.div_mod_to_equations; lia)) in HV.
      assert (NZ : bv_unsigned b <> 0) by (Z.div_mod_to_equations; lia).
      pose proof (txt_nz_lt str j b Hb HJ NZ) as LT.
      zstep. zstep. zstep.
      replace (A + Z.of_nat j + 1) with (A + Z.of_nat (S j)) by lia.
      replace (bv_unsigned b + -48) with (bv_unsigned b - 48) by lia.
      eapply (digits (S (length str - S j)) (S j) 0 (bv_unsigned b - 48) pos); try lia.
  Qed.

  #[using="BY MI"] Lemma ws : forall k j (x10 x14 x15 : word),
    (length str - j < k)%nat -> (j <= length str)%nat ->
    atoi_val (skipn j str) = atoi_val str ->
    evt rsegs POST (ST 0x1fadc x10 (Z_to_bv 64 (A + Z.of_nat j + 1)) (Z_to_bv 64 5) (Z_to_bv 64 32) x14 x15).
  Proof.
    pose proof bnd as BD.
    induction k as [|k IH]; intros j x10 x14 x15 HK HJ HV; [lia|].
    destruct (nth_txt str j HJ) as [b Hb].
    pose proof (rd j b Hb) as RD. pose proof (byte_rng b) as Rb.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - rewrite (val_space str j b Hb HJ (space_t b ltac:(Z.div_mod_to_equations; lia))) in HV.
      assert (NZ : bv_unsigned b <> 0) by (Z.div_mod_to_equations; lia).
      pose proof (txt_nz_lt str j b Hb HJ NZ) as LT.
      zstep.
      fixA (A + Z.of_nat (S j) + 1).
      apply IH; [lia | lia | exact HV].
    - zstep. if_cases K2; zify_cond K2.
      + rewrite (val_space str j b Hb HJ (space_t b ltac:(lia))) in HV.
        assert (NZ : bv_unsigned b <> 0) by lia.
        pose proof (txt_nz_lt str j b Hb HJ NZ) as LT.
        zstep.
        fixA (A + Z.of_nat (S j) + 1).
        apply IH; [lia | lia | exact HV].
      + rewrite (val_nonspace str j b Hb HJ (space_f b ltac:(lia) ltac:(Z.div_mod_to_equations; lia))) in HV.
        zstep. zstep. if_cases K3; zify_cond K3.
        * rewrite (proj2 (Z.eqb_neq _ 45)) in HV by lia. rewrite (proj2 (Z.eqb_eq _ 43)) in HV by lia.
          pose proof (txt_nz_lt str j b Hb HJ ltac:(lia)) as LT.
          destruct (nth_txt str (S j) ltac:(lia)) as [b2 Hb2].
          pose proof (rd (S j) b2 Hb2) as RD2.
          replace (A + Z.of_nat j + 1) with (A + Z.of_nat (S j)) by lia.
          zstep. zstep. zstep.
          eapply (num (S j) true b2); [exact Hb2 | lia | exact HV].
        * zstep. zstep. if_cases K4; zify_cond K4.
          -- rewrite (proj2 (Z.eqb_neq _ 45)) in HV by lia. rewrite (proj2 (Z.eqb_neq _ 43)) in HV by lia.
             zstep. zstep.
             fixA (A + Z.of_nat j).
             eapply (num j true b); [exact Hb | lia | exact HV].
          -- rewrite (proj2 (Z.eqb_eq _ 45)) in HV by lia.
             pose proof (txt_nz_lt str j b Hb HJ ltac:(lia)) as LT.
             destruct (nth_txt str (S j) ltac:(lia)) as [b2 Hb2].
             pose proof (rd (S j) b2 Hb2) as RD2.
             replace (A + Z.of_nat j + 1) with (A + Z.of_nat (S j)) by lia.
             zstep. zstep. zstep.
             eapply (num (S j) false b2); [exact Hb2 | lia | exact HV].
  Qed.
End Atoi.

Theorem atoi_holds : atoi_contract.
Proof.
  unfold atoi_contract, ATOI.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A str BY MI.
  pose proof (bytes_at_bound _ _ _ _ BY) as BD. rewrite length_app in BD. cbn [length] in BD.
  zstep. zstep. zstep. zstep.
  replace (A + 1) with (A + Z.of_nat 0 + 1) by lia.
  eapply (ws ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A str BY MI
            (S (length str)) 0); [lia | lia | reflexivity].
Qed.
