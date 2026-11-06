From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import tolower_c tolower strncasecmp_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.TacDiet2.diet_word_eq_tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require StepFast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Step.zstep ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.TacDiet2.diet_word_eq_tac ].
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require AndN.
Import ListNotations.
Open Scope Z_scope.

Lemma zlower_zero : forall x, 0 <= x < 256 -> (zlower x = 0 <-> x = 0).
Proof. intros x Hx. unfold zlower. destruct (65 <=? x) eqn:E1; destruct (x <=? 90) eqn:E2; cbn; lia. Qed.

Lemma zlower_range : forall x, 0 <= x < 256 -> 0 <= zlower x < 256.
Proof. intros x Hx. unfold zlower. destruct (65 <=? x) eqn:E1; destruct (x <=? 90) eqn:E2; cbn;
  rewrite ?Z.leb_le, ?Z.leb_gt in *; lia. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. Qed.

Lemma u_byte : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

Lemma u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. exact u_byte. Qed.

Lemma land255 : forall b : byte, Z.land (bv_unsigned b) 255 = bv_unsigned b.
Proof.
  intros b. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (byte_range b). change (2 ^ 8) with 256. lia.
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Lemma list_ext_nth : forall {A} (l l' : list A), (forall n, nth_error l n = nth_error l' n) -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. inversion H0; subst. f_equal. apply IH. intros n. exact (H (S n)).
Qed.

Lemma nth_full : forall (s : list byte) i, (i <= length s)%nat -> exists b, nth_error (s ++ [Z_to_bv 8 0]) i = Some b.
Proof.
  intros s i H. destruct (nth_error (s ++ [Z_to_bv 8 0]) i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma nth_full_zero : forall (s : list byte) i b, ~ In (Z_to_bv 8 0) s ->
  nth_error (s ++ [Z_to_bv 8 0]) i = Some b -> (bv_unsigned b = 0 <-> i = length s).
Proof.
  intros s i b NZ E. pose proof (nth_error_lt _ _ _ E) as Hl. rewrite length_app in Hl. cbn in Hl.
  destruct (Nat.eq_dec i (length s)) as [->|NE].
  - rewrite nth_error_app2, Nat.sub_diag in E by lia. cbn in E. inversion E; subst. split; reflexivity.
  - rewrite nth_error_app1 in E by lia. split; [|intros; lia]. intros Hb. exfalso. apply NZ.
    replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma map_u_app0 : forall (s : list byte), map bv_unsigned (s ++ [Z_to_bv 8 0]) = map bv_unsigned s ++ [0].
Proof. intros s. rewrite map_app. reflexivity. Qed.

Lemma nth_case : forall (s : list byte) N j,
  nth_error (map zlower (firstn N (map bv_unsigned s ++ [0]))) j =
  if (j <? N)%nat then option_map (fun b => zlower (bv_unsigned b)) (nth_error (s ++ [Z_to_bv 8 0]) j) else None.
Proof.
  intros s N j. rewrite nth_error_map, nth_error_firstn, <- map_u_app0.
  destruct (j <? N)%nat; [|reflexivity]. rewrite nth_error_map. destruct (nth_error _ j); reflexivity.
Qed.

Lemma ncase_stop : forall (ls rs : list byte) (n : Z) (k : nat) (b1 b2 : byte),
  ~ In (Z_to_bv 8 0) ls -> ~ In (Z_to_bv 8 0) rs -> (k < Z.to_nat n)%nat ->
  nth_error (ls ++ [Z_to_bv 8 0]) k = Some b1 -> nth_error (rs ++ [Z_to_bv 8 0]) k = Some b2 ->
  (forall j, (j < k)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                  zlower (bv_unsigned x) = zlower (bv_unsigned y)) ->
  (bv_unsigned b1 = 0 \/ bv_unsigned b2 = 0 \/ k = (Z.to_nat n - 1)%nat \/
   zlower (bv_unsigned b1) <> zlower (bv_unsigned b2)) ->
  (zlower (bv_unsigned b1) = zlower (bv_unsigned b2) <-> ncase_eq ls rs n).
Proof.
  intros ls rs n k b1 b2 NL NR Kn E1 E2 P D. unfold ncase_eq.
  pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
  split.
  - intros Heq. apply list_ext_nth. intros j. rewrite !nth_case.
    destruct (j <? Z.to_nat n)%nat eqn:Jn; [|reflexivity]. apply Nat.ltb_lt in Jn.
    destruct (Nat.lt_trichotomy j k) as [Jk|[->|Jk]].
    + destruct (P j Jk) as (x & y & Ex & Ey & Exy).
      rewrite nth_error_app1 by (eapply nth_error_lt; eauto). rewrite (nth_error_app1 rs) by (eapply nth_error_lt; eauto).
      rewrite Ex, Ey. cbn. rewrite Exy. reflexivity.
    + rewrite E1, E2. cbn. rewrite Heq. reflexivity.
    + destruct D as [Z1|[Z2|[Kl|Dif]]].
      * assert (Z2 : bv_unsigned b2 = 0).
        { apply zlower_zero; [exact R2|]. rewrite <- Heq. apply zlower_zero; [exact R1| exact Z1]. }
        apply (nth_full_zero ls k b1 NL E1) in Z1. apply (nth_full_zero rs k b2 NR E2) in Z2.
        rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_app; cbn; lia). reflexivity.
      * assert (Z1 : bv_unsigned b1 = 0).
        { apply zlower_zero; [exact R1|]. rewrite Heq. apply zlower_zero; [exact R2| exact Z2]. }
        apply (nth_full_zero ls k b1 NL E1) in Z1. apply (nth_full_zero rs k b2 NR E2) in Z2.
        rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_app; cbn; lia). reflexivity.
      * lia.
      * contradiction.
  - intros Heq. apply (f_equal (fun l => nth_error l k)) in Heq. rewrite !nth_case in Heq.
    replace (k <? Z.to_nat n)%nat with true in Heq by (symmetry; apply Nat.ltb_lt; exact Kn).
    rewrite E1, E2 in Heq. cbn in Heq. inversion Heq. reflexivity.
Qed.

Lemma sub_lower_zero : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  (Z_to_bv 64 (bv_swrap 32 (zlower x - zlower y)) = Z_to_bv 64 0 <-> zlower x = zlower y).
Proof.
  intros x y Hx Hy. pose proof (zlower_range x Hx) as Lx. pose proof (zlower_range y Hy) as Ly.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  split; intros Heq.
  - apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_wrap in Heq. rewrite Z.mod_0_l in Heq by lia.
    Z.div_mod_to_equations. nia.
  - rewrite Heq, Z.sub_diag. reflexivity.
Qed.

Theorem strncasecmp_holds : strncasecmp_contract.
Proof.
  unfold strncasecmp_contract, STRNCASECMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs lo
         ST HL NL HR NR MI LO SL SR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ HL) as BL. pose proof (bytes_at_bound _ _ _ _ HR) as BR.
  rewrite length_app in BL, BR. cbn [length] in BL, BR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bv_unsigned_in_range 64 a2) as A2R. unfold bv_modulus in A2R. cbn in A2R.
  zstep. if_cases K0; zify_cond K0.
  - zstep. zstep. apply evt_done. unfold strncasecmp_post.
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact HL|]. split; [exact HR|].
    unfold ncase_eq. rewrite K0. cbn. split; reflexivity.
  - pose proof tolower_holds as TL. unfold tolower_contract, TOLOWER in TL.
    assert (N1 : (1 <= Z.to_nat (bv_unsigned a2))%nat) by lia.
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
    assert (FIN : forall (k : nat) (b1 b2 : byte) (x1 x8 x9 x11 x12 x18 x19 : word),
      (k < Z.to_nat (bv_unsigned a2))%nat ->
      nth_error (ls ++ [Z_to_bv 8 0]) k = Some b1 -> nth_error (rs ++ [Z_to_bv 8 0]) k = Some b2 ->
      (forall j, (j < k)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                      zlower (bv_unsigned x) = zlower (bv_unsigned y)) ->
      (bv_unsigned b1 = 0 \/ bv_unsigned b2 = 0 \/ k = (Z.to_nat (bv_unsigned a2) - 1)%nat \/
       zlower (bv_unsigned b1) <> zlower (bv_unsigned b2)) ->
      bv_unsigned x8 = bv_unsigned a1 + Z.of_nat k ->
      evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs lo m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (bv_unsigned b1))
                 x11 x12 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1c55c) fc None M1 (seg_rom rsegs))).
    { intros k b1 b2 x1 x8 x9 x11 x12 x18 x19 Kn E1 E2 P D H8.
      pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
      pose proof (nth_error_lt _ _ _ E2) as Lk2. rewrite length_app in Lk2. cbn [length] in Lk2.
      assert (RD2 : ov_read_bytes rsegs M1 x8 1 = Some [b2]).
      { apply (u8ro_read rsegs M1 (bv_unsigned a1) (rs ++ [Z_to_bv 8 0]) (Z.of_nat k) b2 x8 HR);
          [rewrite Nat2Z.id; exact E2 | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
      zstep.
      eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R1. }
      intros ms' [y11 ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
      zstep. zstep. zstep. zstep.
      eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R2. }
      intros ms' [y11' ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
      zstep.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      pose proof (zlower_range _ R1) as ZR1. pose proof (zlower_range _ R2) as ZR2.
      rewrite (Z.mod_small (zlower (bv_unsigned b1)) 18446744073709551616) by lia.
      rewrite (Z.mod_small (zlower (bv_unsigned b2)) 18446744073709551616) by lia.
      apply evt_done. unfold strncasecmp_post.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact HL|].
      split; [exact HR|].
      rewrite (sub_lower_zero _ _ R1 R2).
      exact (ncase_stop ls rs (bv_unsigned a2) k b1 b2 NL NR Kn E1 E2 P D). }
    assert (LOOP : forall (k i : nat) (b1 : byte) (x1 x8 x9 x10 x12 x18 x19 : word),
      (length ls - i = k)%nat -> (i < length ls)%nat -> (i < Z.to_nat (bv_unsigned a2))%nat ->
      nth_error ls i = Some b1 ->
      (forall j, (j < i)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                      zlower (bv_unsigned x) = zlower (bv_unsigned y)) ->
      bv_unsigned x8 = bv_unsigned a1 + Z.of_nat i ->
      bv_unsigned x18 = bv_unsigned a0 + Z.of_nat i + 1 ->
      bv_unsigned x19 = bv_unsigned a2 - 1 - Z.of_nat i ->
      evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs lo m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 x9 x10 (Z_to_bv 64 (bv_unsigned b1))
                 x12 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1c514) fc None M1 (seg_rom rsegs))).
    { induction k as [k IH] using lt_wf_ind.
      intros i b1 x1 x8 x9 x10 x12 x18 x19 Hk Hil HiN E1 P H8 H18 H19.
      pose proof (byte_range b1) as R1.
      assert (NZ1 : bv_unsigned b1 <> 0).
      { intros Zb. apply NL. replace (Z_to_bv 8 0) with b1; [eapply nth_error_In; eauto|].
        apply bv_eq. rewrite Zb. reflexivity. }
      assert (E1f : nth_error (ls ++ [Z_to_bv 8 0]) i = Some b1) by (rewrite nth_error_app1 by lia; exact E1).
      assert (Iy : (i <= length rs)%nat).
      { destruct i as [|i']; [lia|]. destruct (P i' ltac:(lia)) as (x & y & _ & Ey & _).
        apply nth_error_lt in Ey. lia. }
      destruct (nth_full rs i Iy) as [b2 E2]. pose proof (byte_range b2) as R2.
      pose proof (zlower_range _ R1) as ZR1. pose proof (zlower_range _ R2) as ZR2.
      assert (RD2 : ov_read_bytes rsegs M1 x8 1 = Some [b2]).
      { apply (u8ro_read rsegs M1 (bv_unsigned a1) (rs ++ [Z_to_bv 8 0]) (Z.of_nat i) b2 x8 HR);
          [rewrite Nat2Z.id; exact E2 | lia | unfold wa; rewrite <- H8; symmetry; apply Z_to_bv_lit_self]. }
      assert (NEXT : zlower (bv_unsigned b1) = zlower (bv_unsigned b2) ->
                     (i + 1 < Z.to_nat (bv_unsigned a2))%nat -> bv_unsigned b2 <> 0 ->
          forall (y1 y9 y10 y11 y12 : word),
          evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs lo m)
            (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 y9 y10 y11
                     y12 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1c500) fc None M1 (seg_rom rsegs))).
      { intros Heq HiN' NZ2 y1 y9 y10 y11 y12.
        assert (Iy' : (S i <= length rs)%nat).
        { destruct (Nat.eq_dec i (length rs)) as [Ei|]; [|lia]. exfalso. apply NZ2.
          apply (nth_full_zero rs i b2 NR E2). exact Ei. }
        destruct (nth_full ls (S i) ltac:(lia)) as [b1' E1']. destruct (nth_full rs (S i) Iy') as [b2' E2'].
        pose proof (byte_range b1') as R1'.
        assert (P' : forall j, (j < S i)%nat -> exists x y, nth_error ls j = Some x /\ nth_error rs j = Some y /\
                                      zlower (bv_unsigned x) = zlower (bv_unsigned y)).
        { intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [|apply P; lia].
          exists b1, b2. split; [exact E1|]. split; [|exact Heq].
          rewrite nth_error_app1 in E2; [exact E2|]. destruct (Nat.eq_dec i (length rs)) as [Ei|]; [|lia].
          exfalso. apply NZ2. apply (nth_full_zero rs i b2 NR E2). exact Ei. }
        assert (RD1 : ov_read_bytes rsegs M1 x18 1 = Some [b1']).
        { apply (u8ro_read rsegs M1 (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) (Z.of_nat (S i)) b1' x18 HL);
            [rewrite Nat2Z.id; exact E1' | lia | unfold wa; rewrite <- (Z_to_bv_lit_self x18); f_equal; lia]. }
        zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?u_zxb, ?u_byte in K; cbv iota.
        - zstep. zstep. rewrite ?u_zxb, ?u_byte, ?land255.
          eapply FIN with (k := S i); [lia | exact E1' | exact E2' | exact P' | left; exact K | ].
          rewrite unsigned_lit by lia. lia.
        - assert (Il : (S i < length ls)%nat).
          { destruct (Nat.eq_dec (S i) (length ls)) as [Ei|]; [|lia]. exfalso. apply K.
            apply (nth_full_zero ls (S i) b1' NL E1'). exact Ei. }
          rewrite nth_error_app1 in E1' by lia.
          eapply (IH (length ls - S i)%nat); [lia | reflexivity | exact Il | lia | exact E1' | exact P' | | | ];
            rewrite unsigned_lit by lia; lia. }
      step. step. if_cases K1; zify_cond K1; rewrite ?u_zxb, ?u_byte in K1; cbv iota.
      - zstep. zstep. rewrite ?u_zxb, ?u_byte, ?land255.
        eapply FIN with (k := i); [lia | exact E1f | exact E2 | exact P | right; left; exact K1 | exact H8].
      - zstep. zstep. if_cases K2; zify_cond K2; cbv iota.
        + zstep. zstep. rewrite ?u_zxb, ?u_byte, ?land255.
          eapply FIN with (k := i); [lia | exact E1f | exact E2 | exact P | right; right; left; lia | exact H8].
        + zstep. if_cases K3; zify_cond K3; rewrite ?u_zxb, ?u_byte in K3; cbv iota.
          * apply NEXT; [rewrite K3; reflexivity | lia | lia].
          * zstep. rewrite ?u_zxb, ?u_byte, ?land255.
            zstep.
            eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R1. }
            intros ms' [y11 ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
            zstep. zstep. zstep. zstep.
            eapply evt_cut. { eapply TL. rewrite ?u_zxb, ?u_byte. exact R2. }
            intros ms' [y11' ->]. fix_ret. rewrite ?u_zxb, ?u_byte.
            zstep. if_cases K4; zify_cond K4; rewrite ?Z.mod_small in K4 by lia; cbv iota.
            -- apply NEXT; [exact K4 | lia | lia].
            -- assert (RD1b : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned x18 + -1)) 1 = Some [b1]).
               { apply (u8ro_read rsegs M1 (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) (Z.of_nat i) b1 _ HL);
                   [rewrite Nat2Z.id; exact E1f | lia | unfold wa; f_equal; lia]. }
               zstep. zstep. zstep. rewrite ?u_zxb, ?u_byte, ?land255.
               eapply FIN with (k := i); [lia | exact E1f | exact E2 | exact P | right; right; right; exact K4 | exact H8]. }
    destruct (nth_full ls 0 ltac:(lia)) as [b10 E10]. pose proof (byte_range b10) as R10.
    assert (RD0 : ov_read_bytes rsegs M1 a0 1 = Some [b10]).
    { apply (u8ro_read rsegs M1 (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) 0 b10 a0 HL);
        [exact E10 | lia | unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self]. }
    zstep. zstep. if_cases K; zify_cond K; rewrite ?u_zxb, ?u_byte in K; cbv iota.
    + zstep.
      destruct (nth_full rs 0 ltac:(lia)) as [b20 E20].
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (bv_unsigned b10)) by (rewrite K; reflexivity).
      eapply FIN with (k := 0%nat); [lia | exact E10 | exact E20 | intros j Hj; lia | left; exact K | lia].
    + zstep. zstep. zstep.
      assert (Il : (0 < length ls)%nat).
      { destruct (Nat.eq_dec 0 (length ls)) as [Ei|]; [|lia]. exfalso. apply K.
        apply (nth_full_zero ls 0 b10 NL E10). exact Ei. }
      rewrite nth_error_app1 in E10 by lia.
      eapply (LOOP (length ls - 0)%nat 0%nat); [reflexivity | exact Il | lia | exact E10 | intros j Hj; lia | | | ];
        rewrite ?unsigned_lit by lia; lia.
Qed.
