(* reloc-zl14c 33f1f3569fa51f15128307ce75e76af1 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_asan.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanMemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanMemcpyAL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.AsanMemcpyMIS OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.Asan_code_memcpy.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C2.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma c2_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xc6524 : word) (MK k) rom) (mkst regs' (0xc6554 : word) (MK (k + 2)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_c5f7c D_c5f7c k.                            (* [comment removed for export] *)
      stepn F_c5f80 D_c5f80.                            (* [comment removed for export] *)
      stepb_ft F_c5f84 D_c5f84 ltac:(cond).             (* [comment removed for export] *)
      stepn F_c5f88 D_c5f88.                            (* [comment removed for export] *)
      stepb_ft F_c5f8c D_c5f8c ltac:(cond).             (* [comment removed for export] *)
      stepn F_c5f90 D_c5f90.                            (* [comment removed for export] *)
      stepn F_c5f94 D_c5f94.                            (* [comment removed for export] *)
      msb F_c5f98 D_c5f98 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      msb F_c5f9c D_c5f9c (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      stepn F_c5fa0 D_c5fa0.                            (* [comment removed for export] *)
      stepn F_c5fa4 D_c5fa4.                            (* [comment removed for export] *)
      stepn F_c5fa8 D_c5fa8.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
    (ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xc6554 : word) (MK kk) rom)
                   (mkst regs' (0xc65b4 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_c5fac D_c5fac.                          (* [comment removed for export] *)
        mlw F_c5fb0 D_c5fb0 (kk + 2)%Z.                 (* [comment removed for export] *)
        mlw F_c5fb4 D_c5fb4 (kk + 6)%Z.                 (* [comment removed for export] *)
        mlw F_c5fb8 D_c5fb8 (kk + 10)%Z.                (* [comment removed for export] *)
        mlw F_c5fbc D_c5fbc (kk + 14)%Z.                (* [comment removed for export] *)
        stepn F_c5fc0 D_c5fc0. stepn F_c5fc4 D_c5fc4. stepn F_c5fc8 D_c5fc8.   (* [comment removed for export] *)
        stepn F_c5fcc D_c5fcc. stepn F_c5fd0 D_c5fd0. stepn F_c5fd4 D_c5fd4.   (* [comment removed for export] *)
        stepn F_c5fd8 D_c5fd8. stepn F_c5fdc D_c5fdc. stepn F_c5fe0 D_c5fe0.   (* [comment removed for export] *)
        stepn F_c5fe4 D_c5fe4. stepn F_c5fe8 D_c5fe8.                          (* [comment removed for export] *)
        stepn F_c5fec D_c5fec.                          (* [comment removed for export] *)
        msw F_c5ff0 D_c5ff0 kk ltac:(m16).              (* [comment removed for export] *)
        msw F_c5ff4 D_c5ff4 (kk + 4)%Z ltac:(m16).      (* [comment removed for export] *)
        msw F_c5ff8 D_c5ff8 (kk + 8)%Z ltac:(m16).      (* [comment removed for export] *)
        msw F_c5ffc D_c5ffc (kk + 12)%Z ltac:(m16).     (* [comment removed for export] *)
        stepn F_c6000 D_c6000.                          (* [comment removed for export] *)
        stepn F_c6004 D_c6004.                          (* [comment removed for export] *)
        stepb_ft F_c6008 D_c6008 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xc6554 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + eexists. split.
        * stepn F_c5fac D_c5fac.
          mlw F_c5fb0 D_c5fb0 (kk + 2)%Z.
          mlw F_c5fb4 D_c5fb4 (kk + 6)%Z.
          mlw F_c5fb8 D_c5fb8 (kk + 10)%Z.
          mlw F_c5fbc D_c5fbc (kk + 14)%Z.
          stepn F_c5fc0 D_c5fc0. stepn F_c5fc4 D_c5fc4. stepn F_c5fc8 D_c5fc8.
          stepn F_c5fcc D_c5fcc. stepn F_c5fd0 D_c5fd0. stepn F_c5fd4 D_c5fd4.
          stepn F_c5fd8 D_c5fd8. stepn F_c5fdc D_c5fdc. stepn F_c5fe0 D_c5fe0.
          stepn F_c5fe4 D_c5fe4. stepn F_c5fe8 D_c5fe8.
          stepn F_c5fec D_c5fec.
          msw F_c5ff0 D_c5ff0 kk ltac:(m16).
          msw F_c5ff4 D_c5ff4 (kk + 4)%Z ltac:(m16).
          msw F_c5ff8 D_c5ff8 (kk + 8)%Z ltac:(m16).
          msw F_c5ffc D_c5ffc (kk + 12)%Z ltac:(m16).
          stepn F_c6000 D_c6000.
          stepn F_c6004 D_c6004.
          stepb_tk F_c6008 D_c6008 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps ASEGS (mkst regs (0xc65b4 : word) (MK kk) rom)
                   (mkst regs' (0xc6870 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0xc6510 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_c600c D_c600c.                        (* [comment removed for export] *)
          stepn F_c6010 D_c6010.                        (* [comment removed for export] *)
          stepb_tk F_c6014 D_c6014 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0xc675c : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_c600c D_c600c.
          stepn F_c6010 D_c6010.
          stepb_ft F_c6014 D_c6014 ltac:(cond).         (* [comment removed for export] *)
          stepn F_c6018 D_c6018.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0xc67e8 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c2_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps ASEGS (mkst regs (0xc6524 : word) (MK k) rom)
                   (mkst regs' (0xc6870 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
