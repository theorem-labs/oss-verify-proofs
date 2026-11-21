(* reloc-zl14c 2213feb842b6300c334bb5292ad8f3e7 *)
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

Section C1.
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
  Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c1_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xc6524 : word) (MK k) rom) (mkst regs' (0xc66f0 : word) (MK (k + 3)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_c5f7c D_c5f7c k.                            (* [comment removed for export] *)
      stepn F_c5f80 D_c5f80.                            (* [comment removed for export] *)
      stepb_ft F_c5f84 D_c5f84 ltac:(cond).             (* [comment removed for export] *)
      stepn F_c5f88 D_c5f88.                            (* [comment removed for export] *)
      stepb_tk F_c5f8c D_c5f8c ltac:(cond).             (* [comment removed for export] *)
      stepn F_c6124 D_c6124.                            (* [comment removed for export] *)
      stepn F_c6128 D_c6128.                            (* [comment removed for export] *)
      stepn F_c612c D_c612c.                            (* [comment removed for export] *)
      msb F_c6130 D_c6130 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
      msb F_c6134 D_c6134 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
      msb F_c6138 D_c6138 (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      stepn F_c613c D_c613c.                            (* [comment removed for export] *)
      stepn F_c6140 D_c6140.                            (* [comment removed for export] *)
      stepn F_c6144 D_c6144.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0xc66f0 : word) (MK kk) rom)
                   (mkst regs' (0xc6750 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_c6148 D_c6148.                          (* [comment removed for export] *)
        mlw F_c614c D_c614c (kk + 1)%Z.                 (* [comment removed for export] *)
        mlw F_c6150 D_c6150 (kk + 5)%Z.                 (* [comment removed for export] *)
        mlw F_c6154 D_c6154 (kk + 9)%Z.                 (* [comment removed for export] *)
        mlw F_c6158 D_c6158 (kk + 13)%Z.                (* [comment removed for export] *)
        stepn F_c615c D_c615c. stepn F_c6160 D_c6160. stepn F_c6164 D_c6164.
        stepn F_c6168 D_c6168. stepn F_c616c D_c616c. stepn F_c6170 D_c6170.
        stepn F_c6174 D_c6174. stepn F_c6178 D_c6178. stepn F_c617c D_c617c.
        stepn F_c6180 D_c6180. stepn F_c6184 D_c6184.
        stepn F_c6188 D_c6188.                          (* [comment removed for export] *)
        msw F_c618c D_c618c kk ltac:(m24).
        msw F_c6190 D_c6190 (kk + 4)%Z ltac:(m24).
        msw F_c6194 D_c6194 (kk + 8)%Z ltac:(m24).
        msw F_c6198 D_c6198 (kk + 12)%Z ltac:(m24).
        stepn F_c619c D_c619c.                          (* [comment removed for export] *)
        stepn F_c61a0 D_c61a0.                          (* [comment removed for export] *)
        stepb_ft F_c61a4 D_c61a4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xc66f0 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
                         /\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
      + eexists. split.
        * stepn F_c6148 D_c6148.
          mlw F_c614c D_c614c (kk + 1)%Z.
          mlw F_c6150 D_c6150 (kk + 5)%Z.
          mlw F_c6154 D_c6154 (kk + 9)%Z.
          mlw F_c6158 D_c6158 (kk + 13)%Z.
          stepn F_c615c D_c615c. stepn F_c6160 D_c6160. stepn F_c6164 D_c6164.
          stepn F_c6168 D_c6168. stepn F_c616c D_c616c. stepn F_c6170 D_c6170.
          stepn F_c6174 D_c6174. stepn F_c6178 D_c6178. stepn F_c617c D_c617c.
          stepn F_c6180 D_c6180. stepn F_c6184 D_c6184.
          stepn F_c6188 D_c6188.
          msw F_c618c D_c618c kk ltac:(m24).
          msw F_c6190 D_c6190 (kk + 4)%Z ltac:(m24).
          msw F_c6194 D_c6194 (kk + 8)%Z ltac:(m24).
          msw F_c6198 D_c6198 (kk + 12)%Z ltac:(m24).
          stepn F_c619c D_c619c.
          stepn F_c61a0 D_c61a0.
          stepb_tk F_c61a4 D_c61a4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps ASEGS (mkst regs (0xc6750 : word) (MK kk) rom)
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
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xc6510 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_c61a8 D_c61a8.                        (* [comment removed for export] *)
          stepn F_c61ac D_c61ac.                        (* [comment removed for export] *)
          stepb_tk F_c61b0 D_c61b0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0xc675c : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_c61a8 D_c61a8.
          stepn F_c61ac D_c61ac.
          stepb_ft F_c61b0 D_c61b0 ltac:(cond).         (* [comment removed for export] *)
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
  Lemma c1_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
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
    assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
