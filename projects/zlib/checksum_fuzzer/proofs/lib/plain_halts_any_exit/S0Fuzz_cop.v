(* 1.4 pilot: crc32_combine_op at the 1.4 plain image (0x14c44 .. 0x14cb8), re-walked; cop_run keeps its 1.3.1 statement. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk S0FuzzBase S0FuzzIface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import S0Fuzz_code14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section COP.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (retw : word).
  Hypothesis Hret : ret_ok retw.

  Ltac solve_cs := apply (proj2 (keeps_cs_lkeeps _ _)); solve_lkeeps.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | solve_cs ].

  (* the shift block: m >>= 1; b := bstep b *)
  Lemma cop_shift : forall regs (b mreg : Z),
    getr regs 14 = Z_to_bv 64 mreg -> getr regs 15 = Z_to_bv 64 b -> getr regs 16 = Z_to_bv 64 POLY ->
    0 <= mreg < two64 -> 0 <= b < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14cd4 : word) m rom) (mkst r (0x14cec : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (Z.shiftr mreg 1)
      /\ getr r 15 = Z_to_bv 64 (Z.lxor (Z.shiftr b 1) (Z.land (if Z.odd b then ONES64 else 0) POLY))
      /\ getr r 16 = Z_to_bv 64 POLY
      /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11
      /\ getr r 12 = getr regs 12 /\ getr r 13 = getr regs 13
      /\ keeps_cs regs r.
  Proof.
    intros regs b mreg R14 R15 R16 Hm Hb.
    eexists. split.
    - stepz NF_14c74 ND_14c74. rewrite (zv_srli mreg 1 Hm).
      stepz NF_14c78 ND_14c78.
      stepz NF_14c7c ND_14c7c.
      stepz NF_14c80 ND_14c80. rewrite (zv_srli b 1 Hb).
      stepz NF_14c84 ND_14c84.
      stepz NF_14c88 ND_14c88.
      apply mst_refl.
    - post.
  Qed.

  Lemma bstep14 : forall b, Z.lxor (Z.shiftr b 1) (Z.land (if Z.odd b then ONES64 else 0) POLY) = bstep b.
  Proof.
    intros b. unfold bstep. destruct (Z.odd b).
    - replace (Z.land ONES64 POLY) with POLY by reflexivity. reflexivity.
    - rewrite Z.land_0_l, Z.lxor_0_r. reflexivity.
  Qed.

  Lemma bstep14_range : forall b, 0 <= b < two32 -> 0 <= bstep b < two32.
  Proof.
    intros b Hb. unfold bstep.
    assert (Hs : 0 <= Z.shiftr b 1 < two32).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia|].
      apply (Z.le_lt_trans _ b); [apply Z.div_le_upper_bound; lia| lia]. }
    destruct (Z.odd b); [| exact Hs].
    apply (lxor_range _ _ 32); [lia| exact Hs| unfold POLY; change two32 with (2 ^ 32) in *; lia].
  Qed.

  Lemma cop_loop : forall (i : nat) regs (a b p c2 mreg : Z),
    getr regs 1 = retw ->
    getr regs 12 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 mreg -> getr regs 16 = Z_to_bv 64 POLY ->
    getr regs 15 = Z_to_bv 64 b -> getr regs 13 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 c2 ->
    getr regs 10 = Z_to_bv 64 M32 ->
    (i <= 31)%nat -> 0 <= a < two64 -> a mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < two32 -> 0 <= p < two32 -> 0 <= c2 < two64 -> mreg = 2 ^ Z.of_nat i ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14cec : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lxor (mm_loop i a b p) (c2 mod two32))
      /\ keeps_cs regs r.
  Proof.
    induction i as [|i IH]; intros regs a b p c2 mreg R1 R12 R14 R16 R15 R13 R11 R10 Hi Ha Hanz Hb Hp Hc2 Hmi.
    - (* bit 0: the last one *)
      change (Z.of_nat 0 + 1) with 1 in Hanz. change (2 ^ Z.of_nat 0) with 1 in Hmi. subst mreg.
      assert (Ht : Z.testbit a 0 = true).
      { rewrite Z.bit0_odd. change (2 ^ 1) with 2 in Hanz. rewrite Zmod_odd in Hanz.
        destruct (Z.odd a); [reflexivity | exfalso; apply Hanz; reflexivity]. }
      assert (E1 : Z.land 1 a = 1).
      { pose proof (and_m_low 1 a 0 ltac:(lia) ltac:(reflexivity)) as E1. rewrite Ht in E1.
        rewrite Z.mod_small in E1; [exact E1|]. rewrite Z.land_comm.
        pose proof (land_range a 1 ltac:(lia)). change two32 with 4294967296. lia. }
      assert (E2 : Z.land 0 a = 0) by apply Z.land_0_l.
      pose proof (lxor_range p b 32 ltac:(lia) ltac:(change (2 ^ 32) with two32; lia)
                   ltac:(change (2 ^ 32) with two32; lia)) as Hpb.
      eexists. split; [|split].
      + stepz NF_14c8c ND_14c8c.
        stepb_ft NF_14c90 ND_14c90 ltac:(rewrite ?getr_zero; rewrite zc_eq by lia; rewrite E1; reflexivity).
        stepz NF_14c94 ND_14c94.
        stepz NF_14c98 ND_14c98.
        stepz NF_14c9c ND_14c9c.
        stepb_ft NF_14ca0 ND_14ca0 ltac:(rewrite ?getr_zero; rewrite zc_eq by lia; rewrite E2; reflexivity).
        stepz NF_14ca4 ND_14ca4.
        stepz NF_14ca8 ND_14ca8.
        stepret NF_14cac ND_14cac retw ltac:(rwR; reflexivity).
        apply mst_refl.
      + gres. rewrite (mm_loop_exit 0 a b p Ht) by (change (2 ^ Z.of_nat 0) with 1; apply Z.mod_1_r).
        rewrite land_M32. reflexivity.
      + solve_cs.
    - (* bit j = i + 1 *)
      set (j := S i) in *.
      assert (Hj : Z.of_nat j = Z.of_nat i + 1) by (subst j; lia).
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)) as Hp2.
      assert (Hp2' : 2 ^ Z.of_nat j = 2 * 2 ^ Z.of_nat i) by (rewrite Hj, Z.pow_add_r by lia; lia).
      assert (Hp31 : 2 ^ Z.of_nat j <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 31) with 2147483648 in Hp31.
      pose proof (Z.mod_pos_bound a (2 ^ Z.of_nat j) ltac:(lia)) as Hr3.
      pose proof (mod_pow2_succ a (Z.of_nat j) ltac:(lia)) as Hsplit.
      assert (Hm' : Z.shiftr mreg 1 = 2 ^ Z.of_nat i).
      { rewrite Hmi, Hp2', Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
        rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
      assert (Hmr : 0 <= mreg < two64) by lia.
      assert (E2 : Z.land (mreg - 1) a = a mod 2 ^ Z.of_nat j) by (rewrite Hmi; apply land_ones_l; lia).
      pose proof (bstep14_range b Hb) as Hb'.
      destruct (Z.testbit a (Z.of_nat j)) eqn:Ht.
      + (* bit j set: p ^= b *)
        assert (E1 : Z.land mreg a = mreg) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        pose proof (lxor_range p b 32 ltac:(lia) ltac:(change (2 ^ 32) with two32; lia)
                     ltac:(change (2 ^ 32) with two32; lia)) as Hpb.
        change (2 ^ 32) with two32 in Hpb.
        destruct (Z.eq_dec (a mod 2 ^ Z.of_nat j) 0) as [Hz|Hnz].
        * (* no lower bit left: exit *)
          rewrite Hz in E2.
          eexists. split; [|split].
          -- stepz NF_14c8c ND_14c8c.
             stepb_ft NF_14c90 ND_14c90 ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
             stepz NF_14c94 ND_14c94.
             stepz NF_14c98 ND_14c98.
             stepz NF_14c9c ND_14c9c.
             stepb_ft NF_14ca0 ND_14ca0 ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; reflexivity).
             stepz NF_14ca4 ND_14ca4.
             stepz NF_14ca8 ND_14ca8.
             stepret NF_14cac ND_14cac retw ltac:(rwR; reflexivity).
             apply mst_refl.
          -- gres. rewrite (mm_loop_exit j a b p Ht Hz). rewrite land_M32. reflexivity.
          -- solve_cs.
        * (* a lower bit left: shift, go on *)
          eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14cd4 : word) m rom)
                   (fun r => getr r 1 = retw /\ getr r 12 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 mreg
                             /\ getr r 16 = Z_to_bv 64 POLY /\ getr r 15 = Z_to_bv 64 b
                             /\ getr r 13 = Z_to_bv 64 (Z.lxor p b) /\ getr r 11 = Z_to_bv 64 c2
                             /\ getr r 10 = Z_to_bv 64 M32 /\ keeps_cs regs r)).
          { eexists. split.
            - stepz NF_14c8c ND_14c8c.
              stepb_ft NF_14c90 ND_14c90 ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
              stepz NF_14c94 ND_14c94.
              stepz NF_14c98 ND_14c98.
              stepz NF_14c9c ND_14c9c.
              stepb_tk NF_14ca0 ND_14ca0 ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
              apply mst_refl.
            - post. }
          cbv beta. intros r1 (S1 & S12 & S14 & S16 & S15 & S13 & S11 & S10 & K1).
          destruct (cop_shift r1 b mreg S14 S15 S16 Hmr ltac:(lia))
            as (r2 & M2 & T14 & T15 & T16 & T1 & T10 & T11 & T12 & T13 & K2).
          rewrite S1 in T1. rewrite S10 in T10. rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13.
          rewrite Hm' in T14. rewrite bstep14 in T15.
          destruct (IH r2 a (bstep b) (Z.lxor p b) c2 (2 ^ Z.of_nat i) T1 T12 T14 T16 T15 T13 T11 T10
                      ltac:(lia) Ha ltac:(rewrite <- Hj; exact Hnz) Hb' Hpb Hc2 eq_refl) as (r3 & M3 & V3 & K3).
          exists r3. split; [|split].
          -- eapply msteps_trans; [exact M2 | exact M3].
          -- rewrite V3. subst j. rewrite (mm_loop_go i a) by assumption. reflexivity.
          -- eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2| exact K3].
      + (* bit j clear: shift, go on *)
        assert (E1 : Z.land mreg a = 0) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        assert (Hnz : a mod 2 ^ Z.of_nat j <> 0) by (rewrite Hsplit in Hanz; lia).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14cd4 : word) m rom)
                 (fun r => getr r 1 = retw /\ getr r 12 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 mreg
                           /\ getr r 16 = Z_to_bv 64 POLY /\ getr r 15 = Z_to_bv 64 b
                           /\ getr r 13 = Z_to_bv 64 p /\ getr r 11 = Z_to_bv 64 c2
                           /\ getr r 10 = Z_to_bv 64 M32 /\ keeps_cs regs r)).
        { eexists. split.
          - stepz NF_14c8c ND_14c8c.
            stepb_tk NF_14c90 ND_14c90 ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; reflexivity).
            apply mst_refl.
          - post. }
        cbv beta. intros r1 (S1 & S12 & S14 & S16 & S15 & S13 & S11 & S10 & K1).
        destruct (cop_shift r1 b mreg S14 S15 S16 Hmr ltac:(lia))
          as (r2 & M2 & T14 & T15 & T16 & T1 & T10 & T11 & T12 & T13 & K2).
        rewrite S1 in T1. rewrite S10 in T10. rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13.
        rewrite Hm' in T14. rewrite bstep14 in T15.
        destruct (IH r2 a (bstep b) p c2 (2 ^ Z.of_nat i) T1 T12 T14 T16 T15 T13 T11 T10
                    ltac:(lia) Ha ltac:(rewrite <- Hj; exact Hnz) Hb' Hp Hc2 eq_refl) as (r3 & M3 & V3 & K3).
        exists r3. split; [|split].
        -- eapply msteps_trans; [exact M2 | exact M3].
        -- rewrite V3. subst j. rewrite (mm_loop_skip i a) by assumption. reflexivity.
        -- eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2| exact K3].
  Qed.

  (* the 1.3.1 statement, at the 1.4 model *)
  Theorem cop_run : forall regs (crc1 crc2 op : Z),
    getr regs 1 = retw ->
    getr regs 10 = Z_to_bv 64 crc1 -> getr regs 11 = Z_to_bv 64 crc2 -> getr regs 12 = Z_to_bv 64 op ->
    0 <= crc1 < two32 -> 0 <= crc2 < two64 -> 0 <= op < two64 -> op mod two32 <> 0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ca4 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (crc32_combine_op crc1 crc2 op)
      /\ keeps_cs regs r.
  Proof.
    intros regs crc1 crc2 op R1 R10 R11 R12 Hc1 Hc2 Hop Hopnz.
    assert (Hop0 : op <> 0) by (intro E; subst op; apply Hopnz; reflexivity).
    eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14cec : word) m rom)
             (fun r => getr r 1 = retw /\ getr r 12 = Z_to_bv 64 op /\ getr r 14 = Z_to_bv 64 2147483648
                       /\ getr r 16 = Z_to_bv 64 POLY /\ getr r 15 = Z_to_bv 64 (crc1 mod two32)
                       /\ getr r 13 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 crc2
                       /\ getr r 10 = Z_to_bv 64 M32 /\ keeps_cs regs r)).
    { eexists. split.
      - stepb_ft NF_14c44 ND_14c44 ltac:(rewrite R12; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hop0).
        stepz NF_14c48 ND_14c48. stepz NF_14c4c ND_14c4c. stepz NF_14c50 ND_14c50. stepz NF_14c54 ND_14c54.
        stepz NF_14c58 ND_14c58. stepz NF_14c5c ND_14c5c. stepz NF_14c60 ND_14c60. stepz NF_14c64 ND_14c64.
        stepz NF_14c68 ND_14c68. stepz NF_14c6c ND_14c6c. stepz NF_14c70 ND_14c70.
        apply mst_refl.
      - unfold POLY, M32. post. }
    cbv beta. intros r1 (S1 & S12 & S14 & S16 & S15 & S13 & S11 & S10 & K1).
    destruct (cop_loop 31 r1 op (crc1 mod two32) 0 crc2 2147483648 S1 S12 S14 S16 S15 S13 S11 S10
                ltac:(lia) Hop ltac:(change (2 ^ (Z.of_nat 31 + 1)) with two32; exact Hopnz)
                ltac:(apply Z.mod_pos_bound; lia) ltac:(lia) Hc2 ltac:(reflexivity)) as (r2 & M2 & V2 & K2).
    exists r2. split; [exact M2 | split].
    - rewrite V2. unfold crc32_combine_op, multmodp. rewrite (proj2 (Z.eqb_neq op 0) Hop0), !land_M32. reflexivity.
    - eapply keeps_cs_trans; [exact K1 | exact K2].
  Qed.
End COP.
