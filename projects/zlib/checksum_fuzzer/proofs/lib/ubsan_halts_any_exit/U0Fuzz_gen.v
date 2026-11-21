(* 1.4 pilot: crc32_combine_gen64 + its inlined x2nmodp / multmodp at the 1.4 UBSan image
   (0x14c90 .. 0x14d50), re-walked from the plain draft (registers renamed, the UBSan table-bound check added)
   (DRAFT; the shipped text replaces U0Fuzz_gen.v's proofs, statements kept). *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk U0FuzzBase U0FuzzIface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import U0Fuzz_code14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition X2NTv : Z := 72020.   (* x2n_table, 0x11954 (unmoved at 1.4) *)
Definition NX2NT : Z := -72021.  (* ~x2n_table, the UBSan pointer-overflow bound *)

(* a branch condition on literals and in-range values (from the 1.3.1 U0Fuzz_gen.v) *)
Ltac zcond :=
  rwR; rewrite ?zc_ltu_mod, ?zc_eq_mod;
  repeat match goal with
    | |- context [?a mod two64] =>
        lazymatch a with
        | Zneg _ => let v := eval vm_compute in (a mod two64) in change (a mod two64) with v
        | _ => rewrite (mod_small_64 a) by lia
        end
    end;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq | reflexivity ]; lia.

(* the reflected-CRC step as the 1.4 code computes it on a zero-extended 32-bit value *)
Lemma bstep14g : forall b, Z.lxor (Z.shiftr b 1) (Z.land (if Z.odd b then ONES64 else 0) POLY) = bstep b.
Proof.
  intros b. unfold bstep. destruct (Z.odd b).
  - replace (Z.land ONES64 POLY) with POLY by reflexivity. reflexivity.
  - rewrite Z.land_0_l, Z.lxor_0_r. reflexivity.
Qed.

Lemma bstep14g_range : forall b, 0 <= b < two32 -> 0 <= bstep b < two32.
Proof.
  intros b Hb. unfold bstep.
  assert (Hs : 0 <= Z.shiftr b 1 < two32).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia|].
    apply (Z.le_lt_trans _ b); [apply Z.div_le_upper_bound; lia| lia]. }
  destruct (Z.odd b); [| exact Hs].
  apply (lxor_range _ _ 32); [lia| exact Hs| unfold POLY; change two32 with (2 ^ 32) in *; lia].
Qed.

Lemma lxor14g_range : forall p b, 0 <= p < two32 -> 0 <= b < two32 -> 0 <= Z.lxor p b < two32.
Proof.
  intros p b Hp Hb. pose proof (lxor_range p b 32 ltac:(lia) ltac:(change (2 ^ 32) with two32; lia)
                                  ltac:(change (2 ^ 32) with two32; lia)) as H.
  change (2 ^ 32) with two32 in H. exact H.
Qed.

Lemma mm_loop14g_range : forall i a b p, 0 <= b < two32 -> 0 <= p < two32 -> 0 <= mm_loop i a b p < two32.
Proof.
  induction i as [|i IH]; intros a b p Hb Hp; rewrite mm_loop_unfold; cbv zeta.
  - destruct (Z.testbit a (Z.of_nat 0)); cbn [andb]; [destruct (_ =? 0)|]; try apply lxor14g_range; lia.
  - pose proof (lxor14g_range p b Hp Hb). pose proof (bstep14g_range b Hb).
    destruct (Z.testbit a (Z.of_nat (S i))); cbn [andb]; [destruct (_ =? 0)|]; try lia; apply IH; lia.
Qed.

Section GEN.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (retw : word).
  Hypothesis Hret : ret_ok retw.
  Hypothesis Himg : img_ok m.

  Ltac solve_cs := apply (proj2 (keeps_cs_lkeeps _ _)); solve_lkeeps.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | lia | solve_cs ].
  Ltac fix_auipc := match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.

  (* the multmodp shift block: t0 >>= 1; b := bstep b *)
  Lemma gen_shift : forall regs (b mreg : Z),
    getr regs 6 = Z_to_bv 64 mreg -> getr regs 17 = Z_to_bv 64 b -> getr regs 16 = Z_to_bv 64 POLY ->
    0 <= mreg < two64 -> 0 <= b < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14d60 : word) m rom) (mkst r (0x14d78 : word) m rom)
      /\ getr r 6 = Z_to_bv 64 (Z.shiftr mreg 1)
      /\ getr r 17 = Z_to_bv 64 (Z.lxor (Z.shiftr b 1) (Z.land (if Z.odd b then ONES64 else 0) POLY))
      /\ getr r 16 = Z_to_bv 64 POLY
      /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11
      /\ getr r 12 = getr regs 12 /\ getr r 13 = getr regs 13 /\ getr r 14 = getr regs 14
      /\ getr r 5 = getr regs 5 /\ getr r 15 = getr regs 15
      /\ keeps_cs regs r.
  Proof.
    intros regs b mreg R5 R16 R15 Hm Hb.
    eexists. split.
    - stepz NF_14d00 ND_14d00. rewrite (zv_srli mreg 1 Hm).
      stepz NF_14d04 ND_14d04.
      stepz NF_14d08 ND_14d08.
      stepz NF_14d0c ND_14d0c. rewrite (zv_srli b 1 Hb).
      stepz NF_14d10 ND_14d10.
      stepz NF_14d14 ND_14d14.
      apply mst_refl.
    - post.
  Qed.

  (* the inlined multmodp loop from its test (0x14d18) to the x2nmodp latch (0x14cc8) *)
  Lemma gen_mm : forall (i : nat) regs (x b p mreg : Z),
    getr regs 5 = Z_to_bv 64 x -> getr regs 6 = Z_to_bv 64 mreg -> getr regs 17 = Z_to_bv 64 b ->
    getr regs 11 = Z_to_bv 64 p -> getr regs 16 = Z_to_bv 64 POLY ->
    (i <= 31)%nat -> 0 <= x < two32 -> x mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < two32 -> 0 <= p < two32 -> mreg = 2 ^ Z.of_nat i ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14d78 : word) m rom) (mkst r (0x14d28 : word) m rom)
      /\ getr r 11 = Z_to_bv 64 (mm_loop i x b p)
      /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 12 = getr regs 12
      /\ getr r 13 = getr regs 13 /\ getr r 14 = getr regs 14 /\ getr r 16 = Z_to_bv 64 POLY
      /\ getr r 15 = getr regs 15
      /\ keeps_cs regs r.
  Proof.
    induction i as [|i IH]; intros regs x b p mreg R17 R5 R16 R11 R15 Hi Hx Hxnz Hb Hp Hmi.
    - (* bit 0: the last one *)
      change (Z.of_nat 0 + 1) with 1 in Hxnz. change (2 ^ Z.of_nat 0) with 1 in Hmi. subst mreg.
      assert (Ht : Z.testbit x 0 = true).
      { rewrite Z.bit0_odd. change (2 ^ 1) with 2 in Hxnz. rewrite Zmod_odd in Hxnz.
        destruct (Z.odd x); [reflexivity | exfalso; apply Hxnz; reflexivity]. }
      assert (E1 : Z.land 1 x = 1).
      { pose proof (land_pow2_l x 0 ltac:(lia)) as E. rewrite Ht in E. exact E. }
      pose proof (lxor14g_range p b Hp Hb) as Hpb.
      eexists. split; [|split].
      + stepz NF_14d18 ND_14d18.
        stepb_ft NF_14d1c ND_14d1c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; reflexivity).
        stepz NF_14d20 ND_14d20.
        stepz NF_14d24 ND_14d24.
        stepz NF_14d28 ND_14d28.
        stepb_ft NF_14d2c ND_14d2c ltac:(rewrite ?getr_zero; rewrite Z.land_0_l; rewrite zc_eq by lia; reflexivity).
        stepz NF_14d30 ND_14d30.
        apply mst_refl.
      + gres. rewrite (mm_loop_exit 0 x b p Ht) by (change (2 ^ Z.of_nat 0) with 1; apply Z.mod_1_r).
        reflexivity.
      + post.
    - (* bit j = i + 1 *)
      set (j := S i) in *.
      assert (Hj : Z.of_nat j = Z.of_nat i + 1) by (subst j; lia).
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)) as Hp2.
      assert (Hp2' : 2 ^ Z.of_nat j = 2 * 2 ^ Z.of_nat i) by (rewrite Hj, Z.pow_add_r by lia; lia).
      assert (Hp31 : 2 ^ Z.of_nat j <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 31) with 2147483648 in Hp31.
      pose proof (Z.mod_pos_bound x (2 ^ Z.of_nat j) ltac:(lia)) as Hr3.
      pose proof (mod_pow2_succ x (Z.of_nat j) ltac:(lia)) as Hsplit.
      assert (Hm' : Z.shiftr mreg 1 = 2 ^ Z.of_nat i).
      { rewrite Hmi, Hp2', Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
        rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
      assert (Hmr : 0 <= mreg < two64) by lia.
      assert (E2 : Z.land (mreg - 1) x = x mod 2 ^ Z.of_nat j).
      { rewrite Hmi. apply land_ones_l; lia. }
      pose proof (bstep14g_range b Hb) as Hb'.
      destruct (Z.testbit x (Z.of_nat j)) eqn:Ht.
      + (* bit j set: p ^= b *)
        assert (E1 : Z.land mreg x = mreg)
          by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        pose proof (lxor14g_range p b Hp Hb) as Hpb.
        destruct (Z.eq_dec (x mod 2 ^ Z.of_nat j) 0) as [Hz|Hnz].
        * (* no lower bit left: exit *)
          rewrite Hz in E2.
          eexists. split; [|split].
          -- stepz NF_14d18 ND_14d18.
             stepb_ft NF_14d1c ND_14d1c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
             stepz NF_14d20 ND_14d20.
             stepz NF_14d24 ND_14d24.
             stepz NF_14d28 ND_14d28.
             stepb_ft NF_14d2c ND_14d2c ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; reflexivity).
             stepz NF_14d30 ND_14d30.
             apply mst_refl.
          -- gres. rewrite (mm_loop_exit j x b p Ht Hz). reflexivity.
          -- post.
        * (* a lower bit left: shift, go on *)
          eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14d60 : word) m rom)
                   (fun r => getr r 5 = Z_to_bv 64 x /\ getr r 6 = Z_to_bv 64 mreg
                             /\ getr r 17 = Z_to_bv 64 b /\ getr r 11 = Z_to_bv 64 (Z.lxor p b)
                             /\ getr r 16 = Z_to_bv 64 POLY
                             /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 12 = getr regs 12
                             /\ getr r 13 = getr regs 13 /\ getr r 14 = getr regs 14 /\ getr r 15 = getr regs 15
                             /\ keeps_cs regs r)).
          { eexists. split.
            - stepz NF_14d18 ND_14d18.
              stepb_ft NF_14d1c ND_14d1c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
              stepz NF_14d20 ND_14d20.
              stepz NF_14d24 ND_14d24.
              stepz NF_14d28 ND_14d28.
              stepb_tk NF_14d2c ND_14d2c ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
              apply mst_refl.
            - post. }
          cbv beta. intros r1 (S17 & S5 & S16 & S11 & S15 & S1 & S10 & S12 & S13 & S14 & S15x & K1).
          destruct (gen_shift r1 b mreg S5 S16 S15 Hmr ltac:(lia))
            as (r2 & M2 & T5 & T16 & T15 & T1 & T10 & T11 & T12 & T13 & T14 & T17 & T15x & K2).
          rewrite S1 in T1. rewrite S10 in T10. rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13.
          rewrite S14 in T14. rewrite S17 in T17. rewrite S15x in T15x. rewrite Hm' in T5. rewrite bstep14g in T16.
          destruct (IH r2 x (bstep b) (Z.lxor p b) (2 ^ Z.of_nat i) T17 T5 T16 T11 T15
                      ltac:(lia) Hx ltac:(rewrite <- Hj; exact Hnz) Hb' Hpb eq_refl)
            as (r3 & M3 & V3 & U1 & U10 & U12 & U13 & U14 & U15 & U15x & K3).
          exists r3. split; [|split].
          -- eapply msteps_trans; [exact M2 | exact M3].
          -- rewrite V3. subst j. rewrite (mm_loop_go i x) by assumption. reflexivity.
          -- rewrite U1, U10, U12, U13, U14, U15x, T1, T10, T12, T13, T14, T15x.
             repeat split; first [reflexivity | exact U15 |
               (eapply keeps_cs_trans; [exact K1|]; eapply keeps_cs_trans; [exact K2| exact K3])].
      + (* bit j clear: shift, go on *)
        assert (E1 : Z.land mreg x = 0)
          by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        assert (Hnz : x mod 2 ^ Z.of_nat j <> 0) by (rewrite Hsplit in Hxnz; lia).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14d60 : word) m rom)
                 (fun r => getr r 5 = Z_to_bv 64 x /\ getr r 6 = Z_to_bv 64 mreg
                           /\ getr r 17 = Z_to_bv 64 b /\ getr r 11 = Z_to_bv 64 p
                           /\ getr r 16 = Z_to_bv 64 POLY
                           /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 12 = getr regs 12
                           /\ getr r 13 = getr regs 13 /\ getr r 14 = getr regs 14 /\ getr r 15 = getr regs 15
                             /\ keeps_cs regs r)).
        { eexists. split.
          - stepz NF_14d18 ND_14d18.
            stepb_tk NF_14d1c ND_14d1c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; reflexivity).
            apply mst_refl.
          - post. }
        cbv beta. intros r1 (S17 & S5 & S16 & S11 & S15 & S1 & S10 & S12 & S13 & S14 & S15x & K1).
        destruct (gen_shift r1 b mreg S5 S16 S15 Hmr ltac:(lia))
          as (r2 & M2 & T5 & T16 & T15 & T1 & T10 & T11 & T12 & T13 & T14 & T17 & T15x & K2).
        rewrite S1 in T1. rewrite S10 in T10. rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13.
        rewrite S14 in T14. rewrite S17 in T17. rewrite S15x in T15x. rewrite Hm' in T5. rewrite bstep14g in T16.
        destruct (IH r2 x (bstep b) p (2 ^ Z.of_nat i) T17 T5 T16 T11 T15
                    ltac:(lia) Hx ltac:(rewrite <- Hj; exact Hnz) Hb' Hp eq_refl)
          as (r3 & M3 & V3 & U1 & U10 & U12 & U13 & U14 & U15 & U15x & K3).
        exists r3. split; [|split].
        -- eapply msteps_trans; [exact M2 | exact M3].
        -- rewrite V3. subst j. rewrite (mm_loop_skip i x) by assumption. reflexivity.
        -- rewrite U1, U10, U12, U13, U14, U15x, T1, T10, T12, T13, T14, T15x.
           repeat split; first [reflexivity | exact U15 |
             (eapply keeps_cs_trans; [exact K1|]; eapply keeps_cs_trans; [exact K2| exact K3])].
  Qed.

  (* one x2nmodp iteration from its odd test (0x14cd8) to the latch (0x14cc8); b = p on entry *)
  Lemma gen_body : forall regs (n k p : Z),
    getr regs 10 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 k -> getr regs 17 = Z_to_bv 64 p ->
    getr regs 13 = Z_to_bv 64 2147483648 -> getr regs 14 = Z_to_bv 64 X2NTv -> getr regs 16 = Z_to_bv 64 POLY ->
    getr regs 15 = Z_to_bv 64 NX2NT ->
    0 <= n < two64 -> 0 <= k < two64 -> 0 <= p < two32 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14d38 : word) m rom) (mkst r (0x14d28 : word) m rom)
      /\ getr r 11 = Z_to_bv 64 (if Z.odd n then multmodp (x2n (k mod 32)) p else p)
      /\ getr r 1 = getr regs 1 /\ getr r 10 = Z_to_bv 64 n /\ getr r 12 = Z_to_bv 64 k
      /\ getr r 13 = Z_to_bv 64 2147483648 /\ getr r 14 = Z_to_bv 64 X2NTv /\ getr r 16 = Z_to_bv 64 POLY
      /\ getr r 15 = Z_to_bv 64 NX2NT
      /\ keeps_cs regs r.
  Proof.
    intros regs n k p R10 R12 R16 R13 R14 R15 R15x Hn Hk Hp.
    pose proof (land_1_odd n) as Ho.
    destruct (Z.odd n) eqn:Hodd.
    - (* odd: p := multmodp (x2n_table[k & 31], p) *)
      pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hk32.
      pose proof (x2n_range (k mod 32) Hk32) as Hxr.
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14d78 : word) m rom)
               (fun r => getr r 5 = Z_to_bv 64 (x2n (k mod 32)) /\ getr r 6 = Z_to_bv 64 2147483648
                         /\ getr r 17 = Z_to_bv 64 p /\ getr r 11 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 POLY
                         /\ getr r 1 = getr regs 1 /\ getr r 10 = Z_to_bv 64 n /\ getr r 12 = Z_to_bv 64 k
                         /\ getr r 13 = Z_to_bv 64 2147483648 /\ getr r 14 = Z_to_bv 64 X2NTv
                         /\ getr r 15 = Z_to_bv 64 NX2NT
                         /\ keeps_cs regs r)).
      { eexists. split.
        - stepz NF_14cd8 ND_14cd8.
          stepb_ft NF_14cdc ND_14cdc ltac:(rewrite Ho; rewrite zc_eq by lia; reflexivity).
          stepz NF_14ce0 ND_14ce0.
          match goal with |- context [Z_to_bv 64 (Z.land k 31)] => rewrite (land_31_mod k) end.
          stepz NF_14ce4 ND_14ce4.
          stepb_ft NF_14ce8 ND_14ce8 ltac:(rwR; unfold NX2NT; zcond).   (* the UBSan table-bound check *)
          stepz NF_14cec ND_14cec.
          stepz NF_14cf0 ND_14cf0.
          chain_step;
          [ reflexivity
          | eapply step_lwu with (v := Z_to_bv 64 (x2n (k mod 32)));
            [ exact NF_14cf4 | reflexivity | exact ND_14cf4
            | gres; imm_norm; rewrite zv_addi;
              replace (X2NTv + k mod 32 * 2 ^ 2 + 0) with (X2NT + 4 * (k mod 32)) by (unfold X2NTv, X2NT; lia);
              apply rd_x2n; [exact Himg | lia]
            | apply x2n_bs_v; lia ]
          | step_simpl; gres ].
          stepz NF_14cf8 ND_14cf8. stepz NF_14cfc ND_14cfc.
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S17 & S5 & S16 & S11 & S15 & S1 & S10 & S12 & S13 & S14 & S15x & K1).
      destruct (gen_mm 31 r1 (x2n (k mod 32)) p 0 2147483648 S17 S5 S16 S11 S15 ltac:(lia) Hxr
                  ltac:(change (2 ^ (Z.of_nat 31 + 1)) with two32; apply x2n_nz; lia) Hp ltac:(lia)
                  ltac:(reflexivity))
        as (r2 & M2 & V2 & U1 & U10 & U12 & U13 & U14 & U15 & U15x & K2).
      exists r2. split; [exact M2|]. split.
      + rewrite V2. cbv iota. unfold multmodp. reflexivity.
      + rewrite U1, U10, U12, U13, U14, U15x, S1, S10, S12, S13, S14, S15x.
        repeat split; try reflexivity; try assumption.
        eapply keeps_cs_trans; [exact K1 | exact K2].
    - (* even: p unchanged *)
      eexists. split; [|split].
      + stepz NF_14cd8 ND_14cd8.
        stepb_tk NF_14cdc ND_14cdc ltac:(rewrite Ho; rewrite zc_eq by lia; reflexivity).
        stepz NF_14cc4 ND_14cc4.
        apply mst_refl.
      + post.
      + post.
  Qed.

  (* the x2nmodp latch (0x14cc8): n >>= 1; k++; b := p; exit on n = 0 *)
  Lemma gen_latch : forall (f : nat) regs (n k p : Z),
    getr regs 1 = retw ->
    getr regs 10 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 k -> getr regs 11 = Z_to_bv 64 p ->
    getr regs 13 = Z_to_bv 64 2147483648 -> getr regs 14 = Z_to_bv 64 X2NTv -> getr regs 16 = Z_to_bv 64 POLY ->
    getr regs 15 = Z_to_bv 64 NX2NT ->
    0 <= n < two64 -> n < 2 ^ (Z.of_nat f + 1) -> (0 <= k /\ k + Z.of_nat f <= 99) -> 0 <= p < two32 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14d28 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (x2n_loop f (Z.shiftr n 1) (k + 1) p)
      /\ keeps_cs regs r.
  Proof.
    induction f as [|f IH]; intros regs n k p R1 R10 R12 R11 R13 R14 R15 R15x Hn64 Hn Hk Hp.
    - (* fuel 0: n < 2, so n >> 1 = 0 *)
      change (2 ^ (Z.of_nat 0 + 1)) with 2 in Hn.
      assert (Hs : Z.shiftr n 1 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
      eexists. split; [|split].
      + stepz NF_14cc8 ND_14cc8. rewrite (zv_srli n 1 Hn64), Hs.
        stepz NF_14ccc ND_14ccc.
        stepz NF_14cd0 ND_14cd0.
        stepb_tk NF_14cd4 ND_14cd4 ltac:(reflexivity).
        stepz NF_14d34 ND_14d34.
        stepret NF_14d38 ND_14d38 retw ltac:(rwR; reflexivity).
        apply mst_refl.
      + gres. rewrite Hs, x2n_loop_done. rwR. reflexivity.
      + solve_cs.
    - set (g := S f) in *. assert (Hg : Z.of_nat g = Z.of_nat f + 1) by (subst g; lia).
      rewrite Hg in Hn. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat f + 1) ltac:(lia) ltac:(lia)) as Hpf.
      assert (Hpf' : 2 ^ (Z.of_nat f + 1 + 1) = 2 * 2 ^ (Z.of_nat f + 1))
        by (rewrite (Z.pow_add_r 2 (Z.of_nat f + 1) 1) by lia; lia).
      set (n' := Z.shiftr n 1).
      assert (Hn' : 0 <= n' < 2 ^ (Z.of_nat f + 1)).
      { subst n'. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
        split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      pose proof (shiftr_le n 1 ltac:(lia) ltac:(lia)) as Hn'le. fold n' in Hn'le.
      destruct (Z.eq_dec n' 0) as [Hz|Hnz].
      + eexists. split; [|split].
        * stepz NF_14cc8 ND_14cc8. rewrite (zv_srli n 1 Hn64). fold n'. rewrite Hz.
          stepz NF_14ccc ND_14ccc.
          stepz NF_14cd0 ND_14cd0.
          stepb_tk NF_14cd4 ND_14cd4 ltac:(reflexivity).
          stepz NF_14d34 ND_14d34.
          stepret NF_14d38 ND_14d38 retw ltac:(rwR; reflexivity).
          apply mst_refl.
        * gres. rewrite Hz, x2n_loop_done. rwR. reflexivity.
        * solve_cs.
      + eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14d38 : word) m rom)
                 (fun r => getr r 1 = retw /\ getr r 10 = Z_to_bv 64 n' /\ getr r 12 = Z_to_bv 64 (k + 1)
                           /\ getr r 17 = Z_to_bv 64 p /\ getr r 13 = Z_to_bv 64 2147483648
                           /\ getr r 14 = Z_to_bv 64 X2NTv /\ getr r 16 = Z_to_bv 64 POLY
                           /\ getr r 15 = Z_to_bv 64 NX2NT
                           /\ keeps_cs regs r)).
        { eexists. split.
          - stepz NF_14cc8 ND_14cc8. rewrite (zv_srli n 1 Hn64). fold n'.
            stepz NF_14ccc ND_14ccc.
            stepz NF_14cd0 ND_14cd0.
            stepb_ft NF_14cd4 ND_14cd4 ltac:(rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
            apply mst_refl.
          - post. }
        cbv beta. intros r1 (S1 & S10 & S12 & S16 & S13 & S14 & S15 & S15x & K1).
        destruct (gen_body r1 n' (k + 1) p S10 S12 S16 S13 S14 S15 S15x ltac:(lia) ltac:(lia) Hp)
          as (r2 & M2 & V2 & U1 & U10 & U12 & U13 & U14 & U15 & U15x & K2).
        rewrite S1 in U1.
        set (p2 := if Z.odd n' then multmodp (x2n ((k + 1) mod 32)) p else p) in V2.
        assert (Hp2 : 0 <= p2 < two32).
        { subst p2. unfold multmodp. destruct (Z.odd n'); [apply mm_loop14g_range; lia | exact Hp]. }
        destruct (IH r2 n' (k + 1) p2 U1 U10 U12 V2 U13 U14 U15 U15x ltac:(lia) ltac:(lia) ltac:(lia) Hp2)
          as (r3 & M3 & V3 & K3).
        exists r3. split; [|split].
        * eapply msteps_trans; [exact M2 | exact M3].
        * rewrite V3. subst g p2. rewrite (x2n_loop_step f n') by exact Hnz. reflexivity.
        * eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2 | exact K3].
  Qed.

  (* crc32_combine_gen64 (0x14c90), at a length that is not negative *)
  Theorem gen_run : forall regs (n : Z),
    getr regs 1 = retw -> getr regs 10 = Z_to_bv 64 n ->
    0 <= n < 9223372036854775808 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14cf0 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (x2nmodp n 3)
      /\ keeps_cs regs r.
  Proof.
    intros regs n R1 R10 Hn.
    destruct (Z.eq_dec n 0) as [-> | Hnz].
    - eexists. split; [|split].
      + stepb_ft NF_14c90 ND_14c90 ltac:(rewrite R10; apply zc_lts_0_false; lia).
        stepz NF_14c94 ND_14c94.
        stepb_tk NF_14c98 ND_14c98 ltac:(rewrite R10; reflexivity).
        stepz NF_14d44 ND_14d44.
        stepret NF_14d48 ND_14d48 retw ltac:(rwR; reflexivity).
        apply mst_refl.
      + gres. rwR. unfold x2nmodp. rewrite x2n_loop_done. reflexivity.
      + solve_cs.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14d38 : word) m rom)
               (fun r => getr r 1 = retw /\ getr r 10 = Z_to_bv 64 n /\ getr r 12 = Z_to_bv 64 3
                         /\ getr r 17 = Z_to_bv 64 2147483648 /\ getr r 13 = Z_to_bv 64 2147483648
                         /\ getr r 14 = Z_to_bv 64 X2NTv /\ getr r 16 = Z_to_bv 64 POLY
                         /\ getr r 15 = Z_to_bv 64 NX2NT
                         /\ keeps_cs regs r)).
      { eexists. split.
        - stepb_ft NF_14c90 ND_14c90 ltac:(rewrite R10; apply zc_lts_0_false; lia).
          stepz NF_14c94 ND_14c94.
          stepb_ft NF_14c98 ND_14c98 ltac:(rewrite R10; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
          stepz NF_14c9c ND_14c9c. stepz NF_14ca0 ND_14ca0. stepz NF_14ca4 ND_14ca4. try fix_auipc. stepz NF_14ca8 ND_14ca8.
          stepz NF_14cac ND_14cac. stepz NF_14cb0 ND_14cb0. stepz NF_14cb4 ND_14cb4. stepz NF_14cb8 ND_14cb8.
          stepz NF_14cbc ND_14cbc.
          stepz NF_14cc0 ND_14cc0.
          apply mst_refl.
        - unfold X2NTv, NX2NT, POLY. post. }
      cbv beta. intros r1 (S1 & S10 & S12 & S16 & S13 & S14 & S15 & S15x & K1).
      destruct (gen_body r1 n 3 X0 S10 S12 S16 S13 S14 S15 S15x ltac:(lia) ltac:(lia) ltac:(unfold X0; lia))
        as (r2 & M2 & V2 & U1 & U10 & U12 & U13 & U14 & U15 & U15x & K2).
      rewrite S1 in U1.
      set (p2 := if Z.odd n then multmodp (x2n (3 mod 32)) X0 else X0) in V2.
      assert (Hp2 : 0 <= p2 < two32).
      { subst p2. unfold multmodp, X0. destruct (Z.odd n); [apply mm_loop14g_range; lia | lia]. }
      destruct (gen_latch 63 r2 n 3 p2 U1 U10 U12 V2 U13 U14 U15 U15x ltac:(lia)
                  ltac:(change (2 ^ (Z.of_nat 63 + 1)) with two64; lia) ltac:(lia) Hp2) as (r3 & M3 & V3 & K3).
      exists r3. split; [|split].
      + eapply msteps_trans; [exact M2 | exact M3].
      + rewrite V3. unfold x2nmodp. change 64%nat with (S 63).
        rewrite (x2n_loop_step 63 n 3) by exact Hnz. subst p2. reflexivity.
      + eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2 | exact K3].
  Qed.
End GEN.

Theorem u0_crc32_combine_gen {RCa1 : RunCtx}  : U0_crc32_combine_gen_stmt.
Proof.
  intros regs m rom retw len2 R1 Hret R10 Hn Himg.
  (* 1.4: crc32_combine_gen is x2nmodp at a length that is not negative *)
  unfold crc32_combine_gen, crc32_combine_gen64. rewrite (proj2 (Z.ltb_ge len2 0)) by lia.
  exact (gen_run m rom retw Hret Himg regs len2 R1 R10 Hn).
Qed.
