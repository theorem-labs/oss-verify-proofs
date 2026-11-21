(* 1.4 pilot: crc32_combine at the 1.4 UBSan image (0x14dc4 .. 0x14ecc; crc32_combine64 with
   crc32_combine_gen64, x2nmodp, multmodp and crc32_combine_op all inlined), re-walked (DRAFT; the shipped
   text replaces S0Fuzz_comb.v's proofs, the comb_run statement kept). *)
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
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkTables CkModel CkXt CkMultmodp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition X2NTc : Z := 72020.   (* x2n_table, 0x11954 (unmoved at 1.4) *)
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

(* x2nmodp never returns 0 (kept from the 1.3.1 file) *)
Lemma xp_0 : xp 0 = X0.
Proof. reflexivity. Qed.

Lemma x2n_loop_xp : forall f n k e, 0 <= k -> exists e', x2n_loop f n k (xp e) = xp e'.
Proof.
  induction f as [|f IH]; intros n k e Hk; cbn [x2n_loop].
  - exists e. reflexivity.
  - destruct (n =? 0); [exists e; reflexivity|].
    destruct (Z.odd n).
    + pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hm.
      replace (k mod 32) with (Z.of_nat (Z.to_nat (k mod 32))) by lia.
      rewrite x2n_xp by lia. rewrite multmodp_xp_xp. apply IH. lia.
    + apply IH. lia.
Qed.

Lemma x2nmodp_nz_any : forall n k, 0 <= k -> x2nmodp n k mod 2 ^ 32 <> 0.
Proof.
  intros n k Hk. unfold x2nmodp. rewrite <- xp_0.
  destruct (x2n_loop_xp 64 n k 0 Hk) as [e' ->].
  pose proof (xp_range e'). pose proof (xp_nz e'). rewrite Z.mod_small by lia. lia.
Qed.

(* 1.4 helpers *)
Lemma bstep14c : forall b, Z.lxor (Z.shiftr b 1) (Z.land (if Z.odd b then ONES64 else 0) POLY) = bstep b.
Proof.
  intros b. unfold bstep. destruct (Z.odd b).
  - replace (Z.land ONES64 POLY) with POLY by reflexivity. reflexivity.
  - rewrite Z.land_0_l, Z.lxor_0_r. reflexivity.
Qed.

Lemma bstep14c_range : forall b, 0 <= b < two32 -> 0 <= bstep b < two32.
Proof.
  intros b Hb. unfold bstep.
  assert (Hs : 0 <= Z.shiftr b 1 < two32).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia|].
    apply (Z.le_lt_trans _ b); [apply Z.div_le_upper_bound; lia| lia]. }
  destruct (Z.odd b); [| exact Hs].
  apply (lxor_range _ _ 32); [lia| exact Hs| unfold POLY; change two32 with (2 ^ 32) in *; lia].
Qed.

Lemma lxor14c_range : forall p b, 0 <= p < two32 -> 0 <= b < two32 -> 0 <= Z.lxor p b < two32.
Proof.
  intros p b Hp Hb. pose proof (lxor_range p b 32 ltac:(lia) ltac:(change (2 ^ 32) with two32; lia)
                                  ltac:(change (2 ^ 32) with two32; lia)) as H.
  change (2 ^ 32) with two32 in H. exact H.
Qed.

(* the 1.4 inlined multmodp tests the low bits with (m + 0xffffffff) & x, x zero-extended *)
Lemma land_mM32 : forall mreg j x, 0 <= j <= 31 -> mreg = 2 ^ j -> 0 <= x < two32 ->
  Z.land (mreg + M32) x = x mod 2 ^ j.
Proof.
  intros mreg j x Hj -> Hx. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)) as Hp.
  assert (Hp31 : 2 ^ j <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). change (2 ^ 31) with 2147483648 in Hp31.
  pose proof (land_range (2 ^ j + M32) x ltac:(lia)) as Hr.
  rewrite <- (Z.mod_small (Z.land (2 ^ j + M32) x) two32) by lia.
  rewrite <- land_mod32. rewrite (Z.mod_small x two32) by lia.
  replace ((2 ^ j + M32) mod two32) with (2 ^ j - 1).
  - apply land_ones_l. lia.
  - unfold M32. replace (2 ^ j + 4294967295) with ((2 ^ j - 1) + 1 * two32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.


Section COMB.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (retw : word).
  Hypothesis Hret : ret_ok retw.
  Hypothesis Himg : img_ok m.

  Ltac solve_cs := apply (proj2 (keeps_cs_lkeeps _ _)); solve_lkeeps.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | lia | solve_cs ].
  Ltac fix_auipc := match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.

  (* the x2nmodp multmodp shift block: t3 >>= 1; t4 := bstep t4 *)
  Lemma comb_shift : forall regs (b mreg : Z),
    getr regs 29 = Z_to_bv 64 mreg -> getr regs 30 = Z_to_bv 64 b -> getr regs 15 = Z_to_bv 64 POLY ->
    0 <= mreg < two64 -> 0 <= b < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ea0 : word) m rom) (mkst r (0x14eb8 : word) m rom)
      /\ getr r 29 = Z_to_bv 64 (Z.shiftr mreg 1)
      /\ getr r 30 = Z_to_bv 64 (Z.lxor (Z.shiftr b 1) (Z.land (if Z.odd b then ONES64 else 0) POLY))
      /\ getr r 15 = Z_to_bv 64 POLY
      /\ getr r 1 = getr regs 1 /\ getr r 5 = getr regs 5 /\ getr r 6 = getr regs 6 /\ getr r 28 = getr regs 28
      /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11 /\ getr r 12 = getr regs 12
      /\ getr r 13 = getr regs 13 /\ getr r 14 = getr regs 14 /\ getr r 16 = getr regs 16
      /\ getr r 17 = getr regs 17 /\ getr r 7 = getr regs 7
      /\ keeps_cs regs r.
  Proof.
    intros regs b mreg R28 R29 R15 Hm Hb.
    eexists. split.
    - stepz NF_14e40 ND_14e40. rewrite (zv_srli mreg 1 Hm).
      stepz NF_14e44 ND_14e44.
      stepz NF_14e48 ND_14e48.
      stepz NF_14e4c ND_14e4c. rewrite (zv_srli b 1 Hb).
      stepz NF_14e50 ND_14e50.
      stepz NF_14e54 ND_14e54.
      apply mst_refl.
    - post.
  Qed.

  (* the x2nmodp multmodp loop from its test (0x14e58) to the latch (0x14e08); acc in a6 *)
  Lemma comb_mm : forall (i : nat) regs (x b p mreg : Z),
    getr regs 28 = Z_to_bv 64 x -> getr regs 29 = Z_to_bv 64 mreg -> getr regs 30 = Z_to_bv 64 b ->
    getr regs 16 = Z_to_bv 64 p -> getr regs 15 = Z_to_bv 64 POLY -> getr regs 13 = Z_to_bv 64 M32 ->
    (i <= 31)%nat -> 0 <= x < two32 -> x mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < two32 -> 0 <= p < two32 -> mreg = 2 ^ Z.of_nat i ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14eb8 : word) m rom) (mkst r (0x14e68 : word) m rom)
      /\ getr r 16 = Z_to_bv 64 (mm_loop i x b p)
      /\ getr r 1 = getr regs 1 /\ getr r 5 = getr regs 5 /\ getr r 6 = getr regs 6
      /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11 /\ getr r 12 = getr regs 12
      /\ getr r 13 = Z_to_bv 64 M32 /\ getr r 14 = getr regs 14 /\ getr r 15 = Z_to_bv 64 POLY
      /\ getr r 17 = getr regs 17 /\ getr r 7 = getr regs 7
      /\ keeps_cs regs r.
  Proof.
    induction i as [|i IH]; intros regs x b p mreg R7 R28 R29 R16 R15 R13 Hi Hx Hxnz Hb Hp Hmi.
    - (* bit 0: the last one *)
      change (Z.of_nat 0 + 1) with 1 in Hxnz. change (Z.of_nat 0) with 0 in Hmi.
      assert (Ht : Z.testbit x 0 = true).
      { rewrite Z.bit0_odd. change (2 ^ 1) with 2 in Hxnz. rewrite Zmod_odd in Hxnz.
        destruct (Z.odd x); [reflexivity | exfalso; apply Hxnz; reflexivity]. }
      assert (E1 : Z.land mreg x = mreg) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
      assert (E2 : Z.land (mreg + M32) x = 0).
      { rewrite (land_mM32 mreg 0 x ltac:(lia) Hmi Hx). apply Z.mod_1_r. }
      assert (Hmr : 0 <= mreg < two64) by (rewrite Hmi; cbn; lia).
      pose proof (lxor14c_range p b Hp Hb) as Hpb.
      eexists. split; [|split].
      + stepz NF_14e58 ND_14e58.
        stepb_ft NF_14e5c ND_14e5c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; rewrite Hmi; cbn; lia).
        stepz NF_14e60 ND_14e60.
        stepz NF_14e64 ND_14e64.
        stepz NF_14e68 ND_14e68.
        stepb_ft NF_14e6c ND_14e6c ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; reflexivity).
        stepz NF_14e70 ND_14e70.
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
      assert (E2 : Z.land (mreg + M32) x = x mod 2 ^ Z.of_nat j) by (apply land_mM32; lia).
      pose proof (bstep14c_range b Hb) as Hb'.
      destruct (Z.testbit x (Z.of_nat j)) eqn:Ht.
      + (* bit j set: p ^= b *)
        assert (E1 : Z.land mreg x = mreg) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        pose proof (lxor14c_range p b Hp Hb) as Hpb.
        destruct (Z.eq_dec (x mod 2 ^ Z.of_nat j) 0) as [Hz|Hnz].
        * (* no lower bit left: exit *)
          rewrite Hz in E2.
          eexists. split; [|split].
          -- stepz NF_14e58 ND_14e58.
             stepb_ft NF_14e5c ND_14e5c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
             stepz NF_14e60 ND_14e60.
             stepz NF_14e64 ND_14e64.
             stepz NF_14e68 ND_14e68.
             stepb_ft NF_14e6c ND_14e6c ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; reflexivity).
             stepz NF_14e70 ND_14e70.
             apply mst_refl.
          -- gres. rewrite (mm_loop_exit j x b p Ht Hz). reflexivity.
          -- post.
        * (* a lower bit left: shift, go on *)
          eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14ea0 : word) m rom)
                   (fun r => getr r 28 = Z_to_bv 64 x /\ getr r 29 = Z_to_bv 64 mreg
                             /\ getr r 30 = Z_to_bv 64 b /\ getr r 16 = Z_to_bv 64 (Z.lxor p b)
                             /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 13 = Z_to_bv 64 M32
                             /\ getr r 1 = getr regs 1 /\ getr r 5 = getr regs 5 /\ getr r 6 = getr regs 6
                             /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11 /\ getr r 12 = getr regs 12
                             /\ getr r 14 = getr regs 14 /\ getr r 17 = getr regs 17 /\ getr r 7 = getr regs 7 /\ keeps_cs regs r)).
          { eexists. split.
            - stepz NF_14e58 ND_14e58.
              stepb_ft NF_14e5c ND_14e5c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
              stepz NF_14e60 ND_14e60.
              stepz NF_14e64 ND_14e64.
              stepz NF_14e68 ND_14e68.
              stepb_tk NF_14e6c ND_14e6c ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
              apply mst_refl.
            - post. }
          cbv beta. intros r1 (S7 & S28 & S29 & S16 & S15 & S13 & S1 & S5 & S6 & S10 & S11 & S12 & S14 & S17 & S7x & K1).
          destruct (comb_shift r1 b mreg S28 S29 S15 Hmr ltac:(lia))
            as (r2 & M2 & T28 & T29 & T15 & T1 & T5 & T6 & T7 & T10 & T11 & T12 & T13 & T14 & T16 & T17 & T7x & K2).
          rewrite S1 in T1. rewrite S5 in T5. rewrite S6 in T6. rewrite S7 in T7. rewrite S10 in T10.
          rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13. rewrite S14 in T14. rewrite S16 in T16.
          rewrite S17 in T17. rewrite S7x in T7x. rewrite Hm' in T28. rewrite bstep14c in T29.
          destruct (IH r2 x (bstep b) (Z.lxor p b) (2 ^ Z.of_nat i) T7 T28 T29 T16 T15 T13
                      ltac:(lia) Hx ltac:(rewrite <- Hj; exact Hnz) Hb' Hpb eq_refl)
            as (r3 & M3 & V3 & U1 & U5 & U6 & U10 & U11 & U12 & U13 & U14 & U15 & U17 & U7x & K3).
          exists r3. split; [|split].
          -- eapply msteps_trans; [exact M2 | exact M3].
          -- rewrite V3. subst j. rewrite (mm_loop_go i x) by assumption. reflexivity.
          -- rewrite U1, U5, U6, U10, U11, U12, U14, U17, U7x, T1, T5, T6, T10, T11, T12, T14, T17, T7x.
             repeat split; first [reflexivity | exact U13 | exact U15 |
               (eapply keeps_cs_trans; [exact K1|]; eapply keeps_cs_trans; [exact K2| exact K3])].
      + (* bit j clear: shift, go on *)
        assert (E1 : Z.land mreg x = 0) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        assert (Hnz : x mod 2 ^ Z.of_nat j <> 0) by (rewrite Hsplit in Hxnz; lia).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14ea0 : word) m rom)
                 (fun r => getr r 28 = Z_to_bv 64 x /\ getr r 29 = Z_to_bv 64 mreg
                           /\ getr r 30 = Z_to_bv 64 b /\ getr r 16 = Z_to_bv 64 p
                           /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 13 = Z_to_bv 64 M32
                           /\ getr r 1 = getr regs 1 /\ getr r 5 = getr regs 5 /\ getr r 6 = getr regs 6
                           /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11 /\ getr r 12 = getr regs 12
                           /\ getr r 14 = getr regs 14 /\ getr r 17 = getr regs 17 /\ getr r 7 = getr regs 7 /\ keeps_cs regs r)).
        { eexists. split.
          - stepz NF_14e58 ND_14e58.
            stepb_tk NF_14e5c ND_14e5c ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; reflexivity).
            apply mst_refl.
          - post. }
        cbv beta. intros r1 (S7 & S28 & S29 & S16 & S15 & S13 & S1 & S5 & S6 & S10 & S11 & S12 & S14 & S17 & S7x & K1).
        destruct (comb_shift r1 b mreg S28 S29 S15 Hmr ltac:(lia))
          as (r2 & M2 & T28 & T29 & T15 & T1 & T5 & T6 & T7 & T10 & T11 & T12 & T13 & T14 & T16 & T17 & T7x & K2).
        rewrite S1 in T1. rewrite S5 in T5. rewrite S6 in T6. rewrite S7 in T7. rewrite S10 in T10.
        rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13. rewrite S14 in T14. rewrite S16 in T16.
        rewrite S17 in T17. rewrite S7x in T7x. rewrite Hm' in T28. rewrite bstep14c in T29.
        destruct (IH r2 x (bstep b) p (2 ^ Z.of_nat i) T7 T28 T29 T16 T15 T13
                    ltac:(lia) Hx ltac:(rewrite <- Hj; exact Hnz) Hb' Hp eq_refl)
          as (r3 & M3 & V3 & U1 & U5 & U6 & U10 & U11 & U12 & U13 & U14 & U15 & U17 & U7x & K3).
        exists r3. split; [|split].
        -- eapply msteps_trans; [exact M2 | exact M3].
        -- rewrite V3. subst j. rewrite (mm_loop_skip i x) by assumption. reflexivity.
        -- rewrite U1, U5, U6, U10, U11, U12, U14, U17, U7x, T1, T5, T6, T10, T11, T12, T14, T17, T7x.
           repeat split; first [reflexivity | exact U13 | exact U15 |
             (eapply keeps_cs_trans; [exact K1|]; eapply keeps_cs_trans; [exact K2| exact K3])].
  Qed.

  (* one x2nmodp iteration from its odd test (0x14e14) to the latch (0x14e08); p in a6 *)
  Lemma comb_body : forall regs (n k p : Z),
    getr regs 12 = Z_to_bv 64 n -> getr regs 17 = Z_to_bv 64 k -> getr regs 16 = Z_to_bv 64 p ->
    getr regs 5 = Z_to_bv 64 2147483648 -> getr regs 6 = Z_to_bv 64 X2NTc -> getr regs 15 = Z_to_bv 64 POLY ->
    getr regs 13 = Z_to_bv 64 M32 -> getr regs 7 = Z_to_bv 64 NX2NT ->
    0 <= n < two64 -> 0 <= k < two64 -> 0 <= p < two32 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14e74 : word) m rom) (mkst r (0x14e68 : word) m rom)
      /\ getr r 16 = Z_to_bv 64 (if Z.odd n then multmodp (x2n (k mod 32)) p else p)
      /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11
      /\ getr r 14 = getr regs 14 /\ getr r 12 = Z_to_bv 64 n /\ getr r 17 = Z_to_bv 64 k
      /\ getr r 5 = Z_to_bv 64 2147483648 /\ getr r 6 = Z_to_bv 64 X2NTc /\ getr r 15 = Z_to_bv 64 POLY
      /\ getr r 13 = Z_to_bv 64 M32 /\ getr r 7 = Z_to_bv 64 NX2NT
      /\ keeps_cs regs r.
  Proof.
    intros regs n k p R12 R17 R16 R5 R6 R15 R13 R7x Hn Hk Hp.
    pose proof (land_1_odd n) as Ho.
    destruct (Z.odd n) eqn:Hodd.
    - (* odd: p := multmodp (x2n_table[k & 31], p) *)
      pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hk32.
      pose proof (x2n_range (k mod 32) Hk32) as Hxr.
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14eb8 : word) m rom)
               (fun r => getr r 28 = Z_to_bv 64 (x2n (k mod 32)) /\ getr r 29 = Z_to_bv 64 2147483648
                         /\ getr r 30 = Z_to_bv 64 p /\ getr r 16 = Z_to_bv 64 0 /\ getr r 15 = Z_to_bv 64 POLY
                         /\ getr r 13 = Z_to_bv 64 M32
                         /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11
                         /\ getr r 14 = getr regs 14 /\ getr r 12 = Z_to_bv 64 n /\ getr r 17 = Z_to_bv 64 k
                         /\ getr r 5 = Z_to_bv 64 2147483648 /\ getr r 6 = Z_to_bv 64 X2NTc
                         /\ getr r 7 = Z_to_bv 64 NX2NT
                         /\ keeps_cs regs r)).
      { eexists. split.
        - stepz NF_14e14 ND_14e14.
          stepb_ft NF_14e18 ND_14e18 ltac:(rewrite Ho; rewrite zc_eq by lia; reflexivity).
          stepz NF_14e1c ND_14e1c.
          match goal with |- context [Z_to_bv 64 (Z.land k 31)] => rewrite (land_31_mod k) end.
          stepz NF_14e20 ND_14e20.
          stepb_ft NF_14e24 ND_14e24 ltac:(rwR; unfold NX2NT; zcond).   (* the UBSan table-bound check *)
          stepz NF_14e28 ND_14e28.
          chain_step;
          [ reflexivity
          | eapply step_lwu with (v := Z_to_bv 64 (x2n (k mod 32)));
            [ exact NF_14e2c | reflexivity | exact ND_14e2c
            | gres; imm_norm; rewrite zv_addi;
              replace (X2NTc + k mod 32 * 2 ^ 2 + 0) with (X2NT + 4 * (k mod 32)) by (unfold X2NTc, X2NT; lia);
              apply rd_x2n; [exact Himg | lia]
            | apply x2n_bs_v; lia ]
          | step_simpl; gres ].
          stepz NF_14e30 ND_14e30. stepz NF_14e34 ND_14e34. stepz NF_14e38 ND_14e38. stepz NF_14e3c ND_14e3c.
          apply mst_refl.
        - post. }
      cbv beta. intros r1 (S7 & S28 & S29 & S16 & S15 & S13 & S1 & S10 & S11 & S14 & S12 & S17 & S5 & S6 & S7x & K1).
      destruct (comb_mm 31 r1 (x2n (k mod 32)) p 0 2147483648 S7 S28 S29 S16 S15 S13 ltac:(lia) Hxr
                  ltac:(change (2 ^ (Z.of_nat 31 + 1)) with two32; apply x2n_nz; lia) Hp ltac:(lia)
                  ltac:(reflexivity))
        as (r2 & M2 & V2 & U1 & U5 & U6 & U10 & U11 & U12 & U13 & U14 & U15 & U17 & U7x & K2).
      exists r2. split; [exact M2|]. split.
      + rewrite V2. cbv iota. unfold multmodp. reflexivity.
      + rewrite U1, U5, U6, U10, U11, U12, U14, U17, U7x, S1, S5, S6, S10, S11, S12, S14, S17, S7x.
        repeat split; try reflexivity; try assumption.
        eapply keeps_cs_trans; [exact K1 | exact K2].
    - (* even: p unchanged *)
      eexists. split; [|split].
      + stepz NF_14e14 ND_14e14.
        stepb_tk NF_14e18 ND_14e18 ltac:(rewrite Ho; rewrite zc_eq by lia; reflexivity).
        apply mst_refl.
      + post.
      + post.
  Qed.

  (* the x2nmodp latch (0x14e08): n >>= 1; k++; leave to 0x14e74 on n = 0 *)
  Lemma comb_latch : forall (f : nat) regs (n k p : Z),
    getr regs 12 = Z_to_bv 64 n -> getr regs 17 = Z_to_bv 64 k -> getr regs 16 = Z_to_bv 64 p ->
    getr regs 5 = Z_to_bv 64 2147483648 -> getr regs 6 = Z_to_bv 64 X2NTc -> getr regs 15 = Z_to_bv 64 POLY ->
    getr regs 13 = Z_to_bv 64 M32 -> getr regs 7 = Z_to_bv 64 NX2NT ->
    0 <= n < two64 -> n < 2 ^ (Z.of_nat f + 1) -> (0 <= k /\ k + Z.of_nat f <= 99) -> 0 <= p < two32 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14e68 : word) m rom) (mkst r (0x14ed4 : word) m rom)
      /\ getr r 16 = Z_to_bv 64 (x2n_loop f (Z.shiftr n 1) (k + 1) p)
      /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11
      /\ getr r 14 = getr regs 14 /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 13 = Z_to_bv 64 M32
      /\ keeps_cs regs r.
  Proof.
    induction f as [|f IH]; intros regs n k p R12 R17 R16 R5 R6 R15 R13 R7x Hn64 Hn Hk Hp.
    - (* fuel 0: n < 2, so n >> 1 = 0 *)
      change (2 ^ (Z.of_nat 0 + 1)) with 2 in Hn.
      assert (Hs : Z.shiftr n 1 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
      eexists. split; [|split].
      + stepz NF_14e08 ND_14e08. rewrite (zv_srli n 1 Hn64), Hs.
        stepz NF_14e0c ND_14e0c.
        stepb_tk NF_14e10 ND_14e10 ltac:(reflexivity).
        apply mst_refl.
      + gres. rewrite Hs, x2n_loop_done. exact R16.
      + post.
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
        * stepz NF_14e08 ND_14e08. rewrite (zv_srli n 1 Hn64). fold n'. rewrite Hz.
          stepz NF_14e0c ND_14e0c.
          stepb_tk NF_14e10 ND_14e10 ltac:(reflexivity).
          apply mst_refl.
        * gres. rewrite Hz, x2n_loop_done. exact R16.
        * post.
      + eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14e74 : word) m rom)
                 (fun r => getr r 12 = Z_to_bv 64 n' /\ getr r 17 = Z_to_bv 64 (k + 1) /\ getr r 16 = Z_to_bv 64 p
                           /\ getr r 5 = Z_to_bv 64 2147483648 /\ getr r 6 = Z_to_bv 64 X2NTc
                           /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 13 = Z_to_bv 64 M32
                           /\ getr r 1 = getr regs 1 /\ getr r 10 = getr regs 10 /\ getr r 11 = getr regs 11
                           /\ getr r 14 = getr regs 14 /\ getr r 7 = Z_to_bv 64 NX2NT /\ keeps_cs regs r)).
        { eexists. split.
          - stepz NF_14e08 ND_14e08. rewrite (zv_srli n 1 Hn64). fold n'.
            stepz NF_14e0c ND_14e0c.
            stepb_ft NF_14e10 ND_14e10 ltac:(rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
            apply mst_refl.
          - post. }
        cbv beta. intros r1 (S12 & S17 & S16 & S5 & S6 & S15 & S13 & S1 & S10 & S11 & S14 & S7x & K1).
        destruct (comb_body r1 n' (k + 1) p S12 S17 S16 S5 S6 S15 S13 S7x ltac:(lia) ltac:(lia) Hp)
          as (r2 & M2 & V2 & U1 & U10 & U11 & U14 & U12 & U17 & U5 & U6 & U15 & U13 & U7x & K2).
        set (p2 := if Z.odd n' then multmodp (x2n ((k + 1) mod 32)) p else p) in V2.
        assert (Hp2 : 0 <= p2 < two32).
        { subst p2. destruct (Z.odd n'); [apply multmodp_range; exact Hp | exact Hp]. }
        destruct (IH r2 n' (k + 1) p2 U12 U17 V2 U5 U6 U15 U13 U7x ltac:(lia) ltac:(lia) ltac:(lia) Hp2)
          as (r3 & M3 & V3 & W1 & W10 & W11 & W14 & W15 & W13 & K3).
        exists r3. split; [|split].
        * eapply msteps_trans; [exact M2 | exact M3].
        * rewrite V3. subst g p2. rewrite (x2n_loop_step f n') by exact Hnz. reflexivity.
        * rewrite W1, W10, W11, W14, U1, U10, U11, U14, S1, S10, S11, S14.
          repeat split; first [reflexivity | exact W15 | exact W13 |
            (eapply keeps_cs_trans; [exact K1|]; eapply keeps_cs_trans; [exact K2 | exact K3])].
  Qed.

  (* the crc32_combine_op multmodp shift block: a4 >>= 1; a0 := bstep a0 *)
  Lemma comb_fshift : forall regs (b mreg : Z),
    getr regs 14 = Z_to_bv 64 mreg -> getr regs 10 = Z_to_bv 64 b -> getr regs 15 = Z_to_bv 64 POLY ->
    0 <= mreg < two64 -> 0 <= b < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ee4 : word) m rom) (mkst r (0x14efc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (Z.shiftr mreg 1)
      /\ getr r 10 = Z_to_bv 64 (Z.lxor (Z.shiftr b 1) (Z.land (if Z.odd b then ONES64 else 0) POLY))
      /\ getr r 15 = Z_to_bv 64 POLY
      /\ getr r 1 = getr regs 1 /\ getr r 11 = getr regs 11 /\ getr r 12 = getr regs 12
      /\ getr r 13 = getr regs 13 /\ getr r 16 = getr regs 16
      /\ keeps_cs regs r.
  Proof.
    intros regs b mreg R14 R10 R15 Hm Hb.
    eexists. split.
    - stepz NF_14e84 ND_14e84. rewrite (zv_srli mreg 1 Hm).
      stepz NF_14e88 ND_14e88.
      stepz NF_14e8c ND_14e8c.
      stepz NF_14e90 ND_14e90. rewrite (zv_srli b 1 Hb).
      stepz NF_14e94 ND_14e94.
      stepz NF_14e98 ND_14e98.
      apply mst_refl.
    - post.
  Qed.

  (* the crc32_combine_op multmodp loop from its test (0x14e9c) to the return *)
  Lemma comb_fin : forall (i : nat) regs (a b p c2 mreg : Z),
    getr regs 1 = retw ->
    getr regs 16 = Z_to_bv 64 a -> getr regs 14 = Z_to_bv 64 mreg -> getr regs 15 = Z_to_bv 64 POLY ->
    getr regs 10 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 c2 ->
    getr regs 13 = Z_to_bv 64 M32 ->
    (i <= 31)%nat -> 0 <= a < two64 -> a mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < two32 -> 0 <= p < two32 -> 0 <= c2 < two64 -> mreg = 2 ^ Z.of_nat i ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14efc : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lxor (mm_loop i a b p) (c2 mod two32))
      /\ keeps_cs regs r.
  Proof.
    induction i as [|i IH]; intros regs a b p c2 mreg R1 R16 R14 R15 R10 R12 R11 R13 Hi Ha Hanz Hb Hp Hc2 Hmi.
    - (* bit 0: the last one *)
      change (Z.of_nat 0 + 1) with 1 in Hanz. change (2 ^ Z.of_nat 0) with 1 in Hmi. subst mreg.
      assert (Ht : Z.testbit a 0 = true).
      { rewrite Z.bit0_odd. change (2 ^ 1) with 2 in Hanz. rewrite Zmod_odd in Hanz.
        destruct (Z.odd a); [reflexivity | exfalso; apply Hanz; reflexivity]. }
      assert (E1 : Z.land 1 a = 1).
      { pose proof (land_pow2_l a 0 ltac:(lia)) as E. rewrite Ht in E. exact E. }
      assert (E2 : Z.land 0 a = 0) by apply Z.land_0_l.
      pose proof (lxor14c_range p b Hp Hb) as Hpb.
      eexists. split; [|split].
      + stepz NF_14e9c ND_14e9c.
        stepb_ft NF_14ea0 ND_14ea0 ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; reflexivity).
        stepz NF_14ea4 ND_14ea4.
        stepz NF_14ea8 ND_14ea8.
        stepz NF_14eac ND_14eac.
        stepb_ft NF_14eb0 ND_14eb0 ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; reflexivity).
        stepz NF_14eb4 ND_14eb4.
        stepz NF_14eb8 ND_14eb8.
        stepret NF_14ebc ND_14ebc retw ltac:(rwR; reflexivity).
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
      pose proof (bstep14c_range b Hb) as Hb'.
      destruct (Z.testbit a (Z.of_nat j)) eqn:Ht.
      + (* bit j set: p ^= b *)
        assert (E1 : Z.land mreg a = mreg) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        pose proof (lxor14c_range p b Hp Hb) as Hpb.
        destruct (Z.eq_dec (a mod 2 ^ Z.of_nat j) 0) as [Hz|Hnz].
        * (* no lower bit left: exit *)
          rewrite Hz in E2.
          eexists. split; [|split].
          -- stepz NF_14e9c ND_14e9c.
             stepb_ft NF_14ea0 ND_14ea0 ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
             stepz NF_14ea4 ND_14ea4.
             stepz NF_14ea8 ND_14ea8.
             stepz NF_14eac ND_14eac.
             stepb_ft NF_14eb0 ND_14eb0 ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; reflexivity).
             stepz NF_14eb4 ND_14eb4.
             stepz NF_14eb8 ND_14eb8.
             stepret NF_14ebc ND_14ebc retw ltac:(rwR; reflexivity).
             apply mst_refl.
          -- gres. rewrite (mm_loop_exit j a b p Ht Hz). rewrite land_M32. reflexivity.
          -- solve_cs.
        * (* a lower bit left: shift, go on *)
          eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14ee4 : word) m rom)
                   (fun r => getr r 1 = retw /\ getr r 16 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 mreg
                             /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 10 = Z_to_bv 64 b
                             /\ getr r 12 = Z_to_bv 64 (Z.lxor p b) /\ getr r 11 = Z_to_bv 64 c2
                             /\ getr r 13 = Z_to_bv 64 M32 /\ keeps_cs regs r)).
          { eexists. split.
            - stepz NF_14e9c ND_14e9c.
              stepb_ft NF_14ea0 ND_14ea0 ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
              stepz NF_14ea4 ND_14ea4.
              stepz NF_14ea8 ND_14ea8.
              stepz NF_14eac ND_14eac.
              stepb_tk NF_14eb0 ND_14eb0 ltac:(rewrite ?getr_zero; rewrite E2; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
              apply mst_refl.
            - post. }
          cbv beta. intros r1 (S1 & S16 & S14 & S15 & S10 & S12 & S11 & S13 & K1).
          destruct (comb_fshift r1 b mreg S14 S10 S15 Hmr ltac:(lia))
            as (r2 & M2 & T14 & T10 & T15 & T1 & T11 & T12 & T13 & T16 & K2).
          rewrite S1 in T1. rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13. rewrite S16 in T16.
          rewrite Hm' in T14. rewrite bstep14c in T10.
          destruct (IH r2 a (bstep b) (Z.lxor p b) c2 (2 ^ Z.of_nat i) T1 T16 T14 T15 T10 T12 T11 T13
                      ltac:(lia) Ha ltac:(rewrite <- Hj; exact Hnz) Hb' Hpb Hc2 eq_refl) as (r3 & M3 & V3 & K3).
          exists r3. split; [|split].
          -- eapply msteps_trans; [exact M2 | exact M3].
          -- rewrite V3. subst j. rewrite (mm_loop_go i a) by assumption. reflexivity.
          -- eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2| exact K3].
      + (* bit j clear: shift, go on *)
        assert (E1 : Z.land mreg a = 0) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
        assert (Hnz : a mod 2 ^ Z.of_nat j <> 0) by (rewrite Hsplit in Hanz; lia).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14ee4 : word) m rom)
                 (fun r => getr r 1 = retw /\ getr r 16 = Z_to_bv 64 a /\ getr r 14 = Z_to_bv 64 mreg
                           /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 10 = Z_to_bv 64 b
                           /\ getr r 12 = Z_to_bv 64 p /\ getr r 11 = Z_to_bv 64 c2
                           /\ getr r 13 = Z_to_bv 64 M32 /\ keeps_cs regs r)).
        { eexists. split.
          - stepz NF_14e9c ND_14e9c.
            stepb_tk NF_14ea0 ND_14ea0 ltac:(rewrite ?getr_zero; rewrite E1; rewrite zc_eq by lia; reflexivity).
            apply mst_refl.
          - post. }
        cbv beta. intros r1 (S1 & S16 & S14 & S15 & S10 & S12 & S11 & S13 & K1).
        destruct (comb_fshift r1 b mreg S14 S10 S15 Hmr ltac:(lia))
          as (r2 & M2 & T14 & T10 & T15 & T1 & T11 & T12 & T13 & T16 & K2).
        rewrite S1 in T1. rewrite S11 in T11. rewrite S12 in T12. rewrite S13 in T13. rewrite S16 in T16.
        rewrite Hm' in T14. rewrite bstep14c in T10.
        destruct (IH r2 a (bstep b) p c2 (2 ^ Z.of_nat i) T1 T16 T14 T15 T10 T12 T11 T13
                    ltac:(lia) Ha ltac:(rewrite <- Hj; exact Hnz) Hb' Hp Hc2 eq_refl) as (r3 & M3 & V3 & K3).
        exists r3. split; [|split].
        -- eapply msteps_trans; [exact M2 | exact M3].
        -- rewrite V3. subst j. rewrite (mm_loop_skip i a) by assumption. reflexivity.
        -- eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2| exact K3].
  Qed.

  (* crc32_combine (0x14dc4), at a length that is not negative *)
  Theorem comb_run : forall regs (crc1 crc2 len2 : Z),
    getr regs 1 = retw ->
    getr regs 10 = Z_to_bv 64 crc1 -> getr regs 11 = Z_to_bv 64 crc2 -> getr regs 12 = Z_to_bv 64 len2 ->
    0 <= crc1 < two32 -> 0 <= crc2 < two64 -> 0 <= len2 < 9223372036854775808 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14e24 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (crc32_combine crc1 crc2 len2)
      /\ keeps_cs regs r.
  Proof.
    intros regs crc1 crc2 len2 R1 R10 R11 R12 Hc1 Hc2 Hn.
    pose proof (x2nmodp_range_any len2 3) as Hxr. change (2 ^ 32) with two32 in Hxr.
    pose proof (x2nmodp_nz_any len2 3 ltac:(lia)) as Hxnz. change (2 ^ 32) with two32 in Hxnz.
    assert (Hx0 : x2nmodp len2 3 <> 0) by (intro E; apply Hxnz; rewrite E; reflexivity).
    (* to 0x14e78 with op = x2nmodp len2 3 in a6 *)
    eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14ed8 : word) m rom)
             (fun r => getr r 1 = retw /\ getr r 16 = Z_to_bv 64 (x2nmodp len2 3) /\ getr r 14 = Z_to_bv 64 2147483648
                       /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 13 = Z_to_bv 64 M32
                       /\ getr r 10 = Z_to_bv 64 crc1 /\ getr r 11 = Z_to_bv 64 crc2
                       /\ keeps_cs regs r)).
    { destruct (Z.eq_dec len2 0) as [-> | Hnz].
      - eexists. split.
        + stepb_ft NF_14dc4 ND_14dc4 ltac:(rewrite R12; apply zc_lts_0_false; lia).
          stepz NF_14dc8 ND_14dc8. stepz NF_14dcc ND_14dcc. stepz NF_14dd0 ND_14dd0. stepz NF_14dd4 ND_14dd4.
          stepz NF_14dd8 ND_14dd8. stepz NF_14ddc ND_14ddc. stepz NF_14de0 ND_14de0. stepz NF_14de4 ND_14de4.
          stepb_tk NF_14de8 ND_14de8 ltac:(rwR; reflexivity).
          apply mst_refl.
        + unfold POLY, M32. post.
      - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14e74 : word) m rom)
                 (fun r => getr r 12 = Z_to_bv 64 len2 /\ getr r 17 = Z_to_bv 64 3 /\ getr r 16 = Z_to_bv 64 X0
                           /\ getr r 5 = Z_to_bv 64 2147483648 /\ getr r 6 = Z_to_bv 64 X2NTc
                           /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 13 = Z_to_bv 64 M32
                           /\ getr r 1 = retw /\ getr r 10 = Z_to_bv 64 crc1 /\ getr r 11 = Z_to_bv 64 crc2
                           /\ getr r 14 = Z_to_bv 64 2147483648 /\ getr r 7 = Z_to_bv 64 NX2NT
                           /\ keeps_cs regs r)).
        { eexists. split.
          - stepb_ft NF_14dc4 ND_14dc4 ltac:(rewrite R12; apply zc_lts_0_false; lia).
            stepz NF_14dc8 ND_14dc8. stepz NF_14dcc ND_14dcc. stepz NF_14dd0 ND_14dd0. stepz NF_14dd4 ND_14dd4.
            stepz NF_14dd8 ND_14dd8. stepz NF_14ddc ND_14ddc. stepz NF_14de0 ND_14de0. stepz NF_14de4 ND_14de4.
            stepb_ft NF_14de8 ND_14de8 ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hnz).
            stepz NF_14dec ND_14dec. stepz NF_14df0 ND_14df0. stepz NF_14df4 ND_14df4. try fix_auipc.
            stepz NF_14df8 ND_14df8. stepz NF_14dfc ND_14dfc. stepz NF_14e00 ND_14e00. stepz NF_14e04 ND_14e04.
            apply mst_refl.
          - unfold X0, X2NTc, NX2NT, POLY, M32. post. }
        cbv beta. intros r1 (S12 & S17 & S16 & S5 & S6 & S15 & S13 & S1 & S10 & S11 & S14 & S7x & K1).
        destruct (comb_body r1 len2 3 X0 S12 S17 S16 S5 S6 S15 S13 S7x ltac:(lia) ltac:(lia) ltac:(unfold X0; lia))
          as (r2 & M2 & V2 & U1 & U10 & U11 & U14 & U12 & U17 & U5 & U6 & U15 & U13 & U7x & K2).
        set (p2 := if Z.odd len2 then multmodp (x2n (3 mod 32)) X0 else X0) in V2.
        assert (Hp2 : 0 <= p2 < two32).
        { subst p2. destruct (Z.odd len2); [apply multmodp_range; unfold X0; lia | unfold X0; lia]. }
        destruct (comb_latch 63 r2 len2 3 p2 U12 U17 V2 U5 U6 U15 U13 U7x ltac:(lia)
                    ltac:(change (2 ^ (Z.of_nat 63 + 1)) with two64; lia) ltac:(lia) Hp2)
          as (r3 & M3 & V3 & W1 & W10 & W11 & W14 & W15 & W13 & K3).
        assert (Vx : getr r3 16 = Z_to_bv 64 (x2nmodp len2 3)).
        { rewrite V3. unfold x2nmodp. change 64%nat with (S 63).
          rewrite (x2n_loop_step 63 len2 3) by exact Hnz. subst p2. reflexivity. }
        assert (M4 : msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst r3 (0x14ed4 : word) m rom) (mkst r3 (0x14ed8 : word) m rom)).
        { stepb_ft NF_14e74 ND_14e74 ltac:(rewrite Vx; rewrite zc_eq by lia; apply Z.eqb_neq; exact Hx0).
          apply mst_refl. }
        exists r3. split; [eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact M3 | exact M4]]|].
        rewrite W1, W10, W11, W14, U1, U10, U11, U14.
        repeat split; first [exact Vx | exact W15 | exact W13 | assumption |
          (eapply keeps_cs_trans; [exact K1|]; eapply keeps_cs_trans; [exact K2 | exact K3])]. }
    cbv beta. intros r1 (S1 & S16 & S14 & S15 & S13 & S10 & S11 & K1).
    (* 0x14e78: p := 0; b := crc1 & M32; on to the crc32_combine_op loop *)
    eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14efc : word) m rom)
             (fun r => getr r 1 = retw /\ getr r 16 = Z_to_bv 64 (x2nmodp len2 3) /\ getr r 14 = Z_to_bv 64 2147483648
                       /\ getr r 15 = Z_to_bv 64 POLY /\ getr r 10 = Z_to_bv 64 (Z.land crc1 M32)
                       /\ getr r 12 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 crc2 /\ getr r 13 = Z_to_bv 64 M32
                       /\ keeps_cs r1 r)).
    { eexists. split.
      - stepz NF_14e78 ND_14e78. stepz NF_14e7c ND_14e7c. stepz NF_14e80 ND_14e80. apply mst_refl.
      - post. }
    cbv beta. intros r2 (T1 & T16 & T14 & T15 & T10 & T12 & T11 & T13 & K2).
    assert (Hcl : Z.land crc1 M32 = crc1) by (rewrite land_M32; apply Z.mod_small; lia).
    rewrite Hcl in T10.
    destruct (comb_fin 31 r2 (x2nmodp len2 3) crc1 0 crc2 2147483648 T1 T16 T14 T15 T10 T12 T11 T13
                ltac:(lia) ltac:(lia) ltac:(change (2 ^ (Z.of_nat 31 + 1)) with two32; exact Hxnz)
                ltac:(lia) ltac:(lia) Hc2 ltac:(reflexivity)) as (r3 & M3 & V3 & K3).
    exists r3. split; [exact M3 | split].
    - rewrite V3. unfold crc32_combine, crc32_combine64, crc32_combine_op, crc32_combine_gen64.
      rewrite (proj2 (Z.ltb_ge len2 0)) by lia. rewrite (proj2 (Z.eqb_neq _ 0) Hx0).
      unfold multmodp. rewrite Hcl, land_M32. reflexivity.
    - eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2 | exact K3].
  Qed.
End COMB.

Theorem u0_crc32_combine {RCa1 : RunCtx}  : U0_crc32_combine_stmt.
Proof.
  intros regs m rom retw crc1 crc2 len2 R1 Hret R10 R11 R12 Hc1 Hc2 Hn Himg.
  exact (comb_run m rom retw Hret Himg regs crc1 crc2 len2 R1 R10 R11 R12 Hc1 Hc2 Hn).
Qed.
