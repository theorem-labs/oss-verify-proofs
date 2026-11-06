(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Set Keyed Unification.

Import ListNotations.
Local Instance smear_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

Definition sm (a k : Z) : Z := Z.lor a (Z.shiftr a k).

Lemma sm_nonneg : forall a k, 0 <= a -> 0 <= k -> 0 <= sm a k.
Proof. intros a k Ha Hk. unfold sm. apply Z.lor_nonneg. split; [exact Ha | apply Z.shiftr_nonneg; exact Ha]. Qed.

Lemma testbit_high47 : forall a j, 0 <= a < 2 ^ 47 -> 47 <= j -> Z.testbit a j = false.
Proof.
  intros a j Ha Hj. destruct (Z.eq_dec a 0) as [->|Hne]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. assert (Z.log2 a < 47) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lt47_of_testbits : forall a, 0 <= a -> (forall j, 47 <= j -> Z.testbit a j = false) -> a < 2 ^ 47.
Proof.
  intros a Ha H. destruct (Z.eq_dec a 0) as [->|Hne]; [lia|].
  destruct (Z.lt_ge_cases a (2 ^ 47)) as [Hl|Hge]; [exact Hl|].
  exfalso. pose proof (Z.log2_spec a ltac:(lia)) as [Hl1 _].
  assert (47 <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
  pose proof (H (Z.log2 a) ltac:(lia)) as Hb. rewrite Z.bit_log2 in Hb by lia. discriminate.
Qed.

Lemma sm_lt47 : forall a k, 0 <= a < 2 ^ 47 -> 0 <= k -> sm a k < 2 ^ 47.
Proof.
  intros a k Ha Hk. apply lt47_of_testbits; [apply sm_nonneg; lia|].
  intros j Hj. unfold sm. rewrite Z.lor_spec, Z.shiftr_spec by lia.
  rewrite !testbit_high47 by lia. reflexivity.
Qed.

Lemma sm_step : forall a k lo, 0 <= a -> 0 <= k -> lo + k <= 47 ->
  (forall j, lo <= j <= 46 -> Z.testbit a j = true) ->
  forall j, 0 <= j -> lo - k <= j <= 46 -> Z.testbit (sm a k) j = true.
Proof.
  intros a k lo Ha Hk Hlk Hall j Hj0 Hj. unfold sm. rewrite Z.lor_spec, Z.shiftr_spec by lia.
  destruct (Z.le_gt_cases lo j) as [Hl|Hl].
  - rewrite (Hall j ltac:(lia)). reflexivity.
  - rewrite (Hall (j + k) ltac:(lia)). apply orb_true_r.
Qed.

Lemma ones_of_testbits : forall a m, 0 <= m -> 0 <= a < 2 ^ m -> (forall j, 0 <= j < m -> Z.testbit a j = true) -> a = 2 ^ m - 1.
Proof.
  intros a m Hm Ha H. apply Z.bits_inj'. intros j Hj.
  replace (2 ^ m - 1) with (Z.ones m) by (rewrite Z.ones_equiv; lia).
  destruct (Z.lt_ge_cases j m) as [Hl|Hl].
  - rewrite (H j ltac:(lia)). symmetry. apply Z.ones_spec_low. lia.
  - rewrite Z.ones_spec_high by lia. destruct (Z.eq_dec a 0) as [->|Hne]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. assert (Z.log2 a < m) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma smear_top : forall x, 2 ^ 46 <= x < 2 ^ 47 ->
  sm (sm (sm (sm (sm (sm x 1) 2) 4) 8) 16) 32 = 2 ^ 47 - 1
  /\ Z.shiftr (sm (sm (sm (sm (sm x 1) 2) 4) 8) 16) 32 = 2 ^ 15 - 1.
Proof.
  intros x Hx.
  assert (B0 : forall j, 46 <= j <= 46 -> Z.testbit x j = true).
  { intros j Hj. assert (j = 46) by lia. subst j. apply Z.testbit_true; [lia|].
    rewrite Z.mod_small by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    replace (x / 2 ^ 46) with 1; [reflexivity|]. apply Z.div_unique with (x - 2 ^ 46); lia. }
  set (s1 := sm x 1). set (s2 := sm s1 2). set (s4 := sm s2 4). set (s8 := sm s4 8). set (s16 := sm s8 16). set (s32 := sm s16 32).
  assert (N1 : 0 <= s1 < 2 ^ 47) by (split; [apply sm_nonneg; lia | apply sm_lt47; lia]).
  assert (N2 : 0 <= s2 < 2 ^ 47) by (split; [apply sm_nonneg; lia | apply sm_lt47; lia]).
  assert (N4 : 0 <= s4 < 2 ^ 47) by (split; [apply sm_nonneg; lia | apply sm_lt47; lia]).
  assert (N8 : 0 <= s8 < 2 ^ 47) by (split; [apply sm_nonneg; lia | apply sm_lt47; lia]).
  assert (N16 : 0 <= s16 < 2 ^ 47) by (split; [apply sm_nonneg; lia | apply sm_lt47; lia]).
  assert (N32 : 0 <= s32 < 2 ^ 47) by (split; [apply sm_nonneg; lia | apply sm_lt47; lia]).
  assert (B1 : forall j, 45 <= j <= 46 -> Z.testbit s1 j = true) by (intros j Hj; apply (sm_step x 1 46); lia || exact B0).
  assert (B2 : forall j, 43 <= j <= 46 -> Z.testbit s2 j = true) by (intros j Hj; apply (sm_step s1 2 45); lia || exact B1).
  assert (B4 : forall j, 39 <= j <= 46 -> Z.testbit s4 j = true) by (intros j Hj; apply (sm_step s2 4 43); lia || exact B2).
  assert (B8 : forall j, 31 <= j <= 46 -> Z.testbit s8 j = true) by (intros j Hj; apply (sm_step s4 8 39); lia || exact B4).
  assert (B16 : forall j, 15 <= j <= 46 -> Z.testbit s16 j = true) by (intros j Hj; apply (sm_step s8 16 31); lia || exact B8).
  assert (B32 : forall j, 0 <= j <= 46 -> Z.testbit s32 j = true) by (intros j Hj; apply (sm_step s16 32 15); lia || exact B16).
  split.
  - apply ones_of_testbits; [lia | exact N32 |]. intros j Hj. apply B32. lia.
  - apply ones_of_testbits; [lia | |].
    + split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|].
      change (2 ^ 32 * 2 ^ 15) with (2 ^ 47). lia.
    + intros j Hj. rewrite Z.shiftr_spec by lia. apply B16. lia.
Qed.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition SW : list (bv 32) :=
  [0x00155593%bv; 0x55555637%bv; 0x333336b7%bv; 0x0f0f1737%bv; 0x010107b7%bv; 0x00b56533%bv; 0x5556059b%bv; 0x3336861b%bv;
   0xf0f7069b%bv; 0x1017871b%bv; 0x00255793%bv; 0x00f56533%bv; 0x02059793%bv; 0x00f585b3%bv; 0x02061793%bv; 0x00f60633%bv;
   0x02069793%bv; 0x00f686b3%bv; 0x02071793%bv; 0x00f70733%bv; 0x00455793%bv; 0x00f56533%bv; 0x00855793%bv; 0x00f56533%bv;
   0x01055793%bv; 0x00f56533%bv; 0x02055793%bv; 0x00f56533%bv].
Definition sw (i : nat) : bv 32 := nth i SW 0%bv.

Lemma SD0  : decode_any (sw 0)  = Some (ShiftImm ALU_SRL 11 10 1, 4). Proof. vm_refl. Qed.
Lemma SD1  : decode_any (sw 1)  = Some (Lui 12 349525, 4). Proof. vm_refl. Qed.
Lemma SD2  : decode_any (sw 2)  = Some (Lui 13 209715, 4). Proof. vm_refl. Qed.
Lemma SD3  : decode_any (sw 3)  = Some (Lui 14 61681, 4). Proof. vm_refl. Qed.
Lemma SD4  : decode_any (sw 4)  = Some (Lui 15 4112, 4). Proof. vm_refl. Qed.
Lemma SD5  : decode_any (sw 5)  = Some (Op ALU_OR 10 10 11, 4). Proof. vm_refl. Qed.
Lemma SD6  : decode_any (sw 6)  = Some (OpImm32 11 12 1365, 4). Proof. vm_refl. Qed.
Lemma SD7  : decode_any (sw 7)  = Some (OpImm32 12 13 819, 4). Proof. vm_refl. Qed.
Lemma SD8  : decode_any (sw 8)  = Some (OpImm32 13 14 3855, 4). Proof. vm_refl. Qed.
Lemma SD9  : decode_any (sw 9)  = Some (OpImm32 14 15 257, 4). Proof. vm_refl. Qed.
Lemma SD10 : decode_any (sw 10) = Some (ShiftImm ALU_SRL 15 10 2, 4). Proof. vm_refl. Qed.
Lemma SD11 : decode_any (sw 11) = Some (Op ALU_OR 10 10 15, 4). Proof. vm_refl. Qed.
Lemma SD12 : decode_any (sw 12) = Some (ShiftImm ALU_SLL 15 11 32, 4). Proof. vm_refl. Qed.
Lemma SD13 : decode_any (sw 13) = Some (Op ALU_ADD 11 11 15, 4). Proof. vm_refl. Qed.
Lemma SD14 : decode_any (sw 14) = Some (ShiftImm ALU_SLL 15 12 32, 4). Proof. vm_refl. Qed.
Lemma SD15 : decode_any (sw 15) = Some (Op ALU_ADD 12 12 15, 4). Proof. vm_refl. Qed.
Lemma SD16 : decode_any (sw 16) = Some (ShiftImm ALU_SLL 15 13 32, 4). Proof. vm_refl. Qed.
Lemma SD17 : decode_any (sw 17) = Some (Op ALU_ADD 13 13 15, 4). Proof. vm_refl. Qed.
Lemma SD18 : decode_any (sw 18) = Some (ShiftImm ALU_SLL 15 14 32, 4). Proof. vm_refl. Qed.
Lemma SD19 : decode_any (sw 19) = Some (Op ALU_ADD 14 14 15, 4). Proof. vm_refl. Qed.
Lemma SD20 : decode_any (sw 20) = Some (ShiftImm ALU_SRL 15 10 4, 4). Proof. vm_refl. Qed.
Lemma SD21 : decode_any (sw 21) = Some (Op ALU_OR 10 10 15, 4). Proof. vm_refl. Qed.
Lemma SD22 : decode_any (sw 22) = Some (ShiftImm ALU_SRL 15 10 8, 4). Proof. vm_refl. Qed.
Lemma SD23 : decode_any (sw 23) = Some (Op ALU_OR 10 10 15, 4). Proof. vm_refl. Qed.
Lemma SD24 : decode_any (sw 24) = Some (ShiftImm ALU_SRL 15 10 16, 4). Proof. vm_refl. Qed.
Lemma SD25 : decode_any (sw 25) = Some (Op ALU_OR 10 10 15, 4). Proof. vm_refl. Qed.
Lemma SD26 : decode_any (sw 26) = Some (ShiftImm ALU_SRL 15 10 32, 4). Proof. vm_refl. Qed.
Lemma SD27 : decode_any (sw 27) = Some (Op ALU_OR 10 10 15, 4). Proof. vm_refl. Qed.
Lemma SE : forall i, (i < 28)%nat -> is_ecall (sw i) = false.
Proof. intros i Hi. do 28 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.

Section Walk.
Variable segs : list Segment.
Variable p : Z.
Hypothesis Hp : 0 <= p /\ p + 112 < 2 ^ 64.
Hypothesis HF : forall i, (i < 28)%nat -> fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat i)) = Some (sw i).

Ltac red_if :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (if bv_eqb a b then x else y) with x
      | false => change (if bv_eqb a b then x else y) with y
      end
  end.
Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

Lemma u64_of_Z' : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma v_addi_lit1 : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u64_of_Z' by lia. reflexivity. Qed.

Lemma F' : forall i, (i < 28)%nat -> fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat i)) = Some (sw i).
Proof. exact HF. Qed.

Ltac one i D L :=
  eapply mst_step; [reflexivity | eapply (L segs); [ exact (F' i ltac:(lia)) | exact (SE i ltac:(lia)) | exact D ] |];
  red_if; rewrite v_addi_lit1 by lia; replace (p + 4 * Z.of_nat i + 4) with (p + 4 * Z.of_nat (S i)) by lia; gr.

Lemma u_or : forall a b : word, bv_unsigned (v_or a b) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof.
  intros a b. unfold v_or. apply u64_of_Z'. pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 b) as Hb.
  unfold bv_modulus in Ha, Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor (bv_unsigned a) (bv_unsigned b)) 0) as [E|E]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg (bv_unsigned a) (bv_unsigned b)); lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec (bv_unsigned a) 0) as [->|Ea]; [reflexivity || (cbn; lia)|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec (bv_unsigned b) 0) as [->|Eb]; [reflexivity || (cbn; lia)|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma u_srli : forall (a : word) k, 0 <= k -> bv_unsigned (v_srli a k) = Z.shiftr (bv_unsigned a) k.
Proof.
  intros a k Hk. unfold v_srli. apply u64_of_Z'. pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in Ha.
  split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
  eapply Z.le_lt_trans; [apply Z.div_le_upper_bound; [lia|] | exact (proj2 Ha)].
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). nia.
Qed.

Ltac lit_sh := repeat match goal with |- context [@bv_unsigned 6 ?c] =>
                   let v := eval vm_compute in (@bv_unsigned 6 c) in change (@bv_unsigned 6 c) with v end.
Ltac nonneg_sh := match goal with |- 0 <= bv_unsigned ?s => exact (proj1 (bv_unsigned_in_range _ s)) | _ => lia end.

Lemma smear_walk : forall regs mem rom,
  2 ^ 46 <= bv_unsigned (getr regs 10%bv) < 2 ^ 47 ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom) (mkst regs' (Z_to_bv 64 (p + 112)) mem rom)
    /\ getr regs' 10%bv = Z_to_bv 64 (2 ^ 47 - 1)
    /\ getr regs' 11%bv = Z_to_bv 64 0x5555555555555555 /\ getr regs' 12%bv = Z_to_bv 64 0x3333333333333333
    /\ getr regs' 13%bv = Z_to_bv 64 0x0f0f0f0f0f0f0f0f /\ getr regs' 14%bv = Z_to_bv 64 0x0101010101010101
    /\ getr regs' 15%bv = Z_to_bv 64 0x7fff
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom Hx.
  set (x := bv_unsigned (getr regs 10%bv)) in *.
  destruct (smear_top x Hx) as [S32 S16].
  eexists. split.
  - replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 4 * Z.of_nat 0)) by (f_equal; lia).
    one 0%nat SD0 step_srli. one 1%nat SD1 step_lui. one 2%nat SD2 step_lui. one 3%nat SD3 step_lui. one 4%nat SD4 step_lui.
    one 5%nat SD5 step_or. one 6%nat SD6 step_addiw. one 7%nat SD7 step_addiw. one 8%nat SD8 step_addiw. one 9%nat SD9 step_addiw.
    one 10%nat SD10 step_srli. one 11%nat SD11 step_or. one 12%nat SD12 step_slli. one 13%nat SD13 step_add.
    one 14%nat SD14 step_slli. one 15%nat SD15 step_add. one 16%nat SD16 step_slli. one 17%nat SD17 step_add.
    one 18%nat SD18 step_slli. one 19%nat SD19 step_add. one 20%nat SD20 step_srli. one 21%nat SD21 step_or.
    one 22%nat SD22 step_srli. one 23%nat SD23 step_or. one 24%nat SD24 step_srli. one 25%nat SD25 step_or.
    one 26%nat SD26 step_srli. one 27%nat SD27 step_or.
    replace (p + 4 * Z.of_nat 28) with (p + 112) by lia. apply mst_refl.
  - gr. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + apply bv_eq. change (bv_unsigned (Z_to_bv 64 (2 ^ 47 - 1))) with (2 ^ 47 - 1).
      repeat first [rewrite u_or | rewrite u_srli by nonneg_sh]. fold x. lit_sh. unfold sm in S32. rewrite S32. reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + apply bv_eq. change (bv_unsigned (Z_to_bv 64 0x7fff)) with (2 ^ 15 - 1). repeat first [rewrite u_or | rewrite u_srli by nonneg_sh]. fold x. lit_sh. unfold sm in S16. rewrite S16. reflexivity.
    + intros r H10 H11 H12 H13 H14 H15. rewrite !getr_other by assumption. reflexivity.
Qed.
End Walk.

Import AX2. Import AX2S. Import AP. Import APS.

Section Node.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Hypothesis XS_range : 0 <= x_sniff A /\ x_sniff A + 112 < 2 ^ 64.
Hypothesis XS_code : forall i, (i < 28)%nat -> fetch_word SEGS (Z_to_bv 64 (x_sniff A + 4 * Z.of_nat i)) = Some (sw i).

#[local] Notation CSOK := (APS.cs_ok SEGS A nx0 LIMIT SINV argH FS0).

Lemma sr_upd_nth : forall sr n e m, (n < length sr)%nat -> nth m (sr_upd sr n e) (ELit 0) = if Nat.eqb m n then e else nth m sr (ELit 0).
Proof.
  induction sr as [|x sr IH]; intros n e m Hn; [cbn in Hn; lia|].
  destruct n as [|n]; destruct m as [|m]; cbn [sr_upd nth Nat.eqb]; try reflexivity.
  apply IH. cbn in Hn. lia.
Qed.

Theorem node_x_sound_XSniff : APS.x_stmt SEGS A nx0 LIMIT SINV argH FS0 XSniff.
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_x, summary_smear in Hn.
  destruct (Z.eqb (pc cs) (x_sniff A)) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc. cbn [negb] in Hn.
  destruct (erange (kn cs) (reg cs 10)) as [[lo hi]|] eqn:Hr; [|discriminate].
  destruct (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool eqn:Hb; [|discriminate].
  apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
  set (sr' := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (s_regs (a_ss cs))
                10 (ELit (2 ^ 47 - 1))) 11 (ELit 0x5555555555555555)) 12 (ELit 0x3333333333333333))
                13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fff)).
  assert (Hcs : cs' = with_ss cs (mk_ss (x_sniff A + 0x70) sr' (s_know (a_ss cs)) (s_next (a_ss cs)))).
  { injection Hn as <-. reflexivity. }
  subst cs'. clear Hn.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (erange_sound SEGS E _ (kn cs) (reg cs 10) lo hi HK Hr) as Hx.
  assert (R10 : getr R 10%bv = edenot E (reg cs 10)).
  { rewrite (HR 10%bv). unfold sr_get. cbn. reflexivity. }
  set (H := hid A argH E cs model). set (MR := Mr A argH E cs model FULL).
  destruct (smear_walk SEGS (x_sniff A) XS_range XS_code R MR (seg_rom SEGS) ltac:(rewrite R10; lia))
    as (R' & Hms & V10 & V11 & V12 & V13 & V14 & V15 & Vo).
  unfold cfg_of. rewrite Hpc.
  apply (srz_msteps_restricted_T SEGS H (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) SEGS_wx (allowA A E cs)
           (mkst R (Z_to_bv 64 (x_sniff A)) FULL (seg_rom SEGS)) _ model T
           (lazy_cover_cs SEGS A nx0 LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) HULL_ok SINV argH FS0 0%nat E cs R FULL model HC)
           (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs)
           (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) Hms).
  intros model' Hinv' Hsame Hclean.
  set (FULL' := munrestrict H FULL MR).
  assert (Hmr' : Mr A argH E cs model FULL' = MR).
  { unfold Mr, FULL'. apply mrestrict_munrestrict_clean. intros a Ha. exact (Hclean a Ha). }
  specialize (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _))).
  unfold cfg_of, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
  replace (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (x_sniff A)) FULL (seg_rom SEGS)))
             (mkst R' (Z_to_bv 64 (x_sniff A + 112)) MR (seg_rom SEGS)))
    with (mkst R' (Z_to_bv 64 (x_sniff A + 0x70)) FULL' (seg_rom SEGS)) by reflexivity.
  apply Hk.
  - eapply (cs_ok_frame SEGS A nx0 LIMIT SINV argH SINV_frame FS0); [exact HC | exact Hsame | exact Hinv' | | reflexivity | | ].
    +
      cbn [mk_ss s_regs]. intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      * assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r. cbn [edenot]. apply getr_zero.
      * unfold sr'. rewrite !nth_sr_upd.
        destruct (Nat.eqb_spec (ridx r) 15) as [E15|N15]; [rewrite <- (ridx_roundtrip r), E15; exact V15|].
        destruct (Nat.eqb_spec (ridx r) 14) as [E14|N14]; [rewrite <- (ridx_roundtrip r), E14; exact V14|].
        destruct (Nat.eqb_spec (ridx r) 13) as [E13|N13]; [rewrite <- (ridx_roundtrip r), E13; exact V13|].
        destruct (Nat.eqb_spec (ridx r) 12) as [E12|N12]; [rewrite <- (ridx_roundtrip r), E12; exact V12|].
        destruct (Nat.eqb_spec (ridx r) 11) as [E11|N11]; [rewrite <- (ridx_roundtrip r), E11; exact V11|].
        destruct (Nat.eqb_spec (ridx r) 10) as [E10|N10]; [rewrite <- (ridx_roundtrip r), E10; exact V10|].
        rewrite Vo; [|intros X; subst r; apply N10; reflexivity | intros X; subst r; apply N11; reflexivity
                     | intros X; subst r; apply N12; reflexivity | intros X; subst r; apply N13; reflexivity
                     | intros X; subst r; apply N14; reflexivity | intros X; subst r; apply N15; reflexivity].
        rewrite (HR r). unfold sr_get. rewrite Hr0. reflexivity.
    + cbn [mk_ss s_know]. rewrite Hmr'. exact HK.
    + intros a Ha. unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
  - pose proof (same_but_materialized_frame _ _ Hsame) as Hfr. apply Hfr.
Qed.
End Node.
