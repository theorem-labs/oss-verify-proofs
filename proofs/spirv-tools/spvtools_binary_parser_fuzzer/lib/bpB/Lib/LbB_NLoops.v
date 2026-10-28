(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMem BCells BLFrame BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BllocRepX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Conv LbB_DStat LbB_NBr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumWalkTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).

Definition MAGIC10 : Z := 0xCCCCCCCCCCCCCCCD.
Definition MAGIC10_32 : Z := 0xffffffffcccccccd.

Lemma mulhu_Z : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  mul_div M_MULHU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y / 2 ^ 64).
Proof.
  intros x y Hx Hy. cbn [mul_div]. unfold bv_mulhuu. rewrite !u64_of_Z by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma div10_magic : forall x, 0 <= x < 2 ^ 64 -> x * MAGIC10 / 2 ^ 64 / 2 ^ 3 = x / 10.
Proof.
  intros x Hx. rewrite Z.div_div by lia. change (2 ^ 64 * 2 ^ 3) with (2 ^ 67).
  pose proof (Z.div_mod x 10 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hr.
  set (q := x / 10) in *. set (r := x mod 10) in *.
  assert (Hq : 0 <= q < 2 ^ 61) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  clearbody q r. subst x.
  symmetry. apply (Z.div_unique_pos _ _ q (2 * q + r * MAGIC10)); unfold MAGIC10; lia.
Qed.

Module NDig.
  Local Fixpoint ndig_f (n : nat) (v : Z) : Z :=
    match n with O => 0 | S n' => if v <? 10 then 1 else 1 + ndig_f n' (v / 10) end.
  Definition ndig (v : Z) : Z := ndig_f 20 v.
  Local Lemma ndig_f_S : forall n v, ndig_f (S n) v = (if v <? 10 then 1 else 1 + ndig_f n (v / 10)).
  Proof. reflexivity. Qed.
  Local Lemma ndig_f_0 : forall v, ndig_f 0 v = 0.
  Proof. reflexivity. Qed.
  #[global] Opaque ndig_f.
  Local Lemma ndig_f_bound : forall n v, 0 <= ndig_f n v <= Z.of_nat n.
  Proof.
    induction n as [|n IH]; intros v; [rewrite ndig_f_0; lia|].
    rewrite ndig_f_S, Nat2Z.inj_succ. pose proof (IH (v / 10)). destruct (v <? 10); lia.
  Qed.
  Local Lemma pow10_S : forall n, 10 ^ Z.of_nat (S n) = 10 * 10 ^ Z.of_nat n.
  Proof. intros n. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.
  Local Lemma ndig_f_stable : forall n v, 0 <= v < 10 ^ Z.of_nat (S n) -> ndig_f (S (S n)) v = ndig_f (S n) v.
  Proof.
    induction n as [|n IH]; intros v Hv.
    - rewrite !ndig_f_S, ndig_f_0. change (10 ^ Z.of_nat 1) with 10 in Hv. destruct (Z.ltb_spec v 10); [reflexivity | exfalso; lia].
    - rewrite pow10_S in Hv. rewrite (ndig_f_S (S (S n)) v), (ndig_f_S (S n) v). destruct (Z.ltb_spec v 10); [reflexivity|].
      rewrite IH; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma ndig_small : forall v, 0 <= v < 10 -> ndig v = 1.
  Proof. intros v Hv. unfold ndig. rewrite (ndig_f_S 19). destruct (Z.ltb_spec v 10); [reflexivity | exfalso; lia]. Qed.
  Local Lemma pow10_19 : 10 ^ Z.of_nat 19 = 10000000000000000000.
  Proof. reflexivity. Qed.
  Lemma ndig_step : forall v, 10 <= v < 2 ^ 64 -> ndig v = 1 + ndig (v / 10).
  Proof.
    intros v Hv. unfold ndig. rewrite (ndig_f_S 19). destruct (Z.ltb_spec v 10); [exfalso; lia|].
    rewrite (ndig_f_stable 18 (v / 10)); [reflexivity|]. rewrite pow10_19.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma ndig_range : forall v, 1 <= v < 2 ^ 64 -> 1 <= ndig v <= 20.
  Proof.
    intros v Hv. unfold ndig. pose proof (ndig_f_bound 19 (v / 10)) as B. cbn [Z.of_nat] in B. rewrite (ndig_f_S 19).
    generalize dependent (ndig_f 19 (v / 10)). intros k B. destruct (v <? 10); lia.
  Qed.
  Lemma ndig_le19 : forall v, 1 <= v < 10 ^ 19 -> ndig v <= 19.
  Proof.
    intros v Hv. unfold ndig. rewrite (ndig_f_stable 18 v) by (rewrite pow10_19; lia).
    pose proof (ndig_f_bound 19 v). cbn [Z.of_nat] in *. lia.
  Qed.
  Local Fixpoint nhex_f (n : nat) (v : Z) : Z :=
    match n with O => 0 | S n' => if v =? 0 then 0 else 1 + nhex_f n' (v / 16) end.
  Definition nhex (v : Z) : Z := nhex_f 16 v.
  Local Lemma nhex_f_S : forall n v, nhex_f (S n) v = (if v =? 0 then 0 else 1 + nhex_f n (v / 16)).
  Proof. reflexivity. Qed.
  Local Lemma nhex_f_0 : forall v, nhex_f 0 v = 0.
  Proof. reflexivity. Qed.
  #[global] Opaque nhex_f.
  Local Lemma nhex_f_bound : forall n v, 0 <= nhex_f n v <= Z.of_nat n.
  Proof.
    induction n as [|n IH]; intros v; [rewrite nhex_f_0; lia|].
    rewrite nhex_f_S, Nat2Z.inj_succ. pose proof (IH (v / 16)). destruct (v =? 0); lia.
  Qed.
  Local Lemma pow16_S : forall n, 16 ^ Z.of_nat (S n) = 16 * 16 ^ Z.of_nat n.
  Proof. intros n. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.
  Local Lemma nhex_f_stable : forall n v, 0 <= v < 16 ^ Z.of_nat n -> nhex_f (S n) v = nhex_f n v.
  Proof.
    induction n as [|n IH]; intros v Hv.
    - rewrite nhex_f_S, nhex_f_0. change (16 ^ Z.of_nat 0) with 1 in Hv. destruct (Z.eqb_spec v 0); [reflexivity | exfalso; lia].
    - rewrite pow16_S in Hv. rewrite (nhex_f_S (S n) v), (nhex_f_S n v). destruct (Z.eqb_spec v 0); [reflexivity|].
      rewrite IH; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Local Lemma pow16_15 : 16 ^ Z.of_nat 15 = 2 ^ 60.
  Proof. reflexivity. Qed.
  Lemma nhex_0 : nhex 0 = 0. Proof. reflexivity. Qed.
  Lemma nhex_step : forall v, 1 <= v < 2 ^ 64 -> nhex v = 1 + nhex (v / 16).
  Proof.
    intros v Hv. unfold nhex. rewrite (nhex_f_S 15). destruct (Z.eqb_spec v 0); [exfalso; lia|].
    rewrite (nhex_f_stable 15 (v / 16)); [reflexivity|]. rewrite pow16_15.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma nhex_range : forall v, 1 <= v < 2 ^ 64 -> 1 <= nhex v <= 16.
  Proof.
    intros v Hv. unfold nhex. pose proof (nhex_f_bound 15 (v / 16)) as B. cbn [Z.of_nat] in B. rewrite (nhex_f_S 15).
    generalize dependent (nhex_f 15 (v / 16)). intros k B. destruct (Z.eqb_spec v 0); lia.
  Qed.
  #[global] Opaque ndig nhex.
End NDig.
Import NDig.
Definition ndz (v : Z) : Z := if v =? 0 then 0 else ndig v.
Lemma ndz_range : forall v, 0 <= v < 2 ^ 64 -> 0 <= ndz v <= 20 /\ (ndz v = 0 <-> v = 0).
Proof. intros v Hv. unfold ndz. destruct (Z.eqb_spec v 0); [lia|]. pose proof (ndig_range v ltac:(lia)). lia. Qed.
Lemma ndz_le19 : forall v, 0 <= v <= 2 ^ 63 -> ndz v <= 19.
Proof.
  intros v Hv. unfold ndz. destruct (Z.eqb_spec v 0); [lia|]. apply ndig_le19.
  assert (2 ^ 63 < 10 ^ 19) by (cbn; lia). lia.
Qed.
Lemma nhex_range0 : forall v, 0 <= v < 2 ^ 64 -> 0 <= nhex v <= 16 /\ (nhex v = 0 <-> v = 0).
Proof. intros v Hv. destruct (Z.eq_dec v 0) as [->|]; [rewrite nhex_0; lia|]. pose proof (nhex_range v ltac:(lia)). lia. Qed.

Definition FMTU_LOOP : Z := 0x16eedc.
Definition FMTU_EXIT : Z := 0x16ef14.

Definition fmtu_kept : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma pow10_split : forall v k, 1 <= k -> 0 <= v -> v / 10 / 10 ^ (k - 1) = v / 10 ^ k.
Proof.
  intros v k Hk Hv. rewrite Z.div_div by lia. f_equal.
  replace k with (Z.succ (k - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. reflexivity.
Qed.

Section FmtU.
  Context {fx : FPState}.

  Lemma fmt_u_loop : forall (n : nat) v p lo R M,
    ndig v <= Z.of_nat n -> 10 <= v < 2 ^ 64 ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 p -> getr R 14%bv = Z_to_bv 64 10 ->
    getr R 15%bv = Z_to_bv 64 MAGIC10_32 -> getr R 16%bv = Z_to_bv 64 99 ->
    2 ^ 16 <= lo -> ndig v <= p - lo -> p < 2 ^ 47 -> mdef M lo (p - lo) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 FMTU_LOOP) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 FMTU_EXIT) M' (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 (v / 10 ^ (ndig v - 1))
      /\ 1 <= v / 10 ^ (ndig v - 1) < 10
      /\ getr R' 23%bv = Z_to_bv 64 (p - (ndig v - 1)) /\ getr R' 11%bv = Z_to_bv 64 (p - (ndig v - 1))
      /\ (forall r, In r fmtu_kept -> getr R' r = getr R r)
      /\ stores_in (zwin (p - (ndig v - 1)) p) M M'
      /\ 2 <= ndig v <= 20.
  Proof.
    induction n as [|n IH]; intros v p lo R M Hn Hv H10 H11 H14 H15 H16 Hlo Hp Hphi HD.
    { exfalso. pose proof (ndig_range v ltac:(lia)). lia. }
    pose proof (ndig_range v ltac:(lia)) as Hnd. rewrite Nat2Z.inj_succ in Hn.
    pose proof (ndig_step v Hv) as Hst.
    pose proof (Z.div_pos v 10 ltac:(lia) ltac:(lia)) as Hq0.
    assert (Hq : 1 <= v / 10 < 2 ^ 64) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (ndig_range (v / 10) Hq) as Hndq.
    set (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M [KWr (SA (EVar 11) (-1)) (ELit 1); KRange (EVar 11) (2 ^ 16 + 1) (2 ^ 47); KRange (EVar 10) 10 (2 ^ 64 - 1);
                                  KRange (EVar 14) 10 10; KRange (EVar 15) MAGIC10_32 MAGIC10_32; KRange (EVar 16) 99 99]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ p (-1) 1); [evs; exact H11 | lia | lia | lia | lia | eapply mdef_sub; [exact HD | lia | lia]].
      - krv H11. - krv H10. - krv H14. - unfold MAGIC10_32 in *; krv H15. - krv H16. }
    assert (A10 : forall R', getr R' 10%bv = edenot E (EAlu ALU_SRL (EMd M_MULHU (EVar 10) (ELit 14757395258967641293)) (ELit 3)) ->
                             getr R' 10%bv = Z_to_bv 64 (v / 10)).
    { intros R' ->. cbn [edenot]. evs. regsub. change 14757395258967641293 with MAGIC10.
      rewrite mulhu_Z by (unfold MAGIC10; lia).
      assert (0 <= v * MAGIC10 / 2 ^ 64 < 2 ^ 64).
      { split; [apply Z.div_pos; unfold MAGIC10; lia | apply Z.div_lt_upper_bound; unfold MAGIC10; lia]. }
      rewrite alu_Z by lia. cbn [zar]. change (2 ^ (3 mod 64)) with (2 ^ 3). rewrite div10_magic by lia. reflexivity. }
    destruct (Z.lt_ge_cases v 100) as [Hsmall | Hbig].
    -
      xrun_at HR HK fx FMTU_LOOP (seg_rom SEGS) 40%nat [FMTU_LOOP; FMTU_EXIT] (SCR [false] [] []) 40%N.
      { scs_auto. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite v_addi_Z in Hms by lia.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      assert (Hq10 : v / 10 < 10) by (apply Z.div_lt_upper_bound; lia).
      rewrite (ndig_small (v / 10)) in Hst by lia.
      exists R', M1. split; [exact Hms|].
      rewrite Hst. change (1 + 1 - 1) with 1. change (10 ^ 1) with 10.
      rreg HR' (10%bv : reg) X10. apply A10 in X10.
      regval HR' (23%bv : reg) (p - 1) X23. regval HR' (11%bv : reg) (p - 1) X11.
      split; [exact X10|]. split; [lia|]. split; [exact X23|]. split; [exact X11|].
      split; [exact (syms_id_sound R [] _ R' fmtu_kept HR' eq_refl)|]. split; [|lia].
      subst M1. apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia].
    - xrun_at HR HK fx FMTU_LOOP (seg_rom SEGS) 40%nat [FMTU_LOOP; FMTU_EXIT] (SCR [true] [] []) 40%N.
      { scs_auto. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite v_addi_Z in Hms by lia.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      assert (Hq10 : 10 <= v / 10) by (apply Z.div_le_lower_bound; lia).
      rreg HR' (10%bv : reg) X10. apply A10 in X10.
      regval HR' (11%bv : reg) (p - 1) X11.
      pose proof (syms_id_sound R [] _ R' fmtu_kept HR' eq_refl) as KP. cbv beta in KP.
      destruct (IH (v / 10) (p - 1) lo R' M1) as (R2 & M2 & Hms2 & Y10 & Yld & Y23 & Y11 & YK & YS & Ynd);
        [lia | lia | exact X10 | exact X11 | rewrite (KP 14%bv) by inl; exact H14 | rewrite (KP 15%bv) by inl; exact H15
        | rewrite (KP 16%bv) by inl; exact H16 | lia | lia | lia | subst M1; apply mdef_wbytes; eapply mdef_sub; [exact HD | lia | lia] |].
      exists R2, M2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
      rewrite Hst in *. replace (1 + ndig (v / 10) - 1) with (ndig (v / 10)) in * by lia.
      rewrite pow10_split in Y10, Yld by lia.
      split; [exact Y10|]. split; [lia|]. split; [rewrite Y23; f_equal; lia|]. split; [rewrite Y11; f_equal; lia|].
      split; [intros r Hr; rewrite (YK r Hr); exact (KP r Hr)|]. split; [|lia].
      apply (stores_in_trans _ _ M1).
        + subst M1. apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia].
        + eapply stores_in_weaken; [exact YS | intros a Ha; unfold zwin in *; lia].
  Qed.
End FmtU.

Definition FMTU_ENTRY : Z := 0x16eecc.
Definition IFMT_TAIL : Z := 0x16ef2c.
Definition fmtu_kept2 : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma kimg_ro : forall E M, mem_inv asegs M -> kentry_ok SEGS E M (KImg 0x10000 0x17e000).
Proof. intros E M ROC. apply LbB_NBr.kimg_ro. exact ROC. Qed.

Section FmtU2.
  Context {fx : FPState}.

  Lemma fmt_u_spec : forall v sp (a7 : word) R M,
    0 <= v < 2 ^ 64 ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 2%bv = Z_to_bv 64 sp -> getr R 14%bv = Z_to_bv 64 10 -> getr R 17%bv = a7 ->
    fld SEGS M (sp + 40) 8 MAGIC10_32 ->
    2 ^ 16 <= sp -> sp mod 8 = 0 -> sp + 176 < 2 ^ 47 -> mdef M sp 176 ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 FMTU_ENTRY) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 IFMT_TAIL) M' (seg_rom SEGS))
      /\ getr R' 23%bv = Z_to_bv 64 (sp + 176 - ndz v)
      /\ (forall r, In r fmtu_kept2 -> getr R' r = getr R r)
      /\ stores_in (fun a => zwin (sp + 176 - ndz v) (sp + 176) a \/ zwin sp (sp + 8) a) M M'
      /\ fld SEGS M' sp 8 (bv_unsigned a7)
      /\ 0 <= ndz v <= 20 /\ (ndz v = 0 <-> v = 0).
  Proof.
    intros v sp a7 R M Hv H10 H2 H14 H17 F40 Hlo Hal Hhi HD.
    pose proof (ndz_range v Hv) as (Hnz & Hz0).
    set (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HKof : forall lo hi, lo <= v <= hi ->
              know_ok SEGS E M [KWr (SA (EVar 2) 0) (ELit 176); KRange (EVar 2) (2 ^ 16) (2 ^ 47 - 176); KRange (EVar 10) lo hi;
                               KRange (EVar 14) 10 10; KWord (SA (EVar 2) 40) (N.to_nat 8) (ELit MAGIC10_32); KAlign (EVar 2) 8]).
    { intros lo hi Hlh. repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ sp 0 176); [evs; exact H2 | lia | lia | lia | lia | rewrite Z.add_0_r; exact HD].
      - krv H2. - krv H10. - krv H14. - unfold MAGIC10_32 in *; kwv F40 H2.
      - eapply kalign_var; [evs; exact H2 | lia | lia | exact Hal]. }
    destruct (Z.eq_dec v 0) as [Hv0 | Hv0].
    -
      replace (ndz v) with 0 in * by (unfold ndz; subst v; reflexivity). pose proof (HKof 0 0 ltac:(lia)) as HK.
      xrun_at HR HK fx FMTU_ENTRY (seg_rom SEGS) 40%nat [IFMT_TAIL; FMTU_LOOP] (SCR [] [] []) 40%N.
      { scs_auto. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite v_addi_Z in Hms by lia.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      exists R', M1. split; [exact Hms|].
      regval HR' (23%bv : reg) (sp + 176 - 0) X23. split; [exact X23|].
      split; [exact (syms_id_sound R [] _ R' fmtu_kept2 HR' eq_refl)|].
      split; [subst M1; apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia]|].
      split; [|lia]. subst M1. unfold fld. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      apply rdn_wbytes_hit8. rewrite u64_of_Z by lia; lia.
    - pose proof (ndig_range v ltac:(lia)) as Hnd.
      replace (ndz v) with (ndig v) in * by (unfold ndz; destruct (Z.eqb_spec v 0); [lia | reflexivity]).
      destruct (Z.lt_ge_cases v 10) as [Hv10 | Hv10].
      +
        rewrite (ndig_small v) in * by lia. pose proof (HKof 1 9 ltac:(lia)) as HK.
        xrun_at HR HK fx FMTU_ENTRY (seg_rom SEGS) 40%nat [IFMT_TAIL; FMTU_LOOP] (SCR [] [] []) 40%N.
        { scs_auto. }
        unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite !v_addi_Z in Hms by lia.
        lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
        exists R', M1. split; [exact Hms|].
        regval HR' (23%bv : reg) (sp + 176 - 1) X23. split; [exact X23|].
        split; [exact (syms_id_sound R [] _ R' fmtu_kept2 HR' eq_refl)|].
        split; [subst M1; eapply stores_in_wbytes_more; [apply stores_in_wbytes|..]; try lia; cbn; try lia; intros x Hx; cbn in Hx; unfold zwin; lia|].
        split; [|lia]. subst M1. unfold fld. rewrite Z_to_bv_bv_unsigned.
        rewrite SumWalkTac.rdn_wbytes_out_Z by peel_len. rewrite Z.add_0_r. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia; lia.
      +
        pose proof (HKof 10 (2 ^ 64 - 1) ltac:(lia)) as HK.
        xrun_at HR HK fx FMTU_ENTRY (seg_rom SEGS) 40%nat [IFMT_TAIL; FMTU_LOOP] (SCR [] [] []) 40%N.
        { scs_auto. }
        rename R' into R1. rename HR' into HR1. rename Hms into Hms1.
        regval HR1 (10%bv : reg) v X10. regval HR1 (11%bv : reg) (sp + 176) X11. regval HR1 (14%bv : reg) 10 X14.
        regval HR1 (15%bv : reg) MAGIC10_32 X15. regval HR1 (16%bv : reg) 99 X16.
        pose proof (syms_id_sound R [] _ R1 [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv HR1 eq_refl) as KP1. cbv beta in KP1.
        destruct (fmt_u_loop (Z.to_nat (ndig v)) v (sp + 176) sp R1 M) as (R2 & M2 & Hms2 & Y10 & Yld & Y23 & Y11 & YK & YS & Ynd);
          [rewrite Z2Nat.id by lia; lia | lia | exact X10 | exact X11 | exact X14 | exact X15 | exact X16 | lia | lia | lia | replace (sp + 176 - sp) with 176 by lia; exact HD |].

        set (E3 := Eseed R2 []).
        assert (HR3 : regs_ok E3 sr_id R2) by (apply regs_ok_seed).
        assert (R3_2 : getr R2 2%bv = Z_to_bv 64 sp) by (rewrite (YK 2%bv) by inl; rewrite (KP1 2%bv) by inl; exact H2).
        assert (R3_17 : getr R2 17%bv = a7) by (rewrite (YK 17%bv) by inl; rewrite (KP1 17%bv) by inl; exact H17).
        assert (HK3 : know_ok SEGS E3 M2 [KWr (SA (EVar 2) 0) (ELit 176); KRange (EVar 2) (2 ^ 16) (2 ^ 47 - 176);
                        KRange (EVar 10) 1 9; KWr (SA (EVar 23) (-1)) (ELit 1); KRange (EVar 23) (2 ^ 16 + 1) (2 ^ 47); KAlign (EVar 2) 8]).
        { repeat apply Forall_cons; try apply Forall_nil.
          - eapply (kwr_of_mdef _ _ _ _ sp 0 176); [evs; exact R3_2 | lia | lia | lia | lia | rewrite Z.add_0_r; eapply stores_in_mdef; [exact YS | exact HD]].
          - krv R3_2. - krv Y10.
          - eapply (kwr_of_mdef _ _ _ _ (sp + 176 - (ndig v - 1)) (-1) 1); [evs; exact Y23 | lia | lia | lia | lia | eapply mdef_sub; [eapply stores_in_mdef; [exact YS | exact HD] | lia | lia]].
          - krv Y23.
          - eapply kalign_var; [evs; exact R3_2 | lia | lia | exact Hal]. }
        xrun_at HR3 HK3 fx FMTU_EXIT (seg_rom SEGS) 40%nat [IFMT_TAIL; FMTU_LOOP] (SCR [] [] []) 40%N.
        { scs_auto. }
        unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite !v_addi_Z in Hms by lia.
        lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M3 := m) in Hms end.
        exists R', M3. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms]]|].
        regval HR' (23%bv : reg) (sp + 176 - ndig v) X23. split; [exact X23|].
        pose proof (syms_id_sound R2 [] _ R' fmtu_kept2 HR' eq_refl) as KP3. cbv beta in KP3.
        split; [intros r Hr; rewrite (KP3 r Hr); rewrite (YK r) by (revert Hr; clear; cbn; tauto); apply KP1; revert Hr; clear; cbn; tauto|].
        split.
        { apply (stores_in_trans _ _ M2).
          - eapply stores_in_weaken; [exact YS | intros a Ha; unfold zwin in *; lia].
          - subst M3. eapply stores_in_wbytes_more; [apply stores_in_wbytes|..]; try lia; cbn; try lia; intros x Hx; cbn in Hx; unfold zwin; lia. }
        split; [|lia]. subst M3. unfold fld. rewrite Z_to_bv_bv_unsigned.
        rewrite SumWalkTac.rdn_wbytes_out_Z by peel_len. rewrite Z.add_0_r. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia; lia.
  Qed.
End FmtU2.

Definition XDIGITS : Z := 0x6ae00.
Definition FMTX_ENTRY : Z := 0x16ed78.
Definition FMTX_LOOP : Z := 0x16ed90.
Definition FMTX_EXIT : Z := 0x16edb8.
Definition PREFIX_STR : Z := 0x10e1b.
Definition fmtx_kept : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition fmtx_kept2 : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma xdigits_rdn : forall M, mem_inv asegs M -> exists bs16, rdn SEGS M (Z_to_bv 64 XDIGITS) 16 = Some bs16.
Proof.
  intros M ROC.
  destruct (rdn_img SEGS M 16 (Z_to_bv 64 XDIGITS) [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 65; 66; 67; 68; 69; 70]) as (bs & Hbs & _);
    [rewrite u64_of_Z by (unfold XDIGITS; lia); unfold XDIGITS; lia | | vm_compute; reflexivity | exists bs; exact Hbs].
  intros j Hj. rewrite u64_of_Z by (unfold XDIGITS; lia). apply (LbB_NBr.ro_none M _ ROC). unfold XDIGITS. lia.
Qed.

Lemma land_15 : forall k, Z.land k 15 = k mod 16.
Proof. intros k. change 15 with (2 ^ 4 - 1). rewrite land_ones by lia. reflexivity. Qed.

Section FmtX.
  Context {fx : FPState}.

  Lemma fmt_x_loop : forall (n : nat) v p lo lower R M bs16,
    nhex v <= Z.of_nat n -> 1 <= v < 2 ^ 64 ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 23%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 lower -> 0 <= lower < 256 ->
    2 ^ 32 <= lo -> nhex v <= p - lo -> p < 2 ^ 47 -> mdef M lo (p - lo) ->
    rdn SEGS M (Z_to_bv 64 XDIGITS) 16 = Some bs16 ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 FMTX_LOOP) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 FMTX_EXIT) M' (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 0
      /\ getr R' 23%bv = Z_to_bv 64 (p - nhex v)
      /\ (forall r, In r fmtx_kept -> getr R' r = getr R r)
      /\ stores_in (zwin (p - nhex v) p) M M'
      /\ 1 <= nhex v <= 16.
  Proof.
    induction n as [|n IH]; intros v p lo lower R M bs16 Hn Hv H10 H23 H11 Hlower Hlo Hp Hphi HD X16.
    { exfalso. pose proof (nhex_range v ltac:(lia)). lia. }
    pose proof (nhex_range v ltac:(lia)) as Hnh. rewrite Nat2Z.inj_succ in Hn.
    pose proof (nhex_step v Hv) as Hst.
    pose proof (Z.mod_pos_bound v 16 ltac:(lia)) as Hm16.
    pose proof (rdn_byte_Z SEGS M XDIGITS 16 bs16 (Z.to_nat (v mod 16)) X16 ltac:(lia) ltac:(unfold XDIGITS; lia) ltac:(unfold XDIGITS; lia)) as RD1.
    rewrite Z2Nat.id in RD1 by lia. set (b := nth (Z.to_nat (v mod 16)) bs16 (Z_to_bv 8 0)) in RD1.
    pose proof (u8_range b) as Hb.
    set (E := Eseed R [Z_to_bv 64 (bv_unsigned b)]).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HKof : forall lo' hi', lo' <= v <= hi' ->
      know_ok SEGS E M [KWr (SA (EVar 23) (-1)) (ELit 1); KRange (EVar 23) (2 ^ 32 + 1) (2 ^ 47); KRange (EVar 10) lo' hi'; KRange (EVar 11) 0 255]).
    { intros lo' hi' Hlh. repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ p (-1) 1); [evs; exact H23 | lia | lia | lia | lia | eapply mdef_sub; [exact HD | lia | lia]].
      - krv H23. - krv H10. - krv H11. }
    assert (SCRD : sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_AND (EVar 10) (ELit 15)) 437760) 1 false (EVar 32))).
    { cbn [sc_denot]. exists [b]. split.
      - unfold adenot. cbn [a_base a_off edenot]. evs. regsub. rewrite alu_Z by lia. cbn [zar]. rewrite land_15, v_addi_Z by lia.
        replace (v mod 16 + 437760) with (XDIGITS + v mod 16) by (unfold XDIGITS; lia). exact RD1.
      - evs. rewrite extz_false. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. }
    destruct (Z.lt_ge_cases v 16) as [Hsmall | Hbig].
    -
      pose proof (HKof 1 15 ltac:(lia)) as HK.
      xrun_at HR HK fx FMTX_LOOP (seg_rom SEGS) 40%nat [FMTX_LOOP; FMTX_EXIT] (SCR [false] [] []) 32%N.
      { repeat apply Forall_cons; try apply Forall_nil. exact SCRD. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite v_addi_Z in Hms by lia.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      assert (Hq : v / 16 = 0) by (apply Z.div_small; lia).
      rewrite Hq, nhex_0 in Hst.
      exists R', M1. split; [exact Hms|].
      regval HR' (10%bv : reg) 0 X10'.
      split; [exact X10'|].
      regval HR' (23%bv : reg) (p - 1) X23. split; [rewrite X23; f_equal; lia|].
      split; [exact (syms_id_sound R _ _ R' fmtx_kept HR' eq_refl)|]. split; [|lia].
      subst M1. apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia].
    - pose proof (HKof 16 (2 ^ 64 - 1) ltac:(lia)) as HK.
      xrun_at HR HK fx FMTX_LOOP (seg_rom SEGS) 40%nat [FMTX_LOOP; FMTX_EXIT] (SCR [true] [] []) 32%N.
      { repeat apply Forall_cons; try apply Forall_nil. exact SCRD. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite v_addi_Z in Hms by lia.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      assert (Hq : 1 <= v / 16 < 2 ^ 64) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
      pose proof (nhex_range (v / 16) Hq) as Hnhq.
      rreg HR' (10%bv : reg) X10'. revert X10'. regsub. znorm. change (2 ^ (4 mod 64)) with 16. intros X10'.
      regval HR' (23%bv : reg) (p - 1) X23.
      pose proof (syms_id_sound R _ _ R' fmtx_kept HR' eq_refl) as KP. cbv beta in KP.
      assert (X16' : rdn SEGS M1 (Z_to_bv 64 XDIGITS) 16 = Some bs16).
      { rewrite <- X16. subst M1. apply SumWalkTac.rdn_wbytes_out_Z. cbn. unfold XDIGITS. lia. }
      destruct (IH (v / 16) (p - 1) lo lower R' M1 bs16) as (R2 & M2 & Hms2 & Y10 & Y23 & YK & YS & Ynd);
        [lia | lia | exact X10' | exact X23 | rewrite (KP 11%bv) by inl; exact H11 | lia | lia | lia | lia
        | subst M1; apply mdef_wbytes; eapply mdef_sub; [exact HD | lia | lia] | exact X16' |].
      exists R2, M2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
      split; [exact Y10|]. split; [rewrite Y23; f_equal; lia|].
      split; [intros r Hr; rewrite (YK r Hr); exact (KP r Hr)|]. split; [|lia].
      apply (stores_in_trans _ _ M1).
      + subst M1. apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia].
      + eapply stores_in_weaken; [exact YS | intros a Ha; unfold zwin in *; lia].
  Qed.

  Lemma fmt_x_spec : forall v sp R M,
    0 <= v < 2 ^ 64 ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 16%bv = Z_to_bv 64 120 -> getr R 24%bv = Z_to_bv 64 0 ->
    fld SEGS M (sp + 112) 8 v -> mem_inv asegs M ->
    2 ^ 32 <= sp -> sp mod 8 = 0 -> sp + 176 < 2 ^ 47 -> mdef M sp 176 ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 FMTX_ENTRY) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 IFMT_TAIL) M' (seg_rom SEGS))
      /\ getr R' 23%bv = Z_to_bv 64 (sp + 176 - nhex v)
      /\ (forall r, In r fmtx_kept2 -> getr R' r = getr R r)
      /\ stores_in (fun a => zwin (sp + 176 - nhex v) (sp + 176) a \/ zwin sp (sp + 8) a \/ zwin (sp + 24) (sp + 32) a) M M'
      /\ fld SEGS M' sp 8 PREFIX_STR /\ fld SEGS M' (sp + 24) 8 0
      /\ 0 <= nhex v <= 16 /\ (nhex v = 0 <-> v = 0).
  Proof.
    intros v sp R M Hv H2 H16 H24 F112 ROC Hlo Hal Hhi HD.
    pose proof (nhex_range0 v Hv) as (Hnz & Hz0).
    destruct (xdigits_rdn M ROC) as (bs16 & X16).
    set (E := Eseed R [Z_to_bv 64 v]).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HKof : forall lo hi, lo <= v <= hi ->
              know_ok SEGS E M [KWr (SA (EVar 2) 0) (ELit 176); KRange (EVar 2) (2 ^ 32) (2 ^ 47 - 176);
                               KRange (EVar 16) 120 120; KRange (EVar 24) 0 0; KWord (SA (EVar 2) 112) (N.to_nat 8) (EVar 32); KRange (EVar 32) lo hi;
                               KAlign (EVar 2) 8; KImg 0x10000 0x17e000]).
    { intros lo hi Hlh. repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ sp 0 176); [evs; exact H2 | lia | lia | lia | lia | rewrite Z.add_0_r; exact HD].
      - krv H2. - krv H16. - krv H24. - kwv F112 H2.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; exact H2 | lia | lia | exact Hal].
      - apply kimg_ro. exact ROC. }
    destruct (Z.eq_dec v 0) as [Hv0 | Hv0].
    -
      pose proof (HKof 0 0 ltac:(lia)) as HK. rewrite Hv0, nhex_0 in *.
      xrun_at HR HK fx FMTX_ENTRY (seg_rom SEGS) 40%nat [IFMT_TAIL; FMTX_LOOP] (SCR [] [] []) 40%N.
      { scs_auto. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite !v_addi_Z in Hms by lia.
      revert Hms. znorm. intros Hms.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      exists R', M1. split; [exact Hms|].
      regval HR' (23%bv : reg) (sp + 176 - 0) X23. split; [exact X23|].
      split; [exact (syms_id_sound R _ _ R' fmtx_kept2 HR' eq_refl)|].
      split; [subst M1; stores_tower|].
      split; [unfold fld; subst M1; peel|]. split; [unfold fld; subst M1; peel|]. lia.
    - pose proof (nhex_range v ltac:(lia)) as Hnh.
      pose proof (HKof 1 (2 ^ 64 - 1) ltac:(lia)) as HK.
      xrun_at HR HK fx FMTX_ENTRY (seg_rom SEGS) 40%nat [IFMT_TAIL; FMTX_LOOP] (SCR [] [] []) 40%N.
      { scs_auto. }
      rename R' into R1. rename HR' into HR1. rename Hms into Hms1.
      regval HR1 (10%bv : reg) v X10. regval HR1 (23%bv : reg) (sp + 176) X23. regval HR1 (11%bv : reg) 32 X11.
      pose proof (syms_id_sound R _ _ R1 [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv HR1 eq_refl) as KP1. cbv beta in KP1.
      destruct (fmt_x_loop (Z.to_nat (nhex v)) v (sp + 176) sp 32 R1 M bs16) as (R2 & M2 & Hms2 & Y10 & Y23 & YK & YS & Ynd);
        [rewrite Z2Nat.id by lia; lia | lia | exact X10 | exact X23 | exact X11 | lia | lia | lia | lia | replace (sp + 176 - sp) with 176 by lia; exact HD | exact X16 |].
      set (E3 := Eseed R2 []).
      assert (HR3 : regs_ok E3 sr_id R2) by (apply regs_ok_seed).
      assert (R3_2 : getr R2 2%bv = Z_to_bv 64 sp) by (rewrite (YK 2%bv) by inl; rewrite (KP1 2%bv) by inl; exact H2).
      assert (R3_24 : getr R2 24%bv = Z_to_bv 64 0) by (rewrite (YK 24%bv) by inl; rewrite (KP1 24%bv) by inl; exact H24).
      assert (R3_14 : getr R2 14%bv = Z_to_bv 64 PREFIX_STR) by (rewrite (YK 14%bv) by inl; regval HR1 (14%bv : reg) PREFIX_STR X14; exact X14).
      assert (HK3 : know_ok SEGS E3 M2 [KWr (SA (EVar 2) 0) (ELit 176); KRange (EVar 2) (2 ^ 32) (2 ^ 47 - 176); KRange (EVar 24) 0 0; KAlign (EVar 2) 8]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply (kwr_of_mdef _ _ _ _ sp 0 176); [evs; exact R3_2 | lia | lia | lia | lia | rewrite Z.add_0_r; eapply stores_in_mdef; [exact YS | exact HD]].
        - krv R3_2. - krv R3_24.
        - eapply kalign_var; [evs; exact R3_2 | lia | lia | exact Hal]. }
      xrun_at HR3 HK3 fx FMTX_EXIT (seg_rom SEGS) 40%nat [IFMT_TAIL; FMTX_LOOP] (SCR [] [] []) 40%N.
      { scs_auto. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite !v_addi_Z in Hms by lia.
      revert Hms. znorm. intros Hms.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M3 := m) in Hms end.
      exists R', M3. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms]]|].
      regval HR' (23%bv : reg) (sp + 176 - nhex v) X23'. split; [exact X23'|].
      pose proof (syms_id_sound R2 [] _ R' fmtx_kept2 HR' eq_refl) as KP3. cbv beta in KP3.
      split; [intros r Hr; rewrite (KP3 r Hr); rewrite (YK r) by (revert Hr; clear; cbn; tauto); apply KP1; revert Hr; clear; cbn; tauto|].
      split.
      { apply (stores_in_trans _ _ M2).
        - eapply stores_in_weaken; [exact YS | intros a Ha; unfold zwin in *; lia].
        - subst M3. stores_tower. }
      split; [unfold fld; subst M3; peel|]. split; [unfold fld; subst M3; peel|]. lia.
  Qed.
End FmtX.

Definition WIDEN_ENTRY : Z := 0x14dc7c.
Definition WIDEN_LOOP : Z := 0x14dc84.
Definition WIDEN_RET : Z := 0x14dc98.
Definition widen_kept : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Section Widen.
  Context {fx : FPState}.

  Lemma widen_loop : forall (k : nat) cur fin d R M,
    fin - cur = Z.of_nat k -> cur < fin ->
    getr R 10%bv = Z_to_bv 64 cur -> getr R 12%bv = Z_to_bv 64 fin -> getr R 13%bv = Z_to_bv 64 d ->
    2 ^ 32 <= cur -> fin < 2 ^ 47 -> 2 ^ 32 <= d -> d + (fin - cur) < 2 ^ 47 ->
    mdef M cur (fin - cur) -> mdef M d (fin - cur) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 WIDEN_LOOP) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 WIDEN_RET) M' (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 fin /\ getr R' 13%bv = Z_to_bv 64 (d + (fin - cur))
      /\ (forall r, In r widen_kept -> getr R' r = getr R r)
      /\ stores_in (zwin d (d + (fin - cur))) M M'.
  Proof.
    induction k as [|k IH]; intros cur fin d R M Hk Hlt H10 H12 H13 Hc Hf Hd Hdf HDs HDd; [lia|].
    rewrite Nat2Z.inj_succ in Hk.
    destruct (mdef_rdn SEGS M cur (fin - cur) 0 1 HDs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bs & RD & Hlen).
    destruct bs as [|b [|]]; try discriminate Hlen. rewrite Z.add_0_r in RD.
    pose proof (u8_range b) as Hb.
    set (E := Eseed R [Z_to_bv 64 (bv_unsigned b)]).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M [KWr (SA (EVar 13) 0) (ELit 1); KRange (EVar 13) (2 ^ 32) (2 ^ 47 - 2); KRange (EVar 10) (2 ^ 32) (2 ^ 47 - 2);
                                  KRange (EVar 12) (2 ^ 32) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ d 0 1); [evs; exact H13 | lia | lia | lia | lia | eapply mdef_sub; [exact HDd | lia | lia]].
      - krv H13. - krv H10. - krv H12. }
    assert (SCRD : sc_denot SEGS M E (SCReadBase (SA (EVar 10) 0) 1 false (EVar 32))).
    { cbn [sc_denot]. exists [b]. split.
      - unfold adenot. cbn [a_base a_off edenot]. evs. regsub. rewrite v_addi_Z, Z.add_0_r by lia. exact RD.
      - evs. rewrite extz_false. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. }
    destruct (Z.eq_dec (cur + 1) fin) as [Hlast | Hmore].
    - xrun_at HR HK fx WIDEN_LOOP (seg_rom SEGS) 40%nat [WIDEN_LOOP; WIDEN_RET] (SCR [false] [] []) 32%N.
      { repeat apply Forall_cons; try apply Forall_nil; [zbr_auto | exact SCRD]. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite !v_addi_Z, Z.add_0_r in Hms by lia.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      exists R', M1. split; [exact Hms|].
      regval HR' (10%bv : reg) fin X10. regval HR' (13%bv : reg) (d + (fin - cur)) X13.
      split; [exact X10|]. split; [exact X13|].
      split; [exact (syms_id_sound R _ _ R' widen_kept HR' eq_refl)|].
      subst M1. apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia].
    - xrun_at HR HK fx WIDEN_LOOP (seg_rom SEGS) 40%nat [WIDEN_LOOP; WIDEN_RET] (SCR [true] [] []) 32%N.
      { repeat apply Forall_cons; try apply Forall_nil; [zbr_auto | exact SCRD]. }
      unfold adenot in Hms. cbn [a_base a_off] in Hms. evs_in Hms. regsub_in Hms. rewrite !v_addi_Z, Z.add_0_r in Hms by lia.
      lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
      regval HR' (10%bv : reg) (cur + 1) X10. regval HR' (12%bv : reg) fin X12. regval HR' (13%bv : reg) (d + 1) X13.
      pose proof (syms_id_sound R _ _ R' widen_kept HR' eq_refl) as KP. cbv beta in KP.
      destruct (IH (cur + 1) fin (d + 1) R' M1) as (R2 & M2 & Hms2 & Y10 & Y13 & YK & YS);
        [lia | lia | exact X10 | exact X12 | exact X13 | lia | lia | lia | lia
        | subst M1; apply mdef_wbytes; eapply mdef_sub; [exact HDs | lia | lia]
        | subst M1; apply mdef_wbytes; eapply mdef_sub; [exact HDd | lia | lia] |].
      exists R2, M2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
      split; [exact Y10|]. split; [rewrite Y13; f_equal; lia|].
      split; [intros r Hr; rewrite (YK r Hr); exact (KP r Hr)|].
      apply (stores_in_trans _ _ M1).
      + subst M1. apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia].
      + eapply stores_in_weaken; [exact YS | intros a Ha; unfold zwin in *; lia].
  Qed.

  Lemma widen_copy : forall n src dst R M,
    0 <= n ->
    getr R 11%bv = Z_to_bv 64 src -> getr R 12%bv = Z_to_bv 64 (src + n) -> getr R 13%bv = Z_to_bv 64 dst ->
    2 ^ 32 <= src -> src + n < 2 ^ 47 -> 2 ^ 32 <= dst -> dst + n < 2 ^ 47 ->
    mdef M src n -> mdef M dst n ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 WIDEN_ENTRY) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 WIDEN_RET) M' (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 (src + n) /\ getr R' 13%bv = Z_to_bv 64 (dst + n)
      /\ (forall r, In r widen_kept -> getr R' r = getr R r)
      /\ stores_in (zwin dst (dst + n)) M M'.
  Proof.
    intros n src dst R M Hn H11 H12 H13 Hs Hsn Hd Hdn HDs HDd.
    set (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M [KRange (EVar 11) (2 ^ 32) (2 ^ 47); KRange (EVar 12) (2 ^ 32) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. - krv H11. - krv H12. }
    destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
    - subst n. rewrite !Z.add_0_r in *.
      xrun_at HR HK fx WIDEN_ENTRY (seg_rom SEGS) 40%nat [WIDEN_LOOP; WIDEN_RET] (SCR [true] [] []) 32%N.
      { scs_auto. }
      exists R', M. split; [exact Hms|].
      regval HR' (10%bv : reg) src X10. regval HR' (13%bv : reg) dst X13.
      split; [exact X10|]. split; [exact X13|].
      split; [exact (syms_id_sound R _ _ R' widen_kept HR' eq_refl)|]. apply stores_in_refl.
    - xrun_at HR HK fx WIDEN_ENTRY (seg_rom SEGS) 40%nat [WIDEN_LOOP; WIDEN_RET] (SCR [false] [] []) 32%N.
      { scs_auto. }
      regval HR' (10%bv : reg) src X10. regval HR' (12%bv : reg) (src + n) X12. regval HR' (13%bv : reg) dst X13.
      pose proof (syms_id_sound R _ _ R' widen_kept HR' eq_refl) as KP. cbv beta in KP.
      destruct (widen_loop (Z.to_nat n) src (src + n) dst R' M) as (R2 & M2 & Hms2 & Y10 & Y13 & YK & YS);
        [rewrite Z2Nat.id by lia; lia | lia | exact X10 | exact X12 | exact X13 | lia | lia | lia | lia
        | replace (src + n - src) with n by lia; exact HDs | replace (src + n - src) with n by lia; exact HDd |].
      exists R2, M2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
      split; [exact Y10|]. split; [rewrite Y13; f_equal; lia|].
      split; [intros r Hr; rewrite (YK r Hr); exact (KP r Hr)|].
      eapply stores_in_weaken; [exact YS | intros a Ha; unfold zwin in *; lia].
  Qed.
End Widen.
