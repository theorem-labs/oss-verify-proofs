(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg RefMemcpyLib.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanWMemcpy AsanSMat AsanWMat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Section MCWM.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HC : MCCode segs e.

Section LoopM.
Variable CL : list reg.
Hypothesis HCL : forall r, In r MC_CLOB -> In r CL.
Hypothesis HCL1 : ~ In 1 CL.
Variable model0 : Model.
Variable K : TSet.
Variable ms0 : machine_state.
Variables (dst src n : Z) (bs : list byte).
Hypothesis Hh0 : m_halted model0 = None.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Let L : list word := range_pages src (Z.to_nat n) ++ range_pages dst (Z.to_nat n).
Hypothesis Hbud : (vm_backing_used model0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps model0))%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms' m', MCRc CL ms0 ms' -> copied (ms_mem ms') (ms_mem ms0) dst n bs ->
  ms_pc_val ms' = rg ms0 1 -> matin model0 m' L -> realizes_cfg segs cfg (mkCfg ms' m') K.

Lemma mhalt : forall m, matin model0 m L -> m_halted m = None.
Proof. intros m Hm. rewrite (matin_halted _ _ _ Hm). exact Hh0. Qed.

Local Ltac mnext := let m' := fresh "mdl" in let H' := fresh "Hmn" in intros m' H';
  repeat match goal with
         | H : matin model0 ?x L |- _ => lazymatch x with m' => fail | _ => clear H end
         | H : m_halted ?x = None |- _ => lazymatch x with m' => fail | model0 => fail | _ => clear H end
         end;
  let Hm := fresh "Hm" in rename H' into Hm; let Hh := fresh "Hhm" in pose proof (mhalt m' Hm) as Hh.

Lemma Lbs : length bs = Z.to_nat n.
Proof. exact (rdn_length _ _ _ _ _ Hbs). Qed.

Lemma src_rd : forall m k' (k : Z) (c : nat), copied m (ms_mem ms0) dst k' bs -> (0 <= k' <= n)%Z ->
  (0 <= k)%Z -> (k + Z.of_nat c <= n)%Z ->
  rdn segs m (Z_to_bv 64 (src + k)) c = Some (firstn c (skipn (Z.to_nat k) bs)).
Proof.
  intros m k' k c Hc Hk' Hk Hkc.
  assert (E : rdn segs m (Z_to_bv 64 (src + k)) c = rdn segs (ms_mem ms0) (Z_to_bv 64 (src + k)) c).
  { apply rdn_ext; [rewrite bvu_z by lia; lia|].
    intros x Hx. rewrite bvu_z in Hx by lia. apply (proj2 (Hc x)). lia. }
  rewrite E.
  pose proof (SeqExec.rdn_skipn segs (ms_mem ms0) (Z.to_nat n) (Z_to_bv 64 src) bs (Z.to_nat k) Hbs ltac:(lia)) as Hs.
  unfold nat_to_word in Hs. rewrite zw_add, Z2Nat.id in Hs by lia.
  apply (SeqExec.rdn_firstn segs (ms_mem ms0) (Z.to_nat n - Z.to_nat k)); [exact Hs | lia].
Qed.

Lemma sok_sub : forall m k' (k : Z) (c : nat), copied m (ms_mem ms0) dst k' bs ->
  (0 <= k)%Z -> (k + Z.of_nat c <= n)%Z -> store_ok segs m (Z_to_bv 64 (dst + k)) c = true.
Proof.
  intros m k' k c Hc Hk Hkc.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (copied_grows _ _ _ _ _ Hc) | exact Hsok] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Lemma len4 : forall k, (0 <= k)%Z -> (k + 4 <= n)%Z -> length (firstn 4 (skipn (Z.to_nat k) bs)) = 4%nat.
Proof. intros k Hk Hkn. rewrite length_firstn, length_skipn, Lbs. lia. Qed.

Lemma mc_retm : forall S off m, matin model0 m L -> MCRc CL ms0 S -> ms_pc_val S = pcw e off ->
  fetch_word segs (pcw e off) = Some (Z_to_bv 32 0x00008067) ->
  copied (ms_mem S) (ms_mem ms0) dst n bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S off m Hm HS Hpc HF Hf. pose proof (mhalt m Hm) as Hhm.
  eapply rzc_acc; [ exact Hhm | exact (mcr_svc _ _ _ HS) | eapply wacc_Jalr; [ rewrite Hpc; exact HF | reflexivity | exact DC_3d0 ]
                  | apply acc_ok_nil | ].
  apply HK.
  - eapply MCR_setx; [exact HS | left; reflexivity | reflexivity | reflexivity].
  - exact Hf.
  - rewrite pc_setx. rewrite (mcr_regs _ _ _ HS 1) by exact HCL1. apply ret_even. exact Hra.
  - exact Hm.
Qed.

Ltac mcnorm := rgn; unfold w0; rewrite ?alu_add, ?zw_add, ?zw_add_sext; lits; rewrite ?Z.add_0_r, ?Z.add_0_l.
Ltac rwregs := repeat match goal with H : rg ?S ?r = _ |- context [rg ?S ?r] => rewrite H end.
Ltac inc_src := rwregs; mcnorm; apply incl_appl; apply range_pages_incl; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
                 rewrite ?Z2Nat.id by lia; lia.
Ltac inc_dst := rwregs; mcnorm; apply incl_appr; apply range_pages_incl; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
                 rewrite ?Z2Nat.id by lia; lia.
Ltac rd_src Hf := rewrite ?mem_setx; rgn; rwregs; mcnorm;
  first [ (eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]) | (eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]) ].

Lemma t1m : forall S k m, matin model0 m L -> MCRc CL ms0 S -> ms_pc_val S = pcw e 0x3f8 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> (0 <= k)%Z -> (k + 1 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 Hk Hkn Hf. pose proof (mhalt m Hm) as Hhm.

  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | exact (mcr_svc _ _ _ HS) | eapply wacc_Load; [ rewrite Hpc; exact (FC_3f8 segs e HC) | reflexivity | exact DC_3f8 | ] | | exact Hbud | ].
  { rewrite H11. mcnorm. eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]. }
  { inc_src. } mnext.
  rewrite Hpc. pcn.

  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_3fc segs e HC) | reflexivity | exact DC_3fc | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 1); [exact Hf | lia | lia]. }
  { rgn. inc_dst. } mnext.
  pcn. rgn. rewrite H13. mcnorm. rewrite store1_load1 by (rewrite length_firstn, length_skipn, Lbs; lia).
  apply (mc_retm _ 0x400 _ Hm); [ mcr_chain HS | reflexivity | exact (FC_400 segs e HC) | ].
  rewrite ?mem_setx. replace n with (k + Z.of_nat 1)%Z by lia. rewrite <- (Z.add_0_l k) at 2.
  rewrite Z.add_0_l. replace (dst + k)%Z with (dst + k)%Z by reflexivity.
  apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf].
Qed.

Lemma t2m : forall S k r m, matin model0 m L -> MCRc CL ms0 S -> ms_pc_val S = pcw e 0x3c0 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + r mod 4 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhalt m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.

  wst wacc_OpImm (FC_3c0 segs e HC) DC_3c0. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.

  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FC_3c4 segs e HC) | reflexivity | exact DC_3c4 ] | apply acc_ok_nil | ].
  mcnorm. rewrite branch_ne_z by (try (pose proof (Z_land_range r 2); lia); lia). pcn.
  destruct (Z.eqb_spec (Z.land r 2) 0) as [B2|B2]; cbn [negb]; pcn.
  -
    destruct (b2_0 r Hr B2) as [M2 M4].
    wst wacc_OpImm (FC_3c8 segs e HC) DC_3c8. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.
    eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FC_3cc segs e HC) | reflexivity | exact DC_3cc ] | apply acc_ok_nil | ].
    mcnorm. rewrite branch_ne_z by (try (pose proof (Z_land_range r 1); lia); lia). pcn.
    destruct (Z.eqb_spec (Z.land r 1) 0) as [B1|B1]; cbn [negb]; pcn.
    + pose proof (b1_0 r Hr B1). apply (mc_retm _ 0x3d0 _ Hm); [ mcr_chain HS | reflexivity | exact (FC_3d0 segs e HC) | ].
      rewrite ?mem_setx. replace n with k by lia. exact Hf.
    + pose proof (b1_1 r Hr B1). apply (t1m _ k _ Hm); [ mcr_chain HS | reflexivity | | | lia | lia | ].
      * rgn. exact H11.
      * rgn. exact H13.
      * rewrite ?mem_setx. exact Hf.
  -
    destruct (b2_1 r Hr B2) as [M2 M4].

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_3d4 segs e HC) | reflexivity | exact DC_3d4 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]. }
    { rgn. inc_src. } mnext.
    pcn.

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_3d8 segs e HC) | reflexivity | exact DC_3d8 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]. }
    { rgn. inc_src. } mnext.
    pcn.

    wst wacc_OpImm (FC_3dc segs e HC) DC_3dc. wst wacc_OpImm (FC_3e0 segs e HC) DC_3e0.

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_3e4 segs e HC) | reflexivity | exact DC_3e4 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 1); [exact Hf | lia | lia]. }
    { rgn. inc_dst. } mnext.
    pcn. rgn. rewrite H13. mcnorm. rewrite store1_load1 by (rewrite length_firstn, length_skipn, Lbs; lia).
    assert (Hf1 : copied (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 1 (skipn (Z.to_nat k) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 1) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf]. }

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_3e8 segs e HC) | reflexivity | exact DC_3e8 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 1)%Z with (dst + (k + Z.of_nat 1))%Z by lia.
      eapply (sok_sub _ _ _ 1); [exact Hf1 | lia | lia]. }
    { rgn. inc_dst. } mnext.
    pcn. rgn. rewrite H13. mcnorm. rewrite store1_load1 by (rewrite length_firstn, length_skipn, Lbs; lia).
    replace (src + k + 1)%Z with (src + (k + Z.of_nat 1))%Z by lia.
    replace (dst + k + 1)%Z with (dst + (k + Z.of_nat 1))%Z by lia.
    replace (Z.to_nat (k + 1)) with (Z.to_nat (k + Z.of_nat 1)) by (f_equal; lia).
    assert (Hf2 : copied (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 1 (skipn (Z.to_nat k) bs)))
                            (Z_to_bv 64 (dst + (k + Z.of_nat 1))) (firstn 1 (skipn (Z.to_nat (k + Z.of_nat 1)) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 1 + Z.of_nat 1) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf1]. }

    wst wacc_OpImm (FC_3ec segs e HC) DC_3ec. wst wacc_OpImm (FC_3f0 segs e HC) DC_3c8. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.
    eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FC_3f4 segs e HC) | reflexivity | exact DC_3f4 ] | apply acc_ok_nil | ].
    mcnorm. rewrite branch_eq_z by (try (pose proof (Z_land_range r 1); lia); lia). pcn.
    destruct (Z.eqb_spec (Z.land r 1) 0) as [B1|B1]; pcn.
    + pose proof (b1_0 r Hr B1). apply (mc_retm _ 0x3d0 _ Hm); [ mcr_chain HS | reflexivity | exact (FC_3d0 segs e HC) | ].
      rewrite ?mem_setx. replace n with (k + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf2.
    + pose proof (b1_1 r Hr B1). apply (t1m _ (k + 2)%Z _ Hm); [ mcr_chain HS | reflexivity | | | lia | lia | ].
      * rgn. rwregs. mcnorm. f_equal. lia.
      * rgn. rwregs. mcnorm. f_equal. lia.
      * rewrite ?mem_setx. replace (k + 2)%Z with (k + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf2.
Qed.

Lemma t4m : forall S k r m, matin model0 m L -> MCRc CL ms0 S -> ms_pc_val S = pcw e 0x17c ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 16)%Z -> (0 <= k)%Z -> (k + r mod 8 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhalt m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.

  wst wacc_OpImm (FC_17c segs e HC) DC_17c. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.

  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FC_180 segs e HC) | reflexivity | exact DC_180 ] | apply acc_ok_nil | ].
  mcnorm. rewrite branch_eq_z by (try (pose proof (Z_land_range r 4); lia); lia). pcn.
  destruct (Z.eqb_spec (Z.land r 4) 0) as [B4|B4]; pcn.
  - destruct (b4_0 r Hr B4) as [M4 M8].
    apply (t2m _ k r _ Hm); [ mcr_chain HS | reflexivity | rgn; exact H11 | rgn; exact H13 | rgn; exact H12 | lia | lia | lia | ].
    rewrite ?mem_setx. exact Hf.
  - destruct (b4_1 r Hr B4) as [M4 M8].

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_184 segs e HC) | reflexivity | exact DC_164 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
    { rgn. inc_src. } mnext.
    pcn.

    wst wacc_OpImm (FC_188 segs e HC) DC_188.

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_18c segs e HC) | reflexivity | exact DC_16c | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 4); [exact Hf | lia | lia]. }
    { rgn. inc_dst. } mnext.
    pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).

    wst wacc_OpImm (FC_190 segs e HC) DC_190. wst wacc_Jal (FC_194 segs e HC) DC_194.
    apply (t2m _ (k + 4)%Z r _ Hm); [ mcr_chain HS | reflexivity | | | | lia | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. exact H12.
    + rewrite ?mem_setx. replace (k + 4)%Z with (k + Z.of_nat 4)%Z by reflexivity.
      apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf].
Qed.

Lemma t8m : forall S k r m, matin model0 m L -> MCRc CL ms0 S -> ms_pc_val S = pcw e 0x15c ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 16)%Z -> (0 <= k)%Z -> (k + r = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhalt m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.

  wst wacc_OpImm (FC_15c segs e HC) DC_15c. mcnorm.

  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FC_160 segs e HC) | reflexivity | exact DC_160 ] | apply acc_ok_nil | ].
  mcnorm. rewrite H12. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec r 8) as [R8|R8]; pcn.
  - pose proof (b8_lt r ltac:(lia)).
    apply (t4m _ k r _ Hm); [ mcr_chain HS | reflexivity | rgn; exact H11 | rgn; exact H13 | rgn; exact H12 | lia | lia | lia | ].
    rewrite ?mem_setx. exact Hf.
  - pose proof (b8_ge r ltac:(lia)).

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_164 segs e HC) | reflexivity | exact DC_164 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
    { rgn. inc_src. } mnext.
    pcn.
    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_168 segs e HC) | reflexivity | exact DC_168 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
    { rgn. inc_src. } mnext.
    pcn.

    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_16c segs e HC) | reflexivity | exact DC_16c | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 4); [exact Hf | lia | lia]. }
    { rgn. inc_dst. } mnext.
    pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
    assert (Hf1 : copied (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 4) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf]. }
    eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_170 segs e HC) | reflexivity | exact DC_170 | ] | | exact Hbud | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
      eapply (sok_sub _ _ _ 4); [exact Hf1 | lia | lia]. }
    { rgn. inc_dst. } mnext.
    pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
    replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
    replace (Z.to_nat (k + 4)) with (Z.to_nat (k + Z.of_nat 4)) by (f_equal; lia).
    assert (Hf2 : copied (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                            (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf1]. }

    wst wacc_OpImm (FC_174 segs e HC) DC_174. wst wacc_OpImm (FC_178 segs e HC) DC_178.
    apply (t4m _ (k + 8)%Z r _ Hm); [ mcr_chain HS | reflexivity | | | | lia | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. exact H12.
    + rewrite ?mem_setx. replace (k + 8)%Z with (k + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf2.
Qed.

Lemma loop16m : forall (d : nat) S k m, matin model0 m L -> (n - k < 16 * Z.of_nat d)%Z ->
  MCRc CL ms0 S -> ms_pc_val S = pcw e 0x12c ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = Z_to_bv 64 15 -> (16 <= n - k)%Z -> (0 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  induction d as [|d IH]; intros S k m Hm Hd HS Hpc H11 H13 H12 H14 Hnk Hk Hf; [lia|]. pose proof (mhalt m Hm) as Hhm.
  pose proof (mcr_svc _ _ _ HS) as Hsvc.

  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | exact Hsvc | eapply wacc_Load; [ rewrite Hpc; exact (FC_12c segs e HC) | reflexivity | exact DC_12c | ] | | exact Hbud | ].
  { rewrite H11. mcnorm. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { inc_src. } mnext.
  rewrite Hpc. pcn.
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_130 segs e HC) | reflexivity | exact DC_130 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { rgn. inc_src. } mnext.
  pcn.
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_134 segs e HC) | reflexivity | exact DC_134 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { rgn. inc_src. } mnext.
  pcn.
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Load; [ fetch_tac (FC_138 segs e HC) | reflexivity | exact DC_138 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { rgn. inc_src. } mnext.
  pcn.

  wst wacc_OpImm (FC_13c segs e HC) DC_13c. wst wacc_OpImm (FC_140 segs e HC) DC_140.

  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_144 segs e HC) | reflexivity | exact DC_144 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 4); [exact Hf | lia | lia]. }
  { rgn. inc_dst. } mnext.
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  assert (Hf1 : copied (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4) bs) by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf]).
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_148 segs e HC) | reflexivity | exact DC_148 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
    eapply (sok_sub _ _ _ 4); [exact Hf1 | lia | lia]. }
  { rgn. inc_dst. } mnext.
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
  replace (Z.to_nat (k + 4)) with (Z.to_nat (k + Z.of_nat 4)) by (f_equal; lia).
  assert (Hf2 : copied (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4) bs) by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf1]).
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_14c segs e HC) | reflexivity | exact DC_14c | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 8)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
    eapply (sok_sub _ _ _ 4); [exact Hf2 | lia | lia]. }
  { rgn. inc_dst. } mnext.
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  replace (dst + k + 8)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
  replace (Z.to_nat (k + 8)) with (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4)) by (f_equal; lia).
  assert (Hf3 : copied (write_to_mem (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4 + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4)) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) bs)
    by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf2]).
  eapply (rzc_acc_in segs cfg model0 _ L); [ exact Hh0 | exact Hm | reflexivity | eapply wacc_Store; [ fetch_tac (FC_150 segs e HC) | reflexivity | exact DC_150 | ] | | exact Hbud | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 12)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
    eapply (sok_sub _ _ _ 4); [exact Hf3 | lia | lia]. }
  { rgn. inc_dst. } mnext.
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  replace (dst + k + 12)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
  replace (Z.to_nat (k + 12)) with (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)) by (f_equal; lia).
  assert (Hf4 : copied (write_to_mem (write_to_mem (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4 + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4)) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)))
                          (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) bs)
    by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf3]).

  wst wacc_OpImm (FC_154 segs e HC) DC_154.
  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FC_158 segs e HC) | reflexivity | exact DC_158 ] | apply acc_ok_nil | ].
  mcnorm. rewrite H14, H12. mcnorm. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec 15 (n - k + -16)) as [Lt|Ge]; pcn.
  - apply (IH _ (k + 16)%Z _ Hm); [ lia | mcr_chain HS | reflexivity | | | | | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. exact H14.
    + rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf4.
  - apply (t8m _ (k + 16)%Z (n - k + -16)%Z _ Hm); [ mcr_chain HS | reflexivity | | | | lia | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. reflexivity.
    + rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf4.
Qed.

Lemma al120m : forall S k m, matin model0 m L -> MCRc CL ms0 S -> ms_pc_val S = pcw e 0x120 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (0 <= k <= n)%Z -> copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 Hk Hf. pose proof (mhalt m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.

  wst wacc_OpImm (FC_120 segs e HC) DC_120. mcnorm.
  eapply rzc_acc; [ exact Hhm | reflexivity | eapply wacc_Branch; [ fetch_tac (FC_124 segs e HC) | reflexivity | exact DC_124 ] | apply acc_ok_nil | ].
  mcnorm. rewrite H12. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec (n - k) 16) as [N16|N16]; pcn.
  - apply (t8m _ k (n - k)%Z _ Hm); [ mcr_chain HS | reflexivity | rgn; exact H11 | rgn; exact H13 | rgn; exact H12 | lia | lia | lia | ].
    rewrite ?mem_setx. exact Hf.
  - wst wacc_OpImm (FC_128 segs e HC) DC_128. mcnorm.
    apply (loop16m (Z.to_nat ((n - k) / 16) + 1) _ k _ Hm).
    + pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)).
      rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). lia.
    + mcr_chain HS.
    + reflexivity.
    + rgn. exact H11.
    + rgn. exact H13.
    + rgn. exact H12.
    + rgn. reflexivity.
    + lia.
    + lia.
    + rewrite ?mem_setx. exact Hf.
Qed.

End LoopM.

End MCWM.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
