(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxCellFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section RoFrame.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Variable code : itrie finstr.
Variable RO : itrie unit.
Hypothesis Hcode : code_ok segs code.

Local Abbreviation Rr := (R segs IM rho).

(* [comment removed for export] *)
Definition ro_in_r0 (M : itrie region) : Prop :=
  exists rg0, iget 0%uint63 M = Some rg0
    /\ forall c u, iget c RO = Some u -> to_Z (rg_lo rg0) <= to_Z c /\ to_Z c < to_Z (rg_len rg0).

(* [comment removed for export] *)
Definition ro_byte (x : word) : Prop :=
  exists c u, iget c RO = Some u /\ x = Z_to_bv 64 (to_Z c).

(* [comment removed for export] *)
Lemma ro_hitn_false : forall n off, ro_hitn RO n off = false -> to_Z off + Z.of_nat n < 2 ^ 63 ->
  forall c, to_Z off <= to_Z c < to_Z off + Z.of_nat n -> iget c RO = None.
Proof.
  induction n as [|n IH]; intros off H Hb c Hc; [lia|].
  cbn [ro_hitn] in H. destruct (iget off RO) eqn:E; [discriminate|].
  destruct (Z.eq_dec (to_Z c) (to_Z off)) as [Ec|Ec].
  - apply to_Z_inj in Ec. subst c. exact E.
  - pose proof (i63_range off) as Ho.
    assert (E1 : to_Z (off + 1)%uint63 = to_Z off + 1).
    { rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. change wB with (2 ^ 63). apply Z.mod_small. lia. }
    apply (IH (off + 1)%uint63 H); rewrite E1; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fm_store_ro_in_r0 M a sz v M' :
  fm_store IM M a sz v = Some M' -> ro_in_r0 M -> ro_in_r0 M'.
Proof.
  intros Hst (rg0 & H0 & Hc).
  pose proof (fm_store_regions' IM M a sz v M' 0%uint63 Hst) as Hg. rewrite H0 in Hg.
  destruct (iget 0%uint63 M') as [rg0'|] eqn:H0'; [|destruct Hg].
  destruct Hg as (Hlo & Hlen & _ & _).
  exists rg0'. split; [exact H0'|]. intros c u Hcu. rewrite Hlo, Hlen. exact (Hc c u Hcu).
Qed.

Lemma fx_step_ro_in_r0 F F' :
  fx_step IM code RO F = FNext F' -> ro_in_r0 (f_mem F) -> ro_in_r0 (f_mem F').
Proof.
  intros H Hro. destruct (fx_step_mem IM code RO F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. exact Hro.
  - exact (fm_store_ro_in_r0 _ _ _ _ _ Hst Hro).
Qed.

Theorem fx_run_ro_in_r0 : forall bp k F F' r cnt,
  fx_run IM code RO bp k F = (F', r, cnt) -> ro_in_r0 (f_mem F) -> ro_in_r0 (f_mem F').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt H Hro.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63; [injection H as <- <- <-; exact Hro|].
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-; try exact Hro.
    exact (fx_step_ro_in_r0 F s' Es Hro).
  - cbn [fx_run] in H. destruct (fx_run IM code RO bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code RO bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      exact (IH _ _ _ _ E2 (IH _ _ _ _ E1 Hro)).
    + injection H as <- <- <-. exact (IH _ _ _ _ E1 Hro).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fm_store_abs_inv_ro M a sz v M' :
  regs_ok rho M -> fm_store_abs IM RO M a sz v = Some M' ->
  exists a', dv rho a' = dv rho a /\ fm_store IM M a' sz v = Some M'
             /\ (vtag a' = 0%uint63 -> ro_hit RO a' sz = false).
Proof.
  intros HM H. unfold fm_store_abs in H. destruct (ro_hit RO a sz) eqn:Hh; [discriminate|].
  destruct (fm_store IM M a sz v) as [M0|] eqn:E.
  - injection H as <-. exists a. split; [reflexivity|]. split; [exact E|]. intros _; exact Hh.
  - destruct (vtag a =? 0)%uint63 eqn:Et; [|discriminate]. apply Uint63.eqb_spec in Et.
    exists (abs_addr M a (msz_int sz)). split; [apply abs_addr_dv; [exact Hrho0 | exact HM]|]. split; [exact H|].
    destruct a as [t [top off]]. cbn [vtag] in Et. subst t.
    unfold abs_addr. change (0 =? 0)%uint63 with true. cbv iota.
    destruct (abs_find M off (msz_int sz)) as [t'|]; [|intros _; exact Hh].
    destruct (iget t' M) as [rg|]; [|intros _; exact Hh].
    destruct (is_abs rg && (t' <? kind_lim)%uint63); [|intros _; exact Hh].
    cbn [vtag]. intros ->. exact Hh.
Qed.

(* [comment removed for export] *)
Lemma fm_store_abs_ro_out M m a sz v M' (k : nat) x :
  mem_ok segs IM rho M m -> ro_in_r0 M ->
  fm_store_abs IM RO M a sz v = Some M' -> (k < msz_nat sz)%nat ->
  ro_byte x -> x <> aoff (dv rho a) k.
Proof.
  intros Hmok (rg0 & H0 & Hc) Hst Hk (c & u & Hcu & ->) E.
  destruct (Hc c u Hcu) as (Hclo & Hchi).
  destruct Hmok as [Hregs Hsep].
  assert (HM : regs_ok rho M) by (intros t1 rg1 Ht1; exact (proj1 (Hregs t1 rg1 Ht1))).
  destruct (fm_store_abs_inv_ro M a sz v M' HM Hst) as (a' & Ea' & Hst' & Hro).
  rewrite <- Ea' in E. clear Ea' Hst a.
  destruct a' as [t [top off]]. cbn [vtag] in Hro.
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst') as (rg & p & Hrg & _ & _ & C1 & C2 & C3 & _).
  destruct (checks_inv top off sz rg C1 C2 C3) as (Htop & Hcell & Hoff & Hlen & Hlo & Hin).
  pose proof (region_plain segs IM rho M m t rg (conj Hregs Hsep) Hrg) as Hpl.
  destruct (Hregs t rg Hrg) as [Hok _]. destruct (Hregs 0%uint63 rg0 H0) as [Hok0 _].
  pose proof (i63_range off) as Hoff0. pose proof (i63_range c) as Hc0.
  pose proof (i63_range (rg_len rg0)) as Hl0. pose proof (i63_range (rg_lo rg0)).
  rewrite (dv_adr rho t top off Hpl Htop), aoff_adr in E.
  destruct Hok as (_ & _ & Hb & _). destruct Hok0 as (_ & _ & Hb0 & _).
  pose proof (i63_range (rg_lo rg)). pose proof (msz_nat_pos sz).
  apply (f_equal bv_unsigned) in E.
  rewrite adr_unsigned in E by lia.
  rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
  rewrite Z.mod_small in E by lia.
  destruct (t =? 0)%uint63 eqn:Et.
  - (* [comment removed for export] *)
    apply Uint63.eqb_spec in Et. subst t.
    specialize (Hro eq_refl). unfold ro_hit in Hro. change (0 =? 0)%uint63 with true in Hro. cbv iota in Hro.
    rewrite Hrho0, Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
    rewrite (Z.mod_small 0) in E by lia.
    assert (Hcnt : msz_cnt sz = msz_nat sz) by (destruct sz; reflexivity).
    rewrite Hcnt in Hro.
    assert (Hnone : iget c RO = None).
    { apply (ro_hitn_false (msz_nat sz) off Hro); [destruct sz; cbn [msz_nat] in *; lia | lia]. }
    rewrite Hnone in Hcu. discriminate.
  - (* [comment removed for export] *)
    assert (Hne : t <> 0%uint63) by (intros ->; rewrite Uint63.eqb_refl in Et; discriminate).
    specialize (Hsep t 0%uint63 rg rg0 Hne Hrg H0).
    rewrite Hrho0, Z_to_bv_unsigned in Hsep. unfold bv_wrap in Hsep. change (bv_modulus 64) with (2 ^ 64) in Hsep.
    rewrite (Z.mod_small 0) in Hsep by lia.
    lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fx_step_roframe : forall F ms F' ms',
  Rr F ms -> ro_in_r0 (f_mem F) -> fx_step IM code RO F = FNext F' -> step segs ms = MachineOk ms' ->
  forall x, ro_byte x -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros F ms F' ms' HR Hro H Hs x Hx. unfold fx_step in H.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct (code_entry segs IM rho code Hcode F ms fi HR Hi)
    as (Hpc & w & Hf & [[He ->] | (He & i & Hd & Hc)]); [discriminate|].
  destruct (step_mem_frame segs ms w i 4 ms' Hf He Hd Hs) as (report & Hacc & Hns & Hfr).
  destruct (may_store i) eqn:Ems; [|rewrite (Hns eq_refl); reflexivity].
  pose proof (step_accesses_exact segs ms w i 4 report Hf He Hd Hacc) as Hex.
  pose proof (R_regs_ok segs IM rho F ms HR) as HM.
  pose proof (R_regs _ _ _ _ _ HR) as Hregs.
  pose proof (R_mem _ _ _ _ _ HR) as Hmok.
  change (lz_core ms) with (core_of ms) in Hex.
  assert (Hgo : forall a sz v M',
            fm_store_abs IM RO (f_mem F) a sz v = Some M' ->
            dv rho a = exec_addr i (core_of ms) -> msz_nat sz = exec_nbytes i ->
            ms_mem ms' x = ms_mem ms x).
  { intros a sz v M' Es Ea En. apply Hfr. intros r Hr j Hj Ex.
    destruct (proj1 (Forall_forall _ _) Hex r Hr) as [E1 E2]. rewrite E1 in Ex. rewrite E2 in Hj.
    rewrite <- Ea in Ex. rewrite <- En in Hj.
    exact (fm_store_abs_ro_out (f_mem F) (ms_mem ms) a sz v M' j x Hmok Hro Es Hj Hx Ex). }
  destruct i; cbn [may_store] in Ems; try discriminate Ems; cbn [compile] in Hc; try discriminate Hc.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) ALU_ADD (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [a|] eqn:Ea; [|discriminate].
    destruct (fm_store_abs IM RO (f_mem F) a sz (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
    destruct (resv_after_store (f_resv F) a) as [r'|]; [|discriminate].
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold alu64, alu in Ea.
    apply (Hgo a sz _ M' Es0); [exact Ea | destruct sz; reflexivity].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    apply (aligned_for_sound rho Hrho0 _ _ _ HM) in Eal. rewrite <- Hregs in Eal.
    destruct (resv_eqb (f_resv F) (FxState.rget F (ireg rs1))) as [hit|] eqn:Ehit; [|discriminate].
    apply (resv_eqb_sound rho) in Ehit. rewrite <- (R_resv _ _ _ _ _ HR), <- Hregs in Ehit.
    destruct hit.
    + destruct (fm_store_abs IM RO (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
      apply (Hgo _ (awidth_sz w0) _ M' Es0); [rewrite <- Hregs; reflexivity | destruct w0; reflexivity].
    + unfold resv_hit in Ehit.
      apply Hfr. rewrite (step_accesses_sc_fail segs ms w w0 _ _ _ _ _ 4 report Hf He Hd Eal Ehit Hacc).
      intros r [].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    destruct (fm_load_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) true) as [old|] eqn:El0; [|discriminate].
    repeat match type of H with
           | context [match ?y with _ => _ end] => destruct y eqn:?; try discriminate
           | context [if ?y then _ else _] => destruct y eqn:?; try discriminate
           end;
      match goal with
      | Es0 : fm_store_abs IM RO _ _ _ _ = Some _ |- _ =>
          apply (Hgo _ (awidth_sz w0) _ _ Es0); [rewrite <- Hregs; reflexivity | destruct w0; reflexivity]
      end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fx_run_roframe : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code RO bp k F = (F', r, cnt) ->
  forall ms ms', Rr F ms -> ro_in_r0 (f_mem F) -> rsteps segs (nat_of_int cnt) ms = MachineOk ms' ->
  forall x, ro_byte x -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H ms ms' HR Hro Hn x Hx.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. change (nat_of_int 0) with 0%nat in Hn. cbn [rsteps] in Hn. congruence. }
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-;
      try (change (nat_of_int 0) with 0%nat in Hn; cbn [rsteps] in Hn; congruence).
    destruct (fx_step_sound segs IM rho Hrho0 code RO Hcode F ms s' HR Es) as (ms1 & Hs & _).
    change (nat_of_int 1) with 1%nat in Hn. cbn [rsteps] in Hn. rewrite (R_svc _ _ _ _ _ HR), Hs in Hn.
    injection Hn as <-. exact (fx_step_roframe F ms s' ms1 HR Hro Es Hs x Hx).
  - cbn [fx_run] in H. destruct (fx_run IM code RO bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (fx_run_sound segs IM rho Hrho0 code RO Hcode bp k F s1 r1 n1 ltac:(lia) E1) as (Hb1 & IH1).
    assert (Hpow : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    assert (Hlt : 2 ^ Z.of_nat (S k) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & _).
    pose proof (fx_run_ro_in_r0 bp k F s1 r1 n1 E1 Hro) as Hro1.
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code RO bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      destruct (fx_run_sound segs IM rho Hrho0 code RO Hcode bp k s1 s2 r2 n2 ltac:(lia) E2) as (Hb2 & IH2).
      destruct (IH2 ms1 HR1) as (ms2 & Hn2 & _).
      pose proof (Uint63.to_Z_bounded n1). pose proof (Uint63.to_Z_bounded n2).
      assert (Hadd : to_Z (n1 + n2)%uint63 = to_Z n1 + to_Z n2).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
      assert (Hn12 : rsteps segs (nat_of_int (n1 + n2)%uint63) ms = MachineOk ms2).
      { unfold nat_of_int. rewrite Hadd, Z2Nat.inj_add by lia. exact (rsteps_trans segs _ _ _ _ _ Hn1 Hn2). }
      rewrite Hn12 in Hn. injection Hn as <-.
      rewrite (IH _ _ _ _ ltac:(lia) E2 ms1 ms2 HR1 Hro1 Hn2 x Hx).
      exact (IH _ _ _ _ ltac:(lia) E1 ms ms1 HR Hro Hn1 x Hx).
    + injection H as <- <- <-. rewrite Hn1 in Hn. injection Hn as <-.
      exact (IH _ _ _ _ ltac:(lia) E1 ms ms1 HR Hro Hn1 x Hx).
Qed.
End RoFrame.
