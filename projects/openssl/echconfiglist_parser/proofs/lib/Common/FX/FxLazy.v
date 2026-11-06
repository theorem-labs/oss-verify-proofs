(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg LazyAccCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma region_ok_nowrap_lz rho t rg :
  region_ok rho t rg -> bv_unsigned (rho t) + to_Z (rg_len rg) < 2 ^ 63.
Proof. intros (_ & _ & H & _). exact H. Qed.

Section Lazy.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

Local Abbreviation Rr := (R segs IM rho).

(* [comment removed for export] *)
Definition acc_claimed (M : itrie region) (a : word) (n : nat) : Prop :=
  exists t rg pn p j,
    iget t M = Some rg /\ to_Z pn < 2 ^ 50 /\ page_at IM rg t pn = Some p
    /\ 0 <= j /\ j + Z.of_nat n <= 4096
    /\ to_Z pn * 4096 + j + Z.of_nat n <= to_Z (rg_len rg)          (* [comment removed for export] *)
    /\ a = adr rho t (to_Z pn * 4096 + j).

Lemma fm_load_inv M t top off sz sgn v :
  fm_load IM M (FV t (W64 top off)) sz sgn = Some v ->
  exists rg p,
    iget t M = Some rg
    /\ page_at IM rg t (off >> 12)%uint63 = Some p
    /\ negb ((top land 1) =? 0)%uint63 = false
    /\ negb ((off land 7) + msz_int sz <=? 8)%uint63 = false
    /\ negb (in_region rg off (msz_int sz)) = false.
Proof.
  intros H. unfold fm_load in H. cbv zeta in H.
  destruct (negb ((top land 1) =? 0)%uint63) eqn:C1; [discriminate|].
  destruct (negb ((off land 7) + msz_int sz <=? 8)%uint63) eqn:C2; [discriminate|].
  destruct (iget t M) as [rg|] eqn:Hrg; [|discriminate].
  destruct (negb (in_region rg off (msz_int sz))) eqn:C3; [discriminate|].
  destruct (page_at IM rg t (off >> 12)%uint63) as [p|] eqn:Hp; [|discriminate].
  exists rg, p. split; [reflexivity|]. split; [exact Hp|]. split; [reflexivity|]. split; [reflexivity | exact C3].
Qed.

Lemma access_claimed M m t top off sz rg p :
  mem_ok segs IM rho M m ->
  iget t M = Some rg -> page_at IM rg t (off >> 12)%uint63 = Some p ->
  negb ((top land 1) =? 0)%uint63 = false ->
  negb ((off land 7) + msz_int sz <=? 8)%uint63 = false ->
  negb (in_region rg off (msz_int sz)) = false ->
  acc_claimed M (dv rho (FV t (W64 top off))) (msz_nat sz).
Proof.
  intros Hmok Hrg Hp C1 C2 C3.
  destruct (checks_inv top off sz rg C1 C2 C3) as (Htop & Hcell & Hoff & Hlen & Hlo & Hin).
  pose proof (region_plain segs IM rho M m t rg Hmok Hrg) as Hpl.
  pose proof (i63_range off) as Hoff0.
  exists t, rg, (off >> 12)%uint63, p, (to_Z off mod 4096).
  split; [exact Hrg|]. split.
  { rewrite to_Z_lsr12. apply Z.div_lt_upper_bound; lia. }
  split; [exact Hp|].
  pose proof (Z.mod_pos_bound (to_Z off) 4096 ltac:(lia)) as Hm.
  split; [lia|]. split.
  { clear - Hcell Hoff0. Z.div_mod_to_equations. lia. }
  split.
  { rewrite to_Z_lsr12. clear - Hin Hoff0. Z.div_mod_to_equations. lia. }
  rewrite (dv_adr rho t top off Hpl Htop). f_equal. rewrite to_Z_lsr12.
  clear - Hoff0. Z.div_mod_to_equations. lia.
Qed.

Lemma fm_load_claimed M m a sz sgn v :
  mem_ok segs IM rho M m -> fm_load IM M a sz sgn = Some v -> acc_claimed M (dv rho a) (msz_nat sz).
Proof.
  intros Hmok H. destruct a as [t [top off]].
  destruct (fm_load_inv _ _ _ _ _ _ _ H) as (rg & p & Hrg & Hp & C1 & C2 & C3).
  exact (access_claimed M m t top off sz rg p Hmok Hrg Hp C1 C2 C3).
Qed.

Lemma fm_store_claimed M m a sz v M' :
  mem_ok segs IM rho M m -> fm_store IM M a sz v = Some M' -> acc_claimed M (dv rho a) (msz_nat sz).
Proof.
  intros Hmok H. destruct a as [t [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ H) as (rg & p & Hrg & Hp & _ & C1 & C2 & C3 & _).
  exact (access_claimed M m t top off sz rg p Hmok Hrg Hp C1 C2 C3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

Theorem fx_step_acc : forall F ms F' report,
  Rr F ms -> fx_step IM code F = FNext F' ->
  step_accesses segs ms = MachineOk report ->
  Forall (fun r : word * nat => snd r = 0%nat \/ acc_claimed (f_mem F) (fst r) (snd r))
         (@accessed_ranges _ report).
Proof.
  intros F ms F' report HR H Hacc. unfold fx_step in H.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct (code_entry segs IM rho code Hcode F ms fi HR Hi)
    as (Hpc & w & Hf & [[He ->] | (He & i & Hd & Hc)]); [discriminate|].
  pose proof (step_accesses_exact segs ms w i 4 report Hf He Hd Hacc) as Hex.
  pose proof (R_regs_ok segs IM rho F ms HR) as HM.
  pose proof (R_regs _ _ _ _ _ HR) as Hregs.
  pose proof (R_mem _ _ _ _ _ HR) as Hmok.
  change (lz_core ms) with (core_of ms) in Hex.
  destruct i; cbn [compile] in Hc; try discriminate;
    try (solve [eapply Forall_impl; [|exact Hex]; intros r [_ E2]; left; exact E2]).
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) ALU_ADD (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [a|] eqn:Ea; [|discriminate].
    destruct (fm_load_abs IM (f_mem F) a sz signed) as [v|] eqn:El0; [|discriminate].
    destruct (fm_load_abs_inv rho Hrho0 IM _ _ _ _ _ HM El0) as (a' & Ea' & El).
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold alu64, alu in Ea.
    pose proof (fm_load_claimed _ _ _ _ _ _ Hmok El) as Hcl. rewrite Ea', Ea in Hcl.
    eapply Forall_impl; [|exact Hex]. intros r [E1 E2]. right. rewrite E1, E2. cbn [exec_addr exec_nbytes].
    destruct sz; exact Hcl.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) ALU_ADD (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [a|] eqn:Ea; [|discriminate].
    destruct (fm_store_abs IM (f_mem F) a sz (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
    destruct (fm_store_abs_inv rho Hrho0 IM _ _ _ _ _ HM Es0) as (a' & Ea' & Es).
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold alu64, alu in Ea.
    pose proof (fm_store_claimed _ _ _ _ _ _ Hmok Es) as Hcl. rewrite Ea', Ea in Hcl.
    eapply Forall_impl; [|exact Hex]. intros r [E1 E2]. right. rewrite E1, E2. cbn [exec_addr exec_nbytes].
    destruct sz; exact Hcl.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    destruct (fm_load_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) true) as [v|] eqn:El0; [|discriminate].
    destruct (fm_load_abs_inv rho Hrho0 IM _ _ _ _ _ HM El0) as (a' & Ea' & El).
    pose proof (fm_load_claimed _ _ _ _ _ _ Hmok El) as Hcl. rewrite Ea', <- Hregs in Hcl.
    eapply Forall_impl; [|exact Hex]. intros r [E1 E2]. right. rewrite E1, E2. cbn [exec_addr exec_nbytes].
    destruct w0; exact Hcl.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    apply (aligned_for_sound rho Hrho0 _ _ _ HM) in Eal. rewrite <- Hregs in Eal.
    destruct (resv_eqb (f_resv F) (FxState.rget F (ireg rs1))) as [hit|] eqn:Ehit; [|discriminate].
    apply (resv_eqb_sound rho) in Ehit. rewrite <- (R_resv _ _ _ _ _ HR), <- Hregs in Ehit.
    destruct hit.
    + destruct (fm_store_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
      destruct (fm_store_abs_inv rho Hrho0 IM _ _ _ _ _ HM Es0) as (a' & Ea' & Es).
      pose proof (fm_store_claimed _ _ _ _ _ _ Hmok Es) as Hcl. rewrite Ea', <- Hregs in Hcl.
      eapply Forall_impl; [|exact Hex]. intros r [E1 E2]. right. rewrite E1, E2. cbn [exec_addr exec_nbytes].
      destruct w0; exact Hcl.
    + unfold resv_hit in Ehit.
      rewrite (step_accesses_sc_fail segs ms w w0 _ _ _ _ _ 4 report Hf He Hd Eal Ehit Hacc). constructor.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    destruct (fm_load_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) true) as [old|] eqn:El0; [|discriminate].
    destruct (fm_load_abs_inv rho Hrho0 IM _ _ _ _ _ HM El0) as (a' & Ea' & El).
    pose proof (fm_load_claimed _ _ _ _ _ _ Hmok El) as Hcl. rewrite Ea', <- Hregs in Hcl.
    eapply Forall_impl; [|exact Hex]. intros r [E1 E2]. right. rewrite E1, E2. cbn [exec_addr exec_nbytes].
    destruct w0; exact Hcl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable lazy : list (word * word).
Variable A : list (Z * Z).

Definition LZ (M : itrie region) : Prop :=
  forall t rg pn p x,
    iget t M = Some rg -> to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p -> 0 <= x < 4096 ->
    to_Z pn * 4096 + x < to_Z (rg_len rg) ->                        (* [comment removed for export] *)
    page_in_ranges (page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + x)) lazy = true ->
    page_allowedb A (page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + x)) = true.

(* [comment removed for export] *)
Lemma LZ_intro M m :
  mem_ok segs IM rho M m ->
  (forall t rg, iget t M = Some rg ->
     (forall r, In r lazy ->
        bv_unsigned (rho t) + to_Z (rg_len rg) <= bv_unsigned (fst r)
        \/ bv_unsigned (fst r) + bv_unsigned (snd r) <= bv_unsigned (rho t) + to_Z (rg_lo rg))
     \/ (exists iv, In iv A /\ fst iv mod 4096 = 0 /\ snd iv mod 4096 = 0
                    /\ fst iv <= bv_unsigned (rho t) + to_Z (rg_lo rg)
                    /\ bv_unsigned (rho t) + to_Z (rg_len rg) <= snd iv)) ->
  LZ M.
Proof.
  intros [Hmem _] Hcases t rg pn p x Hg Hpn Hp Hx Hhi Hlz.
  destruct (Hmem t rg Hg) as [_ Hpages]. destruct (Hpages pn p Hpn Hp) as (_ & Hlo & _).
  set (z := bv_unsigned (rho t) + to_Z pn * 4096 + x) in *.
  pose proof (u64_range (rho t)) as Hr. pose proof (i63_range pn) as Hpn0.
  assert (Hz0 : 0 <= z) by (unfold z; lia).
  assert (Hq : bv_unsigned (page_base_of z) = z / 4096 * 4096 /\ z / 4096 * 4096 <= z < z / 4096 * 4096 + 4096).
  { unfold page_base_of, page_size. split.
    - apply u64_lit. pose proof (region_ok_nowrap_lz rho t rg (proj1 (Hmem t rg Hg))) as Hnw.
      assert (z < 2 ^ 63) by (unfold z; lia). clear - Hz0 H. Z.div_mod_to_equations. lia.
    - clear - Hz0. Z.div_mod_to_equations. lia. }
  destruct Hq as [Eq Hqz].
  destruct (Hcases t rg Hg) as [Hdisj | (iv & Hiv & Ha1 & Ha2 & Hb1 & Hb2)].
  - exfalso. unfold page_in_ranges in Hlz. apply existsb_exists in Hlz as (r & Hr' & Hb).
    apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1, B2. unfold page_size in B2.
    rewrite Eq in B1, B2. destruct (Hdisj r Hr') as [Hd|Hd]; unfold z in *; lia.
  - unfold page_allowedb. apply existsb_exists. exists iv. split; [exact Hiv|].
    apply andb_true_iff. rewrite Eq. unfold page_size. split; apply Z.leb_le.
    + clear - Ha1 Hb1 Hlo Hqz Hx Hpn0 Hr. unfold z in *. Z.div_mod_to_equations. lia.
    + clear - Ha2 Hb2 Hhi Hqz Hx Hpn0 Hr. unfold z in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma fm_store_page_mono M a sz v M' t rg' pn p' :
  fm_store IM M a sz v = Some M' -> iget t M' = Some rg' -> page_at IM rg' t pn = Some p' ->
  exists rg p, iget t M = Some rg /\ page_at IM rg t pn = Some p /\ rg_len rg' = rg_len rg.
Proof.
  destruct a as [ta [top off]]. intros Hst Hg' Hp'.
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg0 & p0 & Hrg0 & Hp0 & _ & _ & _ & _ & ->).
  rewrite iget_iset in Hg'. destruct (t =? ta)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. injection Hg' as <-.
    rewrite page_at_store_region in Hp'. destruct (pn =? off >> 12)%uint63 eqn:Ep.
    + apply Uint63.eqb_spec in Ep. subst pn. exists rg0, p0. split; [assumption|]. split; [assumption | reflexivity].
    + exists rg0, p'. split; [assumption|]. split; [assumption | reflexivity].
  - exists rg', p'. split; [assumption|]. split; [assumption | reflexivity].
Qed.

Lemma LZ_step F F' : fx_step IM code F = FNext F' -> LZ (f_mem F) -> LZ (f_mem F').
Proof.
  intros H HL. destruct (fx_step_mem IM code F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. exact HL.
  - intros t rg' pn p' x Hg' Hpn Hp' Hx Hxl.
    destruct (fm_store_page_mono _ _ _ _ _ _ _ _ _ Hst Hg' Hp') as (rg & p & Hg & Hp & El).
    rewrite El in Hxl. exact (HL t rg pn p x Hg Hpn Hp Hx Hxl).
Qed.

(* [comment removed for export] *)
Lemma LZ_touch F ms F' :
  Rr F ms -> fx_step IM code F = FNext F' -> LZ (f_mem F) -> touch_ok segs lazy A ms.
Proof.
  intros HR H HL report Hacc. apply touch_allowed_bytes.
  eapply Forall_impl; [|exact (fx_step_acc F ms F' report HR H Hacc)].
  intros r [E0 | (t & rg & pn & p & j & Hg & Hpn & Hp & Hj0 & Hj & Hjl & Ea)] i Hi; [lia|].
  destruct (proj1 (R_mem _ _ _ _ _ HR) t rg Hg) as [Hreg Hpages].
  destruct (Hpages pn p Hpn Hp) as (_ & Hlo & _).
  pose proof (region_ok_nowrap_lz rho t rg Hreg) as Hnw.
  pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rg_lo rg)) as Hl0.
  assert (Eu : bv_unsigned (fst r) = bv_unsigned (rho t) + (to_Z pn * 4096 + j)).
  { rewrite Ea. apply adr_unsigned; lia. }
  rewrite Eu.
  replace (bv_unsigned (rho t) + (to_Z pn * 4096 + j) + i)
    with (bv_unsigned (rho t) + to_Z pn * 4096 + (j + i)) by lia.
  apply (HL t rg pn p (j + i) Hg Hpn Hp); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fx_run_touch : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F', r, cnt) ->
  (LZ (f_mem F) -> LZ (f_mem F'))
  /\ forall ms, Rr F ms -> LZ (f_mem F) ->
       forall j msj, (j < nat_of_int cnt)%nat -> rsteps segs j ms = MachineOk msj ->
                     touch_ok segs lazy A msj.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. split; [intros HL; exact HL|]. intros ms _ _ j msj Hj. change (nat_of_int 0) with 0%nat in Hj. lia. }
    destruct (fx_step IM code F) as [s'| |c] eqn:Es.
    + injection H as <- <- <-. split; [exact (LZ_step F s' Es)|].
      intros ms HR HL j msj Hj Hr. change (nat_of_int 1) with 1%nat in Hj.
      assert (j = 0)%nat by lia. subst j. cbn [rsteps] in Hr. injection Hr as <-.
      exact (LZ_touch F ms s' HR Es HL).
    + injection H as <- <- <-. split; [intros HL; exact HL|]. intros ms _ _ j msj Hj. change (nat_of_int 0) with 0%nat in Hj. lia.
    + injection H as <- <- <-. split; [intros HL; exact HL|]. intros ms _ _ j msj Hj. change (nat_of_int 0) with 0%nat in Hj. lia.
  - cbn [fx_run] in H. destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (IH _ _ _ _ ltac:(lia) E1) as (HL1 & IH1).
    destruct (fx_run_sound segs IM rho Hrho0 code Hcode bp k F s1 r1 n1 ltac:(lia) E1) as (Hb1 & Hs1).
    assert (Hpow : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    assert (Hlt : 2 ^ Z.of_nat (S k) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      destruct (IH _ _ _ _ ltac:(lia) E2) as (HL2 & IH2).
      destruct (fx_run_sound segs IM rho Hrho0 code Hcode bp k s1 s2 r2 n2 ltac:(lia) E2) as (Hb2 & _).
      pose proof (Uint63.to_Z_bounded n1). pose proof (Uint63.to_Z_bounded n2).
      assert (Hadd : to_Z (n1 + n2)%uint63 = to_Z n1 + to_Z n2).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
      split; [intros HL; exact (HL2 (HL1 HL))|].
      intros ms HR HL j msj Hj Hr.
      destruct (Hs1 ms HR) as (ms1 & Hn1 & HR1 & _).
      destruct (Nat.lt_ge_cases j (nat_of_int n1)) as [Hlt1 | Hge1].
      * exact (IH1 ms HR HL j msj Hlt1 Hr).
      * assert (Ej : j = (nat_of_int n1 + (j - nat_of_int n1))%nat) by lia.
        rewrite Ej, rsteps_add, Hn1 in Hr.
        apply (IH2 ms1 HR1 (HL1 HL) (j - nat_of_int n1)%nat msj); [|exact Hr].
        unfold nat_of_int in *. rewrite Hadd, Z2Nat.inj_add in Hj by lia. lia.
    + injection H as <- <- <-. split; [exact HL1 | exact IH1].
Qed.

(* [comment removed for export] *)
Theorem fx_run_pages : forall cfg bp k F F' r cnt ms m,
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F', r, cnt) ->
  Rr F ms -> m_halted m = None -> m_vm_lazy m = lazy -> page_inv A m -> LZ (f_mem F) ->
  exists ms', rsteps segs (nat_of_int cnt) ms = MachineOk ms'
    /\ Rr F' ms' /\ LZ (f_mem F')
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms'))
    /\ (forall x, ~ claimed_wr IM rho (f_mem F) x -> ms_mem ms' x = ms_mem ms x)
    /\ (forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x)
    /\ ms_rom ms' = ms_rom ms /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms
    /\ (forall T, (forall m', lazy_frame m m' -> page_inv A m' -> realizes_cfg cfg segs (mkCfg ms' m') T) ->
                  realizes_cfg cfg segs (mkCfg ms m) T)
    /\ (exists m', lazy_frame m m' /\ page_inv A m' /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')).
Proof.
  intros cfg bp k F F' r cnt ms m Hk Hrun HR Hh Hlz Hinv HL.
  destruct (fx_run_sound_frame segs IM rho Hrho0 code Hcode bp k F F' r cnt Hk Hrun) as (_ & Hmono & Hfr).
  destruct (Hfr ms HR) as (ms' & Hsteps & HR' & Hec & Hframe & Hrom).
  destruct (fx_run_sound_shape segs IM rho Hrho0 code Hcode bp k F F' r cnt Hk Hrun ms HR)
    as (ms'' & Hsteps'' & _ & Hfregs & Hfcsr).
  rewrite Hsteps in Hsteps''. injection Hsteps'' as <-.
  destruct (fx_run_touch bp k F F' r cnt Hk Hrun) as (HL' & Htouch).
  assert (Ht : forall j msj, (j < nat_of_int cnt)%nat -> rsteps segs j ms = MachineOk msj ->
                 touch_ok segs (m_vm_lazy m) A msj).
  { rewrite Hlz. exact (Htouch ms HR HL). }
  exists ms'. split; [exact Hsteps|]. split; [exact HR'|]. split; [exact (HL' HL)|].
  split; [exact Hec|]. split; [exact Hframe|]. split; [exact Hmono|]. split; [exact Hrom|].
  split; [exact Hfregs|]. split; [exact Hfcsr|]. split.
  - intros T HT. exact (rzc_rsteps_pages cfg segs A _ ms ms' m T Hh Hsteps Hinv Ht HT).
  - exact (star_cfg_rsteps_pages cfg segs A _ ms ms' m Hh Hsteps Hinv Ht).
Qed.

(* [comment removed for export] *)
Theorem fx_run_pages_Rn : forall cfg n bp k F F' r cnt ms m,
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F', r, cnt) ->
  Rn segs IM n rho F ms -> m_halted m = None -> m_vm_lazy m = lazy -> page_inv A m -> LZ (f_mem F) ->
  exists ms', rsteps segs (nat_of_int cnt) ms = MachineOk ms'
    /\ Rn segs IM n rho F' ms' /\ LZ (f_mem F')
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms'))
    /\ (forall x, ~ claimed_wr IM rho (f_mem F) x -> ms_mem ms' x = ms_mem ms x)
    /\ (forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x)
    /\ ms_rom ms' = ms_rom ms /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms
    /\ (forall T, (forall m', lazy_frame m m' -> page_inv A m' -> realizes_cfg cfg segs (mkCfg ms' m') T) ->
                  realizes_cfg cfg segs (mkCfg ms m) T)
    /\ (exists m', lazy_frame m m' /\ page_inv A m' /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')).
Proof.
  intros cfg n bp k F F' r cnt ms m Hk Hrun HRn Hh Hlz Hinv HL.
  assert (HR : Rr F ms) by (apply HRn; split; [exact Hrho0 | intros; reflexivity]).
  destruct (fx_run_pages cfg bp k F F' r cnt ms m Hk Hrun HR Hh Hlz Hinv HL)
    as (ms' & Hsteps & _ & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  destruct (fx_run_Rn segs IM code Hcode n rho bp k F F' r cnt ms Hk Hrun Hrho0 HRn)
    as (ms'' & Hsteps'' & HRn' & _).
  rewrite Hsteps in Hsteps''. injection Hsteps'' as <-.
  exists ms'. repeat (split; [assumption|]). exact H11.
Qed.

End Lazy.
