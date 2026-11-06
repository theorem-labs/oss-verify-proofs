(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg LazyAccCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive nosto : eff -> Prop :=
| ns_done : forall c, nosto (EDone c)
| ns_illegal : forall c, nosto (EIllegal c)
| ns_defined_illegal : forall c, nosto (EDefinedIllegal c)
| ns_ecall : forall c, nosto (EEcall c)
| ns_ebreak : forall c, nosto (EEbreak c)
| ns_fault : forall c, nosto (EFault c)
| ns_load : forall n a k, (forall v, nosto (k v)) -> nosto (ELoad n a k).

Ltac nosto_tac :=
  repeat first
    [ apply ns_done | apply ns_illegal | apply ns_defined_illegal | apply ns_ecall
    | apply ns_ebreak | apply ns_fault
    | apply ns_load; intros ?
    | match goal with
      | |- nosto (if ?x then _ else _) => destruct x
      | |- nosto (match ?x with _ => _ end) => destruct x
      | |- nosto ((match ?x with _ => _ end) _) => destruct x
      | |- nosto (?f (match ?x with _ => _ end)) => destruct x
      | |- nosto (?f (match ?x with _ => _ end) _) => destruct x
      end ].

(* [comment removed for export] *)
Definition may_store (i : instr) : bool :=
  match i with
  | Instr.Store _ _ _ _ | Instr.Sc _ _ _ _ _ _ | Instr.Amo _ _ _ _ _ _ _ | Instr.FStore _ _ _ _ => true
  | _ => false
  end.

Theorem exec_nosto : forall sz i c, may_store i = false -> nosto (exec sz i c).
Proof.
  intros sz i c H.
  destruct i; cbn [may_store] in H; try discriminate H;
    cbn [exec]; unfold load_val, store_val, exec_csr; cbv zeta; nosto_tac.
Qed.

Section SpecSide.
Variable segs : list Segment.

Lemma interp_nosto : forall t, nosto t -> forall m report,
  interp_eff_accesses segs t m = MachineOk report -> snd (@access_value _ report) = m.
Proof.
  intros t Ht. induction Ht as [c | c | c | c | c | c | n a k Hk IH];
    intros m report H; cbn [interp_eff_accesses] in H; try discriminate H.
  - inversion H; subst. reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs |]; [| discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value]. exact (IH _ m r0 E).
Qed.

(* [comment removed for export] *)
Definition off_ranges (x : word) (l : list (word * nat)) : Prop :=
  forall r, In r l -> forall j, (j < snd r)%nat -> x <> aoff (fst r) j.

Lemma interp_frame : forall t m report,
  interp_eff_accesses segs t m = MachineOk report ->
  forall x, off_ranges x (@accessed_ranges _ report) -> snd (@access_value _ report) x = m x.
Proof.
  induction t as [c | c | c | c | c | c | n a k IH | n a v k IH];
    intros m report H x Hx; cbn [interp_eff_accesses] in H; try discriminate H.
  - inversion H; subst. reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs |]; [| discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value accessed_ranges] in *.
    apply (IH _ m r0 E). intros r Hr. apply Hx. right. exact Hr.
  - destruct (store_ok segs m a (width_bytes n)); [| discriminate H].
    destruct (interp_eff_accesses segs k
                (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value accessed_ranges] in *.
    rewrite (IH _ r0 E x) by (intros r Hr; apply Hx; right; exact Hr).
    apply write_to_mem_out. intros j Hj. rewrite length_Z_to_le_bytes in Hj.
    exact (Hx (a, width_bytes n) (or_introl eq_refl) j Hj).
Qed.

(* [comment removed for export] *)
Theorem step_mem_frame : forall ms w i isz ms',
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, isz) ->
  step segs ms = MachineOk ms' ->
  exists report,
    step_accesses segs ms = MachineOk report
    /\ (may_store i = false -> ms_mem ms' = ms_mem ms)
    /\ forall x, off_ranges x (@accessed_ranges _ report) -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros ms w i isz ms' Hf He Hd Hs.
  unfold step in Hs. destruct (step_accesses segs ms) as [report | |] eqn:Hacc; try discriminate Hs.
  cbn [drop_access_report] in Hs. exists report. split; [reflexivity|].
  unfold step_accesses in Hacc. rewrite Hf in Hacc.
  unfold decode_exec_accesses in Hacc. rewrite He, Hd in Hacc. fold (lz_core ms) in Hacc.
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 isz) i (lz_core ms)) (ms_mem ms))
    as [r0 | |] eqn:E; try discriminate Hacc.
  pose proof (interp_frame _ _ _ E) as Hfr.
  destruct (@access_value _ r0) as [c m'] eqn:Eav.
  inversion Hacc; subst report. cbn [access_value accessed_ranges] in *.
  inversion Hs; subst ms'. cbn [ms_mem]. cbn [snd] in Hfr. split.
  - intros Hns. pose proof (interp_nosto _ (exec_nosto (Z_to_bv 64 isz) i (lz_core ms) Hns) _ _ E) as Hn.
    rewrite Eav in Hn. exact Hn.
  - exact Hfr.
Qed.
End SpecSide.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FxSide.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

Local Abbreviation Rr := (R segs IM rho).

(* [comment removed for export] *)
Definition cell_expl (M : itrie region) (x : word) : Prop :=
  exists t rg pn p ci,
    iget t M = Some rg /\ iget pn (rg_pages rg) = Some p /\ iget ci (pg_cells p) <> None
    /\ exists j, 0 <= j < 8 /\ x = adr rho t (to_Z pn * 4096 + to_Z ci * 8 + j).

(* [comment removed for export] *)
Lemma fm_store_cell_expl M a sz v M' (k : nat) :
  to_Z (vtag a) < 2 ^ 60 ->
  fm_store IM M a sz v = Some M' -> (k < msz_nat sz)%nat ->
  cell_expl M' (aoff (dv rho a) k).
Proof.
  destruct a as [t [top off]]. cbn [vtag]. intros Hpl Hst Hk.
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & C4 & C1 & C2 & C3 & ->).
  destruct (checks_inv top off sz rg C1 C2 C3) as (Htop & Hcell & Hoff & Hlen & Hlo & Hin).
  pose proof (i63_range off) as Hoff0.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hb.
  exists t, (store_region rg (off >> 12)%uint63
               (store_page IM p (off >> 12)%uint63 ((off land 4095) >> 3)%uint63 (off land 7)%uint63 sz v)),
         (off >> 12)%uint63,
         (store_page IM p (off >> 12)%uint63 ((off land 4095) >> 3)%uint63 (off land 7)%uint63 sz v),
         ((off land 4095) >> 3)%uint63.
  split; [apply iget_iset_same|].
  split; [unfold store_region; cbn [rg_pages]; apply iget_iset_same|].
  split; [unfold store_page; cbn [pg_cells]; rewrite iget_iset_same; discriminate|].
  exists (Z.of_nat (Z.to_nat (to_Z off mod 8) + k)). split; [lia|].
  rewrite <- (access_addr rho t top off k Hpl Htop). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fm_store_cell_mono M a sz v M' :
  fm_store IM M a sz v = Some M' -> forall x, cell_expl M x -> cell_expl M' x.
Proof.
  destruct a as [t [top off]]. intros Hst x (t1 & rg1 & pn1 & p1 & ci1 & H1 & Hp1 & Hc1 & Hj).
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & _ & _ & _ & _ & ->).
  destruct (t1 =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t1. rewrite Hrg in H1. injection H1 as <-.
    set (pn := (off >> 12)%uint63) in *. set (ci := ((off land 4095) >> 3)%uint63) in *.
    set (p' := store_page IM p pn ci (off land 7)%uint63 sz v).
    destruct (pn1 =? pn)%uint63 eqn:Epn.
    + apply Uint63.eqb_spec in Epn. subst pn1.
      assert (Epp : p = p1). { unfold page_at in Hp. rewrite Hp1 in Hp. congruence. }
      subst p1.
      exists t, (store_region rg pn p'), pn, p', ci1.
      split; [apply iget_iset_same|].
      split; [unfold store_region; cbn [rg_pages]; apply iget_iset_same|].
      split; [|exact Hj].
      unfold p', store_page. cbn [pg_cells]. rewrite iget_iset.
      destruct (ci1 =? ci)%uint63; [discriminate | exact Hc1].
    + exists t, (store_region rg pn p'), pn1, p1, ci1.
      split; [apply iget_iset_same|].
      split; [unfold store_region; cbn [rg_pages]; rewrite iget_iset, Epn; exact Hp1|].
      split; [exact Hc1 | exact Hj].
  - exists t1, rg1, pn1, p1, ci1. split; [rewrite iget_iset, Et; exact H1|].
    split; [exact Hp1|]. split; [exact Hc1 | exact Hj].
Qed.

Lemma fm_store_abs_cell_mono M a sz v M' :
  fm_store_abs IM M a sz v = Some M' -> forall x, cell_expl M x -> cell_expl M' x.
Proof.
  unfold fm_store_abs. destruct (fm_store IM M a sz v) as [M0|] eqn:E.
  - intros H. injection H as <-. exact (fm_store_cell_mono M a sz v M0 E).
  - destruct (vtag a =? 0)%uint63; [|discriminate]. intros H. exact (fm_store_cell_mono M _ sz v M' H).
Qed.

Lemma fm_store_abs_cell_expl M m a sz v M' (k : nat) :
  mem_ok segs IM rho M m -> fm_store_abs IM M a sz v = Some M' -> (k < msz_nat sz)%nat ->
  cell_expl M' (aoff (dv rho a) k).
Proof.
  intros Hmok H Hk.
  destruct (fm_store_abs_inv rho Hrho0 IM M a sz v M' (fun t rg Ht => proj1 (proj1 Hmok t rg Ht)) H) as (a' & Ea' & Es).
  rewrite <- Ea'.
  exact (fm_store_cell_expl M a' sz v M' k (fm_store_plain segs IM rho M m a' sz v M' Hmok Es) Es Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fx_step_cell_mono : forall F F',
  fx_step IM code F = FNext F' -> forall x, cell_expl (f_mem F) x -> cell_expl (f_mem F') x.
Proof.
  intros F F' H x Hx. destruct (fx_step_mem IM code F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. exact Hx.
  - exact (fm_store_cell_mono _ _ _ _ _ Hst x Hx).
Qed.

Theorem fx_step_cell : forall F ms F' ms',
  Rr F ms -> fx_step IM code F = FNext F' -> step segs ms = MachineOk ms' ->
  forall x, ~ cell_expl (f_mem F') x -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros F ms F' ms' HR H Hs x Hx. unfold fx_step in H.
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
  (* [comment removed for export] *)
  assert (Hgo : forall a sz v M', f_mem F' = M' ->
            fm_store_abs IM (f_mem F) a sz v = Some M' ->
            dv rho a = exec_addr i (core_of ms) -> msz_nat sz = exec_nbytes i ->
            ms_mem ms' x = ms_mem ms x).
  { intros a sz v M' EM Es Ea En. apply Hfr. intros r Hr j Hj Ex.
    destruct (proj1 (Forall_forall _ _) Hex r Hr) as [E1 E2]. rewrite E1 in Ex. rewrite E2 in Hj.
    apply Hx. rewrite EM, Ex, <- Ea.
    exact (fm_store_abs_cell_expl (f_mem F) (ms_mem ms) a sz v M' j Hmok Es ltac:(rewrite En; exact Hj)). }
  destruct i; cbn [may_store] in Ems; try discriminate Ems; cbn [compile] in Hc; try discriminate Hc.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) ALU_ADD (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [a|] eqn:Ea; [|discriminate].
    destruct (fm_store_abs IM (f_mem F) a sz (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
    destruct (resv_after_store (f_resv F) a) as [r'|]; [|discriminate].
    injection H as <-. cbn [f_mem] in *.
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold alu64, alu in Ea.
    apply (Hgo a sz _ M' eq_refl Es0); [exact Ea | destruct sz; reflexivity].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    apply (aligned_for_sound rho Hrho0 _ _ _ HM) in Eal. rewrite <- Hregs in Eal.
    destruct (resv_eqb (f_resv F) (FxState.rget F (ireg rs1))) as [hit|] eqn:Ehit; [|discriminate].
    apply (resv_eqb_sound rho) in Ehit. rewrite <- (R_resv _ _ _ _ _ HR), <- Hregs in Ehit.
    destruct hit.
    + destruct (fm_store_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
      injection H as <-. cbn [f_mem] in *.
      apply (Hgo _ (awidth_sz w0) _ M' eq_refl Es0); [rewrite <- Hregs; reflexivity | destruct w0; reflexivity].
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
      injection H as <-; cbn [f_mem FxState.rset] in *;
      match goal with
      | Es0 : fm_store_abs IM _ _ _ _ = Some _ |- _ =>
          apply (Hgo _ (awidth_sz w0) _ _ eq_refl Es0); [rewrite <- Hregs; reflexivity | destruct w0; reflexivity]
      end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fx_run_cell_mono : forall bp k F F' r cnt,
  fx_run IM code bp k F = (F', r, cnt) -> forall x, cell_expl (f_mem F) x -> cell_expl (f_mem F') x.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt H x Hx.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63; [injection H as <- <- <-; exact Hx|].
    destruct (fx_step IM code F) as [s'| |c] eqn:Es; injection H as <- <- <-; try exact Hx.
    exact (fx_step_cell_mono F s' Es x Hx).
  - cbn [fx_run] in H. destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      exact (IH _ _ _ _ E2 x (IH _ _ _ _ E1 x Hx)).
    + injection H as <- <- <-. exact (IH _ _ _ _ E1 x Hx).
Qed.

(* [comment removed for export] *)
Theorem fx_run_cellframe : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F', r, cnt) ->
  forall ms ms', Rr F ms -> rsteps segs (nat_of_int cnt) ms = MachineOk ms' ->
  forall x, ~ cell_expl (f_mem F') x -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H ms ms' HR Hn x Hx.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. change (nat_of_int 0) with 0%nat in Hn. cbn [rsteps] in Hn. congruence. }
    destruct (fx_step IM code F) as [s'| |c] eqn:Es; injection H as <- <- <-;
      try (change (nat_of_int 0) with 0%nat in Hn; cbn [rsteps] in Hn; congruence).
    destruct (fx_step_sound segs IM rho Hrho0 code Hcode F ms s' HR Es) as (ms1 & Hs & _).
    change (nat_of_int 1) with 1%nat in Hn. cbn [rsteps] in Hn. rewrite (R_svc _ _ _ _ _ HR), Hs in Hn.
    injection Hn as <-. exact (fx_step_cell F ms s' ms1 HR Es Hs x Hx).
  - cbn [fx_run] in H. destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (fx_run_sound segs IM rho Hrho0 code Hcode bp k F s1 r1 n1 ltac:(lia) E1) as (Hb1 & IH1).
    assert (Hpow : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    assert (Hlt : 2 ^ Z.of_nat (S k) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & _).
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      destruct (fx_run_sound segs IM rho Hrho0 code Hcode bp k s1 s2 r2 n2 ltac:(lia) E2) as (Hb2 & IH2).
      destruct (IH2 ms1 HR1) as (ms2 & Hn2 & _).
      pose proof (Uint63.to_Z_bounded n1). pose proof (Uint63.to_Z_bounded n2).
      assert (Hadd : to_Z (n1 + n2)%uint63 = to_Z n1 + to_Z n2).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
      assert (Hn12 : rsteps segs (nat_of_int (n1 + n2)%uint63) ms = MachineOk ms2).
      { unfold nat_of_int. rewrite Hadd, Z2Nat.inj_add by lia. exact (rsteps_trans segs _ _ _ _ _ Hn1 Hn2). }
      rewrite Hn12 in Hn. injection Hn as <-.
      rewrite (IH _ _ _ _ ltac:(lia) E2 ms1 ms2 HR1 Hn2 x Hx).
      apply (IH _ _ _ _ ltac:(lia) E1 ms ms1 HR Hn1 x).
      intros Hc. apply Hx. exact (fx_run_cell_mono _ _ _ _ _ _ E2 x Hc).
    + injection H as <- <- <-. rewrite Hn1 in Hn. injection Hn as <-.
      exact (IH _ _ _ _ ltac:(lia) E1 ms ms1 HR Hn1 x Hx).
Qed.
End FxSide.
