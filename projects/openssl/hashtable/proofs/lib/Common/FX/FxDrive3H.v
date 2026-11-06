(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive noacc : eff -> Prop :=
| na_done : forall c, noacc (EDone c)
| na_illegal : forall c, noacc (EIllegal c)
| na_defined_illegal : forall c, noacc (EDefinedIllegal c)
| na_ecall : forall c, noacc (EEcall c)
| na_ebreak : forall c, noacc (EEbreak c)
| na_fault : forall c, noacc (EFault c).

Ltac noacc_tac :=
  repeat first
    [ apply na_done | apply na_illegal | apply na_defined_illegal | apply na_ecall
    | apply na_ebreak | apply na_fault
    | match goal with
      | |- noacc (if ?x then _ else _) => destruct x
      | |- noacc (match ?x with _ => _ end) => destruct x
      | |- noacc ((match ?x with _ => _ end) _) => destruct x
      | |- noacc (?f (match ?x with _ => _ end)) => destruct x
      | |- noacc (?f (match ?x with _ => _ end) _) => destruct x
      end ].

Definition is_regop_i (i : instr) : bool :=
  match i with
  | Instr.Op _ _ _ _ | Instr.OpImm _ _ _ _ | Instr.ShiftImm _ _ _ _ | Instr.Branch _ _ _ _ => true
  | _ => false
  end.

Lemma exec_noacc : forall sz i c, is_regop_i i = true -> noacc (exec sz i c).
Proof.
  intros sz i c H. destruct i; cbn [is_regop_i] in H; try discriminate H; cbn [exec]; cbv zeta; noacc_tac.
Qed.

Section SpecSide.
Variable segs : list Segment.

Lemma interp_noacc : forall t, noacc t -> forall m report,
  interp_eff_accesses segs t m = MachineOk report -> @accessed_ranges _ report = [].
Proof.
  intros t Ht m report H. destruct Ht; cbn [interp_eff_accesses] in H; try discriminate H.
  inversion H; subst. reflexivity.
Qed.

Lemma regop_touch_ok lazy A ms w i :
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  is_regop_i i = true -> touch_ok segs lazy A ms.
Proof.
  intros Hf He Hd Hi report Hacc. unfold step_accesses in Hacc. rewrite Hf in Hacc.
  unfold decode_exec_accesses in Hacc. rewrite He, Hd in Hacc.
  match type of Hacc with context [interp_eff_accesses ?a ?b ?c] =>
    destruct (interp_eff_accesses a b c) as [r0| |] eqn:E end; try discriminate Hacc.
  pose proof (interp_noacc _ (exec_noacc _ i _ Hi) _ _ E) as Hnil.
  destruct (access_value _ r0) as [c m']. injection Hacc as <-. cbn [accessed_ranges]. rewrite Hnil.
  apply touch_allowed_nil.
Qed.
End SpecSide.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3H.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
(* [comment removed for export] *)
Variable A0 : list (Z * Z).

Local Abbreviation DI := (DInv cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation erase := (FxDrive3.erase wb0).
Local Abbreviation PX := (pext IM).
Local Abbreviation POK := (pc_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
Lemma DInv3_rho_ext n rho F L3 ms m n' rho' :
  D3 n rho F L3 ms m -> 0 < to_Z n -> to_Z n <= to_Z n' ->
  (forall t, to_Z t < to_Z n -> rho' t = rho t) ->
  D3 n' rho' F L3 ms m.
Proof.
  intros (HDI & HL & HS & HX) Hn0 Hnn Hrho.
  pose proof HDI as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  assert (Hag0 : agree n rho rho) by (split; [exact H0 | intros; reflexivity]).
  assert (Htag : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t).
  { intros t rg Hg. apply Hrho. exact (fxs_Rn_tag_lt segs IM n rho F ms rho t rg HRn Hag0 Hn0 Hg). }
  assert (Hival : forall t rg x, iget t (f_mem F) = Some rg -> (in_ival rho' t rg x <-> in_ival rho t rg x)).
  { intros t rg x Hg. unfold in_ival. rewrite (Htag t rg Hg). reflexivity. }
  assert (Hnoreg : forall x, no_region rho' (f_mem F) x <-> no_region rho (f_mem F) x).
  { intros x. split; intros Hno t rg Hg Hin; apply (Hno t rg Hg); apply (Hival t rg x Hg); exact Hin. }
  assert (Hden_lt : forall e0 : fent, to_Z (fent_tag e0) < to_Z n -> den rho' e0 = den rho e0).
  { intros [[t0 o0] l0] Ht0. cbn [fent_tag fst] in Ht0. cbn [den]. unfold adr. rewrite (Hrho t0 Ht0). reflexivity. }
  destruct HL as [Hpi Hreg Hpw Hml Hsub HAb Hlim Hex Hexna Hexlz H9a H9b Htags HE Hacc Hwfna Hwflz HopsR Hord Hopsf Hres].
  destruct HS as [Hz Hcovs Hsp Hexc].
  apply Forall_app in Htags as [Ht1 Htags]. apply Forall_app in Htags as [Ht2 Ht3].
  destruct (stable_den rho rho' n _ Hrho Ht1) as [Eall _].
  destruct (stable_den rho rho' n _ Hrho Ht3) as [_ EA].
  pose proof (lazy_cov_tags _ _ n Hsub Ht1) as Ht4.
  pose proof (lazy_cov_tags _ _ n Hexc Ht1) as Ht5.
  destruct (ops_apply_ext rho rho' (fl_ops L3)) as [Eops_na Eops_lz].
  { intros o Ho. apply Hden_lt. apply (proj1 (Forall_forall _ _) Ht2). apply in_map. exact Ho. }
  split; [|split; [|split]].
  - (* [comment removed for export] *)
    split.
    { intros rho'' [H0'' Hag'']. apply HRn. split; [exact H0''|]. intros t Ht. rewrite (Hag'' t ltac:(lia)). exact (Hrho t Ht). }
    split; [rewrite (Hrho 0%uint63) by (rewrite to_Z_0; lia); exact H0|].
    split; [exact Hh|]. split; [exact Hnl|]. split; [exact Hli|].
    split.
    { intros t rg Hg. destruct (Hcov t rg Hg) as [Hne Hb]. split; [exact Hne|].
      intros x Hx. apply Hb. apply (Hival t rg x Hg). exact Hx. }
    split.
    { destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). split; [|split].
      - eapply Forall_impl; [|exact Hm1]. intros e He. destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg].
        exact (ent_ok_ext rho rho' _ _ _ _ e (Htag _ _ Hrg) eq_refl (fun q Hq => Hq) He).
      - eapply Forall_impl; [|exact Hm2]. intros e He. destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg].
        exact (ent_ok_ext rho rho' _ _ _ _ e (Htag _ _ Hrg) eq_refl (fun q Hq => Hq) He).
      - exists rgb. split; [exact Hgb|]. rewrite (adr_rho rho rho' _ _ (Htag _ _ Hgb)). exact Hbrk. }
    split; [exact I|].
    split; [apply (XI_rho rho rho'); [intros tx Htx; exact (Hrho tx (Hxt tx Htx)) | exact HXI]|].
    split; [intros tx Htx; pose proof (Hxt tx Htx); lia|].
    intros t Ht. destruct (Hfr t Ht) as [Hpr Hmem]. split; [exact Hpr|].
    intros rg x Hg Hx. apply (Hmem rg x Hg). apply (Hival t rg _ Hg). exact Hx.
  - (* [comment removed for export] *)
    constructor; unfold FxDrive3.allowed; rewrite ?EA; try assumption.
    + intros t rg pn p x Hg Hpn Hp Hx Hxl. rewrite (Htag t rg Hg). exact (Hreg t rg pn p x Hg Hpn Hp Hx Hxl).
    + intros e p He Hp H1 H2. rewrite (Hden_lt e (proj1 (Forall_forall _ _) Ht4 e He)) in H1, H2.
      exact (Hpw e p He Hp H1 H2).
    + rewrite Hex, Eall. reflexivity.
    + rewrite Hexna. symmetry. apply Eops_na.
    + rewrite Hexlz. symmetry. apply Eops_lz.
    + rewrite !Forall_app. split; [|split]; (eapply Forall_impl; [|eassumption]); cbv beta; intros; lia.
    + intros o x p Ho Hp Hx.
      rewrite (Hden_lt (snd o)) in Hx by (apply (proj1 (Forall_forall _ _) Ht2); apply in_map; exact Ho).
      exact (HopsR o x p Ho Hp Hx).
    + apply (ords_ok_ext n rho); [exact Hnn | exact Hrho | exact Hord].
    + apply Forall_forall. intros o Ho.
      assert (Hto : to_Z (fent_tag (snd o)) < to_Z n)
        by (apply (proj1 (Forall_forall _ _) Ht2); apply in_map; exact Ho).
      apply (op_ok_ext n rho rho' m m (fl_all L3) (fl_all L3) o Hrho Hto Ht1 eq_refl (fun e' He' _ => He')).
      exact (proj1 (Forall_forall _ _) Hopsf o Ho).
    + apply (ress_ok_ext n rho); [exact Hnn | exact Hrho | exact Hres].
  - (* [comment removed for export] *)
    constructor.
    + intros x Hx Hno Hnex. apply (Hz x Hx); [apply Hnoreg; exact Hno|].
      intros Hc. apply Hnex. apply (exempted_ext rho rho'); [|exact Hc].
      intros e0 He0. exact (Hden_lt e0 (proj1 (Forall_forall _ _) Ht5 e0 He0)).
    + intros x Hx. destruct (Hcovs x Hx) as (e0 & He0 & Et0 & Hpx). exists e0.
      split; [exact He0|]. split; [exact Et0|]. rewrite (Hden_lt e0) by (rewrite Et0, to_Z_0; lia). exact Hpx.
    + intros t rg Hg. pose proof (Hsp t rg Hg) as Hok. unfold span_ok in *. rewrite (Htag t rg Hg). exact Hok.
    + exact Hexc.
  - (* [comment removed for export] *)
    destruct HX as (X1 & X2 & X3 & X4 & X5). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    split; [|exact X5]. intros x Hx. destruct (X4 x Hx) as (Ht & Hno & Hm). split; [exact Ht|]. split; [|exact Hm].
    apply Hnoreg. exact Hno.
Qed.

(* [comment removed for export] *)
Lemma DInv3_regstep n rho F F' L3 ms ms' m m1 :
  D3 n rho F L3 ms m -> f_mem F' = f_mem F -> Rn n rho F' ms' ->
  ms_mem ms' = ms_mem ms -> ms_rom ms' = ms_rom ms -> ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms ->
  lazy_frame m m1 -> page_inv (allowed A0 rho L3) m1 -> mat_lazy m1 ->
  D3 n rho F' L3 ms' m1.
Proof.
  intros (HDI & HL & HS & HX) EM HRn' Emem Erom Efr Efc Hfr Hpi1 Hml1.
  destruct (lazy_frame_facts m m1 Hfr) as (_ & Evm & _).
  pose proof HDI as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfrm).
  split; [|split; [|split]].
  - rewrite (erase_lazy_frame wb0 m m1 Hfr).
    split; [exact HRn'|]. split; [exact H0|]. split; [exact Hh|]. split; [exact Hnl|]. split; [exact Hli|].
    rewrite EM. split; [exact Hcov|]. split; [exact Hmir|]. split; [exact I|]. split; [exact HXI|]. split; [exact Hxt|].
    rewrite Emem. exact Hfrm.
  - apply (lazy_part_next IM R0 Lim na0 lz0 A0 n rho F F' L3 m m1);
      [|exact Hfr | exact Hpi1 | exact Hml1 | intros t0 Hno; rewrite EM; exact Hno | exact HL].
    rewrite EM. exact (lazy_part_LZ IM R0 Lim na0 lz0 A0 n rho F L3 m HL).
  - destruct HS as [Hz Hcovs Hsp Hexc]. constructor; rewrite ?EM; try assumption.
    intros x Hx Hno Hnex. unfold rview, wview in *. rewrite Emem. exact (Hz x Hx Hno Hnex).
  - destruct HX as (X1 & X2 & X3 & X4 & X5). split; [congruence|]. split; [congruence|]. split; [congruence|].
    rewrite Evm, EM. split; [|exact X5]. intros x Hx. destruct (X4 x Hx) as (Ht & Hno & Hm).
    split; [exact Ht|]. split; [exact Hno|]. rewrite Emem. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma regstep_node n rho n' rho' F F' L3 ms ms' m w i :
  D3 n rho F L3 ms m -> 0 < to_Z n -> to_Z n <= to_Z n' ->
  (forall t, to_Z t < to_Z n -> rho' t = rho t) ->
  regions_lt_b n (f_mem F) = true ->
  f_mem F' = f_mem F -> Rn n' rho' F' ms' ->
  step segs ms = MachineOk ms' ->
  ms_mem ms' = ms_mem ms -> ms_rom ms' = ms_rom ms -> ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms ->
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) -> is_regop_i i = true ->
  exists m1, D3 n' rho' F' L3 ms' m1 /\ PX n rho F L3 ms m n' rho' F' L3 ms' m1
    /\ asteps segs 1 (ms, m) = MachineOk (ms', m1).
Proof.
  intros HD Hn0 Hnn Hrho Hlt EM HRn' Hstep Emem Erom Efr Efc Hf He Hd Hri.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (lp_pi _ _ _ _ _ _ _ _ _ _ _ HL) as Hpi.
  assert (Hr1 : rsteps segs 1 ms = MachineOk ms').
  { cbn [rsteps]. rewrite Hsvc, Hstep. reflexivity. }
  assert (Ht : forall j msj, (j < 1)%nat -> rsteps segs j ms = MachineOk msj ->
                 touch_ok segs (m_vm_lazy m) (allowed A0 rho L3) msj).
  { intros j msj Hj Hrj. assert (j = 0)%nat by lia. subst j. cbn [rsteps] in Hrj. injection Hrj as <-.
    exact (regop_touch_ok segs _ _ ms w i Hf He Hd Hri). }
  destruct (asteps_pages segs (allowed A0 rho L3) 1 ms ms' m Hr1 Hpi Ht) as (m1 & Ha & Hfr & Hpi1).
  pose proof (asteps_mat_lazy segs _ ms m ms' m1 Ha (lp_mat _ _ _ _ _ _ _ _ _ _ _ HL)) as Hml1.
  pose proof (DInv3_rho_ext n rho F L3 ms m n' rho' HD Hn0 Hnn Hrho) as HDe.
  assert (EA : allowed A0 rho' L3 = allowed A0 rho L3).
  { unfold FxDrive3.allowed. f_equal. apply denA_ext. intros e0 He0.
    pose proof (lp_tags _ _ _ _ _ _ _ _ _ _ _ HL) as Htg. apply Forall_app in Htg as [_ Htg]. apply Forall_app in Htg as [_ Htg].
    apply Hrho. exact (proj1 (Forall_forall _ _) Htg e0 He0). }
  exists m1. split; [|split; [|exact Ha]].
  - apply (DInv3_regstep n' rho' F F' L3 ms ms' m m1 HDe); try assumption. rewrite EA. exact Hpi1.
  - destruct (lazy_frame_facts m m1 Hfr) as (_ & Evm & _). split.
    + split; [exact Hnn|]. split; [exact Hrho|]. split; [exact (lazy_frame_same_but_vm m m1 Hfr)|].
      rewrite Evm. repeat split; reflexivity.
    + assert (Htagr : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t).
      { intros t rg Hg. apply Hrho. exact (regions_lt_b_ok n _ Hlt t rg Hg). }
      exists []. split; [symmetry; apply app_nil_r|]. split; [constructor|]. split; [|split].
      * intros y _ _. rewrite Emem. reflexivity.
      * intros y (t & rg & pn & p & j & Hg & Hpn & Hp & Hw & Hj & Hjl & ->). left.
        rewrite EM in Hg. exists t, rg, pn, p, j. repeat (split; [assumption|]).
        unfold adr. rewrite (Htagr t rg Hg). reflexivity.
      * intros y (t & rg & pn & p & ci & Hg & Hp & Hci & j & Hj & ->). left.
        exists t, rg, pn, p, ci. rewrite EM. split; [exact Hg|]. split; [exact Hp|].
        split; [exact Hci|]. exists j. split; [exact Hj|]. unfold adr. rewrite (Htagr t rg Hg). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_opaque (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some fi =>
      match regop_of fi with
      | Some (_, rd) =>
          if tag_ok F n then Some (D3One (FxState.rset F rd (FV n w_zero) (f_pc F + 4)%uint63) L3 (n + 1)%uint63)
          else None
      | None => None
      end
  | None => None
  end.

Theorem xpc_opaque_sound n rho F L3 ms m res :
  xpc_opaque F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_opaque in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct (regop_of fi) as [[op rd]|] eqn:Hro; [|discriminate].
  destruct (tag_ok F n) eqn:Htag; [|discriminate]. injection Hx as <-.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 Hn60].
  apply ltb_spec in Hn0, Hn60. rewrite to_Z_0 in Hn0. change (to_Z 1152921504606846976) with (2 ^ 60) in Hn60.
  pose proof (to_Z_succ61 R0 n Hn60) as Hn1.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & _).
  change (m_halted (erase m)) with (m_halted m) in Hh.
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  (* [comment removed for export] *)
  assert (Hopn : exists wa wb, regop_opnds ms fi = Some (wa, wb)).
  { destruct fi; cbn [regop_of] in Hro; try discriminate Hro; cbn [regop_opnds]; eexists _, _; reflexivity. }
  destruct Hopn as (wa & wb & Hopn).
  destruct (fx_step_regop segs IM rho H0 code Hcode F ms fi op rd wa wb HR Hi Hro Hopn)
    as (ms' & Hstep & Emem & Erom & Efr & Efc & Hmk).
  set (x := alu64 op wa wb).
  set (rho' := rho_upd rho n x).
  set (F' := FxState.rset F rd (FV n w_zero) (f_pc F + 4)%uint63).
  assert (Hrho : forall t, to_Z t < to_Z n -> rho' t = rho t).
  { intros t Ht. unfold rho'. apply rho_upd_other. apply (lt_neq R0). exact Ht. }
  assert (Hdvn : forall rho2, rho2 n = x -> dv rho2 (FV n w_zero) = x).
  { intros rho2 E. rewrite (fk_dv_plain rho2 (FV n w_zero)) by (cbn [vtag]; lia).
    cbn [vtag vw]. rewrite E, wbv_w_zero. apply bv_eq. rewrite bv_add_unsigned. unfold w0.
    change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r. apply bv_wrap_bv_unsigned. }
  (* [comment removed for export] *)
  assert (HRn' : Rn (n + 1)%uint63 rho' F' ms').
  { intros rho2 Hag2. destruct (agree_upd n rho x rho2 ltac:(lia) Hag2) as [Hag Hn2].
    pose proof (HRn rho2 Hag) as HR2.
    destruct (fx_step_regop segs IM rho2 (proj1 Hag) code Hcode F ms fi op rd wa wb HR2 Hi Hro Hopn)
      as (ms2 & Hstep2 & _ & _ & _ & _ & Hmk2).
    rewrite Hstep in Hstep2. injection Hstep2 as <-. apply Hmk2. exact (Hdvn rho2 Hn2). }
  (* [comment removed for export] *)
  destruct (code_entry segs IM rho code Hcode F ms fi HR Hi) as (Hpcb & w & Hf & [[He Efi] | (He & i & Hd & Hc)]).
  { rewrite Efi in Hro. discriminate Hro. }
  assert (Hri : is_regop_i i = true).
  { destruct i; cbn [compile] in Hc; try discriminate Hc; try reflexivity;
      try (destruct (pc_of_word _); try discriminate Hc; try (destruct (pc_of_word _); try discriminate Hc));
      apply some_inj in Hc; subst fi; discriminate Hro. }
  destruct (regstep_node n rho (n + 1)%uint63 rho' F F' L3 ms ms' m w i HD Hn0 ltac:(lia) Hrho Hlt eq_refl HRn'
              Hstep Emem Erom Efr Efc Hf He Hd Hri) as (m1 & HD' & HPX & Ha).
  split.
  - intros T HT. apply (rzc_asteps cfg segs 1 ms m ms' m1 T Hh Ha).
    exact (HT F' L3 (n + 1)%uint63 rho' ms' m1 eq_refl HD' HPX).
  - exists F', L3, (n + 1)%uint63, rho', ms', m1. split; [reflexivity|]. split; [exact HD'|]. split; [exact HPX|].
    exact (asteps_star_cfg cfg segs 1 ms m ms' m1 Hh Ha).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ord_ledger3 (L3 : fledger3) (o : int * int * Z) : fledger3 :=
  FL3 (fl3 L3) (fl_all L3) (fl_ops L3) (fl_lazy L3) (fl_allow L3) (fl_Ab L3) (fl_E L3) (fl_ex L3) (o :: fl_ord L3) (fl_res L3).

(* [comment removed for export] *)
Definition ord_below (ords : list (int * int * Z)) (ta tb : int) (z : Z) : bool :=
  existsb (fun o => (fst (fst o) =? ta)%uint63 && (snd (fst o) =? tb)%uint63 && (z <? snd o)) ords.

Definition ltu_cond (c : branch_cond) : option bool :=
  match c with BC_LTU => Some true | BC_GEU => Some false | _ => None end.

Definition xpc_order (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some (FBranch c rs1 rs2 tgt npc) =>
      let a := FxState.rget F rs1 in
      let b := FxState.rget F rs2 in
      match ltu_cond c with
      | Some isltu =>
        if (vtag a =? vtag b)%uint63 || negb (tag_ok F n) then None else
        match fv_inb_s (f_mem F) a, fv_inb_s (f_mem F) b with
        | Some ra, Some rb =>
            let pc_lt := if isltu then tgt else npc in
            let pc_ge := if isltu then npc else tgt in
            let z := wZ (vw a) - wZ (vw b) in
            if ord_below (fl_ord L3) (vtag a) (vtag b) z then Some (D3One (set_pc F pc_lt) L3 n)
            else if ord_below (fl_ord L3) (vtag b) (vtag a) (- z) then Some (D3One (set_pc F pc_ge) L3 n)
            else Some (D3Two (set_pc F pc_lt) (ord_ledger3 L3 (vtag a, vtag b, to_Z (rg_len ra) - to_Z (rg_lo rb))) n
                             (set_pc F pc_ge) (ord_ledger3 L3 (vtag b, vtag a, to_Z (rg_len rb) - to_Z (rg_lo ra))) n)
        | _, _ => None
        end
      | None => None
      end
  | _ => None
  end.

Lemma ord_below_sound n rho ords ta tb z :
  ord_below ords ta tb z = true -> Forall (ord_ok n rho) ords ->
  bv_unsigned (rho ta) + z < bv_unsigned (rho tb).
Proof.
  intros H Hall. unfold ord_below in H. apply existsb_exists in H as (o & Ho & Hc).
  apply andb_true_iff in Hc as [Hc Hz]. apply andb_true_iff in Hc as [E1 E2].
  apply Uint63.eqb_spec in E1, E2. apply Z.ltb_lt in Hz. subst ta tb.
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & _ & Hd). lia.
Qed.

(* [comment removed for export] *)
Lemma DInv3_add_ord n rho F L3 ms m o :
  D3 n rho F L3 ms m -> ord_ok n rho o -> D3 n rho F (ord_ledger3 L3 o) ms m.
Proof.
  intros (HDI & HL & HS & HX) Ho. split; [exact HDI|]. split; [|split; [|exact HX]].
  - destruct HL. constructor; try assumption. cbn [ord_ledger3 fl_ord]. constructor; assumption.
  - destruct HS. constructor; assumption.
Qed.

Theorem xpc_order_sound n rho F L3 ms m res :
  xpc_order F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_order in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct fi as [| | |c rs1 rs2 tgt npc| | | | | | | | | | | | |]; try discriminate Hx.
  cbv zeta in Hx.
  destruct (ltu_cond c) as [isltu|] eqn:Hc; [|discriminate].
  set (a := FxState.rget F rs1) in *. set (b := FxState.rget F rs2) in *.
  destruct ((vtag a =? vtag b)%uint63 || negb (tag_ok F n)) eqn:Hg; [discriminate|].
  apply orb_false_iff in Hg as [Et Htag]. apply negb_false_iff in Htag. apply eqb_false_spec in Et.
  destruct (fv_inb_s (f_mem F) a) as [ra|] eqn:Ia; [|discriminate].
  destruct (fv_inb_s (f_mem F) b) as [rb|] eqn:Ib; [|discriminate].
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0. rewrite to_Z_0 in Hn0.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & _).
  change (m_halted (erase m)) with (m_halted m) in Hh.
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (R_regs_ok _ _ _ _ _ HR) as HM.
  pose proof (proj2 (R_mem _ _ _ _ _ HR)) as Hsep.
  destruct (fv_inb_s_sound rho (f_mem F) a ra HM Ia) as (Ga & Ua & Oa & La).
  destruct (fv_inb_s_sound rho (f_mem F) b rb HM Ib) as (Gb & Ub & Ob & Lb).
  pose proof (regions_lt_b_ok n _ Hlt) as Hrl.
  pose proof (Hrl _ _ Ga) as Hta. pose proof (Hrl _ _ Gb) as Htb.
  (* [comment removed for export] *)
  destruct (fx_step_branch segs IM rho code Hcode F ms c rs1 rs2 tgt npc HR Hi)
    as (ms' & Hstep & Emem & Erom & Efr & Efc & _ & Ev1 & Ev2).
  fold a in Ev1. fold b in Ev2.
  set (bt := branch_taken c (mval ms rs1) (mval ms rs2)).
  set (F' := set_pc F (if bt then tgt else npc)).
  assert (HRn' : Rn n rho F' ms').
  { intros rho2 Hag2. pose proof (HRn rho2 Hag2) as HR2.
    destruct (fx_step_branch segs IM rho2 code Hcode F ms c rs1 rs2 tgt npc HR2 Hi)
      as (ms2 & Hstep2 & _ & _ & _ & _ & HR2' & _).
    rewrite Hstep in Hstep2. injection Hstep2 as <-. exact HR2'. }
  destruct (code_entry segs IM rho code Hcode F ms _ HR Hi) as (Hpcb & w & Hf & [[He Efi] | (He & i & Hd & Hci)]);
    [discriminate Efi|].
  assert (Hri : is_regop_i i = true).
  { destruct i; cbn [compile] in Hci; try discriminate Hci; try reflexivity;
      try (destruct (pc_of_word _); try discriminate Hci; try (destruct (pc_of_word _); try discriminate Hci)). }
  destruct (regstep_node n rho n rho F F' L3 ms ms' m w i HD Hn0 ltac:(lia) (fun t _ => eq_refl) Hlt eq_refl HRn'
              Hstep Emem Erom Efr Efc Hf He Hd Hri) as (m1 & HD' & HPX & Ha).
  (* [comment removed for export] *)
  set (lt := bv_ltu (dv rho a) (dv rho b)).
  assert (Hbt : bt = if isltu then lt else negb lt).
  { unfold bt, lt. rewrite Ev1, Ev2. destruct c; cbn [ltu_cond] in Hc; try discriminate Hc;
      injection Hc as <-; reflexivity. }
  assert (Hltu : lt = true <-> bv_unsigned (dv rho a) < bv_unsigned (dv rho b)).
  { unfold lt, bv_ltu. apply Z.ltb_lt. }
  assert (HF' : F' = set_pc F (if lt then (if isltu then tgt else npc) else (if isltu then npc else tgt))).
  { unfold F'. rewrite Hbt. destruct isltu, lt; reflexivity. }
  pose proof (lp_ord _ _ _ _ _ _ _ _ _ _ _ HL) as Hord.
  (* [comment removed for export] *)
  assert (Hone : forall Fc Lc, dres3_in (Fc, Lc, n) res -> Fc = F' -> D3 n rho F' Lc ms' m1 ->
            PX n rho F L3 ms m n rho F' Lc ms' m1 -> POK n rho F L3 res ms m).
  { intros Fc Lc Hin -> HDc HPc. split.
    - intros T HT. apply (rzc_asteps cfg segs 1 ms m ms' m1 T Hh Ha). exact (HT F' Lc n rho ms' m1 Hin HDc HPc).
    - exists F', Lc, n, rho, ms', m1. split; [exact Hin|]. split; [exact HDc|]. split; [exact HPc|].
      exact (asteps_star_cfg cfg segs 1 ms m ms' m1 Hh Ha). }
  destruct (ord_below (fl_ord L3) (vtag a) (vtag b) (wZ (vw a) - wZ (vw b))) eqn:B1.
  { (* [comment removed for export] *)
    injection Hx as <-. pose proof (ord_below_sound n rho _ _ _ _ B1 Hord) as Hdz.
    assert (El : lt = true) by (apply Hltu; lia).
    apply (Hone F' L3); [cbn [dres3_in]; rewrite HF', El; reflexivity | reflexivity | exact HD' | exact HPX]. }
  destruct (ord_below (fl_ord L3) (vtag b) (vtag a) (- (wZ (vw a) - wZ (vw b)))) eqn:B2.
  { (* [comment removed for export] *)
    injection Hx as <-. pose proof (ord_below_sound n rho _ _ _ _ B2 Hord) as Hdz.
    assert (El : lt = false).
    { apply not_true_is_false. intros E. apply Hltu in E. lia. }
    apply (Hone F' L3); [cbn [dres3_in]; rewrite HF', El; reflexivity | reflexivity | exact HD' | exact HPX]. }
  (* [comment removed for export] *)
  injection Hx as <-.
  pose proof (Hsep (vtag a) (vtag b) ra rb Et Ga Gb) as Hds.
  destruct (Bool.bool_dec lt true) as [El|El].
  - pose proof (proj1 Hltu El) as Hlt'.
    assert (Ho : ord_ok n rho (vtag a, vtag b, to_Z (rg_len ra) - to_Z (rg_lo rb))).
    { split; [exact Hta|]. split; [exact Htb|]. cbn [fst snd]. lia. }
    apply (Hone F' (ord_ledger3 L3 (vtag a, vtag b, to_Z (rg_len ra) - to_Z (rg_lo rb)))).
    + cbn [dres3_in]. left. rewrite HF', El. reflexivity.
    + reflexivity.
    + exact (DInv3_add_ord _ _ _ _ _ _ _ HD' Ho).
    + exact HPX.
  - assert (El' : ~ bv_unsigned (dv rho a) < bv_unsigned (dv rho b)).
    { intros Hc'. apply Hltu in Hc'. contradiction. }
    apply not_true_is_false in El.
    assert (Ho : ord_ok n rho (vtag b, vtag a, to_Z (rg_len rb) - to_Z (rg_lo ra))).
    { split; [exact Htb|]. split; [exact Hta|]. cbn [fst snd]. lia. }
    apply (Hone F' (ord_ledger3 L3 (vtag b, vtag a, to_Z (rg_len rb) - to_Z (rg_lo ra)))).
    + cbn [dres3_in]. right. rewrite HF', El. reflexivity.
    + reflexivity.
    + exact (DInv3_add_ord _ _ _ _ _ _ _ HD' Ho).
    + exact HPX.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_or (x1 x2 : fstate -> fledger3 -> int -> option dres3) (F : fstate) (L3 : fledger3) (n : int)
    : option dres3 :=
  match x1 F L3 n with Some r => Some r | None => x2 F L3 n end.

Lemma xpc_or_sound (x1 x2 : fstate -> fledger3 -> int -> option dres3) :
  (forall n rho F L3 ms m res, x1 F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m) ->
  (forall n rho F L3 ms m res, x2 F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m) ->
  forall n rho F L3 ms m res, xpc_or x1 x2 F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros H1 H2 n rho F L3 ms m res Hx HD. unfold xpc_or in Hx.
  destruct (x1 F L3 n) as [r|] eqn:E1.
  - injection Hx as <-. exact (H1 _ _ _ _ _ _ _ E1 HD).
  - exact (H2 _ _ _ _ _ _ _ Hx HD).
Qed.

Definition xpc_builtin : fstate -> fledger3 -> int -> option dres3 := xpc_or xpc_order xpc_opaque.

Theorem xpc_builtin_sound n rho F L3 ms m res :
  xpc_builtin F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof. exact (xpc_or_sound _ _ xpc_order_sound xpc_opaque_sound n rho F L3 ms m res). Qed.

(* [comment removed for export] *)
Definition xpc_none (F : fstate) (L3 : fledger3) (n : int) : option dres3 := None.
Lemma xpc_none_sound n rho F L3 ms m res :
  xpc_none F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof. discriminate. Qed.

End Drive3H.
