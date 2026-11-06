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
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S FxDrive3H.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition regop_fvals (F : fstate) (fi : finstr) : option (fval * fval) :=
  match fi with
  | FOp _ _ rs1 rs2 => Some (FxState.rget F rs1, FxState.rget F rs2)
  | FOpImm _ _ rs1 imm => Some (FxState.rget F rs1, FV 0 imm)
  | _ => None
  end.

Lemma regop_opnds_dv (segs : list Segment) (IM : fimage) (rho : int -> word) (Hrho0 : rho 0%uint63 = Z_to_bv 64 0)
    (code : itrie finstr) (Hcode : code_ok segs code) : forall F ms fi wa wb a b,
  R segs IM rho F ms -> iget (f_pc F) code = Some fi ->
  regop_opnds ms fi = Some (wa, wb) -> regop_fvals F fi = Some (a, b) -> wa = dv rho a /\ wb = dv rho b.
Proof.
  intros F ms fi wa wb a b HR Hi Hopn Hfv.
  destruct (code_entry segs IM rho code Hcode F ms fi HR Hi) as (Hpc & w & Hf & [[He ->] | (He & i & Hd & Hc)]);
    [discriminate Hopn|].
  assert (Hmv : forall r : reg, mval ms (ireg r) = Sem.rget (core_of ms) r).
  { intros r. unfold mval. rewrite ireg_to_Z, Z_to_bv_bv_unsigned. reflexivity. }
  pose proof (R_regs _ _ _ _ _ HR) as Hregs.
  destruct i; cbn [compile] in Hc; try discriminate;
    try (destruct (pc_of_word _); try discriminate; try (destruct (pc_of_word _); try discriminate));
    apply some_inj in Hc; subst fi; cbn [regop_fvals regop_opnds] in Hfv, Hopn; try discriminate Hfv;
    injection Hfv as <- <-; injection Hopn as <- <-; rewrite ?Hmv, ?Hregs, ?(dv_conc rho Hrho0); split; reflexivity.
Qed.

Section Drive3T.
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

Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation PX := (pext IM).
Local Abbreviation POK := (pc_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
Definition sprop := int -> (int -> word) -> fstate -> fledger3 -> machine_state -> Model -> Prop.
Definition reach (n : int) (rho : int -> word) (F : fstate) (L3 : fledger3) (ms : machine_state) (m : Model)
    (P : sprop) : Prop :=
  (forall T,
     (forall n' rho' F' L' ms' m', P n' rho' F' L' ms' m' -> D3 n' rho' F' L' ms' m' ->
        PX n rho F L3 ms m n' rho' F' L' ms' m' -> realizes_cfg cfg segs (mkCfg ms' m') T) ->
     realizes_cfg cfg segs (mkCfg ms m) T)
  /\ (exists n' rho' F' L' ms' m', P n' rho' F' L' ms' m' /\ D3 n' rho' F' L' ms' m'
        /\ PX n rho F L3 ms m n' rho' F' L' ms' m' /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')).

Lemma reach_POK n rho F L3 ms m res :
  reach n rho F L3 ms m (fun n' _ F' L' _ _ => dres3_in (F', L', n') res) -> POK n rho F L3 res ms m.
Proof.
  intros [H1 H2]. split.
  - intros T HT. apply H1. intros n' rho' F' L' ms' m' HP HD HX. exact (HT F' L' n' rho' ms' m' HP HD HX).
  - destruct H2 as (n' & rho' & F' & L' & ms' & m' & HP & HD & HX & Hs). exists F', L', n', rho', ms', m'. auto.
Qed.

Lemma reach_ret n rho F L3 ms m (P : sprop) :
  D3 n rho F L3 ms m -> P n rho F L3 ms m -> reach n rho F L3 ms m P.
Proof.
  intros HD HP. split.
  - intros T HT. exact (HT n rho F L3 ms m HP HD (pext_refl IM R0 rom0 hi n rho F L3 ms m)).
  - exists n, rho, F, L3, ms, m. split; [exact HP|]. split; [exact HD|]. split; [apply (pext_refl IM R0 rom0 hi) | apply star_cfg_refl].
Qed.

Lemma reach_bind n rho F L3 ms m (P Q : sprop) :
  reach n rho F L3 ms m P ->
  (forall n' rho' F' L' ms' m', P n' rho' F' L' ms' m' -> D3 n' rho' F' L' ms' m' -> reach n' rho' F' L' ms' m' Q) ->
  reach n rho F L3 ms m Q.
Proof.
  intros [H1 H2] Hk. split.
  - intros T HT. apply H1. intros n1 rho1 F1 L1 ms1 m1 HP HD HX.
    destruct (Hk _ _ _ _ _ _ HP HD) as [K1 _]. apply K1. intros n2 rho2 F2 L2 ms2 m2 HQ HD2 HX2.
    exact (HT _ _ _ _ _ _ HQ HD2 (pext_trans IM R0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX HX2)).
  - destruct H2 as (n1 & rho1 & F1 & L1 & ms1 & m1 & HP & HD & HX & Hs).
    destruct (Hk _ _ _ _ _ _ HP HD) as [_ (n2 & rho2 & F2 & L2 & ms2 & m2 & HQ & HD2 & HX2 & Hs2)].
    exists n2, rho2, F2, L2, ms2, m2. split; [exact HQ|]. split; [exact HD2|].
    split; [exact (pext_trans IM R0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX HX2)|].
    exact (star_cfg_trans cfg segs _ [] _ [] _ Hs Hs2).
Qed.

(* [comment removed for export] *)
Lemma pext_same_mem n rho F L3 ms m n' rho' F' ms' m1 :
  to_Z n <= to_Z n' -> (forall t, to_Z t < to_Z n -> rho' t = rho t) -> regions_lt_b n (f_mem F) = true ->
  f_mem F' = f_mem F -> ms_mem ms' = ms_mem ms -> lazy_frame m m1 ->
  PX n rho F L3 ms m n' rho' F' L3 ms' m1.
Proof.
  intros Hnn Hrho Hlt EM Emem Hfr.
  destruct (lazy_frame_facts m m1 Hfr) as (_ & Evm & _). split.
  - split; [exact Hnn|]. split; [exact Hrho|]. split; [exact (lazy_frame_same_but_vm m m1 Hfr)|].
    rewrite Evm. repeat split; reflexivity.
  - assert (Htagr : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t).
    { intros t rg Hg. apply Hrho. exact (regions_lt_b_ok n _ Hlt t rg Hg). }
    exists []. split; [symmetry; apply app_nil_r|]. split; [constructor|]. split; [|split].
    + intros y _ _. rewrite Emem. reflexivity.
    + intros y (t & rg & pn & p & j & Hg & Hpn & Hp & Hw & Hj & Hjl & ->). left.
      rewrite EM in Hg. exists t, rg, pn, p, j. repeat (split; [assumption|]).
      unfold adr. rewrite (Htagr t rg Hg). reflexivity.
    + intros y (t & rg & pn & p & ci & Hg & Hp & Hci & j & Hj & ->). left.
      exists t, rg, pn, p, ci. rewrite EM. split; [exact Hg|]. split; [exact Hp|].
      split; [exact Hci|]. exists j. split; [exact Hj|]. unfold adr. rewrite (Htagr t rg Hg). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma reach_run n rho F L3 ms m bp k F1 r cnt :
  (k <= 61)%nat -> fx_run IM code bp k F = (F1, r, cnt) -> D3 n rho F L3 ms m ->
  reach n rho F L3 ms m (fun n' rho' F' L' _ _ => n' = n /\ rho' = rho /\ F' = F1 /\ L' = L3).
Proof.
  intros Hk Hrun HD.
  destruct (DInv3_run cfg segs IM code Hcode R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
              n rho F L3 ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & _ & _ & Hm & Hcps & (m1 & Hfr & HD1 & Hst)).
  assert (HPX : forall m2, lazy_frame m m2 -> PX n rho F L3 ms m n rho F1 L3 ms1 m2).
  { intros m2 Hfr2. destruct (lazy_frame_facts m m2 Hfr2) as (_ & Evm & _). split; [|exact Hm].
    split; [lia|]. split; [intros; reflexivity|]. split; [exact (lazy_frame_same_but_vm m m2 Hfr2)|].
    rewrite Evm. repeat split; reflexivity. }
  split.
  - intros T HT. apply Hcps. intros m2 Hfr2 HD2. exact (HT n rho F1 L3 ms1 m2 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) HD2 (HPX m2 Hfr2)).
  - exists n, rho, F1, L3, ms1, m1. split; [repeat split|]. split; [exact HD1|]. split; [exact (HPX m1 Hfr) | exact Hst].
Qed.

(* [comment removed for export] *)
Lemma reach_abs n rho Fc L3 ms m n' rho' F' (P : sprop) :
  D3 n rho Fc L3 ms m -> 0 < to_Z n -> to_Z n <= to_Z n' -> (forall t, to_Z t < to_Z n -> rho' t = rho t) ->
  regions_lt_b n (f_mem Fc) = true ->
  f_mem F' = f_mem Fc -> f_pc F' = f_pc Fc -> f_resv F' = f_resv Fc ->
  (forall rho2, agree n' rho' rho2 -> forall r, dv rho2 (FxState.rget F' r) = dv rho2 (FxState.rget Fc r)) ->
  P n' rho' F' L3 ms m -> reach n rho Fc L3 ms m P.
Proof.
  intros HD Hn0 Hnn Hrho Hlt EM Epc Eresv Hregs HP.
  pose proof (DInv3_rho_ext cfg segs IM R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
                n rho Fc L3 ms m n' rho' HD Hn0 Hnn Hrho) as HDe.
  pose proof HDe as (HDI & HL & _ & _). pose proof HDI as (HRn & _).
  assert (HRn' : Rn n' rho' F' ms).
  { intros rho2 Hag. pose proof (HRn rho2 Hag) as HR. constructor.
    - rewrite Epc. exact (R_pc _ _ _ _ _ HR).
    - intros r. rewrite (Hregs rho2 Hag). exact (R_regs _ _ _ _ _ HR r).
    - exact (R_svc _ _ _ _ _ HR).
    - rewrite Eresv. exact (R_resv _ _ _ _ _ HR).
    - rewrite EM. exact (R_mem _ _ _ _ _ HR). }
  assert (HD' : D3 n' rho' F' L3 ms m).
  { apply (DInv3_regstep cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
             n' rho' Fc F' L3 ms ms m m HDe EM HRn'); try reflexivity.
    - apply lazy_frame_refl.
    - exact (lp_pi _ _ _ _ _ _ _ _ _ _ _ HL).
    - exact (lp_mat _ _ _ _ _ _ _ _ _ _ _ HL). }
  assert (HPX : PX n rho Fc L3 ms m n' rho' F' L3 ms m).
  { apply pext_same_mem; try assumption; [reflexivity | apply lazy_frame_refl]. }
  split.
  - intros T HT. exact (HT n' rho' F' L3 ms m HP HD' HPX).
  - exists n', rho', F', L3, ms, m. split; [exact HP|]. split; [exact HD'|]. split; [exact HPX | apply star_cfg_refl].
Qed.

(* [comment removed for export] *)
Lemma reach_regop_conc n rho F L3 ms m fi op rd a b :
  D3 n rho F L3 ms m -> 0 < to_Z n -> regions_lt_b n (f_mem F) = true ->
  iget (f_pc F) code = Some fi -> regop_of fi = Some (op, rd) -> regop_fvals F fi = Some (a, b) ->
  reach n rho F L3 ms m (fun n' rho' F' L' _ _ => n' = n /\ rho' = rho /\ L' = L3 /\
     F' = FxState.rset F rd (FV 0 (w_of_bv (alu64 op (dv rho a) (dv rho b)))) (f_pc F + 4)%uint63).
Proof.
  intros HD Hn0 Hlt Hi Hro Hfv.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & _).
  change (m_halted (FxDrive3.erase wb0 m)) with (m_halted m) in Hh.
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  assert (Hopn : exists wa wb, regop_opnds ms fi = Some (wa, wb)).
  { destruct fi; cbn [regop_of] in Hro; try discriminate Hro; cbn [regop_opnds]; eexists _, _; reflexivity. }
  destruct Hopn as (wa & wb & Hopn).
  destruct (regop_opnds_dv segs IM rho H0 code Hcode F ms fi wa wb a b HR Hi Hopn Hfv) as [Ea Eb].
  destruct (fx_step_regop segs IM rho H0 code Hcode F ms fi op rd wa wb HR Hi Hro Hopn)
    as (ms' & Hstep & Emem & Erom & Efr & Efc & Hmk).
  set (W := w_of_bv (alu64 op (dv rho a) (dv rho b))).
  set (F' := FxState.rset F rd (FV 0 W) (f_pc F + 4)%uint63).
  assert (HRn' : Rn n rho F' ms').
  { intros rho2 Hag2. pose proof (HRn rho2 Hag2) as HR2.
    destruct (fx_step_regop segs IM rho2 (proj1 Hag2) code Hcode F ms fi op rd wa wb HR2 Hi Hro Hopn)
      as (ms2 & Hstep2 & _ & _ & _ & _ & Hmk2).
    rewrite Hstep in Hstep2. injection Hstep2 as <-. apply Hmk2.
    rewrite (dv_conc rho2 (proj1 Hag2)). unfold W. rewrite wbv_w_of_bv, Ea, Eb. reflexivity. }
  destruct (code_entry segs IM rho code Hcode F ms fi HR Hi) as (Hpcb & w & Hf & [[He Efi] | (He & i & Hd & Hc)]).
  { rewrite Efi in Hro. discriminate Hro. }
  assert (Hri : is_regop_i i = true).
  { destruct i; cbn [compile] in Hc; try discriminate Hc; try reflexivity;
      try (destruct (pc_of_word _); try discriminate Hc; try (destruct (pc_of_word _); try discriminate Hc));
      apply some_inj in Hc; subst fi; discriminate Hro. }
  destruct (regstep_node cfg segs IM R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
              n rho n rho F F' L3 ms ms' m w i HD Hn0 ltac:(lia) (fun t _ => eq_refl) Hlt eq_refl HRn'
              Hstep Emem Erom Efr Efc Hf He Hd Hri) as (m1 & HD' & HPX & Ha).
  split.
  - intros T HT. apply (rzc_asteps cfg segs 1 ms m ms' m1 T Hh Ha).
    exact (HT n rho F' L3 ms' m1 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) HD' HPX).
  - exists n, rho, F', L3, ms', m1. split; [repeat split|]. split; [exact HD'|]. split; [exact HPX|].
    exact (asteps_star_cfg cfg segs 1 ms m ms' m1 Hh Ha).
Qed.

(* [comment removed for export] *)
Lemma i63_succ_neq (x : int) : (x =? x + 1)%uint63 = false.
Proof.
  apply eqb_false_spec. intros E. apply (f_equal to_Z) in E. rewrite add_spec, to_Z_1 in E.
  pose proof (i63_range x) as Hb. rewrite i63_wB in E.
  destruct (Z.eq_dec (to_Z x + 1) (2 ^ 63)) as [Ew|Ew].
  - rewrite Ew, Z.mod_same in E by lia. lia.
  - rewrite Z.mod_small in E by lia. lia.
Qed.

Lemma reach_step n rho F L3 ms m F1 :
  fx_step IM code F = FNext F1 -> D3 n rho F L3 ms m ->
  reach n rho F L3 ms m (fun n' rho' F' L' _ _ => n' = n /\ rho' = rho /\ F' = F1 /\ L' = L3).
Proof.
  intros Hs HD. apply (reach_run n rho F L3 ms m (f_pc F + 1)%uint63 0 F1 SFuel 1%uint63); [lia | | exact HD].
  cbn [fx_run]. rewrite i63_succ_neq, Hs. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fv_alu_conc M op x y : fv_alu M op (FV 0 x) (FV 0 y) = Some (FV 0 (w_alu op x y)).
Proof. destruct op; reflexivity. Qed.

Lemma fx_step_opimm_conc F op rd rs1 imm x :
  iget (f_pc F) code = Some (FOpImm op rd rs1 imm) -> FxState.rget F rs1 = FV 0 x ->
  fx_step IM code F = FNext (FxState.rset F rd (FV 0 (w_alu op x imm)) (f_pc F + 4)%uint63).
Proof. intros Hi Hr. unfold fx_step. rewrite Hi. cbv zeta. rewrite Hr, fv_alu_conc. reflexivity. Qed.

Lemma fx_step_op_conc F op rd rs1 rs2 x y :
  iget (f_pc F) code = Some (FOp op rd rs1 rs2) -> FxState.rget F rs1 = FV 0 x -> FxState.rget F rs2 = FV 0 y ->
  fx_step IM code F = FNext (FxState.rset F rd (FV 0 (w_alu op x y)) (f_pc F + 4)%uint63).
Proof. intros Hi Hr1 Hr2. unfold fx_step. rewrite Hi. cbv zeta. rewrite Hr1, Hr2, fv_alu_conc. reflexivity. Qed.

Lemma fx_step_load_conc F sz sgn rd rs1 imm x v :
  iget (f_pc F) code = Some (FLoad sz sgn rd rs1 imm) -> FxState.rget F rs1 = FV 0 x ->
  fm_load_abs IM (f_mem F) (FV 0 (w_alu ALU_ADD x imm)) sz sgn = Some v ->
  fx_step IM code F = FNext (FxState.rset F rd v (f_pc F + 4)%uint63).
Proof. intros Hi Hr Hl. unfold fx_step. rewrite Hi. cbv zeta. rewrite Hr, fv_alu_conc, Hl. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint all_idx (cnt : nat) (j : int) (f : int -> bool) : bool :=
  match cnt with O => true | S c => f j && all_idx c (j + 1)%uint63 f end.

Lemma all_idx_sound cnt : forall j f, all_idx cnt j f = true -> to_Z j + Z.of_nat cnt < 2 ^ 62 ->
  forall i, to_Z j <= to_Z i < to_Z j + Z.of_nat cnt -> f i = true.
Proof.
  induction cnt as [|c IH]; intros j f H Hb i Hi; [lia|].
  cbn [all_idx] in H. apply andb_true_iff in H as [Hj Hrest].
  destruct (Z.eq_dec (to_Z i) (to_Z j)) as [E|E].
  - apply to_Z_inj in E. subst i. exact Hj.
  - assert (Hj1 : to_Z (j + 1)%uint63 = to_Z j + 1).
    { pose proof (to_Z_bounded j). rewrite add_spec, to_Z_1. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    apply (IH (j + 1)%uint63 f Hrest); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition get_opimm (o : option finstr) : option (aluop * int * int * w64) :=
  match o with Some (FOpImm op rd rs imm) => Some (op, rd, rs, imm) | _ => None end.
Definition get_op (o : option finstr) : option (aluop * int * int * int) :=
  match o with Some (FOp op rd rs1 rs2) => Some (op, rd, rs1, rs2) | _ => None end.
Definition get_load (o : option finstr) : option (msize * bool * int * int * w64) :=
  match o with Some (FLoad sz sgn rd rs imm) => Some (sz, sgn, rd, rs, imm) | _ => None end.
Definition is_srl (op : aluop) : bool := match op with ALU_SRL => true | _ => false end.
Definition is_sll (op : aluop) : bool := match op with ALU_SLL => true | _ => false end.
Definition is_add (op : aluop) : bool := match op with ALU_ADD => true | _ => false end.

Lemma get_opimm_inv o op rd rs imm : get_opimm o = Some (op, rd, rs, imm) -> o = Some (FOpImm op rd rs imm).
Proof. destruct o as [[]|]; cbn; intros H; try discriminate H. injection H as -> -> -> ->. reflexivity. Qed.
Lemma get_op_inv o op rd rs1 rs2 : get_op o = Some (op, rd, rs1, rs2) -> o = Some (FOp op rd rs1 rs2).
Proof. destruct o as [[]|]; cbn; intros H; try discriminate H. injection H as -> -> -> ->. reflexivity. Qed.
Lemma get_load_inv o sz sgn rd rs imm : get_load o = Some (sz, sgn, rd, rs, imm) -> o = Some (FLoad sz sgn rd rs imm).
Proof. destruct o as [[]|]; cbn; intros H; try discriminate H. injection H as -> -> -> -> ->. reflexivity. Qed.

Definition tl_addr (lit sh imm : w64) (j : int) : fval :=
  FV 0 (w_alu ALU_ADD (w_alu ALU_ADD lit (w_alu ALU_SLL (W64 0 j) sh)) imm).

Definition tl_check (M : itrie region) (lit sh imm : w64) (sz : msize) (sgn : bool) (w0 : w64) (j : int) : bool :=
  match fm_load_abs IM M (tl_addr lit sh imm j) sz sgn with
  | Some v => (vtag v =? 0)%uint63 && w_eqb (vw v) w0
  | None => false
  end.

Definition xpc_table (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  let pc := f_pc F in
  match get_opimm (iget pc code), get_opimm (iget (pc + 4)%uint63 code),
        get_op (iget (pc + 4 + 4)%uint63 code), get_load (iget (pc + 4 + 4 + 4)%uint63 code) with
  | Some (op1, rI, rP, k), Some (op2, rJ, rI', sh), Some (op3, rJ2, rB, rJ'), Some (sz, sgn, rD, rJ2', imm) =>
      match fv_ival (f_mem F) (FxState.rget F rP) with
      | Some (lo, hi) =>
          let lit := vw (FxState.rget F rB) in
          let wl := w_srl lo k in
          let wh := w_srl hi k in
          let jl := wlo wl in
          let jh := wlo wh in
          if (is_srl op1 && is_sll op2 && is_add op3
              && (rI' =? rI) && (rJ' =? rJ) && (rJ2' =? rJ2)
              && negb (rI =? 0) && negb (rJ =? 0) && negb (rJ2 =? 0) && negb (rB =? 0)
              && negb (rB =? rI) && negb (rB =? rJ)
              && (vtag (FxState.rget F rB) =? 0)
              && tag_ok F n && (n <? 576460752303423488)
              && ((wtop wl land 1) =? 0) && ((wtop wh land 1) =? 0)
              && (jl <=? jh) && (jh <? 2305843009213693952) && (jh - jl <? 65536))%uint63
          then
            match fm_load_abs IM (f_mem F) (tl_addr lit sh imm jl) sz sgn with
            | Some v0 =>
                if (vtag v0 =? 0)%uint63
                   && all_idx (S (Z.to_nat (to_Z (jh - jl)%uint63))) jl (tl_check (f_mem F) lit sh imm sz sgn (vw v0))
                then Some (D3One (FxState.rset (FxState.rset (FxState.rset (FxState.rset F
                                    rI (FV n w_zero) (pc + 4)%uint63)
                                    rJ (FV (n + 1)%uint63 w_zero) (pc + 4 + 4)%uint63)
                                    rJ2 (FV (n + 1 + 1)%uint63 w_zero) (pc + 4 + 4 + 4)%uint63)
                                    rD (FV 0 (vw v0)) (pc + 4 + 4 + 4 + 4)%uint63)
                                 L3 (n + 1 + 1 + 1)%uint63)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _, _ => None
  end.

Lemma dv_opaque rho2 t : to_Z t < 2 ^ 60 -> dv rho2 (FV t w_zero) = rho2 t.
Proof.
  intros Ht. rewrite (fk_dv_plain rho2 (FV t w_zero)) by (cbn [vtag]; exact Ht).
  cbn [vtag vw]. rewrite wbv_w_zero. apply bv_eq. rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma w_of_bv_small (x : word) : bv_unsigned x < 2 ^ 63 -> w_of_bv x = W64 0 (of_Z (bv_unsigned x)).
Proof.
  intros H. unfold w_of_bv, w_of_Z. pose proof (bv_unsigned_in_range _ x) as Hr.
  rewrite Z.div_small by lia. reflexivity.
Qed.

Theorem xpc_table_sound n rho F L3 ms m res :
  xpc_table F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_table in Hx. cbv zeta in Hx.
  destruct (get_opimm (iget (f_pc F) code)) as [[[[op1 rI] rP] k]|] eqn:G1; [|discriminate].
  destruct (get_opimm (iget (f_pc F + 4)%uint63 code)) as [[[[op2 rJ] rI'] sh]|] eqn:G2; [|discriminate].
  destruct (get_op (iget (f_pc F + 4 + 4)%uint63 code)) as [[[[op3 rJ2] rB] rJ']|] eqn:G3; [|discriminate].
  destruct (get_load (iget (f_pc F + 4 + 4 + 4)%uint63 code)) as [[[[[sz sgn] rD] rJ2'] imm]|] eqn:G4; [|discriminate].
  destruct (fv_ival (f_mem F) (FxState.rget F rP)) as [[blo bhi]|] eqn:Hiv; [|discriminate].
  match type of Hx with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  set (lit := vw (FxState.rget F rB)) in *.
  set (jl := wlo (w_srl blo k)) in *. set (jh := wlo (w_srl bhi k)) in *.
  destruct (fm_load_abs IM (f_mem F) (tl_addr lit sh imm jl) sz sgn) as [v0|] eqn:Hl0; [|discriminate].
  match type of Hx with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  injection Hx as <-.
  apply andb_true_iff in C2 as [Hv0 Hall].
  apply andb_true_iff in C as [C Hcnt]. apply andb_true_iff in C as [C Hjh]. apply andb_true_iff in C as [C Hjlh].
  apply andb_true_iff in C as [C Hth]. apply andb_true_iff in C as [C Htl]. apply andb_true_iff in C as [C Hn59].
  apply andb_true_iff in C as [C Htag]. apply andb_true_iff in C as [C HtB]. apply andb_true_iff in C as [C HBJ].
  apply andb_true_iff in C as [C HBI]. apply andb_true_iff in C as [C HB0]. apply andb_true_iff in C as [C HJ20].
  apply andb_true_iff in C as [C HJ0]. apply andb_true_iff in C as [C HI0]. apply andb_true_iff in C as [C EJ2].
  apply andb_true_iff in C as [C EJ]. apply andb_true_iff in C as [C EI]. apply andb_true_iff in C as [C Hop3].
  apply andb_true_iff in C as [Hop1 Hop2].
  destruct op1; try discriminate Hop1. destruct op2; try discriminate Hop2. destruct op3; try discriminate Hop3.
  apply Uint63.eqb_spec in EI, EJ, EJ2. subst rI' rJ' rJ2'.
  apply negb_true_iff in HI0, HJ0, HJ20, HB0, HBI, HBJ.
  apply get_opimm_inv in G1, G2. apply get_op_inv in G3. apply get_load_inv in G4.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0, Hn59, Hjh, Hcnt. apply leb_spec in Hjlh. rewrite to_Z_0 in Hn0.
  change (to_Z 576460752303423488) with (2 ^ 59) in Hn59. change (to_Z 2305843009213693952) with (2 ^ 61) in Hjh.
  change (to_Z 65536) with 65536 in Hcnt.
  assert (Hn1 : to_Z (n + 1)%uint63 = to_Z n + 1) by (apply (to_Z_succ61 R0); lia).
  assert (Hn2 : to_Z (n + 1 + 1)%uint63 = to_Z n + 2) by (rewrite (to_Z_succ61 R0) by lia; lia).
  assert (Hn3 : to_Z (n + 1 + 1 + 1)%uint63 = to_Z n + 3) by (rewrite (to_Z_succ61 R0) by lia; lia).
  pose proof HD as (HDI & _). pose proof HDI as (HRn & H0 & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (R_regs_ok _ _ _ _ _ HR) as HM.
  (* [comment removed for export] *)
  set (a := FxState.rget F rP) in *.
  set (i0w := alu64 ALU_SRL (dv rho a) (dv rho (FV 0 k))).
  assert (Hi0 : to_Z jl <= bv_unsigned i0w <= to_Z jh).
  { unfold i0w. rewrite srl_unsigned, (dv_conc rho H0), wbv_unsigned.
    pose proof (fv_ival_sound rho H0 (f_mem F) a blo bhi HM Hiv) as [Hlo Hhi].
    assert (El : to_Z jl = wZ blo / 2 ^ (wZ k mod 64)).
    { rewrite <- wZ_w_srl. unfold jl. destruct (w_srl blo k) as [t l]. cbn [wtop wlo] in *. rewrite wZ_W64.
      apply Uint63.eqb_spec in Htl. rewrite <- i63_land1, Htl. reflexivity. }
    assert (Eh : to_Z jh = wZ bhi / 2 ^ (wZ k mod 64)).
    { rewrite <- wZ_w_srl. unfold jh. destruct (w_srl bhi k) as [t l]. cbn [wtop wlo] in *. rewrite wZ_W64.
      apply Uint63.eqb_spec in Hth. rewrite <- i63_land1, Hth. reflexivity. }
    rewrite El, Eh.
    assert (Hd : 0 < 2 ^ (wZ k mod 64)) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
    split; apply Z.div_le_mono; lia. }
  set (j0 := of_Z (bv_unsigned i0w)).
  assert (Hj0 : to_Z j0 = bv_unsigned i0w).
  { unfold j0. rewrite of_Z_spec, i63_wB. apply Z.mod_small. pose proof (i63_range jl). lia. }
  assert (EW : w_of_bv i0w = W64 0 j0) by (apply w_of_bv_small; lia).
  assert (Hsub : to_Z (jh - jl)%uint63 = to_Z jh - to_Z jl).
  { rewrite sub_spec, i63_wB. apply Z.mod_small. pose proof (i63_range jl). pose proof (i63_range jh). lia. }
  (* [comment removed for export] *)
  assert (Hchk : tl_check (f_mem F) lit sh imm sz sgn (vw v0) j0 = true).
  { apply (all_idx_sound _ jl _ Hall).
    - rewrite Nat2Z.inj_succ, Z2Nat.id by lia. pose proof (i63_range jl). lia.
    - rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
  unfold tl_check in Hchk.
  destruct (fm_load_abs IM (f_mem F) (tl_addr lit sh imm j0) sz sgn) as [v|] eqn:Hl; [|discriminate].
  apply andb_true_iff in Hchk as [Hvt Hvw]. apply w_eqb_true_bv in Hvw.
  (* [comment removed for export] *)
  apply reach_POK.
  apply (reach_bind _ _ _ _ _ _ _ _ (reach_regop_conc n rho F L3 ms m _ ALU_SRL rI a (FV 0 k) HD Hn0 Hlt G1 eq_refl eq_refl)).
  intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1. fold i0w in HD1. rewrite EW in HD1.
  set (F1c := FxState.rset F rI (FV 0 (W64 0 j0)) (f_pc F + 4)%uint63) in *.
  assert (Hs2 : fx_step IM code F1c = FNext (FxState.rset F1c rJ (FV 0 (w_alu ALU_SLL (W64 0 j0) sh)) (f_pc F1c + 4)%uint63)).
  { apply (fx_step_opimm_conc F1c ALU_SLL rJ rI sh (W64 0 j0)); [exact G2|]. unfold F1c. rewrite fx_rget_rset, HI0, Uint63.eqb_refl. reflexivity. }
  apply (reach_bind _ _ _ _ _ _ _ _ (reach_step n rho F1c L3 ms1 m1 _ Hs2 HD1)).
  intros n2 rho2 F2 L2 ms2 m2 (-> & -> & -> & ->) HD2.
  set (c2 := w_alu ALU_SLL (W64 0 j0) sh) in *.
  set (F2c := FxState.rset F1c rJ (FV 0 c2) (f_pc F1c + 4)%uint63) in *.
  assert (HrB : FxState.rget F2c rB = FV 0 lit).
  { unfold F2c, F1c. rewrite !fx_rget_rset, HB0, HBJ, HBI. unfold lit.
    destruct (FxState.rget F rB) as [tB wB']. cbn [vtag vw] in *. apply Uint63.eqb_spec in HtB. subst tB. reflexivity. }
  assert (Hs3 : fx_step IM code F2c = FNext (FxState.rset F2c rJ2 (FV 0 (w_alu ALU_ADD lit c2)) (f_pc F2c + 4)%uint63)).
  { apply (fx_step_op_conc F2c ALU_ADD rJ2 rB rJ lit c2); [exact G3 | exact HrB |]. unfold F2c. rewrite fx_rget_rset, HJ0, Uint63.eqb_refl. reflexivity. }
  apply (reach_bind _ _ _ _ _ _ _ _ (reach_step n rho F2c L3 ms2 m2 _ Hs3 HD2)).
  intros n3 rho3 F3 L3' ms3 m3 (-> & -> & -> & ->) HD3.
  set (c3 := w_alu ALU_ADD lit c2) in *.
  set (F3c := FxState.rset F2c rJ2 (FV 0 c3) (f_pc F2c + 4)%uint63) in *.
  assert (Hs4 : fx_step IM code F3c = FNext (FxState.rset F3c rD v (f_pc F3c + 4)%uint63)).
  { apply (fx_step_load_conc F3c sz sgn rD rJ2 imm c3 v); [exact G4 | | exact Hl].
    unfold F3c. rewrite fx_rget_rset, HJ20, Uint63.eqb_refl. reflexivity. }
  apply (reach_bind _ _ _ _ _ _ _ _ (reach_step n rho F3c L3 ms3 m3 _ Hs4 HD3)).
  intros n4 rho4 F4 L4 ms4 m4 (-> & -> & -> & ->) HD4.
  set (F4c := FxState.rset F3c rD v (f_pc F3c + 4)%uint63) in *.
  (* [comment removed for export] *)
  set (rho' := rho_upd (rho_upd (rho_upd rho n (wbv (W64 0 j0))) (n + 1)%uint63 (wbv c2)) (n + 1 + 1)%uint63 (wbv c3)).
  set (F' := FxState.rset (FxState.rset (FxState.rset (FxState.rset F
              rI (FV n w_zero) (f_pc F + 4)%uint63)
              rJ (FV (n + 1)%uint63 w_zero) (f_pc F + 4 + 4)%uint63)
              rJ2 (FV (n + 1 + 1)%uint63 w_zero) (f_pc F + 4 + 4 + 4)%uint63)
              rD (FV 0 (vw v0)) (f_pc F + 4 + 4 + 4 + 4)%uint63).
  assert (Hrho' : forall t, to_Z t < to_Z n -> rho' t = rho t).
  { intros t Ht. unfold rho'. rewrite !rho_upd_other; [reflexivity | | |]; apply (lt_neq R0); lia. }
  assert (Hregs : forall rhoX, agree (n + 1 + 1 + 1)%uint63 rho' rhoX ->
            forall r, dv rhoX (FxState.rget F' r) = dv rhoX (FxState.rget F4c r)).
  { intros rhoX [H0X HagX] r. unfold F', F4c, F3c, F2c, F1c. rewrite !fx_rget_rset.
    destruct (r =? 0)%uint63; [reflexivity|].
    destruct (r =? rD)%uint63.
    { destruct v as [tv wv]. cbn [vtag vw] in Hvt, Hvw. apply Uint63.eqb_spec in Hvt. subst tv.
      rewrite !(dv_conc rhoX H0X). symmetry. exact Hvw. }
    destruct (r =? rJ2)%uint63.
    { rewrite (dv_opaque rhoX) by lia. rewrite (HagX (n + 1 + 1)%uint63) by lia.
      unfold rho'. rewrite rho_upd_same, (dv_conc rhoX H0X). reflexivity. }
    destruct (r =? rJ)%uint63.
    { rewrite (dv_opaque rhoX) by lia. rewrite (HagX (n + 1)%uint63) by lia.
      unfold rho'. rewrite rho_upd_other by (apply (lt_neq R0); lia). rewrite rho_upd_same, (dv_conc rhoX H0X). reflexivity. }
    destruct (r =? rI)%uint63; [|reflexivity].
    rewrite (dv_opaque rhoX) by lia. rewrite (HagX n) by lia.
    unfold rho'. rewrite !rho_upd_other by (apply (lt_neq R0); lia). rewrite rho_upd_same, (dv_conc rhoX H0X). reflexivity. }
  assert (Hn3' : to_Z n <= to_Z (n + 1 + 1 + 1)%uint63) by lia.
  exact (reach_abs n rho F4c L3 ms4 m4 (n + 1 + 1 + 1)%uint63 rho' F' _ HD4 Hn0 Hn3' Hrho' Hlt
           eq_refl eq_refl eq_refl Hregs eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_builtin4 : fstate -> fledger3 -> int -> option dres3 :=
  xpc_or (xpc_order code) (xpc_or xpc_table (xpc_opaque code)).

Theorem xpc_builtin4_sound n rho F L3 ms m res :
  xpc_builtin4 F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  apply (xpc_or_sound cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
  - exact (xpc_order_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
  - apply (xpc_or_sound cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
    + exact xpc_table_sound.
    + exact (xpc_opaque_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Qed.

End Drive3T.
