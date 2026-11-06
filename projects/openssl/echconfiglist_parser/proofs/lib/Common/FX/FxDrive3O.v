(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S FxDrive3H FxDrive3T.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nowrap_lo (M : itrie region) (ords : list (int * int * Z)) (t : int) (z : Z) : bool :=
  existsb (fun o => (snd (fst o) =? t)%uint63
                    && match iget (fst (fst o)) M with
                       | Some ra => (0 <=? to_Z (rg_clo ra) + snd o + z)
                       | None => false
                       end) ords.
Definition nowrap_hi (M : itrie region) (ords : list (int * int * Z)) (t : int) (z : Z) : bool :=
  existsb (fun o => (fst (fst o) =? t)%uint63
                    && match iget (snd (fst o)) M with
                       | Some _ => (z - snd o <=? 2 ^ 63)
                       | None => false
                       end) ords.

Definition locate (F : fstate) (L3 : fledger3) (n : int) (v : fval) : option (int * Z) :=
  match fv_inb_s (f_mem F) v with
  | Some _ => Some (vtag v, wZ (vw v))
  | None =>
      let t := vtag v in
      match iget t (f_mem F) with
      | Some _ => None
      | None =>
          if is_plain t && negb (t =? 0)%uint63 && (t <? n)%uint63
             && nowrap_lo (f_mem F) (fl_ord L3) t (wS (vw v)) && nowrap_hi (f_mem F) (fl_ord L3) t (wS (vw v))
          then Some (t, wS (vw v)) else None
      end
  end.

Definition ord_lt (ords : list (int * int * Z)) (ta tb : int) (z : Z) : bool :=
  existsb (fun o => (fst (fst o) =? ta)%uint63 && (snd (fst o) =? tb)%uint63 && (z <? snd o)) ords.
Definition ord_le (ords : list (int * int * Z)) (ta tb : int) (z : Z) : bool :=
  existsb (fun o => (fst (fst o) =? ta)%uint63 && (snd (fst o) =? tb)%uint63 && (z <=? snd o)) ords.

(* [comment removed for export] *)
Definition decide_loc (ords : list (int * int * Z)) (la lb : int * Z) : option bool :=
  let '(ta, za) := la in
  let '(tb, zb) := lb in
  if (ta =? tb)%uint63 then Some (za <? zb)
  else if ord_lt ords ta tb (za - zb) then Some true
  else if ord_le ords tb ta (zb - za) then Some false
  else None.

Section Drive3O.
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


Local Abbreviation reach := (FxDrive3T.reach cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nowrap_lo_sound n rho M ords t z :
  (forall ta ra, iget ta M = Some ra -> region_ok rho ta ra) -> Forall (ord_ok n rho) ords ->
  nowrap_lo M ords t z = true -> 0 <= bv_unsigned (rho t) + z.
Proof.
  intros Hreg Hall H. unfold nowrap_lo in H. apply existsb_exists in H as (o & Ho & Hc).
  apply andb_true_iff in Hc as [Et Hb]. apply Uint63.eqb_spec in Et.
  destruct (iget (fst (fst o)) M) as [ra|] eqn:Hg; [|discriminate]. apply Z.leb_le in Hb.
  destruct (Hreg _ _ Hg) as (_ & _ & _ & _ & _ & [Hclo _] & _).
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & _ & Hd). rewrite Et in Hd. lia.
Qed.

Lemma nowrap_hi_sound n rho M ords t z :
  (forall ta ra, iget ta M = Some ra -> region_ok rho ta ra) -> Forall (ord_ok n rho) ords ->
  nowrap_hi M ords t z = true -> bv_unsigned (rho t) + z < 2 ^ 64.
Proof.
  intros Hreg Hall H. unfold nowrap_hi in H. apply existsb_exists in H as (o & Ho & Hc).
  apply andb_true_iff in Hc as [Et Hb]. apply Uint63.eqb_spec in Et.
  destruct (iget (snd (fst o)) M) as [ra|] eqn:Hg; [|discriminate]. apply Z.leb_le in Hb.
  destruct (Hreg _ _ Hg) as (_ & _ & Hnw & _). pose proof (i63_range (rg_len ra)) as Hl.
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & _ & Hd). rewrite Et in Hd. lia.
Qed.

Lemma locate_sound n rho F L3 ms m v t z :
  D3 n rho F L3 ms m -> regions_lt_b n (f_mem F) = true ->
  locate F L3 n v = Some (t, z) ->
  bv_unsigned (dv rho v) = bv_unsigned (rho t) + z /\ to_Z t < to_Z n.
Proof.
  intros HD Hlt H. pose proof HD as (HDI & HL & _ & _). pose proof HDI as (HRn & H0 & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (R_regs_ok _ _ _ _ _ HR) as HM.
  pose proof (lp_ord _ _ _ _ _ _ _ _ _ _ _ HL) as Hord.
  unfold locate in H.
  destruct (fv_inb_s (f_mem F) v) as [rg|] eqn:Ei.
  - injection H as <- <-. destruct (fv_inb_s_sound rho (f_mem F) v rg HM Ei) as (Hg & Hu & _).
    split; [exact Hu | exact (regions_lt_b_ok n _ Hlt _ _ Hg)].
  - cbv zeta in H. destruct (iget (vtag v) (f_mem F)) as [rg|] eqn:Hg; [discriminate|].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
    injection H as <- <-.
    apply andb_true_iff in C as [C Hhi]. apply andb_true_iff in C as [C Hlo]. apply andb_true_iff in C as [C Htn].
    apply andb_true_iff in C as [Hpl _]. apply ltb_spec in Htn. split; [|exact Htn].
    unfold is_plain in Hpl. apply ltb_spec in Hpl. change (to_Z kind_lim) with (2 ^ 60) in Hpl.
    assert (Hreg : forall ta ra, iget ta (f_mem F) = Some ra -> region_ok rho ta ra)
      by (intros ta ra Hga; exact (R_region_ok _ _ _ _ _ _ _ HR Hga)).
    pose proof (nowrap_lo_sound n rho _ _ _ _ Hreg Hord Hlo) as B1.
    pose proof (nowrap_hi_sound n rho _ _ _ _ Hreg Hord Hhi) as B2.
    rewrite (fk_dv_plain rho v Hpl), bv_add_unsigned, wbv_unsigned.
    pose proof (wS_wZ (vw v)) as Ews. pose proof (Z_mod2_cases (to_Z (wtop (vw v)))) as Hm.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    destruct Hm as [Hm|Hm]; rewrite Hm in Ews.
    + rewrite Z.mul_0_l, Z.sub_0_r in Ews. rewrite <- Ews. apply Z.mod_small. lia.
    + replace (bv_unsigned (rho (vtag v)) + wZ (vw v)) with ((bv_unsigned (rho (vtag v)) + wS (vw v)) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ord_lt_sound n rho ords ta tb z :
  ord_lt ords ta tb z = true -> Forall (ord_ok n rho) ords -> bv_unsigned (rho ta) + z < bv_unsigned (rho tb).
Proof.
  intros H Hall. unfold ord_lt in H. apply existsb_exists in H as (o & Ho & Hc).
  apply andb_true_iff in Hc as [Hc Hz]. apply andb_true_iff in Hc as [E1 E2].
  apply Uint63.eqb_spec in E1, E2. apply Z.ltb_lt in Hz. subst ta tb.
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & _ & Hd). lia.
Qed.

Lemma ord_le_sound n rho ords ta tb z :
  ord_le ords ta tb z = true -> Forall (ord_ok n rho) ords -> bv_unsigned (rho ta) + z <= bv_unsigned (rho tb).
Proof.
  intros H Hall. unfold ord_le in H. apply existsb_exists in H as (o & Ho & Hc).
  apply andb_true_iff in Hc as [Hc Hz]. apply andb_true_iff in Hc as [E1 E2].
  apply Uint63.eqb_spec in E1, E2. apply Z.leb_le in Hz. subst ta tb.
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & _ & Hd). lia.
Qed.

Lemma decide_loc_sound n rho ords ta za tb zb (xa xb : word) r :
  Forall (ord_ok n rho) ords ->
  bv_unsigned xa = bv_unsigned (rho ta) + za -> bv_unsigned xb = bv_unsigned (rho tb) + zb ->
  decide_loc ords (ta, za) (tb, zb) = Some r -> bv_ltu xa xb = r.
Proof.
  intros Hall Ea Eb H. unfold decide_loc in H. unfold bv_ltu. rewrite Ea, Eb.
  destruct (ta =? tb)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst tb. injection H as <-.
    destruct (za <? zb) eqn:E; [apply Z.ltb_lt in E; apply Z.ltb_lt; lia | apply Z.ltb_ge in E; apply Z.ltb_ge; lia].
  - destruct (ord_lt ords ta tb (za - zb)) eqn:E1.
    + injection H as <-. pose proof (ord_lt_sound n rho _ _ _ _ E1 Hall). apply Z.ltb_lt. lia.
    + destruct (ord_le ords tb ta (zb - za)) eqn:E2; [|discriminate]. injection H as <-.
      pose proof (ord_le_sound n rho _ _ _ _ E2 Hall). apply Z.ltb_ge. lia.
Qed.


Local Abbreviation rbind := (FxDrive3T.reach_bind cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation rret := (FxDrive3T.reach_ret cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation rpok := (FxDrive3T.reach_POK cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation rregop :=
  (FxDrive3T.reach_regop_conc cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reach_branch n rho F L3 ms m c rs1 rs2 tgt npc :
  D3 n rho F L3 ms m -> 0 < to_Z n -> regions_lt_b n (f_mem F) = true ->
  iget (f_pc F) code = Some (FBranch c rs1 rs2 tgt npc) ->
  reach n rho F L3 ms m (fun n' rho' F' L' _ _ => n' = n /\ rho' = rho /\ L' = L3 /\
     F' = set_pc F (if branch_taken c (dv rho (FxState.rget F rs1)) (dv rho (FxState.rget F rs2)) then tgt else npc)).
Proof.
  intros HD Hn0 Hlt Hi.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & _).
  change (m_halted (FxDrive3.erase wb0 m)) with (m_halted m) in Hh.
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  destruct (fx_step_branch segs IM rho code Hcode F ms c rs1 rs2 tgt npc HR Hi)
    as (ms' & Hstep & Emem & Erom & Efr & Efc & _ & Ev1 & Ev2).
  rewrite <- Ev1, <- Ev2.
  set (F' := set_pc F (if branch_taken c (mval ms rs1) (mval ms rs2) then tgt else npc)).
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
  destruct (regstep_node cfg segs IM R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
              n rho n rho F F' L3 ms ms' m w i HD Hn0 ltac:(lia) (fun t _ => eq_refl) Hlt eq_refl HRn'
              Hstep Emem Erom Efr Efc Hf He Hd Hri) as (m1 & HD' & HPX & Ha).
  split.
  - intros T HT. apply (rzc_asteps cfg segs 1 ms m ms' m1 T Hh Ha).
    exact (HT n rho F' L3 ms' m1 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) HD' HPX).
  - exists n, rho, F', L3, ms', m1. split; [repeat split|]. split; [exact HD'|]. split; [exact HPX|].
    exact (asteps_star_cfg cfg segs 1 ms m ms' m1 Hh Ha).
Qed.

Lemma reach_ord n rho F L3 ms m o (P : sprop) :
  D3 n rho F L3 ms m -> ord_ok n rho o -> P n rho F (ord_ledger3 L3 o) ms m -> reach n rho F L3 ms m P.
Proof.
  intros HD Ho HP.
  pose proof (DInv3_add_ord cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 n rho F L3 ms m o HD Ho) as HD'.
  assert (HPX : PX n rho F L3 ms m n rho F (ord_ledger3 L3 o) ms m) by (exact (pext_refl IM R0 rom0 hi n rho F L3 ms m)).
  split.
  - intros T HT. exact (HT n rho F (ord_ledger3 L3 o) ms m HP HD' HPX).
  - exists n, rho, F, (ord_ledger3 L3 o), ms, m. split; [exact HP|]. split; [exact HD'|]. split; [exact HPX | apply star_cfg_refl].
Qed.

(* [comment removed for export] *)
Lemma fork_fact_lt n rho ta za tb zb (xa xb : word) :
  to_Z ta < to_Z n -> to_Z tb < to_Z n ->
  bv_unsigned xa = bv_unsigned (rho ta) + za -> bv_unsigned xb = bv_unsigned (rho tb) + zb ->
  bv_ltu xa xb = true -> ord_ok n rho (ta, tb, za - zb + 1).
Proof.
  intros Ha Hb Ea Eb H. unfold bv_ltu in H. apply Z.ltb_lt in H. split; [exact Ha|]. split; [exact Hb|]. cbn [fst snd]. lia.
Qed.
Lemma fork_fact_ge n rho ta za tb zb (xa xb : word) :
  to_Z ta < to_Z n -> to_Z tb < to_Z n ->
  bv_unsigned xa = bv_unsigned (rho ta) + za -> bv_unsigned xb = bv_unsigned (rho tb) + zb ->
  bv_ltu xa xb = false -> ord_ok n rho (tb, ta, zb - za).
Proof.
  intros Ha Hb Ea Eb H. unfold bv_ltu in H. apply Z.ltb_ge in H. split; [exact Hb|]. split; [exact Ha|]. cbn [fst snd]. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_ltu (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some (FBranch c rs1 rs2 tgt npc) =>
      match ltu_cond c with
      | Some isltu =>
        if tag_ok F n then
          match locate F L3 n (FxState.rget F rs1), locate F L3 n (FxState.rget F rs2) with
          | Some la, Some lb =>
              let pc_lt := if isltu then tgt else npc in
              let pc_ge := if isltu then npc else tgt in
              match decide_loc (fl_ord L3) la lb with
              | Some true => Some (D3One (set_pc F pc_lt) L3 n)
              | Some false => Some (D3One (set_pc F pc_ge) L3 n)
              | None => Some (D3Two (set_pc F pc_lt) (ord_ledger3 L3 (fst la, fst lb, snd la - snd lb + 1)) n
                                    (set_pc F pc_ge) (ord_ledger3 L3 (fst lb, fst la, snd lb - snd la)) n)
              end
          | _, _ => None
          end
        else None
      | None => None
      end
  | _ => None
  end.

Theorem xpc_ltu_sound n rho F L3 ms m res :
  xpc_ltu F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_ltu in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct fi as [| | |c rs1 rs2 tgt npc| | | | | | | | | | | | |]; try discriminate Hx.
  destruct (ltu_cond c) as [isltu|] eqn:Hc; [|discriminate].
  destruct (tag_ok F n) eqn:Htag; [|discriminate].
  destruct (locate F L3 n (FxState.rget F rs1)) as [[ta za]|] eqn:La; [|discriminate].
  destruct (locate F L3 n (FxState.rget F rs2)) as [[tb zb]|] eqn:Lb; [|discriminate].
  cbv zeta in Hx. cbn [fst snd] in Hx.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0. rewrite to_Z_0 in Hn0.
  destruct (locate_sound n rho F L3 ms m _ _ _ HD Hlt La) as [Ea Hta].
  destruct (locate_sound n rho F L3 ms m _ _ _ HD Hlt Lb) as [Eb Htb].
  pose proof HD as (_ & HL & _ & _). pose proof (lp_ord _ _ _ _ _ _ _ _ _ _ _ HL) as Hord.
  assert (Hbt : forall x y, branch_taken c x y = if isltu then bv_ltu x y else negb (bv_ltu x y)).
  { intros x y. destruct c; cbn [ltu_cond] in Hc; try discriminate Hc; injection Hc as <-; reflexivity. }
  apply rpok.
  apply (rbind _ _ _ _ _ _ _ _ (reach_branch n rho F L3 ms m c rs1 rs2 tgt npc HD Hn0 Hlt Hi)).
  intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1. rewrite Hbt in HD1 |- *.
  destruct (decide_loc (fl_ord L3) (ta, za) (tb, zb)) as [r|] eqn:Hdec.
  - pose proof (decide_loc_sound n rho _ _ _ _ _ _ _ r Hord Ea Eb Hdec) as El. rewrite El in HD1 |- *.
    apply rret; [exact HD1|]. destruct r; injection Hx as <-; destruct isltu; reflexivity.
  - injection Hx as <-.
    destruct (bv_ltu (dv rho (FxState.rget F rs1)) (dv rho (FxState.rget F rs2))) eqn:El.
    + apply (reach_ord _ _ _ _ _ _ (ta, tb, za - zb + 1)); [exact HD1 | exact (fork_fact_lt n rho _ _ _ _ _ _ Hta Htb Ea Eb El) |].
      cbn [dres3_in]. left. destruct isltu; reflexivity.
    + apply (reach_ord _ _ _ _ _ _ (tb, ta, zb - za)); [exact HD1 | exact (fork_fact_ge n rho _ _ _ _ _ _ Hta Htb Ea Eb El) |].
      cbn [dres3_in]. right. destruct isltu; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_sltu (op : aluop) : bool := match op with ALU_SLTU => true | _ => false end.

Definition xpc_sltu (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some (FOp op rd rs1 rs2) =>
      if is_sltu op && tag_ok F n then
        match locate F L3 n (FxState.rget F rs1), locate F L3 n (FxState.rget F rs2) with
        | Some la, Some lb =>
            let F1 := FxState.rset F rd (FV 0 (W64 0 1)) (f_pc F + 4)%uint63 in
            let F0 := FxState.rset F rd (FV 0 (W64 0 0)) (f_pc F + 4)%uint63 in
            match decide_loc (fl_ord L3) la lb with
            | Some true => Some (D3One F1 L3 n)
            | Some false => Some (D3One F0 L3 n)
            | None => Some (D3Two F1 (ord_ledger3 L3 (fst la, fst lb, snd la - snd lb + 1)) n
                                  F0 (ord_ledger3 L3 (fst lb, fst la, snd lb - snd la)) n)
            end
        | _, _ => None
        end
      else None
  | _ => None
  end.

Lemma sltu_word (x y : word) :
  w_of_bv (alu64 ALU_SLTU x y) = if bv_ltu x y then W64 0 1 else W64 0 0.
Proof. unfold alu64, alu. destruct (bv_ltu x y); reflexivity. Qed.

Theorem xpc_sltu_sound n rho F L3 ms m res :
  xpc_sltu F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_sltu in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct fi as [| | | | | | |op rd rs1 rs2| | | | | | | | |]; try discriminate Hx.
  destruct (is_sltu op && tag_ok F n) eqn:C; [|discriminate].
  apply andb_true_iff in C as [Hop Htag]. destruct op; try discriminate Hop.
  destruct (locate F L3 n (FxState.rget F rs1)) as [[ta za]|] eqn:La; [|discriminate].
  destruct (locate F L3 n (FxState.rget F rs2)) as [[tb zb]|] eqn:Lb; [|discriminate].
  cbv zeta in Hx. cbn [fst snd] in Hx.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0. rewrite to_Z_0 in Hn0.
  destruct (locate_sound n rho F L3 ms m _ _ _ HD Hlt La) as [Ea Hta].
  destruct (locate_sound n rho F L3 ms m _ _ _ HD Hlt Lb) as [Eb Htb].
  pose proof HD as (_ & HL & _ & _). pose proof (lp_ord _ _ _ _ _ _ _ _ _ _ _ HL) as Hord.
  apply rpok.
  apply (rbind _ _ _ _ _ _ _ _ (rregop n rho F L3 ms m _ ALU_SLTU rd (FxState.rget F rs1) (FxState.rget F rs2)
                                  HD Hn0 Hlt Hi eq_refl eq_refl)).
  intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1. rewrite sltu_word in HD1 |- *.
  destruct (decide_loc (fl_ord L3) (ta, za) (tb, zb)) as [r|] eqn:Hdec.
  - pose proof (decide_loc_sound n rho _ _ _ _ _ _ _ r Hord Ea Eb Hdec) as El. rewrite El in HD1 |- *.
    apply rret; [exact HD1|]. destruct r; injection Hx as <-; reflexivity.
  - injection Hx as <-.
    destruct (bv_ltu (dv rho (FxState.rget F rs1)) (dv rho (FxState.rget F rs2))) eqn:El.
    + apply (reach_ord _ _ _ _ _ _ (ta, tb, za - zb + 1)); [exact HD1 | exact (fork_fact_lt n rho _ _ _ _ _ _ Hta Htb Ea Eb El) |].
      cbn [dres3_in]. left. reflexivity.
    + apply (reach_ord _ _ _ _ _ _ (tb, ta, zb - za)); [exact HD1 | exact (fork_fact_ge n rho _ _ _ _ _ _ Hta Htb Ea Eb El) |].
      cbn [dres3_in]. right. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lo_ge (M : itrie region) (ords : list (int * int * Z)) (t : int) (z k : Z) : bool :=
  existsb (fun o => (snd (fst o) =? t)%uint63
                    && match iget (fst (fst o)) M with
                       | Some ra => (k <=? to_Z (rg_clo ra) + snd o + z)
                       | None => false
                       end) ords.
Definition is_zero_v (v : fval) : bool := (vtag v =? 0)%uint63 && w_eqb (vw v) w_zero.
Definition eqne_cond (c : branch_cond) : option bool :=
  match c with BC_EQ => Some false | BC_NE => Some true | _ => None end.

Definition xpc_pgnz (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some (FBranch c rs1 rs2 tgt npc) =>
      match eqne_cond c with
      | Some isne =>
          let a := FxState.rget F rs1 in
          let t := vbase (vtag a) in
          match iget t (f_mem F) with
          | Some _ => None
          | None =>
              if (vkind (vtag a) =? K_PG)%uint63 && is_zero_v (FxState.rget F rs2) && tag_ok F n
                 && lo_ge (f_mem F) (fl_ord L3) t (wS (vw a)) 4096 && nowrap_hi (f_mem F) (fl_ord L3) t (wS (vw a))
              then Some (D3One (set_pc F (if isne then tgt else npc)) L3 n) else None
          end
      | None => None
      end
  | _ => None
  end.

Lemma lo_ge_sound n rho M ords t z k :
  (forall ta ra, iget ta M = Some ra -> region_ok rho ta ra) -> Forall (ord_ok n rho) ords ->
  lo_ge M ords t z k = true -> k <= bv_unsigned (rho t) + z.
Proof.
  intros Hreg Hall H. unfold lo_ge in H. apply existsb_exists in H as (o & Ho & Hc).
  apply andb_true_iff in Hc as [Et Hb]. apply Uint63.eqb_spec in Et.
  destruct (iget (fst (fst o)) M) as [ra|] eqn:Hg; [|discriminate]. apply Z.leb_le in Hb.
  destruct (Hreg _ _ Hg) as (_ & _ & _ & _ & _ & [Hclo _] & _).
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & _ & Hd). rewrite Et in Hd. lia.
Qed.

Lemma add_signed_nowrap (x : word) (w : w64) :
  0 <= bv_unsigned x + wS w < 2 ^ 64 -> bv_unsigned (bv_add x (wbv w)) = bv_unsigned x + wS w.
Proof.
  intros B. rewrite bv_add_unsigned, wbv_unsigned.
  pose proof (wS_wZ w) as Ews. pose proof (Z_mod2_cases (to_Z (wtop w))) as Hm.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  destruct Hm as [Hm|Hm]; rewrite Hm in Ews.
  - rewrite Z.mul_0_l, Z.sub_0_r in Ews. rewrite <- Ews. apply Z.mod_small. lia.
  - replace (bv_unsigned x + wZ w) with ((bv_unsigned x + wS w) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Theorem xpc_pgnz_sound n rho F L3 ms m res :
  xpc_pgnz F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_pgnz in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct fi as [| | |c rs1 rs2 tgt npc| | | | | | | | | | | | |]; try discriminate Hx.
  destruct (eqne_cond c) as [isne|] eqn:Hc; [|discriminate]. cbv zeta in Hx.
  destruct (iget (vbase (vtag (FxState.rget F rs1))) (f_mem F)) as [rg|] eqn:Hg; [discriminate|].
  match type of Hx with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  injection Hx as <-.
  apply andb_true_iff in C as [C Hhi]. apply andb_true_iff in C as [C Hlo]. apply andb_true_iff in C as [C Htag].
  apply andb_true_iff in C as [Hk Hz]. apply Uint63.eqb_spec in Hk.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0. rewrite to_Z_0 in Hn0.
  pose proof HD as (HDI & HL & _ & _). pose proof HDI as (HRn & H0 & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (lp_ord _ _ _ _ _ _ _ _ _ _ _ HL) as Hord.
  assert (Hreg : forall ta ra, iget ta (f_mem F) = Some ra -> region_ok rho ta ra)
    by (intros ta ra Hga; exact (R_region_ok _ _ _ _ _ _ _ HR Hga)).
  pose proof (lo_ge_sound n rho _ _ _ _ _ Hreg Hord Hlo) as B1.
  pose proof (nowrap_hi_sound n rho _ _ _ _ Hreg Hord Hhi) as B2.
  set (a := FxState.rget F rs1) in *. set (b := FxState.rget F rs2) in *.
  (* [comment removed for export] *)
  assert (Ha : 1 <= bv_unsigned (dv rho a)).
  { unfold dv. rewrite Hk, fk_dvk_PG, fk_pg_unsigned, add_signed_nowrap by lia.
    apply Z.div_le_lower_bound; lia. }
  assert (Hb : dv rho b = Z_to_bv 64 0).
  { unfold is_zero_v in Hz. apply andb_true_iff in Hz as [Hz1 Hz2].
    rewrite (dv_tag0 rho H0 b Hz1). apply w_eqb_true_bv in Hz2. rewrite Hz2. reflexivity. }
  assert (Hbt : branch_taken c (dv rho a) (dv rho b) = isne).
  { assert (Hne : bv_eqb (dv rho a) (dv rho b) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite Hb. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia. }
    destruct c; cbn [eqne_cond] in Hc; try discriminate Hc; injection Hc as <-; cbn [branch_taken]; rewrite Hne; reflexivity. }
  apply rpok.
  apply (rbind _ _ _ _ _ _ _ _ (reach_branch n rho F L3 ms m c rs1 rs2 tgt npc HD Hn0 Hlt Hi)).
  intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1. fold a b in HD1 |- *. rewrite Hbt in HD1 |- *.
  apply rret; [exact HD1 | reflexivity].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition res_ledger3 (L3 : fledger3) (o : int * Z * Z) : fledger3 :=
  FL3 (fl3 L3) (fl_all L3) (fl_ops L3) (fl_lazy L3) (fl_allow L3) (fl_Ab L3) (fl_E L3) (fl_ex L3) (fl_ord L3) (o :: fl_res L3).

Definition mask_log (imm : w64) : option Z :=
  List.find (fun j => (wS imm =? - 2 ^ j)) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12].

Definition res_find (ress : list (int * Z * Z)) (t : int) (j : Z) : option Z :=
  match List.find (fun o => (fst (fst o) =? t)%uint63 && (snd (fst o) mod 2 ^ j =? 0)) ress with
  | Some o => Some (snd o mod 2 ^ j)
  | None => None
  end.

Definition is_and (op : aluop) : bool := match op with ALU_AND => true | _ => false end.

Definition align_res (a : fval) (j c : Z) : fval :=
  FV (vtag a) (w_sub (vw a) (w_of_Z ((c + wZ (vw a)) mod 2 ^ j))).

Definition xpc_align (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some (FOpImm op rd rs1 imm) =>
      let a := FxState.rget F rs1 in
      let t := vtag a in
      if is_and op && tag_ok F n && is_plain t && negb (t =? 0)%uint63 && (t <? n)%uint63 then
        match mask_log imm with
        | Some j =>
            match res_find (fl_res L3) t j with
            | Some c => Some (D3One (FxState.rset F rd (align_res a j c) (f_pc F + 4)%uint63) L3 n)
            | None =>
                if (to_Z (base_align (f_mem F) t) =? j - 1)
                then Some (D3Two (FxState.rset F rd (align_res a j 0) (f_pc F + 4)%uint63) (res_ledger3 L3 (t, 2 ^ j, 0)) n
                                 (FxState.rset F rd (align_res a j (2 ^ (j - 1))) (f_pc F + 4)%uint63)
                                 (res_ledger3 L3 (t, 2 ^ j, 2 ^ (j - 1))) n)
                else None
            end
        | None => None
        end
      else None
  | _ => None
  end.

Lemma mask_log_spec imm j : mask_log imm = Some j -> 1 <= j <= 12 /\ wS imm = - 2 ^ j.
Proof.
  unfold mask_log. intros H. apply find_some in H as [Hin Hb]. apply Z.eqb_eq in Hb. split; [|exact Hb].
  cbn [In] in Hin. lia.
Qed.

Lemma res_find_sound n rho ress t j c :
  1 <= j -> Forall (res_ok n rho) ress -> res_find ress t j = Some c -> bv_unsigned (rho t) mod 2 ^ j = c.
Proof.
  intros Hj Hall H. unfold res_find in H.
  destruct (List.find _ ress) as [o|] eqn:Hf; [|discriminate]. injection H as <-.
  apply find_some in Hf as [Ho Hb]. apply andb_true_iff in Hb as [Et Hm]. apply Uint63.eqb_spec in Et. apply Z.eqb_eq in Hm.
  destruct (proj1 (Forall_forall _ _) Hall o Ho) as (_ & Hpos & Hc). rewrite Et in Hc. rewrite <- Hc.
  symmetry. apply Z.mod_mod_divide. apply Z.mod_divide; [|exact Hm].
  pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma and_neg_pow2 (x : word) (imm : w64) j :
  1 <= j <= 12 -> wS imm = - 2 ^ j ->
  bv_and x (wbv imm) = bv_sub x (Z_to_bv 64 (bv_unsigned x mod 2 ^ j)).
Proof.
  intros Hj Hs. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 64) with (2 ^ 64) in Hx.
  assert (Hp : 0 < 2 ^ j <= 2 ^ 12) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  change (2 ^ 12) with 4096 in Hp.
  assert (Hz : wZ imm = 2 ^ 64 - 2 ^ j).
  { pose proof (wS_wZ imm) as E. pose proof (wZ_range imm) as Hr.
    destruct (Z_mod2_cases (to_Z (wtop imm))) as [Hm|Hm]; rewrite Hm in E; lia. }
  pose proof (Z.mod_pos_bound (bv_unsigned x) (2 ^ j) ltac:(lia)) as Hmu.
  pose proof (Z.mod_le (bv_unsigned x) (2 ^ j) ltac:(lia) ltac:(lia)) as Hle.
  apply bv_eq. rewrite bv_and_unsigned, bv_sub_unsigned, wbv_unsigned, Hz.
  rewrite (Z_to_bv_unsigned), (bv_wrap_small 64 (bv_unsigned x mod 2 ^ j))
    by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  rewrite (land_round (bv_unsigned x) (2 ^ 64 - 2 ^ j) (2 ^ j - 1) j); try lia.
  - change (2 ^ j - 1) with (Z.pred (2 ^ j)). rewrite <- Z.ones_equiv, Z.land_ones by lia.
    rewrite Z.mod_mod by lia. symmetry. apply bv_wrap_small.
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). lia.
  - change (Z.ones 64) with (2 ^ 64 - 1). lia.
Qed.

Lemma align_val rho2 (a : fval) imm j c :
  to_Z (vtag a) < 2 ^ 60 -> 1 <= j <= 12 -> wS imm = - 2 ^ j -> bv_unsigned (rho2 (vtag a)) mod 2 ^ j = c ->
  dv rho2 (align_res a j c) = alu64 ALU_AND (dv rho2 a) (wbv imm).
Proof.
  intros Hpl Hj Hs Hc. destruct a as [t w]. cbn [vtag] in *. unfold align_res. cbn [vtag vw].
  rewrite (fk_dv_plain rho2 (FV t _)) by exact Hpl. rewrite (fk_dv_plain rho2 (FV t w)) by exact Hpl. cbn [vtag vw].
  unfold alu64, alu. rewrite (and_neg_pow2 _ imm j Hj Hs).
  rewrite wbv_w_sub, wbv_w_of_Z.
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (E : bv_unsigned (bv_add (rho2 t) (wbv w)) mod 2 ^ j = (c + wZ w) mod 2 ^ j).
  { rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_mod_divide by (exists (2 ^ (64 - j)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite <- Hc. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
  rewrite E. bv_solve.
Qed.


(* [comment removed for export] *)
Lemma reach_regop_val n rho F L3 ms m fi op rd a b v :
  D3 n rho F L3 ms m -> 0 < to_Z n -> regions_lt_b n (f_mem F) = true ->
  iget (f_pc F) code = Some fi -> regop_of fi = Some (op, rd) -> regop_fvals F fi = Some (a, b) ->
  (forall rho2, agree n rho rho2 -> dv rho2 v = alu64 op (dv rho a) (dv rho b)) ->
  reach n rho F L3 ms m (fun n' rho' F' L' _ _ => n' = n /\ rho' = rho /\ L' = L3 /\
     F' = FxState.rset F rd v (f_pc F + 4)%uint63).
Proof.
  intros HD Hn0 Hlt Hi Hro Hfv Hval.
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
  set (F' := FxState.rset F rd v (f_pc F + 4)%uint63).
  assert (HRn' : Rn n rho F' ms').
  { intros rho2 Hag2. pose proof (HRn rho2 Hag2) as HR2.
    destruct (fx_step_regop segs IM rho2 (proj1 Hag2) code Hcode F ms fi op rd wa wb HR2 Hi Hro Hopn)
      as (ms2 & Hstep2 & _ & _ & _ & _ & Hmk2).
    rewrite Hstep in Hstep2. injection Hstep2 as <-. apply Hmk2.
    rewrite (Hval rho2 Hag2), Ea, Eb. reflexivity. }
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
Lemma DInv3_add_res n rho F L3 ms m o :
  D3 n rho F L3 ms m -> res_ok n rho o -> D3 n rho F (res_ledger3 L3 o) ms m.
Proof.
  intros (HDI & HL & HS & HX) Ho. split; [exact HDI|]. split; [|split; [|exact HX]].
  - destruct HL. constructor; try assumption. cbn [res_ledger3 fl_res]. constructor; assumption.
  - destruct HS. constructor; assumption.
Qed.

Lemma reach_res n rho F L3 ms m o (P : sprop) :
  D3 n rho F L3 ms m -> res_ok n rho o -> P n rho F (res_ledger3 L3 o) ms m -> reach n rho F L3 ms m P.
Proof.
  intros HD Ho HP. pose proof (DInv3_add_res n rho F L3 ms m o HD Ho) as HD'.
  assert (HPX : PX n rho F L3 ms m n rho F (res_ledger3 L3 o) ms m) by (exact (pext_refl IM R0 rom0 hi n rho F L3 ms m)).
  split.
  - intros T HT. exact (HT n rho F (res_ledger3 L3 o) ms m HP HD' HPX).
  - exists n, rho, F, (res_ledger3 L3 o), ms, m. split; [exact HP|]. split; [exact HD'|]. split; [exact HPX | apply star_cfg_refl].
Qed.

Theorem xpc_align_sound n rho F L3 ms m res :
  xpc_align F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_align in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct fi as [| | | | | |op rd rs1 imm| | | | | | | | | |]; try discriminate Hx.
  cbv zeta in Hx. set (a := FxState.rget F rs1) in *.
  match type of Hx with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  apply andb_true_iff in C as [C Htn]. apply andb_true_iff in C as [C Ht0]. apply andb_true_iff in C as [C Hpl].
  apply andb_true_iff in C as [Hop Htag]. destruct op; try discriminate Hop.
  destruct (mask_log imm) as [j|] eqn:Hm; [|discriminate]. destruct (mask_log_spec imm j Hm) as [Hj Hs].
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0, Htn. rewrite to_Z_0 in Hn0.
  unfold is_plain in Hpl. apply ltb_spec in Hpl. change (to_Z kind_lim) with (2 ^ 60) in Hpl.
  pose proof HD as (HDI & HL & _ & _). pose proof HDI as (HRn & H0 & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR. pose proof (R_regs_ok _ _ _ _ _ HR) as HM.
  pose proof (lp_res _ _ _ _ _ _ _ _ _ _ _ HL) as Hress.
  (* [comment removed for export] *)
  assert (Hval : forall c, bv_unsigned (rho (vtag a)) mod 2 ^ j = c ->
            forall rho2, agree n rho rho2 -> dv rho2 (align_res a j c) = alu64 ALU_AND (dv rho a) (dv rho (FV 0 imm))).
  { intros c Hc rho2 [H02 Hag2]. rewrite (dv_conc rho H0).
    assert (Er : rho2 (vtag a) = rho (vtag a)) by (apply Hag2; exact Htn).
    rewrite (align_val rho2 a imm j c Hpl Hj Hs) by (rewrite Er; exact Hc).
    f_equal. rewrite !(fk_dv_plain _ a Hpl), Er. reflexivity. }
  apply rpok.
  destruct (res_find (fl_res L3) (vtag a) j) as [c|] eqn:Hf.
  - injection Hx as <-. pose proof (res_find_sound n rho (fl_res L3) (vtag a) j c (proj1 Hj) Hress Hf) as Hc.
    apply (rbind _ _ _ _ _ _ _ _ (reach_regop_val n rho F L3 ms m _ ALU_AND rd a (FV 0 imm) (align_res a j c)
                                    HD Hn0 Hlt Hi eq_refl eq_refl (Hval c Hc))).
    intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1. apply rret; [exact HD1 | reflexivity].
  - destruct (to_Z (base_align (f_mem F) (vtag a)) =? j - 1) eqn:Eal; [|discriminate]. injection Hx as <-.
    apply Z.eqb_eq in Eal.
    (* [comment removed for export] *)
    pose proof (lb_align rho (f_mem F) (vtag a) HM) as Hlb. unfold lb in Hlb.
    rewrite (fk_vkind_plain _ Hpl), (fk_vbase_plain _ Hpl) in Hlb. cbn [Uint63.eqb orb] in Hlb.
    change ((0 =? 1)%uint63 || (0 =? 4)%uint63) with false in Hlb. cbv iota in Hlb. rewrite Eal in Hlb.
    assert (Hp1 : 0 < 2 ^ (j - 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Ep : 2 ^ j = 2 * 2 ^ (j - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Hcases : bv_unsigned (rho (vtag a)) mod 2 ^ j = 0 \/ bv_unsigned (rho (vtag a)) mod 2 ^ j = 2 ^ (j - 1)).
    { rewrite Ep. set (P := 2 ^ (j - 1)) in *. set (X := bv_unsigned (rho (vtag a))) in *.
      assert (EX : X = P * (X / P)) by (rewrite (Z.div_mod X P) at 1 by lia; rewrite Hlb; lia).
      rewrite EX, (Z.mul_comm 2 P), Z.mul_mod_distr_l by lia.
      destruct (Z_mod2_cases (X / P)) as [-> | ->]; [left | right]; lia. }
    destruct Hcases as [Hc|Hc].
    + apply (rbind _ _ _ _ _ _ _ _ (reach_regop_val n rho F L3 ms m _ ALU_AND rd a (FV 0 imm) (align_res a j 0)
                                      HD Hn0 Hlt Hi eq_refl eq_refl (Hval 0 Hc))).
      intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1.
      apply (reach_res _ _ _ _ _ _ (vtag a, 2 ^ j, 0)); [exact HD1 | |cbn [dres3_in]; left; reflexivity].
      split; [exact Htn|]. split; [cbn [fst snd]; lia | exact Hc].
    + apply (rbind _ _ _ _ _ _ _ _ (reach_regop_val n rho F L3 ms m _ ALU_AND rd a (FV 0 imm) (align_res a j (2 ^ (j - 1)))
                                      HD Hn0 Hlt Hi eq_refl eq_refl (Hval _ Hc))).
      intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1.
      apply (reach_res _ _ _ _ _ _ (vtag a, 2 ^ j, 2 ^ (j - 1))); [exact HD1 | |cbn [dres3_in]; right; reflexivity].
      split; [exact Htn|]. split; [cbn [fst snd]; lia | exact Hc].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition res_know_plain (M : itrie region) (ress : list (int * Z * Z)) (t : int) (i : Z) : option Z :=
  if (i <=? to_Z (base_align M t)) then Some 0 else res_find ress t i.

Definition res_know (M : itrie region) (ress : list (int * Z * Z)) (t : int) (j : Z) : option Z :=
  match res_know_plain M ress t j with
  | Some c => Some c
  | None =>
      match iget t M with
      | Some rg =>
          match rg_kind rg with
          | RK_shadow p =>
              match res_know_plain M ress p (j + 3) with
              | Some c' => Some ((c' / 8 + to_Z shadow_K) mod 2 ^ j)
              | None => None
              end
          | RK_plain => None
          end
      | None => None
      end
  end.

Definition root_tag (M : itrie region) (t : int) (j : Z) : int * Z :=
  match iget t M with
  | Some rg => match rg_kind rg with RK_shadow p => (p, j + 3) | RK_plain => (t, j) end
  | None => (t, j)
  end.

Definition first_unknown (M : itrie region) (ress : list (int * Z * Z)) (tau : int) (J : Z) : option Z :=
  List.find (fun i => (i <=? J) && match res_know_plain M ress tau i with None => true | Some _ => false end)
            [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15].

Definition xpc_align2 (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match iget (f_pc F) code with
  | Some (FOpImm op rd rs1 imm) =>
      let a := FxState.rget F rs1 in
      let t := vtag a in
      if is_and op && tag_ok F n && is_plain t && negb (t =? 0)%uint63 && (t <? n)%uint63 then
        match mask_log imm with
        | Some j =>
            match res_know (f_mem F) (fl_res L3) t j with
            | Some c => Some (D3One (FxState.rset F rd (align_res a j c) (f_pc F + 4)%uint63) L3 n)
            | None =>
                let tau := fst (root_tag (f_mem F) t j) in
                if (tau <? n)%uint63 && is_plain tau then
                  match first_unknown (f_mem F) (fl_res L3) tau (snd (root_tag (f_mem F) t j)) with
                  | Some i =>
                      match res_know_plain (f_mem F) (fl_res L3) tau (i - 1) with
                      | Some c0 => Some (D3Two F (res_ledger3 L3 (tau, 2 ^ i, c0)) n
                                               F (res_ledger3 L3 (tau, 2 ^ i, c0 + 2 ^ (i - 1))) n)
                      | None => None
                      end
                  | None => None
                  end
                else None
            end
        | None => None
        end
      else None
  | _ => None
  end.

Lemma res_know_plain_sound n rho M ress t i c :
  regs_ok rho M -> Forall (res_ok n rho) ress -> to_Z t < 2 ^ 60 -> 0 <= i ->
  res_know_plain M ress t i = Some c -> bv_unsigned (rho t) mod 2 ^ i = c.
Proof.
  intros HM Hall Hpl Hi H. unfold res_know_plain in H.
  destruct (i <=? to_Z (base_align M t)) eqn:E.
  - injection H as <-. apply Z.leb_le in E.
    pose proof (lb_align rho M t HM) as Hlb. unfold lb in Hlb.
    rewrite (fk_vkind_plain _ Hpl), (fk_vbase_plain _ Hpl) in Hlb.
    change ((0 =? 1)%uint63 || (0 =? 4)%uint63) with false in Hlb. cbv iota in Hlb.
    set (al := to_Z (base_align M t)) in *.
    rewrite <- (Z.mod_mod_divide _ (2 ^ al) (2 ^ i)), Hlb; [apply Z.mod_0_l; apply Z.pow_nonzero; lia|].
    exists (2 ^ (al - i)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
  - apply Z.leb_gt in E. pose proof (i63_range (base_align M t)).
    exact (res_find_sound n rho ress t i c ltac:(lia) Hall H).
Qed.

Lemma res_know_sound n rho M ress t j c :
  regs_ok rho M -> (forall t' rg, iget t' M = Some rg -> region_ok rho t' rg) ->
  Forall (res_ok n rho) ress -> to_Z t < 2 ^ 60 -> 1 <= j ->
  res_know M ress t j = Some c -> bv_unsigned (rho t) mod 2 ^ j = c.
Proof.
  intros HM Hreg Hall Hpl Hj H. unfold res_know in H.
  destruct (res_know_plain M ress t j) as [c1|] eqn:E1.
  - injection H as <-. exact (res_know_plain_sound n rho M ress t j c1 HM Hall Hpl ltac:(lia) E1).
  - destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
    destruct (rg_kind rg) as [|p] eqn:Ek; [discriminate|].
    destruct (res_know_plain M ress p (j + 3)) as [c'|] eqn:E2; [|discriminate]. injection H as <-.
    destruct (Hreg t rg Hg) as (_ & _ & _ & _ & _ & _ & Hrk). rewrite Ek in Hrk. destruct Hrk as [Hpt Hsh].
    pose proof (res_know_plain_sound n rho M ress p (j + 3) c' HM Hall ltac:(lia) ltac:(lia) E2) as Hc'.
    rewrite Hsh. set (X := bv_unsigned (rho p)) in *.
    assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    assert (E8 : 2 ^ (j + 3) = 8 * 2 ^ j) by (rewrite Z.pow_add_r by lia; lia).
    rewrite E8 in Hc'.
    assert (EX : X / 8 = 2 ^ j * (X / (8 * 2 ^ j)) + c' / 8).
    { rewrite (Z.div_mod X (8 * 2 ^ j)) at 1 by lia. rewrite Hc'.
      replace (8 * 2 ^ j * (X / (8 * 2 ^ j)) + c') with (c' + (2 ^ j * (X / (8 * 2 ^ j))) * 8) by lia.
      rewrite Z.div_add by lia. lia. }
    rewrite EX. rewrite <- Z.add_assoc, Z.add_comm, Z.mul_comm, Z.mod_add by lia. reflexivity.
Qed.

Lemma mod_next_bit X i c0 :
  1 <= i -> X mod 2 ^ (i - 1) = c0 -> X mod 2 ^ i = c0 \/ X mod 2 ^ i = c0 + 2 ^ (i - 1).
Proof.
  intros Hi Hc. set (P := 2 ^ (i - 1)) in *.
  assert (HP : 0 < P) by (apply Z.pow_pos_nonneg; lia).
  assert (Ep : 2 ^ i = 2 * P) by (unfold P; rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  rewrite Ep. pose proof (Z.mod_pos_bound X P HP) as Hb. rewrite Hc in Hb.
  assert (EX : X = P * (X / P) + c0) by (rewrite <- Hc; apply Z.div_mod; lia).
  destruct (Z_mod2_cases (X / P)) as [E|E].
  - left. rewrite EX at 1. rewrite (Z.div_mod (X / P) 2) at 1 by lia. rewrite E.
    replace (P * (2 * (X / P / 2) + 0) + c0) with (c0 + (X / P / 2) * (2 * P)) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - right. rewrite EX at 1. rewrite (Z.div_mod (X / P) 2) at 1 by lia. rewrite E.
    replace (P * (2 * (X / P / 2) + 1) + c0) with ((c0 + P) + (X / P / 2) * (2 * P)) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Theorem xpc_align2_sound n rho F L3 ms m res :
  xpc_align2 F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_align2 in Hx.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct fi as [| | | | | |op rd rs1 imm| | | | | | | | | |]; try discriminate Hx.
  cbv zeta in Hx. set (a := FxState.rget F rs1) in *.
  match type of Hx with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  apply andb_true_iff in C as [C Htn]. apply andb_true_iff in C as [C Ht0]. apply andb_true_iff in C as [C Hpl].
  apply andb_true_iff in C as [Hop Htag]. destruct op; try discriminate Hop.
  destruct (mask_log imm) as [j|] eqn:Hm; [|discriminate]. destruct (mask_log_spec imm j Hm) as [Hj Hs].
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0, Htn. rewrite to_Z_0 in Hn0.
  unfold is_plain in Hpl. apply ltb_spec in Hpl. change (to_Z kind_lim) with (2 ^ 60) in Hpl.
  pose proof HD as (HDI & HL & _ & _). pose proof HDI as (HRn & H0 & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR. pose proof (R_regs_ok _ _ _ _ _ HR) as HM.
  assert (Hreg : forall t' rg, iget t' (f_mem F) = Some rg -> region_ok rho t' rg)
    by (intros t' rg Hg; exact (R_region_ok _ _ _ _ _ _ _ HR Hg)).
  pose proof (lp_res _ _ _ _ _ _ _ _ _ _ _ HL) as Hress.
  apply rpok.
  destruct (res_know (f_mem F) (fl_res L3) (vtag a) j) as [c|] eqn:Hk.
  - injection Hx as <-.
    pose proof (res_know_sound n rho _ _ _ _ _ HM Hreg Hress Hpl (proj1 Hj) Hk) as Hc.
    assert (Hval : forall rho2, agree n rho rho2 -> dv rho2 (align_res a j c) = alu64 ALU_AND (dv rho a) (dv rho (FV 0 imm))).
    { intros rho2 [H02 Hag2]. rewrite (dv_conc rho H0).
      assert (Er : rho2 (vtag a) = rho (vtag a)) by (apply Hag2; exact Htn).
      rewrite (align_val rho2 a imm j c Hpl Hj Hs) by (rewrite Er; exact Hc).
      f_equal. rewrite !(fk_dv_plain _ a Hpl), Er. reflexivity. }
    apply (rbind _ _ _ _ _ _ _ _ (reach_regop_val n rho F L3 ms m _ ALU_AND rd a (FV 0 imm) (align_res a j c)
                                    HD Hn0 Hlt Hi eq_refl eq_refl Hval)).
    intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & ->) HD1. apply rret; [exact HD1 | reflexivity].
  - set (tau := fst (root_tag (f_mem F) (vtag a) j)) in *.
    destruct ((tau <? n)%uint63 && is_plain tau) eqn:Ct; [|discriminate].
    apply andb_true_iff in Ct as [Htau Hplt]. apply ltb_spec in Htau.
    unfold is_plain in Hplt. apply ltb_spec in Hplt. change (to_Z kind_lim) with (2 ^ 60) in Hplt.
    destruct (first_unknown (f_mem F) (fl_res L3) tau (snd (root_tag (f_mem F) (vtag a) j))) as [i|] eqn:Hfu; [|discriminate].
    destruct (res_know_plain (f_mem F) (fl_res L3) tau (i - 1)) as [c0|] eqn:Hc0; [|discriminate]. injection Hx as <-.
    assert (Hi1 : 1 <= i).
    { unfold first_unknown in Hfu. apply find_some in Hfu as [Hin _]. cbn [In] in Hin. lia. }
    assert (Hi0 : 0 <= i - 1) by lia.
    pose proof (res_know_plain_sound n rho (f_mem F) (fl_res L3) tau (i - 1) c0 HM Hress Hplt Hi0 Hc0) as Hc.
    assert (Hp : 0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
    destruct (mod_next_bit _ i c0 Hi1 Hc) as [Hc'|Hc'].
    + apply (reach_res _ _ _ _ _ _ (tau, 2 ^ i, c0)); [exact HD | | cbn [dres3_in]; left; reflexivity].
      split; [exact Htau|]. split; [exact Hp | exact Hc'].
    + apply (reach_res _ _ _ _ _ _ (tau, 2 ^ i, c0 + 2 ^ (i - 1))); [exact HD | | cbn [dres3_in]; right; reflexivity].
      split; [exact Htau|]. split; [exact Hp | exact Hc'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_builtin5 : fstate -> fledger3 -> int -> option dres3 :=
  xpc_or (xpc_order code) (xpc_or xpc_ltu (xpc_or xpc_sltu (xpc_or xpc_pgnz (xpc_or xpc_align2
         (xpc_or (xpc_table IM code) (xpc_opaque code)))))).

Theorem xpc_builtin5_sound n rho F L3 ms m res :
  xpc_builtin5 F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  pose proof (xpc_or_sound cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0) as Hor.
  apply Hor; [exact (xpc_order_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  apply Hor; [exact xpc_ltu_sound|]. apply Hor; [exact xpc_sltu_sound|]. apply Hor; [exact xpc_pgnz_sound|].
  apply Hor; [exact xpc_align2_sound|].
  apply Hor; [exact (xpc_table_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0)|].
  exact (xpc_opaque_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Qed.


End Drive3O.
