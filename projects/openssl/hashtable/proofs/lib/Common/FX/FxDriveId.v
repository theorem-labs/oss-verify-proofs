(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg MiscCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxSys FxMisc FxDrive.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sextw (w : word) : word := sext 64 (low32 w).

Definition id_XI (tu tg : int) (rho : int -> word) (m : Model) : Prop :=
  rho tu = sextw (cr_uid (m_creds m)) /\ cr_euid (m_creds m) = cr_uid (m_creds m)
  /\ rho tg = sextw (cr_gid (m_creds m)) /\ cr_egid (m_creds m) = cr_gid (m_creds m).

Definition id_xtags (tu tg : int) : list int := [tu; tg].

Lemma id_XI_rho : forall tu tg rho rho' m,
  (forall t, In t (id_xtags tu tg) -> rho' t = rho t) -> id_XI tu tg rho m -> id_XI tu tg rho' m.
Proof.
  intros tu tg rho rho' m H (H1 & H2 & H3 & H4). unfold id_XI.
  rewrite (H tu (or_introl eq_refl)), (H tg (or_intror (or_introl eq_refl))).
  repeat split; assumption.
Qed.

Lemma id_XI_creds : forall tu tg rho m m',
  m_creds m' = m_creds m -> id_XI tu tg rho m -> id_XI tu tg rho m'.
Proof. intros tu tg rho m m' E H. unfold id_XI in *. rewrite E. exact H. Qed.

Lemma id_XI_init : forall tu tg rho inp m,
  creds_from inp m ->
  rho tu = sextw (in_uid inp) -> rho tg = sextw (in_gid inp) ->
  id_XI tu tg rho m.
Proof.
  intros tu tg rho inp m Hc Hu Hg.
  pose proof (getid_ret_from inp m 174 cr_uid Hc getid_uid) as E1.
  pose proof (getid_ret_from inp m 176 cr_gid Hc getid_gid) as E2.
  cbv beta iota in E1, E2. change (174 <? 176) with true in E1. change (176 <? 176) with false in E2.
  cbv iota in E1, E2.
  unfold id_XI. rewrite E1, E2.
  split; [exact Hu |]. split; [rewrite <- E1; exact (getid_uid_euid_same inp m Hc) |].
  split; [exact Hg |]. rewrite <- E2. exact (getid_gid_egid_same inp m Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section IdDefs.
Local Open Scope uint63_scope.
Variable code : itrie finstr.
Variables tu tg : int.

(* [comment removed for export] *)
Definition id_tag (nr : int) : option int :=
  if (nr =? 174) || (nr =? 175) then (if is_plain tu then Some tu else None)
  else if (nr =? 176) || (nr =? 177) then (if is_plain tg then Some tg else None)
  else None.

(* [comment removed for export] *)
Definition is_sextw_a0 (fi : finstr) : bool :=
  match fi with
  | FOpImm32 ALU_ADD rd rs1 imm => (rd =? 10) && (rs1 =? 10) && w_eqb imm w_zero
  | _ => false
  end.

Definition xsys_id (F : fstate) (L : fledger) (n : int) : option dres :=
  if negb (ecall_here code F) then None else
  match conc (FxState.rget F 17) with
  | None => None
  | Some nr =>
      match id_tag nr with
      | None => None
      | Some t =>
          match iget (f_pc F + 4) code with
          | Some fi =>
              if is_sextw_a0 fi
              then Some (DOne (FxState.rset F 10 (FV t w_zero) (f_pc F + 4 + 4)) L n)
              else None
          | None => None
          end
      end
  end.

(* [comment removed for export] *)
Definition xsys_none : fstate -> fledger -> int -> option dres := fun _ _ _ => None.
Definition xsys_or (x1 x2 : fstate -> fledger -> int -> option dres)
    : fstate -> fledger -> int -> option dres :=
  fun F L n => match x1 F L n with Some r => Some r | None => x2 F L n end.
End IdDefs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Step32.
Variable segs : list Segment.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

Lemma opimm32_step : forall (pc : int) op rd rs1 imm ms,
  iget pc code = Some (FOpImm32 op rd rs1 imm) ->
  ms_pc_val ms = Z_to_bv 64 (to_Z pc) ->
  exists rdr rs1r : reg,
    ireg rdr = rd /\ ireg rs1r = rs1 /\ to_Z pc < pc_bound - 4 /\
    RiscvSemantics.step segs ms =
      MachineOk (ms_of ms
        (Sem.rset rdr (sext 64 (alu32 op (low32 (Sem.rget (core_of ms) rs1r)) (low32 (wbv imm))))
                  (with_pc (Z_to_bv 64 (to_Z (pc + 4)%uint63)) (core_of ms)))
        (ms_mem ms)).
Proof.
  intros pc op rd rs1 imm ms Hi Hpc.
  pose proof (Hcode _ _ Hi) as Hb. unfold build_entry in Hb.
  destruct ((to_Z pc <? pc_bound - 4) && (0 <=? to_Z pc)) eqn:Hrng; [| discriminate Hb].
  apply andb_true_iff in Hrng as [Hlt _]. apply Z.ltb_lt in Hlt.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w |] eqn:Hf; [| discriminate Hb].
  destruct (is_ecall w) eqn:Ee; [discriminate Hb |].
  destruct (decode_any w) as [[i sz] |] eqn:Hd; [| discriminate Hb].
  destruct sz as [| p | p]; try discriminate Hb.
  do 3 (destruct p as [p | p |]; try discriminate Hb).
  assert (Hf' : fetch_word segs (ms_pc ms) = Some w) by (unfold ms_pc; rewrite Hpc; exact Hf).
  pose proof (pc_plus4 pc Hlt) as Enpc.
  destruct i; cbn [compile] in Hb;
    repeat match type of Hb with
           | context [match ?x with _ => _ end] => destruct x
           end; try discriminate Hb.
  - (* [comment removed for export] *)
    injection Hb as <- <- <- <-.
    exists rd0, rs0. split; [reflexivity |]. split; [reflexivity |]. split; [exact Hlt |].
    rewrite (step_decode segs ms w _ Hf' Ee Hd).
    rewrite wbv_w_of_bv, low32_sext64.
    unfold exec. cbn [core_of c_pc]. rewrite Hpc, Enpc. reflexivity.
  - (* [comment removed for export] *)
    injection Hb as <- <- <- <-.
    exists rd0, rs0. split; [reflexivity |]. split; [reflexivity |]. split; [exact Hlt |].
    rewrite (step_decode segs ms w _ Hf' Ee Hd).
    rewrite wbv_w_of_bv, low32_zext64.
    unfold exec. cbn [core_of c_pc]. rewrite Hpc, Enpc. reflexivity.
Qed.
End Step32.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section IdSound.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Variable R0 : list (word * word).
Variable Lim : Z.
Variable rl : role.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Variables tu tg : int.
Hypothesis Htu : In tu xtags.
Hypothesis Htg : In tg xtags.
Hypothesis HXI : forall rho m, XI rho m -> id_XI tu tg rho m.

Local Abbreviation DInv' := (DInv cfg segs IM R0 Lim rl keep mem0 XI xtags).
Local Abbreviation sys_ok' := (sys_ok cfg segs IM R0 Lim rl keep mem0 XI xtags).
Local Abbreviation sys_okX' := (sys_okX cfg segs IM R0 Lim rl keep mem0 XI xtags).

Lemma ireg_10 : forall r : reg, ireg r = 10%uint63 -> r = (10%bv : bv 5).
Proof.
  intros r H. apply bv_eq. rewrite <- ireg_to_Z, H. reflexivity.
Qed.

Lemma sextw_addiw0 : forall (x : word) imm,
  w_eqb imm w_zero = true ->
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (wbv imm))) = sextw x.
Proof.
  intros x imm H. apply w_eqb_true_iff in H.
  assert (E : wbv imm = wbv w_zero) by (unfold wbv; rewrite H; reflexivity).
  rewrite E, wbv_w_zero. unfold sextw. f_equal.
  unfold alu32, alu.
  assert (E0 : low32 w0 = Z_to_bv 32 0) by (apply bv_eq; reflexivity).
  rewrite E0. apply bv_eq. rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 32 0)) with 0. rewrite Z.add_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma is_plain_lt : forall t, is_plain t = true -> to_Z t < 2 ^ 60.
Proof. intros t H. unfold is_plain in H. apply Uint63.ltb_spec in H. exact H. Qed.

Lemma id_tag_sound : forall nr t rho m,
  id_tag tu tg nr = Some t -> id_XI tu tg rho m ->
  exists sel, getid_no (to_Z nr) sel /\ rho t = sextw (sel (m_creds m)) /\ In t xtags
              /\ to_Z t < 2 ^ 60.
Proof.
  intros nr t rho m H (Hu & Heu & Hg & Heg). unfold id_tag in H.
  destruct (nr =? 174)%uint63 eqn:E174.
  { apply eqb_lit in E174. cbn [orb] in H. destruct (is_plain tu) eqn:Hp; [| discriminate H]. injection H as <-.
    exists cr_uid. rewrite E174. split; [exact getid_uid |]. split; [exact Hu |]. split; [exact Htu | exact (is_plain_lt _ Hp)]. }
  destruct (nr =? 175)%uint63 eqn:E175.
  { apply eqb_lit in E175. cbn [orb] in H. destruct (is_plain tu) eqn:Hp; [| discriminate H]. injection H as <-.
    exists cr_euid. rewrite E175. split; [exact getid_euid |]. split; [rewrite Heu; exact Hu |].
    split; [exact Htu | exact (is_plain_lt _ Hp)]. }
  cbn [orb] in H.
  destruct (nr =? 176)%uint63 eqn:E176.
  { apply eqb_lit in E176. cbn [orb] in H. destruct (is_plain tg) eqn:Hp; [| discriminate H]. injection H as <-.
    exists cr_gid. rewrite E176. split; [exact getid_gid |]. split; [exact Hg |]. split; [exact Htg | exact (is_plain_lt _ Hp)]. }
  destruct (nr =? 177)%uint63 eqn:E177; cbn [orb] in H; [| discriminate H].
  apply eqb_lit in E177. destruct (is_plain tg) eqn:Hp; [| discriminate H]. injection H as <-.
  exists cr_egid. rewrite E177. split; [exact getid_egid |]. split; [rewrite Heg; exact Hg |].
  split; [exact Htg | exact (is_plain_lt _ Hp)].
Qed.

(* [comment removed for export] *)
Theorem xsys_id_soundX : forall n rho F L ms m res,
  xsys_id code tu tg F L n = Some res ->
  DInv' n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_okX' n rho F L res ms m.
Proof.
  intros n rho F L ms m res Hsys HD Hstep.
  pose proof HD as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HX & Hxt & Hfr).
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  unfold xsys_id in Hsys.
  destruct (ecall_here code F) eqn:Hec; cbn [negb] in Hsys; [| discriminate Hsys].
  pose proof (ecall_here_at segs code Hcode F Hec) as Hat.
  destruct (conc (FxState.rget F 17)) as [nr |] eqn:Hnr; [| discriminate Hsys].
  destruct (conc_sound R0 rho _ _ H0 Hnr) as [_ Hx8]. rewrite <- (pend_x8 segs IM rho F ms HR) in Hx8.
  destruct (id_tag tu tg nr) as [t |] eqn:Htag; [| discriminate Hsys].
  destruct (iget (f_pc F + 4)%uint63 code) as [fi |] eqn:Hfi; [| discriminate Hsys].
  destruct (is_sextw_a0 fi) eqn:Hsx; [| discriminate Hsys]. injection Hsys as <-.
  destruct fi as [| | | | | | | | op rd rs1 imm | | | | | | | |]; try discriminate Hsx.
  destruct op; try discriminate Hsx. cbn [is_sextw_a0] in Hsx.
  rewrite !andb_true_iff in Hsx. destruct Hsx as [[Erd Ers] Eimm].
  apply Uint63.eqb_spec in Erd, Ers. subst rd rs1.
  destruct (id_tag_sound nr t rho m Htag (HXI rho m HX)) as (sel & Hno & Hrt & Hin & Htpl).
  (* [comment removed for export] *)
  pose proof (getid_step_iff cfg segs (ms_pend ms) (ms_reg ms 17) m (to_Z nr) sel Hno Hx8 Hh (proj1 Hnl)
                (ms_pend_svc ms)) as Hiff.
  set (idw := sel (m_creds m)) in *.
  set (ms1 := sysret (ms_pend ms) idw (ms_mem (ms_pend ms))) in *.
  exists unit, tt, (fun _ => mkCfg ms1 m).
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) [] (SNext (mkCfg ms1 m))).
  { apply Hiff. split; reflexivity. }
  (* [comment removed for export] *)
  assert (Hpc1 : ms_pc_val ms1 = Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)).
  { unfold ms1. cbn [sysret ms_pc_val]. unfold ms_pc. cbn [ms_pend ms_pc_val].
    rewrite (R_pc _ _ _ _ _ HR). apply pc_plus4. exact Hat. }
  destruct (opimm32_step segs code Hcode _ _ _ _ _ ms1 Hfi Hpc1)
    as (rdr & rs1r & Erd & Ers & Hlt1 & Hstep1).
  apply ireg_10 in Erd, Ers. subst rdr rs1r.
  assert (Hrs : Sem.rget (core_of ms1) (10%bv : bv 5) = idw).
  { unfold Sem.rget. change (is_x0 (10%bv : bv 5)) with false. cbv iota.
    unfold ms1. cbn [core_of c_regs].
    unfold sysret. cbn [ms_regs]. unfold Sem.reg_get.
    rewrite Riscv.Prelude.bvmap_get_set_same. reflexivity. }
  rewrite Hrs, (sextw_addiw0 idw imm Eimm) in Hstep1.
  set (ms2 := ms_of ms1 (Sem.rset (10%bv : bv 5) (sextw idw)
                 (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4 + 4)%uint63)) (core_of ms1))) (ms_mem ms1)) in *.
  assert (Hk : rsteps segs 1 ms1 = MachineOk ms2).
  { cbn [rsteps]. change (ms_svc_pending ms1) with (@None word). rewrite Hstep1. reflexivity. }
  (* [comment removed for export] *)
  assert (Hreg : reg_step ms ms2 (10%bv : bv 5) (sextw idw) (f_pc F + 4 + 4)%uint63).
  { unfold reg_step. split; [reflexivity |]. split; [| split; [reflexivity | split; reflexivity]].
    intros r. unfold ms2. rewrite core_of_ms_of, sem_rget_rset, sem_rget_with_pc.
    destruct (is_x0 r) eqn:Ex0; [reflexivity |].
    destruct (bv_eqb r (10%bv : bv 5)) eqn:Er; [reflexivity |].
    unfold Sem.rget. rewrite Ex0. unfold ms1. cbn [core_of c_regs].
    rewrite (sysret_reg_other (ms_pend ms) idw (ms_mem (ms_pend ms)) r); [reflexivity |].
    intros ->. unfold bv_eqb in Er. rewrite Z.eqb_refl in Er. discriminate Er. }
  assert (HRn2 : Rn segs IM n rho (FxState.rset F 10%uint63 (FV t w_zero) (f_pc F + 4 + 4)%uint63) ms2).
  { change 10%uint63 with (ireg (10%bv : bv 5)).
    apply (fx_rd_known_sound segs IM n rho F ms ms2 _ (sextw idw) _ _ HRn Hreg).
    intros rho' [_ Hag]. rewrite (fk_dv_plain rho' (FV t w_zero)) by exact Htpl.
    cbn [vtag vw]. rewrite (Hag t (Hxt t Hin)), Hrt, wbv_w_zero.
    unfold w0. apply fxs_bv_add_0. }
  (* [comment removed for export] *)
  pose proof (budget_pend cfg segs rl ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  pose proof (budget_step cfg segs rl _ _ _ _ _ Hbud1 Hstepa) as Hbud2.
  assert (Hbud3 : budget cfg segs rl ms2 m).
  { unfold budget in *. destruct rl; [| exact I].
    eapply within_budget_cfg_star; [exact Hbud2 |].
    exact (rsteps_star_cfg cfg segs 1 ms1 m ms2 Hh (proj1 Hnl) Hk). }
  eexists _, _, _, rho, ms2, m, 1%nat. cbn [cfg_ms cfg_model].
  split; [reflexivity |]. split; [exact Hk |]. split; [reflexivity |].
  split.
  2:{ apply node_ext_same; [lia | intros; reflexivity | intros; reflexivity | reflexivity | reflexivity
                            | reflexivity | reflexivity | reflexivity]. }
  apply (DInv_same_mem cfg segs IM R0 Lim rl keep mem0 XI xtags n rho F _ L ms ms2 m HD);
    [reflexivity | reflexivity | exact HRn2 | exact Hbud3].
Qed.

Theorem xsys_id_sound : forall n rho F L ms m res,
  xsys_id code tu tg F L n = Some res ->
  DInv' n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_ok' res ms m.
Proof.
  intros n rho F L ms m res H HD Hs.
  exact (sys_okX_ok cfg segs IM R0 Lim rl keep mem0 XI xtags n rho F L res ms m (xsys_id_soundX n rho F L ms m res H HD Hs)).
Qed.

(* [comment removed for export] *)
Definition xsys_sound_for (xsys : fstate -> fledger -> int -> option dres) : Prop :=
  forall n rho F L ms m res, xsys F L n = Some res -> DInv' n rho F L ms m ->
    RiscvSemantics.step segs ms = MachineOk (ms_pend ms) -> sys_ok' res ms m.

Lemma xsys_none_sound : xsys_sound_for xsys_none.
Proof. intros n rho F L ms m res H. discriminate H. Qed.

Lemma xsys_or_sound : forall x1 x2,
  xsys_sound_for x1 -> xsys_sound_for x2 -> xsys_sound_for (xsys_or x1 x2).
Proof.
  intros x1 x2 H1 H2 n rho F L ms m res H HD Hs. unfold xsys_or in H.
  destruct (x1 F L n) as [r |] eqn:E.
  - injection H as <-. exact (H1 n rho F L ms m r E HD Hs).
  - exact (H2 n rho F L ms m res H HD Hs).
Qed.

Lemma xsys_id_sound_for : xsys_sound_for (xsys_id code tu tg).
Proof. exact xsys_id_sound. Qed.

(* [comment removed for export] *)
Definition xsys_sound_forX (xsys : fstate -> fledger -> int -> option dres) : Prop :=
  forall n rho F L ms m res, xsys F L n = Some res -> DInv' n rho F L ms m ->
    RiscvSemantics.step segs ms = MachineOk (ms_pend ms) -> sys_okX' n rho F L res ms m.

Lemma xsys_none_soundX : xsys_sound_forX xsys_none.
Proof. intros n rho F L ms m res H. discriminate H. Qed.

Lemma xsys_or_soundX : forall x1 x2,
  xsys_sound_forX x1 -> xsys_sound_forX x2 -> xsys_sound_forX (xsys_or x1 x2).
Proof.
  intros x1 x2 H1 H2 n rho F L ms m res H HD Hs. unfold xsys_or in H.
  destruct (x1 F L n) as [r |] eqn:E.
  - injection H as <-. exact (H1 n rho F L ms m r E HD Hs).
  - exact (H2 n rho F L ms m res H HD Hs).
Qed.

Lemma xsys_id_sound_forX : xsys_sound_forX (xsys_id code tu tg).
Proof. exact xsys_id_soundX. Qed.
End IdSound.
