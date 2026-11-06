(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymStepR.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep PIosFxSound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegFPSteps SegDisch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AX2F.

Module SFP.

Definition rm_okb (rm : bv 3) : bool := (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool.

Definition fmt_bytes (fmt : ffmt) : nat := match fmt with FMT_D => 8%nat | FMT_S => 4%nat end.

Definition is_fp_instr (i : instr) : bool :=
  match i with
  | FLoad _ _ _ _ | FStore _ _ _ _ | Fmv _ _ _ _ | Fsgnj _ _ _ _ _ | Fari _ _ _ _ _ _ | Fcvt _ _ _ _ _
  | Fcmp _ _ _ _ _ | Fclass _ _ _ | Fsqrt _ _ _ _ | Fma _ _ _ _ _ _ _ | Fminmax _ _ _ _ _
  | Csr _ _ _ _ | CsrI _ _ _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Definition sfresh (ss : sym_state) (rd : reg) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EVar (s_next ss)))
      (s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss).

(* [comment removed for export] *)
Definition sfresh01 (ss : sym_state) (rd : reg) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EAlu ALU_SLTU (ELit 0) (EVar (s_next ss))))
      (s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss).

Definition fcvt_is_fp (t : fcvt_ty) : bool := match t with FC_S | FC_D => true | _ => false end.

(* [comment removed for export] *)
Definition fp_step (segs : list Segment) (i : instr) (ss : sym_state) : stepres :=
  if negb (s_clean ss) then SStop else
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let fk := facts_of (s_know ss) in
  match i with
  | FLoad fmt rd rs imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      match sym_read segs ss fk scr_nil a n false with
      | None => SStop
      | Some (_, scs, scr', nx') => SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | FStore fmt rs1 rs2 imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      SOk (SSR (p + 4) (s_regs ss) (SE a n (EVar (s_next ss)) :: s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss))
          (flat_sc fk a n ++ storeok_sc fk a n) scr_nil
  | Fmv FMV_X_F _ rd _ => SOk (sfresh ss rd (p + 4)) [] scr_nil
  | Fmv FMV_F_X _ _ _ => SOk (sjump ss (p + 4)) [] scr_nil
  | Fsgnj _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr_nil
  | Fari _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr_nil else SStop
  | Fcvt dst src rd _ rm =>
      if negb (rm_okb rm) then SStop else
      if fcvt_is_fp dst then SOk (sjump ss (p + 4)) [] scr_nil           (* [comment removed for export] *)
      else if fcvt_is_fp src then SOk (sfresh ss rd (p + 4)) [] scr_nil    (* [comment removed for export] *)
      else SStop
  | Fcmp _ _ rd _ _ => SOk (sfresh01 ss rd (p + 4)) [] scr_nil
  | Fclass _ rd _ => SOk (sfresh ss rd (p + 4)) [] scr_nil
  | Csr CSR_RS rd rs1 csr =>      (* [comment removed for export] *)
      if (bv_eqb rs1 0 && Z.eqb (bv_unsigned csr) 2)%bool then SOk (sset ss rd (ELit 0) (p + 4)) [] scr_nil else SStop
  | CsrI CSR_RS rd uimm csr =>    (* [comment removed for export] *)
      if (bv_eqb rd 0 && Z.eqb (bv_unsigned csr) 1)%bool then SOk (sjump ss (p + 4)) [] scr_nil else SStop
  | _ => SStop
  end.

Lemma fp_step_know : forall segs i ss ss' scs scr', fp_step segs i ss = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros segs i ss ss' scs scr' H. unfold fp_step in H. destruct (negb (s_clean ss)); [discriminate|].
  destruct i; try discriminate H.
  - destruct op; try discriminate H. destruct (_ && _)%bool; [|discriminate H]. injection H as <- _ _. reflexivity.
  - destruct op; try discriminate H. destruct (_ && _)%bool; [|discriminate H]. injection H as <- _ _. reflexivity.
  - destruct (sym_read segs ss _ scr_nil _ _ false) as [[[[v scs0] scr0] nx]|]; [|discriminate H]. injection H as <- _ _. reflexivity.
  - injection H as <- _ _. reflexivity.
  - destruct (rm_okb rm); [|discriminate H]. injection H as <- _ _. reflexivity.
  - injection H as <- _ _. reflexivity.
  - injection H as <- _ _. reflexivity.
  - destruct (negb (rm_okb rm)); [discriminate H|]. destruct (fcvt_is_fp dst); [injection H as <- _ _; reflexivity|].
    destruct (fcvt_is_fp src); [injection H as <- _ _; reflexivity | discriminate H].
  - destruct dir; injection H as <- _ _; reflexivity.
  - injection H as <- _ _. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fx_of (ms : machine_state) : FPState := mkFP (ms_fregs ms) (ms_fcsr ms).

Lemma fx_of_mkst : forall (fx : FPState) regs pc mem rom, fx_of (@mkst fx regs pc mem rom) = fx.
Proof. intros [fr cs] regs pc mem rom. reflexivity. Qed.

Lemma fx_of_mkstR : forall (fx : FPState) regs pc mem rom rv, fx_of (@mkstR fx regs pc mem rom rv) = fx.
Proof. intros [fr cs] regs pc mem rom rv. reflexivity. Qed.

Definition st_okXF (segs : list Segment) (E : env) (base rom : word -> option byte) (ss : sym_state) (ms : machine_state) : Prop :=
  frm_zero (ms_fcsr ms) /\ @st_okX (fx_of ms) segs E base rom ss ms.

(* [comment removed for export] *)
Lemma st_okX_XF : forall (fx : FPState) segs E base rom ss ms,
  frm_zero (@fp_csr fx) -> @st_okX fx segs E base rom ss ms -> st_okXF segs E base rom ss ms.
Proof.
  intros fx segs E base rom ss ms Hz HX.
  destruct (st_okR_parts segs E base rom ss ms (st_okX_R segs E base rom ss ms HX)) as (_ & _ & _ & _ & Hms).
  assert (Hfx : fx_of ms = fx) by (rewrite Hms; apply fx_of_mkstR).
  split; [|rewrite Hfx; exact HX].
  rewrite Hms. destruct fx as [fr cs]. exact Hz.
Qed.

Lemma st_okXF_X : forall segs E base rom ss ms,
  st_okXF segs E base rom ss ms -> frm_zero (@fp_csr (fx_of ms)) /\ @st_okX (fx_of ms) segs E base rom ss ms.
Proof. intros segs E base rom ss ms [Hz HX]. split; [exact Hz | exact HX]. Qed.

Lemma st_okXF_agree : forall segs E E' base rom ss ms,
  st_okXF segs E base rom ss ms -> eagree (s_next ss) E E' -> st_okXF segs E' base rom ss ms.
Proof. intros segs E E' base rom ss ms [Hz HX] Ha. split; [exact Hz|]. eapply st_okX_agree; [exact HX | exact Ha]. Qed.

Lemma rm_okb_sound : forall rm, rm_okb rm = true -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z.
Proof.
  intros rm H. unfold rm_okb in H. apply orb_prop in H as [H|H]; [left; apply Z.leb_le; exact H | right; apply Z.eqb_eq; exact H].
Qed.

(* [comment removed for export] *)
Lemma fp_step_fclass : forall (fx : FPState) segs regs pc mem rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass fmt rd rs1, 4%Z) ->
  exists v : word,
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w fmt rd rs1 Hf He Hd.
  destruct fx as [fr cs].
  eexists. fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; [reflexivity|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma find_readbase_flat_storeok : forall i fk a n,
  find_readbase i (flat_sc fk a n ++ storeok_sc fk a n) = None.
Proof.
  intros i fk a n. unfold flat_sc, storeok_sc.
  destruct (base_range fk (a_base a)) as [[lo hi]|]; [destruct (_ && _)%bool|]; destruct (wr_covered fk fk a n); reflexivity.
Qed.

Section Sound.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma fp_step_sound : forall (fx : FPState) E base rom ss ms i ss' scs scr' w,
  is_fp_instr i = true ->
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  fp_step segs i ss = SOk ss' scs scr' ->
  (s_next ss <= s_next ss')%nat -> SDI.disch_all segs ss ss' scs ->
  frm_zero (@fp_csr fx) ->
  @st_okX fx segs E base rom ss ms ->
  exists E1 ms', eagree (s_next ss) E E1
    /\ RiscvSemantics.step segs ms = MachineOk ms'
    /\ st_okXF segs E1 base rom ss' ms'
    /\ (forall E'', eagree (s_next ss') E1 E'' -> scs_denot segs base E'' scs).
Proof.
  intros fx E base rom ss ms i ss' scs scr' w Hfp Hf He Hd Hs Hle Hdis Hz HX.
  unfold fp_step in Hs.
  destruct (s_clean ss) eqn:Hcl; [|discriminate]. cbn [negb] in Hs.
  apply s_clean_None in Hcl.
  pose proof (st_okX_R _ _ _ _ _ _ HX) as HR0.
  destruct (st_okR_parts _ E base rom ss ms HR0) as (Hregs0 & Hmem0 & Hlf0 & Hkn0 & Hms).
  rewrite Hcl in Hms. cbn [resv_denot] in Hms. rewrite mkstR_None in Hms.
  set (regs := ms_regs ms) in *.
  set (pc := Z_to_bv 64 (s_pc ss)) in *. set (MEM := mem_denot E base (s_log ss)) in *.
  pose proof (facts_of_ok segs E base _ Hkn0) as Hfk. set (fk := facts_of (s_know ss)) in *.
  assert (PARTS : forall E'', eagree (s_next ss) E E'' ->
            regs_ok E'' (s_regs ss) regs /\ mem_denot E'' base (s_log ss) = MEM /\ log_flat E'' (s_log ss)
            /\ know_ok segs E'' base (s_know ss)).
  { intros E'' Ha''. destruct (st_okR_parts _ E'' base rom ss ms (HX E'' Ha'')) as (R1 & M1 & L1 & K1 & _).
    split; [exact R1|]. split; [|split; [exact L1 | exact K1]]. rewrite <- Hmem0. symmetry. exact M1. }
  (* [comment removed for export] *)
  assert (GEN : forall (fx' : FPState) sr' regs' nx' E',
    frm_zero (@fp_csr fx') ->
    eagree (s_next ss) E E' -> (s_next ss <= nx')%nat ->
    (forall E'', eagree nx' E' E'' -> regs_ok E'' sr' regs') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' regs' (v_addi pc 4) MEM rom) ->
    exists ms', RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF segs E' base rom (SSR (s_pc ss + 4) sr' (s_log ss) (s_know ss) nx' (s_resv ss)) ms').
  { intros fx' sr' regs' nx' E' Hz' Ha' Hle' Hregs' Hstep.
    eexists. split; [exact Hstep|].
    split; [destruct fx'; exact Hz'|].
    rewrite fx_of_mkst. intros E'' Ha''. cbn [s_next] in Ha''.
    assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [exact Ha' | eapply eagree_le; [exact Ha'' | exact Hle']]).
    destruct (PARTS E'' HaE) as (R1 & M1 & L1 & K1).
    exists regs'. cbn [s_pc s_regs s_log s_know s_resv s_next]. rewrite Hcl. cbn [resv_denot]. rewrite mkstR_None.
    split; [unfold pc; rewrite SymExec.v_addi_lit, M1; reflexivity|].
    split; [exact (Hregs' E'' Ha'')|]. split; [exact L1 | exact K1]. }
  (* [comment removed for export] *)
  assert (GEN_same : forall (fx' : FPState),
    frm_zero (@fp_csr fx') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' regs (v_addi pc 4) MEM rom) ->
    exists E1 ms', eagree (s_next ss) E E1 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF segs E1 base rom (sjump ss (s_pc ss + 4)) ms').
  { intros fx' Hz' Hstep. unfold sjump.
    destruct (GEN fx' (s_regs ss) regs (s_next ss) E Hz' (eagree_refl _ _) ltac:(lia)) as (ms' & H2 & H3); [| exact Hstep |].
    { intros E'' Ha''. exact (proj1 (PARTS E'' Ha'')). }
    exists E, ms'. split; [apply eagree_refl|]. split; [exact H2 | exact H3]. }
  assert (GEN_fresh : forall (fx' : FPState) rd (v : word),
    frm_zero (@fp_csr fx') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) MEM rom) ->
    exists E1 ms', eagree (s_next ss) E E1 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF segs E1 base rom (sfresh ss rd (s_pc ss + 4)) ms').
  { intros fx' rd v Hz' Hstep. unfold sfresh.
    destruct (GEN fx' (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EVar (s_next ss))) (if bv_eqb rd 0 then regs else regupd regs rd v) (S (s_next ss)) (eupd E (s_next ss) v) Hz' (eagree_upd _ _ _)
                ltac:(lia)) as (ms' & H2 & H3); [| exact Hstep |].
    { intros E'' Ha''.
      assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha'' | lia]]).
      apply regs_ok_upd; [exact (proj1 (PARTS E'' HaE))|]. cbn [edenot].
      destruct Ha'' as [Hv _]. rewrite <- (Hv (s_next ss)) by lia. apply eupd_at. }
    exists (eupd E (s_next ss) v), ms'. split; [apply eagree_upd|]. split; [exact H2 | exact H3]. }
  assert (GEN_fresh01 : forall (fx' : FPState) rd (b : bool),
    frm_zero (@fp_csr fx') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' (if bv_eqb rd 0 then regs else regupd regs rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0)) (v_addi pc 4) MEM rom) ->
    exists E1 ms', eagree (s_next ss) E E1 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF segs E1 base rom (sfresh01 ss rd (s_pc ss + 4)) ms').
  { intros fx' rd b Hz' Hstep. unfold sfresh01. set (v := if b then Z_to_bv 64 1 else Z_to_bv 64 0) in *.
    destruct (GEN fx' (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EAlu ALU_SLTU (ELit 0) (EVar (s_next ss))))
                (if bv_eqb rd 0 then regs else regupd regs rd v) (S (s_next ss)) (eupd E (s_next ss) v) Hz' (eagree_upd _ _ _)
                ltac:(lia)) as (ms' & H2 & H3); [| exact Hstep |].
    { intros E'' Ha''.
      assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha'' | lia]]).
      apply regs_ok_upd; [exact (proj1 (PARTS E'' HaE))|]. cbn [edenot].
      destruct Ha'' as [Hv _]. rewrite <- (Hv (s_next ss)) by lia. rewrite eupd_at.
      rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. unfold v.
      destruct b; vm_compute; reflexivity. }
    exists (eupd E (s_next ss) v), ms'. split; [apply eagree_upd|]. split; [exact H2 | exact H3]. }
  assert (GEN_set0 : forall (fx' : FPState) rd,
    frm_zero (@fp_csr fx') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) MEM rom) ->
    exists E1 ms', eagree (s_next ss) E E1 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF segs E1 base rom (sset ss rd (ELit 0) (s_pc ss + 4)) ms').
  { intros fx' rd Hz' Hstep. unfold sset.
    destruct (GEN fx' (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0)) (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (s_next ss) E Hz' (eagree_refl _ _) ltac:(lia))
      as (ms' & H2 & H3); [| exact Hstep |].
    { intros E'' Ha''. apply regs_ok_upd; [exact (proj1 (PARTS E'' Ha''))|]. apply edenot_lit. }
    exists E, ms'. split; [apply eagree_refl|]. split; [exact H2 | exact H3]. }
  (* [comment removed for export] *)
  Local Ltac fin0 G :=
    let E1 := fresh "E1" in let ms1 := fresh "ms1" in let A := fresh "A" in let B := fresh "B" in let C := fresh "C" in
    destruct G as (E1 & ms1 & A & B & C); exists E1, ms1; split; [exact A|]; split; [exact B|]; split; [exact C | intros; constructor].
  (* [comment removed for export] *)
  destruct i; try discriminate Hfp.
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    destruct (bv_eqb rs1 0 && Z.eqb (bv_unsigned csr) 2)%bool eqn:Hc; [|discriminate].
    injection Hs as <- <- <-. apply andb_prop in Hc as [Hrs1 Hcsr].
    assert (rs1 = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hrs1; apply Z.eqb_eq in Hrs1; exact Hrs1).
    assert (csr = 2%bv) as -> by (apply bv_eq; apply Z.eqb_eq in Hcsr; exact Hcsr).
    fin0 (GEN_set0 fx rd Hz ltac:(rewrite Hms; apply (fp_step_frrm fx segs regs pc MEM rom w rd Hf He Hd Hz))).
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    destruct (bv_eqb rd 0 && Z.eqb (bv_unsigned csr) 1)%bool eqn:Hc; [|discriminate].
    injection Hs as <- <- <-. apply andb_prop in Hc as [Hrd Hcsr].
    assert (rd = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hrd; apply Z.eqb_eq in Hrd; exact Hrd).
    assert (csr = 1%bv) as -> by (apply bv_eq; apply Z.eqb_eq in Hcsr; exact Hcsr).
    destruct (fp_step_csrsi_fflags fx segs regs pc MEM rom w uimm Hf He Hd Hz) as (cs' & Hz' & Hstep).
    fin0 (GEN_same (mkFP (@fp_regs fx) cs') Hz' ltac:(rewrite Hms; exact Hstep)).
  - (* [comment removed for export] *)
    set (n := fmt_bytes fmt) in Hs.
    set (a := to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm)) in Hs.
    destruct (sym_read segs ss fk scr_nil a n false) as [[[[v0 rscs] rscr] nx']|] eqn:Hr; [|discriminate Hs].
    injection Hs as <- <- <-. cbn [s_next] in Hle.
    assert (Hn18 : (1 <= n)%nat /\ (n <= 8)%nat) by (unfold n; destruct fmt; cbn; lia). destruct Hn18 as [Hn1 Hn8].
    destruct (SDI.disch_val segs E base rom ss ms (SSR (s_pc ss + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) rscs Hle Hdis HX)
      as (E1 & Ha1 & Hscs).
    destruct (PARTS E1 Ha1) as (R1 & M1 & L1 & K1).
    destruct (sym_read_sound segs E1 base ss scr_nil a n false v0 rscs rscr nx' Hr (Hscs E1 (eagree_refl _ _)) L1 K1 Hn1 Hn8)
      as [Hfl (bs & Hrd & Hlen & _)].
    rewrite M1 in Hrd.
    assert (Hadr : adenot E1 a = v_addi (getr regs rs1) (bv_signed imm)).
    { subst a. rewrite (to_saddrK_denot segs E1 base fk _ _ (facts_of_ok segs E1 base _ K1)), R1. reflexivity. }
    rewrite Hadr in Hrd.
    assert (HREG : forall E'', eagree nx' E1 E'' -> regs_ok E'' (s_regs ss) regs).
    { intros E'' Ha''. apply (proj1 (PARTS E'' ltac:(eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]]))). }
    destruct fmt.
    + (* [comment removed for export] *)
      destruct (GEN (mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) (@fp_regs fx)) (@fp_csr fx))
                   (s_regs ss) regs nx' E1 Hz Ha1 Hle HREG) as (ms' & H2 & H3).
      { rewrite Hms. apply (fp_step_flw fx segs regs pc MEM rom w rd rs1 imm _ bs Hf He Hd eq_refl). exact Hrd. }
      exists E1, ms'. split; [exact Ha1|]. split; [exact H2|]. split; [exact H3 | exact Hscs].
    + (* [comment removed for export] *)
      destruct (GEN (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
                   (s_regs ss) regs nx' E1 Hz Ha1 Hle HREG) as (ms' & H2 & H3).
      { rewrite Hms. apply (fp_step_fld fx segs regs pc MEM rom w rd rs1 imm _ bs Hf He Hd eq_refl). exact Hrd. }
      exists E1, ms'. split; [exact Ha1|]. split; [exact H2|]. split; [exact H3 | exact Hscs].
  - (* [comment removed for export] *)
    set (n := fmt_bytes fmt) in *.
    set (a := to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm)) in *.
    injection Hs as <- <- <-.
    assert (Hn18 : (1 <= n)%nat /\ (n <= 8)%nat) by (unfold n; destruct fmt; cbn; lia). destruct Hn18 as [Hn1 Hn8].
    set (sval := match fmt with
                 | FMT_D => reg_get (@fp_regs fx) rs2
                 | FMT_S => Z_to_bv 64 (bv_unsigned (low32 (reg_get (@fp_regs fx) rs2)))
                 end).
    set (E' := eupd E (s_next ss) sval).
    assert (Ha' : eagree (s_next ss) E E') by apply eagree_upd.
    assert (SCS : forall E'', eagree (s_next ss) E E'' -> scs_denot segs base E'' (flat_sc fk a n ++ storeok_sc fk a n)).
    { exact (SDI.disch_closed segs E base rom ss ms _ _ (find_readbase_flat_storeok _ _ _ _) Hdis HX). }
    assert (ADR : forall E'', eagree (s_next ss) E E'' -> adenot E'' a = v_addi (getr regs rs1) (bv_signed imm)).
    { intros E'' Ha''. destruct (PARTS E'' Ha'') as (R1 & _ & _ & K1).
      subst a. rewrite (to_saddrK_denot segs E'' base fk _ _ (facts_of_ok segs E'' base _ K1)), R1. reflexivity. }
    assert (FLOK : forall E'', eagree (s_next ss) E E'' ->
              flat E'' a (Z.of_nat n) /\ RiscvSemantics.store_ok segs MEM (v_addi (getr regs rs1) (bv_signed imm)) n = true).
    { intros E'' Ha''. destruct (PARTS E'' Ha'') as (R1 & M1 & _ & K1).
      pose proof (facts_of_ok segs E'' base _ K1) as Hfk''.
      destruct (flat_sc_sound segs E'' base fk _ _ _ Hfk'' Hn1 Hn8 (SCS E'' Ha'')) as [Hfl Hsc].
      split; [exact Hfl|].
      pose proof (storeok_sc_sound segs E'' base fk a n Hfk'' Hfl Hn1 Hn8 Hsc) as Hok.
      rewrite <- (ADR E'' Ha''). rewrite <- M1. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
    destruct (FLOK E (eagree_refl _ _)) as [_ Hok].
    exists E'. eexists. split; [exact Ha'|].
    assert (STEP : RiscvSemantics.step segs ms =
                   MachineOk (@mkst fx regs (v_addi pc 4) (wbytes MEM (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes n sval)) rom)).
    { rewrite Hms. destruct fmt.
      - rewrite (fp_step_fsw fx segs regs pc MEM rom w rs1 rs2 imm _ Hf He Hd eq_refl Hok). do 2 f_equal.
        unfold sval, word_to_le_bytes. rewrite u_small; [reflexivity|].
        pose proof (bv_unsigned_in_range _ (low32 (reg_get (@fp_regs fx) rs2))) as Hr32. unfold bv_modulus in Hr32. cbn in Hr32. lia.
      - rewrite (fp_step_fsd fx segs regs pc MEM rom w rs1 rs2 imm _ Hf He Hd eq_refl Hok). reflexivity. }
    split; [exact STEP|].
    split.
    { split; [cbn [ms_fcsr mkst]; destruct fx; exact Hz|].
      rewrite fx_of_mkst. intros E'' Ha''. cbn [s_next] in Ha''.
      assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [exact Ha' | eapply eagree_le; [exact Ha'' | lia]]).
      destruct (PARTS E'' HaE) as (R1 & M1 & L1 & K1). destruct (FLOK E'' HaE) as [Hfl'' _].
      exists regs. cbn [s_pc s_regs s_log s_know s_resv]. rewrite Hcl. cbn [resv_denot mem_denot]. rewrite mkstR_None.
      split.
      + unfold pc. rewrite SymExec.v_addi_lit, M1, (ADR E'' HaE). cbn [edenot].
        destruct Ha'' as [Hv _]. rewrite <- (Hv (s_next ss)) by lia. unfold E'. rewrite eupd_at. reflexivity.
      + split; [exact R1|]. split; [|exact K1]. cbn [log_flat]. split; [exact Hn8|]. split; [exact Hfl'' | exact L1]. }
    intros E'' Ha''. cbn [s_next] in Ha''. apply SCS.
    eapply eagree_trans; [exact Ha' | eapply eagree_le; [exact Ha'' | lia]].
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    destruct (rm_okb rm) eqn:Hrm; [|discriminate]. injection Hs as <- <- <-.
    destruct (fp_step_fari fx segs regs pc MEM rom w op fmt rd rs1 rs2 rm Hf He Hd Hz (rm_okb_sound rm Hrm)) as (fr' & cs' & Hz' & Hstep).
    fin0 (GEN_same (mkFP fr' cs') Hz' ltac:(rewrite Hms; exact Hstep)).
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    destruct (fp_step_fsgnj fx segs regs pc MEM rom w op fmt rd rs1 rs2 Hf He Hd) as (fr' & Hstep).
    fin0 (GEN_same (mkFP fr' (@fp_csr fx)) Hz ltac:(rewrite Hms; exact Hstep)).
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    destruct (fp_step_fcmp fx segs regs pc MEM rom w op fmt rd rs1 rs2 Hf He Hd Hz) as (b & cs' & Hz' & Hstep).
    fin0 (GEN_fresh01 (mkFP (@fp_regs fx) cs') rd b Hz' ltac:(rewrite Hms; exact Hstep)).
  - (* [comment removed for export] *)
    destruct (rm_okb rm) eqn:Hrm; [|discriminate]. cbn [negb] in Hs.
    pose proof (rm_okb_sound rm Hrm) as Hrm'.
    destruct (fcvt_is_fp dst) eqn:Hdst.
    + injection Hs as <- <- <-.
      assert (Hdst' : dst = FC_S \/ dst = FC_D) by (destruct dst; try discriminate; auto).
      destruct (fp_step_fcvt_to_f fx segs regs pc MEM rom w dst src rd rs1 rm Hf He Hd Hdst' Hz Hrm') as (fr' & cs' & Hz' & Hstep).
      fin0 (GEN_same (mkFP fr' cs') Hz' ltac:(rewrite Hms; exact Hstep)).
    + destruct (fcvt_is_fp src) eqn:Hsrc; [|discriminate]. injection Hs as <- <- <-.
      assert (Hdst' : dst = FC_W \/ dst = FC_WU \/ dst = FC_L \/ dst = FC_LU) by (destruct dst; try discriminate; auto).
      assert (Hsrc' : src = FC_S \/ src = FC_D) by (destruct src; try discriminate; auto).
      destruct (fp_step_fcvt_to_x fx segs regs pc MEM rom w dst src rd rs1 rm Hf He Hd Hdst' Hsrc' Hz Hrm') as (v & cs' & Hz' & Hstep).
      fin0 (GEN_fresh (mkFP (@fp_regs fx) cs') rd v Hz' ltac:(rewrite Hms; exact Hstep)).
  - (* [comment removed for export] *)
    destruct dir.
    + (* [comment removed for export] *)
      injection Hs as <- <- <-.
      destruct fmt.
      * fin0 (GEN_fresh fx rd (sext 64 (low32 (reg_get (@fp_regs fx) rs1))) Hz
                 ltac:(rewrite Hms; apply (fp_step_fmv_x_w fx segs regs pc MEM rom w rd rs1 Hf He Hd))).
      * fin0 (GEN_fresh fx rd (reg_get (@fp_regs fx) rs1) Hz
                 ltac:(rewrite Hms; apply (fp_step_fmv_x_d fx segs regs pc MEM rom w rd rs1 Hf He Hd))).
    + (* [comment removed for export] *)
      injection Hs as <- <- <-.
      destruct fmt.
      * fin0 (GEN_same (mkFP (bvmap_set rd (nan_box (low32 (getr regs rs1))) (@fp_regs fx)) (@fp_csr fx)) Hz
                 ltac:(rewrite Hms; apply (fp_step_fmv_w_x fx segs regs pc MEM rom w rd rs1 Hf He Hd))).
      * fin0 (GEN_same (mkFP (bvmap_set rd (getr regs rs1) (@fp_regs fx)) (@fp_csr fx)) Hz
                 ltac:(rewrite Hms; apply (fp_step_fmv_d_x fx segs regs pc MEM rom w rd rs1 Hf He Hd))).
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    destruct (fp_step_fclass fx segs regs pc MEM rom w fmt rd rs1 Hf He Hd) as (v & Hstep).
    fin0 (GEN_fresh fx rd v Hz ltac:(rewrite Hms; exact Hstep)).
Qed.

End Sound.
End SFP.
