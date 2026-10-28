(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeAt_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmSmall Require Import SmallAt_u SmallWin_u SmallCur_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_after_value_csrc_T_u Cut_after_value_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module AfterValueProof.
Module G := Cut_after_value_csrc_u.
Module GT := Cut_after_value_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Definition Pb : expr := EVar 10.  Definition Eb : expr := EVar 11.  Definition Vb : expr := EVar 49.
Definition RETPC : Z := nth 0 GT.ENDS 0.
Definition DEADPC : Z := nth 1 GT.ENDS 0.
Definition PARENT : Z := PML.PC_PARENT.
Definition SCR : Z := CH.hd_scr G.HDECL.

Definition CONSTS : PSK.consts := PSK.CONSTS PML.VT_PARSER PML.VT_FUNC PML.VT_VISITOR 0x10000 0xf8000 0x10000 PML.IMG_RO_HI SCR [] 0.
Definition X0 : PSK.pexprs := PSK.PX (EVar 41) (EVar 32) (ELit 17) (EVar 43) (EVar 44) (ELit 0) (EVar 46) (EVar 35) (EVar 36) (EVar 37) (EVar 38) (EVar 39) (EVar 40) (EVar 47) (EVar 48) (ELit 0).
Lemma kn0_eq : CC.cp_know G.cp0 = SPK.kn CONSTS false Pb Vb Eb (EVar 2) (EVar 33) X0.
Proof. vmc_refl. Qed.

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition PE : expr := EVar 37.  Definition CE : expr := APC.escale 2 (EVar 35).

Definition GP : expr := EVar (CC.cp_nx (nth 1 G.CPS G.cp0) - APC.NCS - 1).

Definition view_chk (cells : list kentry) (stv : expr) : bool :=
  match SPA.pview_w cells Pb PE CE with
  | Some pv => (expr_eqb (PB4.pv_level pv) (EVar 41) && expr_eqb (PB4.pv_wend pv) (EVar 33) && expr_eqb (PB4.pv_wptr pv) (EVar 32) && expr_eqb (PB4.pv_st pv) stv
                && expr_eqb (PB4.pv_sst pv) (EVar 43) && expr_eqb (PB4.pv_nst pv) (EVar 44) && expr_eqb (PB4.pv_more pv) (ELit 0) && expr_eqb (PB4.pv_done pv) (EVar 46)
                && expr_eqb (PB4.pv_size pv) (EVar 36) && expr_eqb (PB4.pv_sb pv) (EVar 38) && expr_eqb (PB4.pv_send pv) (APC.eadd (EVar 38) (EVar 39))
                && expr_eqb (PB4.pv_scend pv) (APC.eadd (EVar 38) (EVar 40)))%bool
  | None => false
  end.
Definition parent_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  if (expr_eqb (nth 10 regs (ELit 0)) Pb && CH2.blocks_eqb BLj BLi && view_chk (SR.ps_cells ps) (ELit 17))%bool
  then CH2.custom_chk GT.NF G.HDECL 48 1 BLi [] [KRange (EVar nx) 0 255] (Some (EVar nx)) c ps cj BLi
  else None.
Definition sltu0 (c : Z) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB GP (ELit c)) (ELit 1)) 0 0.
Definition BL0 : CA.blocks := [(PE, CE); (EVar 38, EVar 40)].

Definition gh_is (cells : list kentry) (x : Z) : bool :=
  (PB.has cells (KRange GP x x) || PB.has cells (KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB GP (ELit x)) (ELit 1)) 1 1))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PARENT then
        (Z.eqb (SR.ps_pc ps) PARENT && Nat.eqb i 0 &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj => (Nat.eqb j 1 && match parent_chk c ps cj (nth i G.BLS []) (nth j G.BLS []) with Some ci => Nat.eqb (CC.cp_nx cj) (CH2.ci_nx ci + 1 + APC.NCS) | None => false end)%bool
                     | None => false end
         | None => false end)%bool
      else if Z.eqb pc DEADPC then (Nat.eqb i 1 && PB.has cells (sltu0 0) && PB.has cells (sltu0 8) && PB.has cells (sltu0 14))%bool
      else (Nat.eqb i 1 && PB.exit_base_chk GT.NF RETPC c ps && CH2.blocks_eqb (nth i G.BLS []) BL0 && PB.has cells (KWord (SA Eb 0) 4 (ELit 0))
            && ((view_chk cells (ELit 2) && gh_is cells 0) || (view_chk cells (ELit 7) && (gh_is cells 8 || gh_is cells 14))))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.

Lemma last_cases : forall (l : list Z), l = [] \/ exists l' y, l = l' ++ [y].
Proof. intros l. destruct l as [|a l0]; [left; reflexivity|]. right. destruct (@exists_last _ (a :: l0) ltac:(discriminate)) as (l' & y & H). exists l', y. exact H. Qed.

Lemma win_le : forall (M : mem) P ps, PML.parser_at M P ps -> match PML.ps_win ps with Some (p, e) => p <= e | None => True end.
Proof.
  intros M P ps H. unfold PML.parser_at in H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _).
  destruct (PML.ps_win ps) as [[p e]|]; [exact (proj2 (proj2 Hw)) | exact I].
Qed.

Section Main.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PARENT_OK : PMS.parent_spec L.

Variables (mw : option (Z * Z)) (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Hypothesis HH : hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis Hentry : PML.entry L R M sp r PMS.AFTERV_SCR.
Hypothesis Ha0 : PML.a0 R P.
Hypothesis Ha1 : PML.a1 R E.
Hypothesis Hmore : PML.ps_more ps = false.
Hypothesis Hst : PML.ps_st ps = PML.ST_NUMBER.
Hypothesis HPA : PML.parser_at M P (PML.ps_set_win ps mw).
Hypothesis HWF : PML.wf_ps_stale ps.
Hypothesis HWF1 : PML.wf_ps_stale (PMCUR.ps_set_more ps true).
Hypothesis HWIN : PML.win_ok M LBo ps.
Hypothesis HBB : PMS.buf_bound_stale ps B.
Hypothesis HVIS : PML.vis_at M V.
Hypothesis HEC : PML.ec_at M E 0.
Hypothesis HLS : PML.ls_ok g M.
Hypothesis HG : g <> PML.LS0.
Hypothesis HPC : PML.pcredit_x L cr ps kx bx.
Hypothesis OP : PML.obj_on_stack L sp P 272.
Hypothesis OV : PML.obj_on_stack L sp V 48.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis AP1 : PML.apart P 272 V 48.
Hypothesis AP2 : PML.apart P 272 E 16.
Hypothesis AP3 : PML.apart V 48 E 16.

Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
   PML.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      (PML.parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) /\ PMCUR.wf_c ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code /\
      (code <> 0 -> PML.ps_more ps' = false) /\ PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g /\ code <> 0) /\
      LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PML.W_par P E /\ PML.pcredit_x L cr' ps' kx bx /\
      (PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ code = 0 /\ PML.ps_more ps' = false /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
       PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps /\
       PML.ps_bptr ps' = PML.ps_bptr ps /\ length (PML.ps_buf ps') = length (PML.ps_buf ps))) ->
   regs_preserved R R' -> L5C.hpres L LBk sp PMS.AFTERV_SCR W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
   srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Variables (line0 pos0 : Z).
Hypothesis Hline0 : PML.u64 M (P + 160) line0.
Hypothesis Hpos0 : PML.u64 M (P + 168) pos0.
Hypothesis Hlpr : 0 <= line0 < 2 ^ 64 /\ 0 <= pos0 < 2 ^ 64.

Let psm := PML.ps_set_win ps mw.
Let wptr := fst (PSA.wincells mw).
Let wend := snd (PSA.wincells mw).
Let bcap := PML.ps_bcap ps.
Let k0 := bcap / 2.
Let bptr := PML.ps_bptr ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Let done := PML.b2z (PML.ps_done ps).

Definition E0 : env :=
  Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [wptr; wend; B; k0; size0; bptr; sb; slen; scap; level; PML.ps_st ps; PML.ps_sst ps; PML.ps_nst ps; 0; done; line0; pos0; V] 0)))
      (fun _ => []).

Lemma SPF : sp mod 16 = 0 /\ 0x7fff7f800000 + 512 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ L5.defined M (sp - 512) 512 /\ hl_ceil L + 512 <= sp.
Proof.
  destruct Hentry as (_ & _ & _ & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as F. destruct Hstk as (S1 & S2 & S3 & S4 & S5). unfold PMS.AFTERV_SCR in *.
  repeat split; try lia; try assumption.
Qed.

Lemma NUM :
  block_range L bptr bcap /\ block_range L sb scap /\ L5.defined M bptr bcap /\ L5.defined M sb scap /\ (bptr + bcap <= sb \/ sb + scap <= bptr) /\
  bcap = 2 * k0 /\ 264 <= bcap <= 2 ^ 27 /\ size0 < bcap /\ 1 <= slen <= 1027 /\ slen <= scap /\ 66 <= scap <= 1056 /\
  0 <= PML.ps_sst ps <= 11 /\ 0 <= PML.ps_nst ps <= 7 /\ 0 <= level <= 1024 /\ 0 <= done <= 1.
Proof.
  pose proof HPA as H. unfold PML.parser_at, psm in H. cbn [PML.ps_set_win PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_sb PML.ps_scap PML.ps_stack] in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & Hb264 & _ & _ & _ & _ & Hsl & _).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (I1 : In (bptr, bcap) (PML.ps_blocks ps ++ LBo)) by (left; reflexivity).
  assert (I2 : In (sb, scap) (PML.ps_blocks ps ++ LBo)) by (right; left; reflexivity).
  destruct (Hwf _ I1) as (BR1 & BD1 & BA1). destruct (Hwf _ I2) as (BR2 & BD2 & BA2). cbn [fst snd] in *.
  unfold PML.ps_blocks in Hnd. fold bptr bcap sb scap in Hnd. cbn [map fst app] in Hnd. inversion Hnd as [|x l N1 N2]; subst.
  assert (Nsb : sb <> bptr) by (intros X; apply N1; apply list_elem_of_In; left; exact X).
  pose proof (L5C.blocks_apart_in _ _ _ sb scap BA1 (L5C.in_lb_remove_neq bptr sb scap _ I2 Nsb)) as A1.
  destruct Hstr as (_ & Hc8 & Hlt). fold bcap size0 in Hc8, Hlt.
  assert (Hk : bcap = 2 * k0).
  { unfold k0. pose proof (Z.div_mod bcap 8 ltac:(lia)) as D. rewrite Hc8 in D. rewrite D at 2. replace (8 * (bcap / 8) + 0) with ((4 * (bcap / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
  destruct HWF1 as (Wn & n' & W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). cbn [PMCUR.ps_set_more PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level] in *.
  destruct (W7 eq_refl) as (W8 & W9 & _). cbn [PML.ps_level PML.ps_set_nst] in W8, W9.
  destruct HPC as (_ & _ & (HP27 & _)).
  assert (Hs1 : 1 <= slen) by (unfold slen; rewrite W5; cbn [length]; lia).
  assert (Hsc : 66 <= scap <= 1056) by (fold scap in W4; cbn [In] in W4; lia).
  fold bcap in HP27. fold level in W9.
  split; [exact BR1|]. split; [exact BR2|]. split; [exact BD1|]. split; [exact BD2|]. split; [exact A1|]. split; [exact Hk|].
  unfold done. repeat split; try assumption; try lia; try (destruct (PML.ps_done ps); cbn; lia); try (unfold slen; lia).
Qed.

Lemma EV0 : forall x : reg, ev E0 (ridx x) = getr R x.
Proof. intros x. apply CL5.ev_reg. Qed.
Lemma UU : uv E0 (EVar 2) = sp /\ uv E0 Pb = P /\ uv E0 Eb = E /\ uv E0 Vb = V.
Proof.
  destruct Hentry as (_ & _ & Hsp & _). pose proof SPF as (S1 & S2 & S3 & S4 & _). destruct OP as (OP1 & OP2 & _), OV as (OV1 & OV2 & _), OE as (OE1 & OE2 & _).
  unfold PB.uv, Pb, Eb, Vb. cbn [edenot].
  split; [rewrite (EV0 2%bv), Hsp; apply u64_of_Z; lia|]. split; [rewrite (EV0 10%bv), Ha0; apply u64_of_Z; lia|]. split; [rewrite (EV0 11%bv), Ha1; apply u64_of_Z; lia|].
  change (ev E0 49) with (Z_to_bv 64 V). apply u64_of_Z. lia.
Qed.

Lemma At0 : CC.At RSEGS G.cp0 E0 R M.
Proof.
  pose proof UU as (U2 & UP & UE & UV). pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof NUM as (BR1 & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct OP as (OP1 & OP2 & OP3), OV as (OV1 & OV2 & _), OE as (OE1 & OE2 & _). destruct Hlpr as (Q1 & Q2).
  destruct HBB as (HB1 & HB2 & HB3). fold size0 in HB1.
  assert (SCRV : SCR = 512) by reflexivity.
  split; [exact (regs_ok_id R _ _)|]. rewrite kn0_eq. unfold SPK.kn, know_ok. rewrite Forall_app. split.
  - eapply (SPA.kn_sem_ok CONSTS eq_refl eq_refl (conj eq_refl eq_refl) ltac:(cbn [PSK.c_scr CONSTS]; rewrite SCRV; lia) Pb Vb Eb (EVar 2) (EVar 33) X0 E0 M P E V sp psm line0 pos0 0
             UP UE UV U2) with (L := L); cbn [PSK.c_scr CONSTS PSK.x_level PSK.x_wptr PSK.x_st PSK.x_sst PSK.x_nst PSK.x_more PSK.x_done PSK.x_k PSK.x_size PSK.x_p PSK.x_sb PSK.x_slen PSK.x_scap PSK.x_line PSK.x_pos PSK.x_ec X0];
      unfold psm; cbn [PML.ps_set_win PML.ps_level PML.ps_win PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_bcap PML.ps_buf PML.ps_bptr PML.ps_sb PML.ps_stack PML.ps_scap];
      rewrite ?SCRV; fold bcap bptr size0 sb scap slen level.
    all: try (split; lia). all: try lia.
    all: try exact HPA. all: try exact Hline0. all: try exact Hpos0. all: try exact LAY. all: try (destruct HEC as (X & _); exact X).
    all: try reflexivity.
    all: try (unfold PB.uv; cbn [edenot]; apply u64_of_Z; first [lia | unfold level, done, size0, slen in *; lia]).
    + rewrite Hst. reflexivity.
    + rewrite Hmore. reflexivity.
    + unfold PB.uv. cbn [edenot]. change (ev E0 35) with (Z_to_bv 64 k0). rewrite u64_of_Z by lia. lia.
    + destruct BR1 as (B0 & B1 & B2 & B3 & B4). unfold PB.uv. cbn [edenot]. change (ev E0 37) with (Z_to_bv 64 bptr). apply u64_of_Z. unfold hl_ceil in B4. lia.
    + destruct BR2 as (B0 & B1 & B2 & B3 & B4). unfold PB.uv. cbn [edenot]. change (ev E0 38) with (Z_to_bv 64 sb). apply u64_of_Z. unfold hl_ceil in B4. lia.
    + rewrite Hst. unfold PML.ST_NUMBER. lia.
    + split; assumption.
    + split; assumption.
  - destruct HLS as (IMGRO & _). destruct HEC as (_ & HEdef & _). unfold PML.apart in AP1, AP2, AP3.
    pose proof HPA as HPA'. unfold PML.parser_at in HPA'. destruct HPA' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HdefP).
    apply (SPA.kn_frz_ok CONSTS eq_refl (conj eq_refl eq_refl) ltac:(cbn [PSK.c_scr CONSTS]; rewrite SCRV; lia) Pb Vb Eb (EVar 2) E0 M P E V sp UP UE UV U2);
      cbn [PSK.c_scr CONSTS]; rewrite ?SCRV; try assumption; try (split; lia); try lia.
Qed.

Definition W : list L5.range := PML.W_par P E.
Lemma SCRV : CH.hd_scr G.HDECL = 512.
Proof. reflexivity. Qed.
Lemma STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). rewrite SCRV. repeat split; lia. Qed.
Lemma SCRP : 0 <= CH.hd_scr G.HDECL.
Proof. rewrite SCRV. lia. Qed.
Lemma NF32 : (32 <= GT.NF)%nat.
Proof. unfold GT.NF. lia. Qed.
Lemma U2 : bv_unsigned (ev E0 2) = sp.
Proof. exact (proj1 UU). Qed.
Lemma TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Proof. destruct Hentry as (_ & _ & _ & Htp & _). rewrite (EV0 4%bv), Htp, (PmLayout.ly_tp L LAY). reflexivity. Qed.
Lemma STATW : forall a, 0xd4df8 <= a < 0xd4dfa \/ 0xf6848 <= a < 0xf6848 + 544 -> CH2.wclient L sp a.
Proof.
  intros a Ha. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). split; [lia|]. right. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). split; [lia|].
  split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia|].
  split; [intros X; destruct (PmLayout.ly_ro_img L LAY a X ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia|].
  unfold in_errno. rewrite (PmLayout.ly_errno L LAY). lia.
Qed.
Lemma W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a.
Proof.
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). destruct OP as (OP1 & OP2 & _), OE as (OE1 & OE2 & _).
  intros w a Hw Hin. unfold W, PML.W_par in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - apply STATW. lia.
  - apply STATW. lia.
Qed.
Lemma CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a).
Proof.
  pose proof UU as (_ & _ & _ & UV). pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). destruct OV as (OV1 & OV2 & _).
  intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
  unfold PB.uv, Vb in UV. cbn [edenot] in UV. rewrite UV in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia].
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a).
Proof.
  pose proof UU as (_ & UP & UE & _). unfold PB.uv, Pb, Eb in UP, UE. cbn [edenot] in UP, UE.
  intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
  - rewrite UP in Ha. rewrite u64_of_Z in Ha by lia. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - rewrite UE in Ha. rewrite u64_of_Z in Ha by lia. exists (E, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Proof.
  intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). split; [lia|].
  split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
Qed.
Lemma DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL).
Proof. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). rewrite SCRV. exact S5. Qed.

Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := cr1 = cr.

Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop :=
  (forall a, 0 <= a < 2 ^ 40 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
  L5.bytes_at RSEGS M1 sb (PML.ps_stack ps) /\
  (i = 1%nat -> exists rest x, PML.ps_stack ps = rest ++ [x] /\ uv E1 GP = x).

Definition F0 : list SGP.region := CC.cp_F G.cp0.
Lemma foot_ok : CC.cps_all G.CPS (fun _ c => SP.F_sub (CC.cp_F c) F0) = true.
Proof. vmc_refl. Qed.
Lemma below_frame : forall i c E' (M1 M' : mem), nth_error G.CPS i = Some c -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' (CC.cp_F c) a -> M' a = M1 a) -> forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros i c E' M1 M' Hc Hag HF a Ha. apply HF. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ (CC.cps_all_sound _ _ foot_ok i c Hc) Hin) as Hin0.
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). destruct OP as (OP1 & OP2 & _). pose proof UU as (U2' & UP & _ & _).
  unfold hl_ceil in *. rewrite L5.unsigned_lit by lia. left.
  unfold F0 in Hin0. cbn [G.cp0 CC.cp_F In] in Hin0. destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-.
  - rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-512) Hag eq_refl). unfold estart. cbn [a_base a_off]. fold (uv E0 (EVar 2)). rewrite U2'. lia.
  - unfold Pb in UP. rewrite (PB.estart_agree GT.NF E0 E' (EVar 10) 0 Hag eq_refl). unfold estart. cbn [a_base a_off]. fold (uv E0 (EVar 10)). rewrite UP. lia.
Qed.

Lemma xi_below : forall i E1 (M1 M' : mem), (forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> XI i E1 M1 ->
  (forall a, 0 <= a < 2 ^ 40 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ L5.bytes_at RSEGS M' sb (PML.ps_stack ps).
Proof.
  intros i E1 M1 M' HB (X1 & X2 & _). pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof NUM as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  split; [intros a Ha; rewrite (HB a ltac:(unfold hl_ceil; lia)); exact (X1 a Ha)|].
  assert (FR : L5.frame_but [(hl_ceil L, 2 ^ 64 - hl_ceil L)] M1 M').
  { intros x Hout. rewrite <- (Z_to_bv_bv_unsigned _ x). pose proof (bv_unsigned_in_range _ x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. apply HB.
    split; [lia|]. destruct (Z_lt_dec (bv_unsigned x) (hl_ceil L)) as [Y|Y]; [exact Y|]. exfalso. apply (Hout (hl_ceil L, 2 ^ 64 - hl_ceil L) ltac:(left; reflexivity)). unfold L5.in_rng. cbn [fst snd]. lia. }
  apply (PB2.bytes_fr _ M1 M' FR); [|exact X2].
  split; [lia|]. split; [unfold hl_ceil in *; fold slen; lia|]. intros j Hj w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. fold slen in Hj. lia.
Qed.

Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.

Lemma CRED_BLK : forall i j E1 E2 cr1, CH2.den E2 (nth j G.BLS []) = CH2.den E1 (nth i G.BLS []) -> Cred i E1 cr1 -> Cred j E2 cr1.
Proof. intros i j E1 E2 cr1 _ H. exact H. Qed.

Lemma FRZ : forall E', env_agree GT.NF E0 E' ->
  uv E' (EVar 2) = sp /\ uv E' Pb = P /\ uv E' Eb = E /\ uv E' (EVar 41) = level /\ uv E' (EVar 43) = PML.ps_sst ps /\ uv E' (EVar 44) = PML.ps_nst ps /\ uv E' (EVar 46) = done /\
  uv E' (EVar 36) = size0 /\ uv E' (EVar 38) = sb /\ uv E' (EVar 40) = scap /\ uv E' (APC.eadd (EVar 38) (EVar 39)) = sb + slen /\ uv E' (APC.eadd (EVar 38) (EVar 40)) = sb + scap /\
  uv E' PE = bptr /\ uv E' CE = bcap /\ edenot E' (EVar 32) = Z_to_bv 64 wptr /\ edenot E' (EVar 33) = Z_to_bv 64 wend.
Proof.
  intros E' Hag. pose proof UU as (U2' & UP & UE & _).
  pose proof NUM as ((B0 & B1 & B2 & B3 & B4) & (C0 & C1 & C2 & C3 & C4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). unfold hl_ceil in *.
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (A : forall x, APC.expr_vars_lt GT.NF x = true -> uv E' x = uv E0 x) by (intros x Hx; exact (PB.uv_agree GT.NF E0 E' x Hag Hx)).
  assert (G : forall v z, (32 <= v < GT.NF)%nat -> ev E0 v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> uv E' (EVar v) = z).
  { intros v z Hv Hev Hz. rewrite A by (cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia). unfold PB.uv. cbn [edenot]. rewrite Hev. apply u64_of_Z. exact Hz. }
  assert (G38 : uv E' (EVar 38) = sb) by (apply G; [unfold GT.NF; lia | reflexivity | lia]).
  assert (G39 : uv E' (EVar 39) = slen) by (apply G; [unfold GT.NF; lia | reflexivity | lia]).
  assert (G40 : uv E' (EVar 40) = scap) by (apply G; [unfold GT.NF; lia | reflexivity | lia]).
  split; [rewrite A by reflexivity; exact U2'|]. split; [rewrite A by reflexivity; exact UP|]. split; [rewrite A by reflexivity; exact UE|].
  split; [apply G; [unfold GT.NF; lia | reflexivity | lia]|]. split; [apply G; [unfold GT.NF; lia | reflexivity | lia]|]. split; [apply G; [unfold GT.NF; lia | reflexivity | lia]|].
  split; [apply G; [unfold GT.NF; lia | reflexivity | lia]|]. split; [apply G; [unfold GT.NF; lia | reflexivity | unfold size0 in *; lia]|].
  split; [exact G38|]. split; [exact G40|].
  split; [rewrite PB.uv_eadd, G38, G39; apply Z.mod_small; lia|]. split; [rewrite PB.uv_eadd, G38, G40; apply Z.mod_small; lia|].
  split; [apply G; [unfold GT.NF; lia | reflexivity | lia]|].
  split; [unfold CE; rewrite PB.uv_escale; rewrite (G 35%nat k0 ltac:(unfold GT.NF; lia) eq_refl ltac:(lia)); rewrite Z.mod_small by lia; lia|].
  destruct Hag as [Hev _]. cbn [edenot]. split; [rewrite <- (Hev 32%nat) by (unfold GT.NF; lia) | rewrite <- (Hev 33%nat) by (unfold GT.NF; lia)]; reflexivity.
Qed.

Lemma last_stack : exists rest x, PML.ps_stack ps = rest ++ [x] /\ ((x = 0 /\ level = 0) \/ ((x = 8 \/ x = 14) /\ 1 <= level)) /\
  exists C, PML.ps_stack ps = PML.ST_ROOT :: C /\ Forall PML.is_container C /\ Z.of_nat (length C) = level.
Proof.
  destruct HWF1 as (Wn & n' & W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)). cbn [PMCUR.ps_set_more PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st] in *.
  destruct (W7 eq_refl) as (W8 & W9 & _ & W11 & _). rewrite Hst in W11.
  assert (HT : T = []).
  { unfold PML.transient, PML.comment_or_cr, PML.ST_NUMBER, PML.ST_STRING, PML.ST_CR in W11. destruct W11 as [(HT & _)|[(_ & X)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [exact HT | lia | lia | lia]. }
  subst T. rewrite app_nil_r in W5. fold level in W8.
  destruct (last_cases C) as [->|(C' & y & ->)].
  - exists [], 0. split; [exact W5|]. split; [left; split; [reflexivity | cbn in W8; lia]|]. exists []. split; [exact W5|]. split; [constructor | exact W8].
  - exists (PML.ST_ROOT :: C'), y. split; [rewrite W5; reflexivity|]. split.
    + right. pose proof W6 as W6'. apply Forall_app in W6' as [_ W6']. inversion W6' as [|y' l' Hy _]; subst. unfold PML.is_container, PML.ST_OBJECT, PML.ST_ARRAY in Hy.
      split; [exact Hy | rewrite length_app in W8; cbn [length] in W8; lia].
    + exists (C' ++ [y]). split; [exact W5|]. split; [exact W6 | exact W8].
Qed.

Lemma amb_def : forall i E1 (M1 : mem) model1 a n, HAMB i E1 M1 model1 -> L5.defined M a n -> (sp <= a /\ a + n <= 2 ^ 47) \/ (exists ch, In (ch, 16384) LBo /\ ch <= a /\ a + n <= ch + 16384) -> L5.defined M1 a n.
Proof.
  intros i E1 M1 model1 a n (_ & _ & _ & (cr1 & HH1 & _) & _ & Hdf) Hd Hc q Hq. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct Hc as [[C1 C2]|(ch & Hch & C1 & C2)].
  - apply Hdf; [lia | | apply Hd; exact Hq]. split; [right; left; unfold hl_ceil; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
  - destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
    destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *.
    apply Hdf; [unfold hl_ceil in B4; lia | | apply Hd; exact Hq].
    split; [left; exists (ch, 16384); split; [exact Hch | cbn [fst snd]; lia] | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1; lia].
Qed.

Lemma view_sound : forall cells stv E' (M' : mem), view_chk cells stv = true -> know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' ->
  L5.bytes_at RSEGS M' sb (PML.ps_stack ps) -> L5.defined M' P 272 ->
  exists buf, PML.parser_at M' P (PML.PS (uv E' stv) (PML.ps_sst ps) (PML.ps_nst ps) false (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf mw) /\ Z.of_nat (length buf) = size0.
Proof.
  intros cells stv E' M' HV HK Hag HB HdP. unfold view_chk in HV. destruct (SPA.pview_w cells Pb PE CE) as [pv|] eqn:HPV; [|discriminate].
  apply andb_prop in HV as [HV Y12]. apply andb_prop in HV as [HV Y11]. apply andb_prop in HV as [HV Y10]. apply andb_prop in HV as [HV Y9]. apply andb_prop in HV as [HV Y8].
  apply andb_prop in HV as [HV Y7]. apply andb_prop in HV as [HV Y6]. apply andb_prop in HV as [HV Y5]. apply andb_prop in HV as [HV Y4]. apply andb_prop in HV as [HV Y3].
  apply andb_prop in HV as [Y1 Y2]. apply expr_eqb_eq in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12.
  destruct (FRZ E' Hag) as (G2 & GP' & GE & G41 & G43 & G44 & G46 & G36 & G38 & G40 & GSE & GSC & GPE & GCE & G32 & G33).
  pose proof NUM as (BR1 & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). destruct OP as (OP1 & OP2 & OP3).
  pose proof (win_le M P psm HPA) as HWM. unfold psm in HWM. cbn [PML.ps_set_win PML.ps_win] in HWM.
  destruct (SPA.parser_view_w E' M' cells Pb PE CE pv P false (PML.ps_done ps) (PML.ps_stack ps) scap mw HK HPV GP' ltac:(lia) ltac:(lia)) as (buf & HPA' & Hlen & _).
  - rewrite Y7. rewrite PB2.uv_lit by lia. reflexivity.
  - rewrite Y8, G46. reflexivity.
  - rewrite Y10, G38. exact HB.
  - rewrite Y11, Y10, GSE, G38. reflexivity.
  - rewrite Y12, Y10, GSC, G38. reflexivity.
  - fold slen. lia.
  - rewrite Y3. exact G32.
  - rewrite Y2. exact G33.
  - exact HWM.
  - exact HdP.
  - exists buf. rewrite Y4, Y5, Y6, Y1, Y10, G43, G44, G41, G38, GCE, GPE in HPA'. rewrite Y9, G36 in Hlen. split; [exact HPA' | exact Hlen].
Qed.

Lemma leaf_know : forall c ps1 E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps1).
Proof. intros c ps1 E' R' M1 M' HLF. unfold know_ok. apply Forall_forall. intros X HX. rewrite <- LS. exact (CC.lf_cells _ _ _ _ _ _ _ HLF X HX). Qed.

Lemma cut1 : forall c, nth_error G.CPS 1 = Some c -> c = nth 1 G.CPS G.cp0.
Proof. intros c H. symmetry. exact (nth_error_nth _ _ _ H). Qed.

Lemma ghost_at : forall c E1 E' (M1 : mem), nth_error G.CPS 1 = Some c -> env_agree (CC.cp_nx c) E1 E' -> XI 1 E1 M1 ->
  exists rest x, PML.ps_stack ps = rest ++ [x] /\ uv E' GP = x.
Proof.
  intros c E1 E' M1 Hc Hag (_ & _ & X3). destruct (X3 eq_refl) as (rest & x & Hs & Hx). exists rest, x. split; [exact Hs|].
  rewrite (cut1 c Hc) in Hag. rewrite (PB.uv_agree _ E1 E' GP Hag ltac:(vm_compute; reflexivity)). exact Hx.
Qed.
Lemma app_last_inj : forall (l1 l2 : list Z) x y, l1 ++ [x] = l2 ++ [y] -> x = y.
Proof. intros l1 l2 x y H. apply app_inj_tail in H. exact (proj2 H). Qed.

Lemma leaf_exit : forall c k ps1 pc stz x, is_leaf 1 c k ps1 (CC.TOther pc) -> PB.exit_base_chk GT.NF RETPC c ps1 = true -> CH2.blocks_eqb (nth 1 G.BLS []) BL0 = true ->
  PB.has (SR.ps_cells ps1) (KWord (SA Eb 0) 4 (ELit 0)) = true -> view_chk (SR.ps_cells ps1) (ELit stz) = true -> gh_is (SR.ps_cells ps1) x = true ->
  (stz = 2 /\ x = 0) \/ (stz = 7 /\ (x = 8 \/ x = 14)) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 1 c ps1.
Proof.
  intros c k ps1 pc stz x IL Hbase HBL Hec HV HGh Hsx fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). destruct Hentry as (Hra & Hraok & _).
  assert (Hc : nth_error G.CPS 1 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K XI DEF0 (fun _ => 0) (fun _ => 0) PMS.AFTERV_SCR
           ltac:(rewrite SCRV; unfold PMS.AFTERV_SCR; lia) ltac:(unfold PMS.AFTERV_SCR; lia) S5 R EV0 r Hra Hraok heap_ok3 RETPC 1%nat c k ps1 _ ret_at IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  pose proof NUM as (BR1 & BR2 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  destruct OP as (OP1 & OP2 & OP3), OE as (OE1 & OE2 & OE3).
  pose proof HPA as HPA0. unfold PML.parser_at in HPA0. destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HdefP).
  destruct HEC as (_ & HEd & _).
  assert (HdP' : L5.defined M' P 272) by (apply (amb_def 1%nat E1 M' model1 P 272 HA' HdefP); left; lia).
  assert (HdE' : L5.defined M' E 16) by (apply (amb_def 1%nat E1 M' model1 E 16 HA' HEd); left; lia).
  assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { apply (below_frame 1%nat c E' M1 M' Hc HagE'). exact (CC.lf_frame _ _ _ _ _ _ _ HLF). }
  destruct (xi_below 1%nat E1 M1 M' HLOW HX) as (HST & HBY).
  destruct (view_sound _ (ELit stz) E' M' HV HK HagE' HBY HdP') as (buf & HPA' & Hlen).
  rewrite PB2.uv_lit in HPA' by lia.
  destruct (FRZ E' HagE') as (G2 & GP' & GE & G41 & G43 & G44 & G46 & G36 & G38 & G40 & GSE & GSC & GPE & GCE & G32 & G33).

  destruct (ghost_at c E1 E' M1 Hc Hag HX) as (rest & x' & Hs & Hx').
  assert (HGK : uv E' GP = x).
  { assert (Rx : 0 <= x < 2 ^ 64) by (destruct Hsx as [(_ & ->)|(_ & [-> | ->])]; lia).
    unfold gh_is in HGh. apply orb_prop in HGh as [HGh|HGh]; pose proof (PB.has_ok E' M' _ _ HK HGh) as Q; cbn [kentry_ok] in Q.
    - fold (uv E' GP) in Q. lia.
    - fold (uv E' (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB GP (ELit x)) (ELit 1))) in Q. apply (SPW.sltu_sub_eq E' GP x); [lia | exact Rx]. }
  assert (Hxx : x' = x) by lia. clear Hx'. subst x'.
  destruct last_stack as (rest0 & x0 & Hs0 & Hx0 & (C & HSC & HCC & HCL)). assert (x0 = x) by (rewrite Hs in Hs0; symmetry; exact (app_last_inj _ _ _ _ Hs0)). subst x0.
  set (ps' := PML.PS stz (PML.ps_sst ps) (PML.ps_nst ps) false (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf (PML.ps_win ps)).
  set (psT := PMCUR.ps_set_more ps' true).
  destruct (FRZ E1 ltac:(destruct HAmb as (_ & _ & X & _); exact X)) as (_ & _ & _ & _ & _ & _ & _ & _ & H38 & H40 & _ & _ & HPE & HCE & _ & _).
  assert (Hden : CH2.den E1 (nth 1 G.BLS []) = PML.ps_blocks ps').
  { rewrite (CH2.blocks_eqb_eq _ _ HBL). unfold CH2.den, BL0, PML.ps_blocks, ps'. cbn [map fst snd PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap].
    fold (uv E1 PE) (uv E1 CE) (uv E1 (EVar 38)) (uv E1 (EVar 40)). rewrite HPE, HCE, H38, H40. reflexivity. }
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf). unfold Cred in HC1. subst cr1.
  unfold CH2.cur in HH1. rewrite Hden in HH1.
  apply (Hcont fx' R' M' model1 (PML.ps_blocks ps' ++ LBo) cr LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
  assert (WT : PML.wf_ps psT).
  {
    destruct HWF as (Wn & n' & W1 & W2 & W3 & W4 & _). cbn [PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap] in *.
    unfold PML.wf_ps, psT, ps'. cbn [PMCUR.ps_set_more PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
    split; [exact W1|]. split; [exact Wn|]. split; [exact W3|]. split; [exact W4|]. exists C, []. rewrite app_nil_r. split; [exact HSC|]. split; [exact HCC|]. intros _.
    split; [exact HCL|]. split; [lia|].
    unfold PML.handled, PML.transient, PML.comment_or_cr, PML.ST_EXPECT_COMMA_OR_END, PML.ST_NUMBER, PML.ST_CR.
    split; [destruct Hsx as [(-> & _)|(-> & _)]; lia|]. split; [left; split; [reflexivity | destruct Hsx as [(-> & _)|(-> & _)]; lia]|].
    split; [intros [Hq|[]]; destruct Hsx as [(-> & ->)|(-> & Hx8)]; [discriminate Hq | destruct Hx0 as [(Hq0 & _)|(_ & Hq1)]; [lia | exact Hq1]]|].
    intros Hq. destruct Hsx as [(-> & _)|(-> & _)]; discriminate Hq. }
  assert (LT : PMCUR.lvl_ok psT).
  { apply (SCU.lvl_ok_rootc psT C); [exact HSC | exact HCC|]. intros Hin _. unfold psT, ps'. cbn [PMCUR.ps_set_more PML.ps_st PML.ps_level] in Hin |- *.
    destruct Hsx as [(-> & ->)|(-> & Hx8)]; [exfalso; unfold PMCUR.ICS in Hin; cbn in Hin; unfold PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin; lia|].
    destruct Hx0 as [(Hq0 & _)|(_ & Hq1)]; [lia | exact Hq1]. }
  exists ps', 0, g.
  split; [split; [exact HPA' | reflexivity]|].
  split; [exact (SCU.wf_c_stop ps' eq_refl WT)|].
  split.
  { unfold PML.win_ok, ps'. cbn [PML.ps_win]. pose proof HWIN as HW. unfold PML.win_ok in HW. destruct (PML.ps_win ps) as [[p e]|]; [|exact I].
    destruct HW as (ch & Hch & C1 & C2 & Hwd). exists ch. split; [exact Hch|]. split; [exact C1|]. split; [exact C2|].
    apply (amb_def 1%nat E1 M' model1 p (e - p) HA' Hwd). right. exists ch. split; [exact Hch | lia]. }
  split.
  { destruct HBB as (HB1 & HB2 & HB3). unfold PML.buf_bound, PML.buf_need, PML.winlen, ps' in *. cbn [PML.ps_buf PML.ps_win PML.ps_more PML.ps_st PML.ps_sst]. rewrite Hlen. fold size0 in HB1.
    replace (stz =? PML.ST_STRING) with false by (destruct Hsx as [(-> & _)|(-> & _)]; reflexivity). cbn [andb]. split; [lia | exact HB2]. }
  split.
  { split; [|split; [exact HdE' | left; reflexivity]].
    pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Hec)) as T. rewrite PB2.uv_lit in T by lia. apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Eb). rewrite GE. lia. }
  split; [intros Hq; exfalso; apply Hq; reflexivity|].
  split; [apply (PB2.ls_ok_keep M M'); [|exact HG | exact HLS]; intros a Ha; apply HST; unfold PB2.ls_foot, PML.IMG_RO_HI in Ha; lia|].
  split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HPC|].
  split; [exact (conj WT LT)|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | apply Nat2Z.inj; exact Hlen]]]]].
  unfold ps'. cbn [PML.ps_st]. fold level. unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END.
  destruct Hsx as [(-> & ->)|(-> & Hx8)]; destruct Hx0 as [(Hq0 & Hl0)|(Hq1 & Hl1)]; try lia.
  - rewrite Hl0. reflexivity.
  - destruct (Z.eqb_spec level 0); [lia | reflexivity].
Qed.

Lemma leaf_dead : forall c k ps1, is_leaf 1 c k ps1 (CC.TOther DEADPC) ->
  PB.has (SR.ps_cells ps1) (sltu0 0) = true -> PB.has (SR.ps_cells ps1) (sltu0 8) = true -> PB.has (SR.ps_cells ps1) (sltu0 14) = true ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 1 c ps1.
Proof.
  intros c k ps1 IL H0 H8 H14 fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _. exfalso.
  assert (Hc : nth_error G.CPS 1 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
  destruct (ghost_at c E1 E' M1 Hc Hag HX) as (rest & x & Hs & Hx).
  destruct last_stack as (rest0 & x0 & Hs0 & Hx0 & _). assert (x0 = x) by (rewrite Hs in Hs0; symmetry; exact (app_last_inj _ _ _ _ Hs0)). subst x0.
  assert (NE : forall cst, PB.has (SR.ps_cells ps1) (sltu0 cst) = true -> 0 <= cst < 2 ^ 64 -> x <> cst).
  { intros cst Hh Hr. pose proof (PB.has_ok E' M' _ _ HK Hh) as Q. unfold sltu0 in Q. cbn [kentry_ok] in Q. rewrite <- Hx. apply SPA.sltu_sub_ne; [|exact Hr]. unfold PB.uv. lia. }
  pose proof (NE 0 H0 ltac:(lia)). pose proof (NE 8 H8 ltac:(lia)). pose proof (NE 14 H14 ltac:(lia)). lia.
Qed.

Lemma leaf_parent : forall c k ps1 j cj ci, is_leaf 0 c k ps1 (CC.TOther PARENT) -> CH2.ret_of G.RETS 0 k = Some j -> nth_error G.CPS j = Some cj -> j = 1%nat -> SR.ps_pc ps1 = PARENT ->
  parent_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS []) = Some ci -> CC.cp_nx cj = (CH2.ci_nx ci + 1 + APC.NCS)%nat ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok 0 c ps1.
Proof.
  intros c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk Hnx. unfold parent_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb HV]. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  assert (Hc : nth_error G.CPS 0 = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  assert (HGP : GP = EVar (CH2.ci_nx ci)).
  { unfold GP. subst j. rewrite (nth_error_nth _ _ G.cp0 Hcj), Hnx. f_equal. unfold APC.NCS. lia. }
  set (nx := (CC.cp_nx cj - APC.NCS - 1)%nat) in *.
  assert (Hnxv : nx = CH2.ci_nx ci) by (unfold nx; rewrite Hnx; lia).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K XI DEF0 CRED_BLK
           PARENT 48 1%nat [] [KRange (EVar nx) 0 255] (Some (EVar nx)) [] 0%nat c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [].
  - intros E' _ w a [].
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    pose proof (leaf_know c ps1 E' R' M1 M' HLF) as HK.
    pose proof NUM as (BR1 & (B0 & B1 & B2 & B3 & B4) & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
    pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). destruct OP as (OP1 & OP2 & OP3).
    pose proof HPA as HPA0. unfold PML.parser_at in HPA0. destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HdefP).
    assert (HdP' : L5.defined M' P 272) by (apply (amb_def 0%nat E1 M' model1 P 272 HA' HdefP); left; lia).
    assert (HLOW : forall a, 0 <= a < hl_ceil L -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { apply (below_frame 0%nat c E' M1 M' Hc HagE'). exact (CC.lf_frame _ _ _ _ _ _ _ HLF). }
    destruct (xi_below 0%nat E1 M1 M' HLOW HX) as (HST & HBY).
    destruct (view_sound _ (ELit 17) E' M' HV HK HagE' HBY HdP') as (buf & HPA' & Hlen).
    destruct (FRZ E' HagE') as (G2 & GP' & GE & _).
    destruct last_stack as (rest & x & Hs & Hx0 & _).
    assert (Ra0 : PML.a0 R' P).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Pb)). fold (uv E' Pb). rewrite GP'. reflexivity. }
    set (psx := PML.PS (uv E' (ELit 17)) (PML.ps_sst ps) (PML.ps_nst ps) false (PML.ps_done ps) level (PML.ps_stack ps) sb scap bcap bptr buf mw) in *.
    apply (PARENT_OK P x (sp + CH2.ci_csp ci) (CC.cp_pc cj) psx rest fx' R' M' model1 K Hmh Hml HKnil HFP).
    { split; [exact Hent|]. split; [exact Ra0|]. split; [exact HPA'|]. unfold psx. cbn [PML.ps_stack PML.ps_sb PML.ps_scap].
      split; [exact Hs|]. split; [unfold PML.obj_on_stack; repeat split; lia|]. split; [lia|]. split; [lia | exact B4]. }
    intros fx2 R2 M2 HFP2 Hpost HRP HFB HGR.
    apply (RET fx2 R2 M2 [Z_to_bv 64 x] eq_refl HFP2 HRP HFB HGR).
    + rewrite Hnxv. cbn [edenot]. pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. rewrite GG. exact Hpost.
    + intros X [<-|[]]. cbn [kentry_ok edenot]. rewrite Hnxv. pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. rewrite GG.
      cbn [nth]. rewrite u64_of_Z by lia. lia.
    + intros _. subst j.
      assert (HLOW2 : forall a, 0 <= a < hl_ceil L -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { destruct Hent as (_ & _ & _ & _ & Hstk'). pose proof (L5C.stk_window _ _ _ _ Hstk') as (SW1 & _).
        intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia). intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold hl_ceil in *. lia. }
      assert (HX' : XI 0%nat E1 M') by (destruct (xi_below 0%nat E1 M1 M' HLOW HX) as (Q1 & Q2); split; [exact Q1 | split; [exact Q2 | intros Q; discriminate Q]]).
      destruct (xi_below 0%nat E1 M' M2 HLOW2 HX') as (Q1 & Q2). split; [exact Q1|]. split; [exact Q2|]. intros _. exists rest, x. split; [exact Hs|].
      rewrite HGP. unfold PB.uv. cbn [edenot]. pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 x] R2 0 ltac:(cbn; lia)) as GG. rewrite Nat.add_0_r in GG. rewrite GG.
      cbn [nth]. apply u64_of_Z. lia.
Qed.

Lemma leaves : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. cbn [leaf_chk] in X.
  destruct (Z.eqb_spec pc PARENT) as [->|N1].
  - apply andb_prop in X as [X XR]. apply andb_prop in X as [Hpc Hi]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hi. subst i.
    destruct (CH2.ret_of G.RETS 0 k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    apply andb_prop in XR as [Hj XC]. apply Nat.eqb_eq in Hj. destruct (parent_chk c ps1 cj (nth 0 G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.eqb_eq in XC.
    exact (leaf_parent c k ps1 j cj ci IL Hret Hcj Hj Hpc Hchk XC).
  - destruct (Z.eqb_spec pc DEADPC) as [->|N2].
    + apply andb_prop in X as [X H14]. apply andb_prop in X as [X H8]. apply andb_prop in X as [Hi H0]. apply Nat.eqb_eq in Hi. subst i. exact (leaf_dead c k ps1 IL H0 H8 H14).
    + apply andb_prop in X as [X XV]. apply andb_prop in X as [X Hec]. apply andb_prop in X as [X HBL]. apply andb_prop in X as [Hi Hbase]. apply Nat.eqb_eq in Hi. subst i.
      apply orb_prop in XV as [XV|XV]; apply andb_prop in XV as [HV HG'].
      * exact (leaf_exit c k ps1 pc 2 0 IL Hbase HBL Hec HV HG' ltac:(left; split; reflexivity)).
      * apply orb_prop in HG' as [HG'|HG'].
        -- exact (leaf_exit c k ps1 pc 7 8 IL Hbase HBL Hec HV HG' ltac:(right; split; [reflexivity | left; reflexivity])).
        -- exact (leaf_exit c k ps1 pc 7 14 IL Hbase HBL Hec HV HG' ltac:(right; split; [reflexivity | right; reflexivity])).
Qed.

Lemma main : srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_AFTER_VALUE M model) K.
Proof.
  unfold PML.cfg. change PML.PC_AFTER_VALUE with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2.cert_sound3 L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS XI) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros i c k ps1 j s IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - intros i c k ps1 j s IL. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. discriminate X.
  - exact leaves.
  - reflexivity.
  - rewrite LS. exact At0.
  - destruct (FRZ E0 (CC.env_agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & _ & _ & H38 & H40 & _ & _ & HPE & HCE & _ & _).
    assert (Hden0 : CH2.den E0 (nth 0 G.BLS []) = PML.ps_blocks ps).
    { change (nth 0 G.BLS []) with BL0. unfold CH2.den, BL0, PML.ps_blocks. cbn [map fst snd]. fold (uv E0 PE) (uv E0 CE) (uv E0 (EVar 38)) (uv E0 (EVar 40)). rewrite HPE, HCE, H38, H40. reflexivity. }
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur; rewrite Hden0; exact HH | reflexivity].
    + split; [intros a _; reflexivity|]. split; [|intros Q; discriminate Q].
      pose proof HPA as H. unfold PML.parser_at, psm in H. cbn [PML.ps_set_win PML.ps_sb PML.ps_stack] in H.
      destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _). exact Hb.
  - exact Hfp.
Qed.
End Main.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PARENT_OK : PMS.parent_spec L.

Theorem after_value_ok : PMS.after_value_spec L HI.
Proof.
  unfold PMS.after_value_spec, PMS.ptrans_stalek, PMS.ptrans_gbk. intros mw LBo cr sp r P V E B kx bx g ps. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Ha1 & Hmore & Hst & (HWF1 & _)) & HPA & (HWF & _) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  assert (HdP : L5.defined M P 272) by (unfold PML.parser_at in HPA; repeat (destruct HPA as [_ HPA]); exact HPA).
  destruct (PB2.cell_exists M (P + 160) 8 ltac:(lia)) as (line0 & Rc1 & Hc1); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M (P + 168) 8 ltac:(lia)) as (pos0 & Rc2 & Hc2); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  exact (main L HI HIok LAY FPM PARENT_OK mw LBo cr sp r P V E B kx bx g ps fx R M model K HH Hmo HKnil Hfp Hentry Ha0 Ha1 Hmore Hst HPA HWF HWF1 HWIN HBB HVIS HEC HLS HG HPC OP OV OE AP1 AP2 AP3
           Hcont line0 pos0 Hc1 Hc2 (conj Rc1 Rc2)).
Qed.
End Final.
End AfterValueProof.

