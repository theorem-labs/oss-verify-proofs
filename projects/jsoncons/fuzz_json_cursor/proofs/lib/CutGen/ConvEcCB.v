(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_conv_ec_cboth_T Cut_conv_ec_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_conv_ec_cboth.
Module GT := Cut_conv_ec_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module SCVA.
Definition PC_ACQ : Z := 863640.
Definition PC_CXA : Z := 436716.
Definition PC_REL : Z := 863720.
Definition RETPC : Z := 729616.
Definition GD : Z := 6882176.
Definition AXT : Z := 7020000.
Definition HND : Z := 986684.
Definition OBJ : Z := 1412176.
Definition DSO : Z := 1401640.
Definition SBz : Z := 2147450880.
Definition EE := EVar 10.
Definition FFS : list (list (expr * Z * Z)) := [[]; []; []; []; []].
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition GREG : list SGP.region := [(ELit 0, GD, ELit 2)].
Definition AXREG : list SGP.region := [(ELit 0, AXT, ELit 544)].
Definition CPF : list SGP.region := [(EVar 2, -1024, ELit 1024); (EE, 0, ELit 16)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition call_chk (pc scr : Z) (wregs : list SGP.region) (a0x : option expr) (i0 j0 : nat) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match CH2.ret_of G.RETS i k with
  | Some j => match nth_error G.CPS j with
              | Some cj => (Z.eqb (SR.ps_pc ps) pc && Nat.eqb i i0 && Nat.eqb j j0 && CBA.regions_eqb (CC.cp_F c) CPF
                            && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                            && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr 0 [] [] wregs STAT a0x c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS [])))%bool
              | None => false end
  | None => false end.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      if Z.eqb pc PC_ACQ then (call_chk PC_ACQ 64 GREG (Some (ELit 1)) 1 2 i c k ps && CL.ps_reg_is ps 10 (ELit GD))%bool
      else if Z.eqb pc PC_CXA then (call_chk PC_CXA 512 AXREG (Some (ELit 0)) 2 3 i c k ps && CL.ps_reg_is ps 10 (ELit HND) && CL.ps_reg_is ps 11 (ELit OBJ) && CL.ps_reg_is ps 12 (ELit DSO))%bool
      else if Z.eqb pc PC_REL then (call_chk PC_REL 64 GREG None 3 4 i c k ps && CL.ps_reg_is ps 10 (ELit GD))%bool
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && (Nat.eqb i 0 || Nat.eqb i 4) && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) && CBA.regions_eqb (CC.cp_F c) CPF
         && CL.ps_reg_is ps 10 EE && has cells (KWord (SA EE 0) 8 (EVar 11)) && has cells (KWord (SA EE 8) 8 (ELit OBJ)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma knc_ok : firstn 14 (CC.cp_know G.cp1) = firstn 14 (CC.cp_know G.cp0) /\ CC.cp_regs G.cp1 = CC.cp_regs G.cp0 /\ CC.cp_pc G.cp1 = CC.cp_pc G.cp0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma guard_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 GD) 2 = true. Proof. vmc_refl. Qed.
Lemma tab_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 AXT) 544 = true. Proof. vmc_refl. Qed.

Lemma writable_static : forall (M : word -> option byte) A (N : nat), StreamSim.wseg_ok RSEGS (Z_to_bv 64 A) N = true -> 0 <= A < 2 ^ 64 -> A + Z.of_nat N <= 2 ^ 64 -> L5.writable RSEGS M A (Z.of_nat N).
Proof.
  intros M A N H HA HN d k Hd Hk. destruct k as [|k]; [reflexivity|].
  apply (store_ok_sub RSEGS M (Z_to_bv 64 A) (Z_to_bv 64 (A + d)) N (Datatypes.S k)); [rewrite u64_of_Z by lia; lia | apply store_ok_wseg; exact H | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; lia].
Qed.

Lemma u64_u32_low : forall segs (M : word -> option byte) a w, L5.u64_at segs M a w -> L5.u32_at segs M a w.
Proof.
  intros segs M a w H. unfold L5.u64_at, L5.u32_at in *.
  assert (EQ : forall x (n : nat), rdn segs M x (Datatypes.S n) = match (match M x with Some b => Some b | None => seg_rom segs x end) with
                 | Some b => match rdn segs M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end) by reflexivity.
  set (x0 := Z_to_bv 64 a) in *.
  rewrite (EQ x0 7%nat) in H. rewrite (EQ x0 3%nat).
  destruct (match M x0 with Some b => Some b | None => seg_rom segs x0 end) as [b0|]; [|discriminate].
  rewrite (EQ (x0 + 1)%bv 6%nat) in H. rewrite (EQ (x0 + 1)%bv 2%nat).
  destruct (match M (x0 + 1)%bv with Some b => Some b | None => seg_rom segs (x0 + 1)%bv end) as [b1|]; [|discriminate].
  rewrite (EQ (x0 + 1 + 1)%bv 5%nat) in H. rewrite (EQ (x0 + 1 + 1)%bv 1%nat).
  destruct (match M (x0 + 1 + 1)%bv with Some b => Some b | None => seg_rom segs (x0 + 1 + 1)%bv end) as [b2|]; [|discriminate].
  rewrite (EQ (x0 + 1 + 1 + 1)%bv 4%nat) in H. rewrite (EQ (x0 + 1 + 1 + 1)%bv 0%nat).
  destruct (match M (x0 + 1 + 1 + 1)%bv with Some b => Some b | None => seg_rom segs (x0 + 1 + 1 + 1)%bv end) as [b3|]; [|discriminate].
  destruct (rdn segs M (x0 + 1 + 1 + 1 + 1)%bv 4) as [rest|]; [|discriminate]. cbn [rdn].
  unfold word_to_le_bytes in *. cbn [Z_to_le_bytes] in *. injection H as H0 H1 H2 H3 _. subst. reflexivity.
Qed.

Lemma atexit_state_ag : forall segs (M M' : word -> option byte) (Sg : Z -> Prop) AX hs,
  (forall a, Sg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall i, AX <= i < AX + 544 -> Sg i) -> 0 <= AX -> AX + 544 <= 2 ^ 64 -> hs <> [] ->
  atexit_state_at segs AX M hs -> atexit_state_at segs AX M' hs.
Proof.
  intros segs M M' Sg AX hs AG HS A0 A1 Hne (T1 & T2 & T3).
  assert (CE : forall a (n : nat) v, AX <= a -> a + Z.of_nat n <= AX + 544 -> cell_is segs M a n v -> cell_is segs M' a n v).
  { intros a n v Ha Hn Hc. apply (PTA.cell_ag segs M M' Sg AG a n v); [|exact Hc]. split; [lia|]. split; [lia|]. intros i Hi. apply HS. lia. }
  split; [apply CE; [lia | cbn; lia | exact T1]|]. split; [apply CE; [lia | cbn; lia | exact T2]|].
  destruct hs as [|h0 hs']; [exfalso; exact (Hne eq_refl)|].
  destruct T3 as (X0 & X1 & X2 & X3 & X4). split; [exact X0|]. split; [apply CE; [lia | cbn; lia | exact X1]|]. split; [apply CE; [lia | cbn; lia | exact X2]|].
  split; [apply CE; [lia | cbn; lia | exact X3]|]. intros i f a Hn. destruct (X4 i f a Hn) as (Y1 & Y2).
  assert (Hi : Z.of_nat i < 32).
  { pose proof (nth_error_Some (h0 :: hs') i) as G0. rewrite Hn in G0. assert ((i < length (h0 :: hs'))%nat) by (apply G0; discriminate). lia. }
  split; [apply CE; [lia | cbn; lia | exact Y1] | apply CE; [lia | cbn; lia | exact Y2]].
Qed.
End SCVA.

Section ConvEcOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis ACQ_OK : PMSA.guard_acquire_specA L ar HI SCVA.PC_ACQ.
Hypothesis REL_OK : PMSA.guard_release_specA L ar HI SCVA.PC_REL.

Variable IL0 : icpt_layout.
Variable ILX : icpt_layout_x.
Variable ANNOTATE : Prop.
Hypothesis ICok : pm_aicpt_ok L ar IL0 ILX SCFG HI ANNOTATE.
Hypothesis CXA_PC : iclx_cxa_atexit ILX = SCVA.PC_CXA.
Hypothesis CXA_SCR : 0 <= iclx_scr_cxa ILX <= 512.
Hypothesis CXA_TAB : iclx_atexit_tab ILX = PMLA.ATEXIT_TAB IC.
Hypothesis CXA_AT : iclx_atcxa ILX = PMLA.ATCXA_HANDLER IC.
Hypothesis CXA_NL : iclx_need_locks ILX = PMLA.NEED_LOCKS IC.

Lemma FFSnil : forall i, nth i SCVA.FFS [] = [].
Proof. intros i. unfold SCVA.FFS. do 6 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma BLSnil : forall i, nth i G.BLS [] = [].
Proof. intros i. do 6 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.

Lemma PTKF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
                   \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
                   \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a.
Proof.
  intros a Ha. pose proof PMTA.C_cboth_wf as [T1 T2 T3 _ T5 T6 T7 T8 _ _ T9]. unfold PMTA.cell_in_foot, PmIcptIfaceA.ATEXIT_TAB_BYTES in *.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]];
    [apply (proj2 (proj2 T5)); exact Ha | apply (proj2 (proj2 T6)); exact Ha | apply (proj2 (proj2 T7)); exact Ha | apply (proj2 (proj2 T8)); exact Ha
    | apply (proj2 (proj2 T1)); exact Ha | subst a; apply (proj2 (proj2 T2)); clear; lia | apply (proj2 (proj2 T3)); exact Ha | apply (proj2 (proj2 T9)); exact Ha].
Qed.
Lemma FOOTRG : forall a, PMLA.in_foot IC a -> 65536 <= a < 7028736.
Proof. intros a (iv & Hiv & Hr). cbn in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hiv. Qed.

Lemma EGof : forall g (M : word -> option byte), g <> PML.LS0 -> PMLA.ls_ok (hl_segs L) IC g M -> PMLA.convcat_guard (hl_segs L) IC M (PML.cbit g).
Proof. intros g M Hg H. destruct g; [exfalso; exact (Hg eq_refl) | | | | |]; exact (proj2 (proj2 (proj2 (proj2 H)))). Qed.

Lemma ls_ok_2 : forall (g : PML.ls_state) (M M' : word -> option byte) (Sg : Z -> Prop),
  (g = PML.LS1 \/ g = PML.J) ->
  (forall a, Sg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> ~ (SCVA.GD <= a < SCVA.GD + 2) -> ~ (SCVA.AXT <= a < SCVA.AXT + 544) -> Sg a) ->
  PMLA.ls_ok (hl_segs L) IC g M ->
  atexit_state_at (hl_segs L) (PMLA.ATEXIT_TAB IC) M' (PMLA.HS0 IC ++ PMLA.ls_atexit IC (PML.regC g)) ->
  L5.u8_at (hl_segs L) M' SCVA.GD 1 -> L5.u8_at (hl_segs L) M' (SCVA.GD + 1) 1 ->
  PMLA.ls_ok (hl_segs L) IC (PML.regC g) M'.
Proof.
  intros g M M' Sg Hg AG HS HL HT HG0 HG1.
  assert (OF : forall a n, 0 < n -> (forall i, a <= i < a + n -> PMLA.in_foot IC i /\ ~ (SCVA.GD <= i < SCVA.GD + 2) /\ ~ (SCVA.AXT <= i < SCVA.AXT + 544)) -> PTA.out Sg a n).
  { intros a n Hn Hi. pose proof (FOOTRG a (proj1 (Hi a ltac:(lia)))) as R0. pose proof (FOOTRG (a + n - 1) (proj1 (Hi (a + n - 1) ltac:(lia)))) as R1.
    split; [clear - R0; lia|]. split; [clear - R1; lia|]. intros i Hii. destruct (Hi i Hii) as (F1 & F2 & F3). exact (HS i (or_intror F1) F2 F3). }
  destruct Hg as [-> | ->]; destruct HL as (IR & ((_ & _ & _) & (Q1 & Q2)) & ((LD1 & LD2 & LD3) & (CG0 & CG1) & _));
  unfold PMLA.ls_ok, PMLA.atexit_ok, PMLA.libc_quiet, PMLA.loc_done, PMLA.errcat_guard, PMLA.convcat_guard, PMLA.img_ro, PMLA.u8, PMLA.u64 in *;
  (split; [|split; [split; [exact HT | split]|split; [split; [|split]|split; [split|split; [exact HG0 | exact HG1]]]]]).
  all: try (apply (PTA.clear_ag M M' Sg AG); [|exact IR]; intros i Hi; apply HS; [left; exact Hi | cbn in Hi; unfold SCVA.GD; clear - Hi; lia | cbn in Hi; unfold SCVA.AXT; clear - Hi; lia]).
  all: try (apply (PTA.cell_ag _ M M' Sg AG); [|exact Q1]; apply OF; [clear; lia|]; intros i Hi; split; [apply PTKF; do 5 right; left; cbn in Hi |- *; clear - Hi; lia | cbn in Hi; unfold SCVA.GD, SCVA.AXT; clear - Hi; lia]).
  all: try (apply (PTA.cell_ag _ M M' Sg AG); [|exact Q2]; apply OF; [clear; lia|]; intros i Hi; split; [apply PTKF; do 6 right; left; cbn in Hi |- *; clear - Hi; lia | cbn in Hi; unfold SCVA.GD, SCVA.AXT; clear - Hi; lia]).
  all: try (apply (PTA.u8_ag _ M M' Sg AG); [|exact LD1]; apply OF; [clear; lia|]; intros i Hi; split; [apply PTKF; left; cbn in Hi |- *; clear - Hi; lia | cbn in Hi; unfold SCVA.GD, SCVA.AXT; clear - Hi; lia]).
  all: try (apply (PTA.u64_ag _ M M' Sg AG); [|exact LD2]; apply OF; [clear; lia|]; intros i Hi; split; [apply PTKF; right; left; cbn in Hi |- *; clear - Hi; lia | cbn in Hi; unfold SCVA.GD, SCVA.AXT; clear - Hi; lia]).
  all: try (apply (PTA.u8_ag _ M M' Sg AG); [|exact LD3]; apply OF; [clear; lia|]; intros i Hi; split; [apply PTKF; right; right; left; cbn in Hi |- *; clear - Hi; lia | cbn in Hi; unfold SCVA.GD, SCVA.AXT; clear - Hi; lia]).
  all: try (apply (PTA.u8_ag _ M M' Sg AG); [|first [exact CG0 | exact CG1]]; apply OF; [clear; lia|]; intros i Hi; split; [apply PTKF; do 3 right; left; cbn in Hi |- *; clear - Hi; lia | cbn in Hi; unfold SCVA.GD, SCVA.AXT; clear - Hi; lia]).
Qed.

Theorem conv_ec_ok : PMCSA.conv_ec_specA L ar HI IC 729476.
Proof.
  intros LB FF LK cr A E code sp r g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hcode & HdefE & OE & Hstksh & HLS & HG) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.SETEC_SCR, PMSA.fobj in *.
  destruct OE as (Efr & E8 & Esh).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF E 16 RFx Efr ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in Q5. change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in Q7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (HGD : PMLA.CONVCAT_GUARD IC = SCVA.GD) by reflexivity. assert (HAXT : PMLA.ATEXIT_TAB IC = SCVA.AXT) by reflexivity.

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 E) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 code) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = E) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = code) by (rewrite V11; apply u64_of_Z; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 1024) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (WW := [(E, 16); (PMLA.CONVCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, PmIcptIfaceA.ATEXIT_TAB_BYTES)]).
  assert (WINC : incl [(E, 16)] WW) by (intros y [<-|[]]; left; reflexivity).
  assert (WOK : forall (w : L5.range) (a : Z), In w [(E, 16)] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ E 16 a RFx Efr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [(E, 16)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (E, 16). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (SHE : forall a, S E <= a < S E + 2 -> in_shadow_of E 16 a).
  { intros a Ha. apply (CL5A.shreg_in_shadow E 2); [exact E8 | clear; lia | unfold S, SB in *; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha; unfold CHA.sclientA.
    rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) E 16 a RFx Efr ltac:(clear; lia) (SHE a ltac:(unfold S, SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (inW := fun a : Z => exists w, In w WW /\ L5.in_rng w a).
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (FOOTCL : forall a, PMLA.in_foot IC a -> 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a).
  { intros a Hf. pose proof (FOOTRG a Hf) as RG. split; [exact RG|]. intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - RG; lia | exact (proj1 (FOOTC2 a Hf))]. }
  set (GX := fun a : Z => SCVA.GD <= a < SCVA.GD + 2 \/ SCVA.AXT <= a < SCVA.AXT + 544).
  assert (GXF : forall a, GX a -> PMLA.in_foot IC a) by (intros a [Ha|Ha]; apply PTKF; [do 7 right; rewrite HGD; exact Ha | do 4 right; left; rewrite HAXT; exact Ha]).
  assert (WCL : forall a, inW a -> 0 <= a /\ a < ahl_ceil ar /\ (a < 2147446784 \/ 17594333495296 <= a) /\ (forall sp' scr', aclient L ar LB FF sp' scr' a)
                             /\ (E <= a < E + 16 \/ GX a)).
  { intros a (w & Hw & Hin). unfold L5.in_rng in Hin. unfold WW in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin.
    - split; [clear - Hin Q3; lia|]. split; [clear - Hin Q4; lia|]. split; [unfold hid in Q5; clear - Hin Q5; lia|].
      split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' E 16 a Efr Hin)) | left; exact Hin].
    - assert (HX : GX a) by (left; rewrite HGD in Hin; cbn in Hin; exact Hin). destruct (FOOTCL a (GXF a HX)) as (RG & CLa).
      split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | right; exact HX].
    - assert (HX : GX a) by (right; rewrite HAXT in Hin; cbn in Hin; unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; exact Hin). destruct (FOOTCL a (GXF a HX)) as (RG & CLa).
      split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | right; exact HX]. }

  assert (DECW : forall a, a < 7028736 -> GX a \/ L5.outside WW a).
  { intros a Ha. destruct (Z_le_dec SCVA.GD a) as [G1|G1]; [destruct (Z_lt_dec a (SCVA.GD + 2)) as [G2|G2]|].
    - left. left. clear - G1 G2. lia.
    - destruct (Z_le_dec SCVA.AXT a) as [G3|G3]; [destruct (Z_lt_dec a (SCVA.AXT + 544)) as [G4|G4]|].
      + left. right. clear - G3 G4. lia.
      + right. intros w Hw Hin. unfold WW in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
        destruct Hw as [<-|[<-|[<-|[]]]]; cbn in Hin; [clear - Hin Ha Q1 FSLO; lia | unfold SCVA.GD in *; clear - Hin G2; lia | unfold SCVA.AXT, PmIcptIfaceA.ATEXIT_TAB_BYTES in *; clear - Hin G4; lia].
      + right. intros w Hw Hin. unfold WW in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
        destruct Hw as [<-|[<-|[<-|[]]]]; cbn in Hin; [clear - Hin Ha Q1 FSLO; lia | unfold SCVA.GD in *; clear - Hin G2; lia | unfold SCVA.AXT, PmIcptIfaceA.ATEXIT_TAB_BYTES in *; clear - Hin G3; lia].
    - right. intros w Hw Hin. unfold WW in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
      destruct Hw as [<-|[<-|[<-|[]]]]; cbn in Hin; [clear - Hin Ha Q1 FSLO; lia | unfold SCVA.GD in *; clear - Hin G1; lia | unfold SCVA.AXT, SCVA.GD, PmIcptIfaceA.ATEXIT_TAB_BYTES in *; clear - Hin G1; lia]. }

  assert (KFT : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> ~ (SCVA.GD <= a < SCVA.GD + 2) -> ~ (SCVA.AXT <= a < SCVA.AXT + 544) ->
                 0 <= a < 2 ^ 63 /\ CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha N1 N2.
    assert (RG : 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a).
    { destruct Ha as [Ha|Ha]; [|exact (FOOTCL a Ha)]. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha. split; [clear - Ha; lia|].
      intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia]. }
    destruct RG as (RG & CLa). split; [clear - RG; lia|]. split; [clear - RG; lia|]. split; [exact (CLa _ _)|].
    destruct (DECW a (proj2 RG)) as [[X|X]|Ho]; [exfalso; exact (N1 X) | exfalso; exact (N2 X) | exact Ho]. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (AGX := fun (M1 : word -> option byte) => forall a, GX a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  set (AGT := fun (M1 : word -> option byte) => forall a, SCVA.AXT <= a < SCVA.AXT + 544 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  set (TAB2 := fun (M1 : word -> option byte) => atexit_state_at (hl_segs L) (PMLA.ATEXIT_TAB IC) M1 (PMLA.HS0 IC ++ PMLA.ls_atexit IC (PML.regC g))).
  set (GRD1 := fun (M1 : word -> option byte) => L5.u8_at (hl_segs L) M1 SCVA.GD 1 /\ L5.u8_at (hl_segs L) M1 (SCVA.GD + 1) 1).
  set (XI := fun (i : nat) (_ : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) =>
               (i = 0%nat -> PML.cbit g = 1 /\ AGX M1) /\ (i <> 0%nat -> g = PML.LS1 \/ g = PML.J) /\ (i = 1%nat -> AGX M1) /\ (i = 2%nat -> AGT M1) /\ (i = 3%nat -> TAB2 M1) /\ (i = 4%nat -> TAB2 M1 /\ GRD1 M1)).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg IL. pose proof (CH2.leaves_all_sound _ _ _ SCVA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.

  assert (HI0 : exists i0 : nat, (i0 = 0%nat /\ PML.cbit g = 1) \/ (i0 = 1%nat /\ (g = PML.LS1 \/ g = PML.J))).
  { destruct g; [exfalso; exact (HG eq_refl) | exists 1%nat; right; split; [reflexivity | left; reflexivity] | exists 1%nat; right; split; [reflexivity | right; reflexivity]
                | exists 0%nat; left; split; reflexivity | exists 0%nat; left; split; reflexivity | exists 0%nat; left; split; reflexivity]. }
  destruct HI0 as (i0 & Hi0).
  assert (Hc0 : nth_error G.CPS i0 = Some (nth i0 G.CPS G.cp0) /\ CC.cp_pc (nth i0 G.CPS G.cp0) = 729476) by (destruct Hi0 as [(-> & _)|(-> & _)]; split; reflexivity).
  destruct Hc0 as (Hc0 & HPC0). rewrite <- HPC0.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [(E, 16)] G.BLS SCVA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact SCVA.heap_ok.
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ SCVA.leaf_ok _ _ _ _ _ IL) as X. unfold SCVA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW [(E, 16)] G.BLS SCVA.FFS Cred 0 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.

    assert (CALLDEC : forall pc0 scr wregs a0x i1 j1, SCVA.call_chk pc0 scr wregs a0x i1 j1 i c kk ps0 = true ->
              exists j cj ci, CH2.ret_of G.RETS i kk = Some j /\ nth_error G.CPS j = Some cj /\ SR.ps_pc ps0 = pc0 /\ i = i1 /\ j = j1 /\ CC.cp_F c = SCVA.CPF
                /\ CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i SCVA.FFS []) = true
                /\ CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr 0 [] [] wregs SCVA.STAT a0x c ps0 cj (nth i G.BLS []) (nth i SCVA.FFS []) (nth j G.BLS []) (nth j SCVA.FFS []) = Some ci).
    { intros pc0 scr wregs a0x i1 j1 HC. unfold SCVA.call_chk in HC.
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in HC as [HC Y5]. apply andb_prop in HC as [HC Y4]. apply andb_prop in HC as [HC YF]. apply andb_prop in HC as [HC Y2]. apply andb_prop in HC as [Y0 Y1].
      apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y5 with SCVA.isSome ?t = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      exists j, cj, ci. repeat split; assumption. }

    assert (LEAFK : forall E1 A1 M1 m1 E' R' M' m', CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SCVA.FFS Cred 0 i E1 A1 M1 m1 ->
              env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> nth_error G.CPS i = Some c -> CC.cp_F c = SCVA.CPF ->
              bv_unsigned (ev E' 2) = sp /\ bv_unsigned (ev E' 10) = E /\ bv_unsigned (ev E' 11) = code
              /\ (forall a, 0 <= a < 7028736 -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
              /\ (forall X0, SCVA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
              /\ (forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)).
    { intros E1 A1 M1 m1 E' R' M' m' HA Hag HLF Hc YF.
      pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SCVA.FFS Cred 0 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hc) Hag) as HagE'.
      assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
      assert (W10 : bv_unsigned (ev E' 10) = E) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
      assert (W11 : bv_unsigned (ev E' 11) = code) by (rewrite <- (proj1 HagE' 11%nat) by (apply Nat.ltb_lt; reflexivity); exact U11).
      split; [exact W2|]. split; [exact W10|]. split; [exact W11|]. split; [|split].
      - intros a Ha. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside. rewrite L5.unsigned_lit by (clear - Ha; lia).
        unfold SCVA.CPF. repeat (apply Forall_cons); [.. | apply Forall_nil]; unfold SCVA.EE; cbn [fst snd]; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; rewrite ?W2, ?W10;
          rewrite u64_of_Z by (clear; lia); clear - Ha S2 CL Q1 FSLO; lia.
      - intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0).
      - intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
    assert (OUTG0 : PTA.out GX SCVA.GD 1) by (split; [unfold SCVA.GD; clear; lia|]; split; [unfold SCVA.GD; clear; lia|]; intros y Hy; left; clear - Hy; lia).
    assert (OUTG1 : PTA.out GX (SCVA.GD + 1) 1) by (split; [unfold SCVA.GD; clear; lia|]; split; [unfold SCVA.GD; clear; lia|]; intros y Hy; left; clear - Hy; lia).
    assert (CSTAT : PMSA.cstatic L (PMLA.CONVCAT_GUARD IC) 2).
    { intros x Hx. rewrite HGD in Hx. rewrite ILO, IHI. split; [unfold SCVA.GD in Hx; clear - Hx; lia | exact (FOOTC2 x (GXF x (or_introl Hx)))]. }
    assert (AXCL : forall a sp' scr', SCVA.AXT <= a < SCVA.AXT + 544 -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp' scr' a /\ L5.outside [(PMLA.CONVCAT_GUARD IC, 2)] a).
    { intros a sp' scr' Ha. destruct (FOOTCL a (GXF a (or_intror Ha))) as (RG & CLa). split; [clear - RG; lia|]. split; [exact (CLa _ _)|].
      intros w [<-|[]]. unfold L5.in_rng. rewrite HGD. cbn [fst snd]. unfold SCVA.AXT, SCVA.GD in *. clear - Ha. lia. }
    destruct (Z.eqb_spec pc SCVA.PC_ACQ) as [->|Hne1].
    {
      apply andb_prop in X as [X Y10]. destruct (CALLDEC _ _ _ _ _ _ X) as (j & cj & ci & Hret & Hcj & Y0 & Hi & Hj & YF & Yfoot & Hchk). clear X. subst i j.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HX].
      destruct HX as (_ & HgL & HX1 & _). specialize (HgL ltac:(discriminate)). specialize (HX1 eq_refl).
      assert (Hc : nth_error G.CPS 1 = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
      destruct (LEAFK E1 A1 M1 m1 E' R' M' m' HA Hag HLF Hc YF) as (W2 & W10 & W11 & LOWF & CELL & REG).
      assert (HcB : CHA.curB LB G.BLS 1 E1 = LB) by reflexivity. assert (HcF : CHA.curF FF sp SCVA.FFS 1 E1 = FF) by reflexivity.
      refine (CALLEE SCVA.PC_ACQ 64 0%nat [] SCVA.GREG SCVA.STAT (Some (ELit 1)) 0 1%nat c ps0 2%nat cj ci Hcj Hchk Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [reflexivity | cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
      assert (AGX' : forall a, GX a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. pose proof (FOOTRG a (GXF a Ha)) as RG. rewrite (LOWF a ltac:(clear - RG; lia)). exact (HX1 a Ha). }
      pose proof (EGof g M HG HLS) as HLS1. assert (J0 : PML.cbit g = 0) by (destruct HgL as [-> | ->]; reflexivity). rewrite J0 in HLS1.
      destruct HLS1 as (EG0 & EG1). unfold PMLA.u8 in EG0, EG1. rewrite HGD in EG0, EG1.
      eexists. eexists. split; [exact (ACQ_OK LB FF LK1 cr A1 (PMLA.CONVCAT_GUARD IC) (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
      {
        unfold PMSA.a0, PMSA.u8. rewrite HGD.
        split; [exact (REG 10%nat _ _ Y10 ltac:(cbn [edenot]; rewrite L5.unsigned_lit by (unfold SCVA.GD; clear; lia); reflexivity))|].
        split; [unfold SCVA.GD; clear; lia|].
        split; [exact (PTA.u8_ag _ M M' GX AGX' _ _ OUTG0 EG0)|]. split; [exact (PTA.u8_ag _ M M' GX AGX' _ _ OUTG1 EG1)|].
        split; [rewrite <- HGD; exact CSTAT|].
        rewrite LS. exact (SCVA.writable_static _ SCVA.GD 2 SCVA.guard_wr ltac:(unfold SCVA.GD; clear; lia) ltac:(unfold SCVA.GD; clear; lia)). }
      {
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hg0 & Hg2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta.
        split; [unfold PMSA.a0 in Ha0'; cbn [edenot]; exact Ha0'|].
        split; [cbn [CH2.den map app]; apply incl_refl|].
        split.
        { intros w a [<-|[]] Hin. exists (ELit 0, SCVA.GD, ELit 2). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, CL5A.uv. cbn [a_base a_off edenot fst snd].
          rewrite !L5.unsigned_lit by (unfold SCVA.GD; clear; lia). unfold L5.in_rng in Hin. rewrite HGD in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
        split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko _ (or_intror (or_introl eq_refl)) Hin)|].
        split; [exact HH2|]. split; [reflexivity|].
        split.
        { unfold XI. split; [intros X0; discriminate X0|]. split; [intros _; exact HgL|]. split; [intros X0; discriminate X0|]. split; [|split; intros X0; discriminate X0].
          intros _ a Ha. rewrite <- (AGX' a (or_intror Ha)). apply (proj1 HP). exact (AXCL a _ _ Ha). }
        intros X0 HX0 _. unfold SCVA.STAT in HX0. cbn [In] in HX0.
        destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ _ _ HH2); reflexivity). } }
    destruct (Z.eqb_spec pc SCVA.PC_CXA) as [->|Hne2].
    {
      apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10].
      destruct (CALLDEC _ _ _ _ _ _ X) as (j & cj & ci & Hret & Hcj & Y0 & Hi & Hj & YF & Yfoot & Hchk). clear X. subst i j.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HX].
      destruct HX as (_ & HgL & _ & HX2 & _). specialize (HgL ltac:(discriminate)). specialize (HX2 eq_refl).
      assert (Hc : nth_error G.CPS 2 = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
      destruct (LEAFK E1 A1 M1 m1 E' R' M' m' HA Hag HLF Hc YF) as (W2 & W10 & W11 & LOWF & CELL & REG).
      assert (HcB : CHA.curB LB G.BLS 2 E1 = LB) by reflexivity. assert (HcF : CHA.curF FF sp SCVA.FFS 2 E1 = FF) by reflexivity.
      refine (CALLEE SCVA.PC_CXA 512 0%nat [] SCVA.AXREG SCVA.STAT (Some (ELit 0)) 0 2%nat c ps0 3%nat cj ci Hcj Hchk Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [reflexivity | cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
      assert (AGT' : forall a, SCVA.AXT <= a < SCVA.AXT + 544 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. rewrite (LOWF a ltac:(unfold SCVA.AXT in Ha; clear - Ha; lia)). exact (HX2 a Ha). }
      pose proof HLS as HLS1. unfold PMSA.ls_ok in HLS1. destruct HLS1 as (_ & (HAT & HQ1 & HQ2) & _). rewrite HAXT in HAT.
      assert (OUTNL : PTA.out (CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW) (PMLA.NEED_LOCKS IC) (Z.of_nat 1)).
      { split; [cbn; clear; lia|]. split; [cbn; clear; lia|]. intros y Hy. apply (proj2 (KFT y (or_intror (PTKF y ltac:(do 5 right; left; cbn in Hy |- *; clear - Hy; lia))) ltac:(cbn in Hy; unfold SCVA.GD; clear - Hy; lia) ltac:(cbn in Hy; unfold SCVA.AXT; clear - Hy; lia))). }
      rewrite <- CXA_PC.
      eexists. eexists. split; [exact (CRC.cxa_atexit_cps' L ar HI IL0 ILX ANNOTATE ICok PMSA.fp_ok 512 LB FF LK1 cr A1 (PMLA.ATEXIT_HANDLER IC) (PMLA.OBJ_CONV_CATEGORY IC) SCVA.DSO (PMLA.HS0 IC ++ PMLA.ls_atexit IC g)
                                       (sp + CH2.ci_csp ci) (CC.cp_pc cj) CXA_SCR)|]. split.
      {
        unfold CRC.cxa_pre'. rewrite CXA_TAB, CXA_NL, HAXT.
        split; [exact (REG 10%nat _ _ Y10 ltac:(cbn [edenot]; rewrite L5.unsigned_lit by (unfold SCVA.HND; clear; lia); reflexivity))|].
        split; [exact (REG 11%nat _ _ Y11 ltac:(cbn [edenot]; rewrite L5.unsigned_lit by (unfold SCVA.OBJ; clear; lia); reflexivity))|].
        split; [exact (REG 12%nat _ _ Y12 ltac:(cbn [edenot]; rewrite L5.unsigned_lit by (unfold SCVA.DSO; clear; lia); reflexivity))|].
        split; [cbn; clear; lia|]. split; [cbn; clear; lia|].
        split; [apply (SCVA.atexit_state_ag _ M M' (fun a => SCVA.AXT <= a < SCVA.AXT + 544) SCVA.AXT _ AGT'); [intros y Hy; exact Hy | unfold SCVA.AXT; clear; lia | unfold SCVA.AXT; clear; lia | cbn; discriminate | exact HAT]|].
        split; [destruct HgL as [-> | ->]; cbn; clear; lia|]. split; [destruct HgL as [-> | ->]; cbn; discriminate|].
        split; [exact (PTA.cell_ag _ M M' _ Hfr1 _ _ _ OUTNL HQ1)|].
        rewrite LS. exact (SCVA.writable_static _ SCVA.AXT 544 SCVA.tab_wr ltac:(unfold SCVA.AXT; clear; lia) ltac:(unfold SCVA.AXT; clear; lia)). }
      {
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Htab & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta.
        split; [cbn [edenot]; exact Ha0'|].
        split; [cbn [CH2.den map app]; apply incl_refl|].
        rewrite CXA_TAB, HAXT.
        split.
        { intros w a [<-|[]] Hin. exists (ELit 0, SCVA.AXT, ELit 544). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, CL5A.uv. cbn [a_base a_off edenot fst snd].
          rewrite !L5.unsigned_lit by (unfold SCVA.AXT; clear; lia). unfold L5.in_rng, PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
        split; [intros w a [<-|[]] Hin (_ & _ & Ko); apply (Ko (PMLA.ATEXIT_TAB IC, PmIcptIfaceA.ATEXIT_TAB_BYTES) (or_intror (or_intror (or_introl eq_refl)))); rewrite HAXT; exact Hin|].
        split; [exact HH2|]. split; [reflexivity|].
        split.
        { unfold XI. split; [intros X0; discriminate X0|]. split; [intros _; exact HgL|]. split; [intros X0; discriminate X0|]. split; [intros X0; discriminate X0|]. split; [|intros X0; discriminate X0].
          intros _. unfold TAB2. rewrite CXA_TAB, CXA_AT in Htab.
          replace (PMLA.HS0 IC ++ PMLA.ls_atexit IC (PML.regC g)) with ((PMLA.HS0 IC ++ PMLA.ls_atexit IC g) ++ [(PMLA.ATEXIT_HANDLER IC, PMLA.OBJ_CONV_CATEGORY IC); (PMLA.ATCXA_HANDLER IC, 0)]);
            [exact Htab | rewrite <- app_assoc; f_equal; destruct HgL as [-> | ->]; reflexivity]. }
        intros X0 HX0 _. unfold SCVA.STAT in HX0. cbn [In] in HX0.
        destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ _ _ HH2); reflexivity). } }
    destruct (Z.eqb_spec pc SCVA.PC_REL) as [->|Hne3].
    {
      apply andb_prop in X as [X Y10]. destruct (CALLDEC _ _ _ _ _ _ X) as (j & cj & ci & Hret & Hcj & Y0 & Hi & Hj & YF & Yfoot & Hchk). clear X. subst i j.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HX].
      destruct HX as (_ & HgL & _ & _ & HX3 & _). specialize (HgL ltac:(discriminate)). specialize (HX3 eq_refl).
      assert (Hc : nth_error G.CPS 3 = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
      destruct (LEAFK E1 A1 M1 m1 E' R' M' m' HA Hag HLF Hc YF) as (W2 & W10 & W11 & LOWF & CELL & REG).
      assert (HcB : CHA.curB LB G.BLS 3 E1 = LB) by reflexivity. assert (HcF : CHA.curF FF sp SCVA.FFS 3 E1 = FF) by reflexivity.
      refine (CALLEE SCVA.PC_REL 64 0%nat [] SCVA.GREG SCVA.STAT None 0 3%nat c ps0 4%nat cj ci Hcj Hchk Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [reflexivity | cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
      eexists. eexists. split; [exact (REL_OK LB FF LK1 cr A1 (PMLA.CONVCAT_GUARD IC) (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
      {
        unfold PMSA.a0. rewrite HGD.
        split; [exact (REG 10%nat _ _ Y10 ltac:(cbn [edenot]; rewrite L5.unsigned_lit by (unfold SCVA.GD; clear; lia); reflexivity))|].
        split; [unfold SCVA.GD; clear; lia|].
        split; [rewrite <- HGD; exact CSTAT|].
        rewrite LS. exact (SCVA.writable_static _ SCVA.GD 2 SCVA.guard_wr ltac:(unfold SCVA.GD; clear; lia) ltac:(unfold SCVA.GD; clear; lia)). }
      {
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Hg1 & Hg1' & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        split; [cbn [CH2.den map app]; apply incl_refl|].
        split.
        { intros w a [<-|[]] Hin. exists (ELit 0, SCVA.GD, ELit 2). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, CL5A.uv. cbn [a_base a_off edenot fst snd].
          rewrite !L5.unsigned_lit by (unfold SCVA.GD; clear; lia). unfold L5.in_rng in Hin. rewrite HGD in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
        split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko _ (or_intror (or_introl eq_refl)) Hin)|].
        split; [exact HH2|]. split; [reflexivity|].
        split.
        { unfold XI. split; [intros X0; discriminate X0|]. split; [intros _; exact HgL|]. split; [intros X0; discriminate X0|]. split; [intros X0; discriminate X0|]. split; [intros X0; discriminate X0|].
          intros _. split.
          - unfold TAB2 in HX3 |- *. rewrite HAXT in HX3 |- *.
            apply (SCVA.atexit_state_ag _ M' M2 (fun a => SCVA.AXT <= a < SCVA.AXT + 544) SCVA.AXT _ (fun a Ha => proj1 HP a (AXCL a _ _ Ha)));
              [intros y Hy; exact Hy | unfold SCVA.AXT; clear; lia | unfold SCVA.AXT; clear; lia | cbn; discriminate |].
            apply (SCVA.atexit_state_ag _ M1 M' (fun a => SCVA.AXT <= a < SCVA.AXT + 544) SCVA.AXT _ (fun a Ha => LOWF a ltac:(unfold SCVA.AXT in Ha; clear - Ha; lia)));
              [intros y Hy; exact Hy | unfold SCVA.AXT; clear; lia | unfold SCVA.AXT; clear; lia | cbn; discriminate | exact HX3].
          - unfold GRD1. unfold PMSA.u8 in Hg1, Hg1'. rewrite HGD in Hg1, Hg1'. split; [exact Hg1 | exact Hg1']. }
        intros X0 HX0 _. unfold SCVA.STAT in HX0. cbn [In] in HX0.
        destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ _ _ HH2); reflexivity). } }

    apply andb_prop in X as [X Yc8]. apply andb_prop in X as [X Yc0]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Yfoot]. apply andb_prop in X as [Xbase Yi].
    apply CBA.regions_eqb_eq in YF.
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HX].
    assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
    destruct (LEAFK E1 A1 M1 m1 E' R' M' m' HA Hag HLF Hc YF) as (W2 & W10 & W11 & LOWF & CELL & REG).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [(E, 16)] G.BLS SCVA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok SCVA.RETPC i c ps0 _ Xbase Yfoot (FFSnil i) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact SCVA.ret_at |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB G.BLS i E1 = LB) by (unfold CHA.curB; rewrite BLSnil; reflexivity). rewrite HB in HH1.
    pose proof HP as (HP1 & HP2 & HP3).
    pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SCVA.FFS Cred 0 i E1 A1 M' m' HA') as Hoff.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [|split; [|split; [|repeat split; reflexivity]]].
    +
      pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (E + 0) (CELL _ Yc0) ltac:(unfold estart, SCVA.EE; cbn [a_base a_off edenot]; rewrite W10; reflexivity)) as EC0.
      apply (CL5A.u64_full (hl_segs L) _ Hoff) in EC0. unfold CL5A.uv in EC0. cbn [edenot] in EC0. rewrite W11, Z.add_0_r in EC0.
      pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (E + 8) (CELL _ Yc8) ltac:(unfold estart, SCVA.EE; cbn [a_base a_off edenot]; rewrite W10; reflexivity)) as EC8.
      apply (CL5A.u64_full (hl_segs L) _ Hoff) in EC8. unfold CL5A.uv in EC8. cbn [edenot] in EC8. rewrite L5.unsigned_lit in EC8 by (unfold SCVA.OBJ; clear; lia).
      unfold PMCSA.ec_conv_atA, PMLA.u32, PMLA.u64. split; [exact (SCVA.u64_u32_low _ _ _ _ EC0)|]. split; [|exact EC8].
      intros k Hk. apply (HP3 (E + k)); [clear - Hk Q3 Q6; lia | | exact (HdefE k Hk)].
      exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp _ E 16 (E + k) Efr ltac:(clear - Hk; lia))).
    +
      destruct HX as (HX0 & HgL & _ & _ & _ & HX4).
      assert (DECGX : forall a, GX a \/ (~ (SCVA.GD <= a < SCVA.GD + 2) /\ ~ (SCVA.AXT <= a < SCVA.AXT + 544))).
      { intros a. unfold GX. destruct (Z_le_dec SCVA.GD a) as [D1|D1]; destruct (Z_lt_dec a (SCVA.GD + 2)) as [D2|D2]; destruct (Z_le_dec SCVA.AXT a) as [D3|D3]; destruct (Z_lt_dec a (SCVA.AXT + 544)) as [D4|D4]; clear - D1 D2 D3 D4; lia. }
      apply orb_prop in Yi. destruct Yi as [Yi|Yi]; apply Nat.eqb_eq in Yi; subst i.
      *
        destruct (HX0 eq_refl) as (Hg2 & AGX1).
        set (Sg := fun a => CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a \/ GX a).
        assert (AG : forall a, Sg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a [Ha|Ha]; [exact (HP1 a Ha)|]. pose proof (FOOTRG a (GXF a Ha)) as RG. rewrite (LOWF a ltac:(clear - RG; lia)). exact (AGX1 a Ha). }
        assert (RJ : PML.regC g = g) by (destruct g; try discriminate Hg2; reflexivity).
        unfold PMSA.ls_ok. rewrite RJ. apply (PTA.ls_ok_ag (hl_segs L) IC M M' Sg AG g HG); [| exact PTKF | exact HLS].
        intros a Ha. destruct (DECGX a) as [D|(D1 & D2)].
        -- split; [|right; exact D]. pose proof (FOOTRG a (GXF a D)) as RG. clear - RG. lia.
        -- destruct (KFT a Ha D1 D2) as (R0 & K0). split; [exact R0 | left; exact K0].
      *
        specialize (HgL ltac:(discriminate)). destruct (HX4 eq_refl) as (HT1 & HG1 & HG1').
        assert (OUTL : forall a, 0 <= a -> a + 1 <= 7028736 -> PTA.out (fun y => 0 <= y < 7028736) a 1) by (intros a Ba0 Ba1; split; [exact Ba0|]; split; [clear - Ba1; lia|]; intros y Hy; clear - Hy Ba0 Ba1; lia).
        unfold PMSA.ls_ok. apply (ls_ok_2 g M M' (fun a => CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a) HgL HP1).
        -- intros a Ha N1 N2. exact (proj2 (KFT a Ha N1 N2)).
        -- exact HLS.
        -- unfold TAB2 in HT1. rewrite HAXT in HT1 |- *.
           apply (SCVA.atexit_state_ag _ M1 M' (fun a => SCVA.AXT <= a < SCVA.AXT + 544) SCVA.AXT _ (fun a Ha => LOWF a ltac:(unfold SCVA.AXT in Ha; clear - Ha; lia)));
             [intros y Hy; exact Hy | unfold SCVA.AXT; clear; lia | unfold SCVA.AXT; clear; lia | destruct HgL as [-> | ->]; cbn; discriminate | exact HT1].
        -- exact (PTA.u8_ag _ M1 M' _ LOWF _ _ (OUTL SCVA.GD ltac:(unfold SCVA.GD; clear; lia) ltac:(unfold SCVA.GD; clear; lia)) HG1).
        -- exact (PTA.u8_ag _ M1 M' _ LOWF _ _ (OUTL (SCVA.GD + 1) ltac:(unfold SCVA.GD; clear; lia) ltac:(unfold SCVA.GD; clear; lia)) HG1').
    +
      unfold PMSA.a0. exact (REG 10%nat _ _ Y10 ltac:(cbn [edenot]; exact W10)).
  - exact Hc0.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VE : CL5A.visr (ahid A model) E 16).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 E 16 (E + k) RFx Efr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSE : forall j, 0 <= j < 2 -> ahid A model (Z_to_bv 64 (S E + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 E 16 (S E + j) RFx Efr ltac:(clear; lia) (SHE (S E + j) ltac:(clear - Hj; lia))) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 1024) 1024).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    assert (VG : CL5A.visr (ahid A model) SCVA.GD 2).
    { intros k Hk. assert (HXk : GX (SCVA.GD + k)) by (left; clear - Hk; lia). destruct (FOOTCL (SCVA.GD + k) (GXF _ HXk)) as (RG & CLa). apply CLV; [clear - RG; lia | exact (CLa _ _) |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - RG. lia. }
    set (Mv := CCA.vis A model M).
    assert (DE : L5.defined Mv E 16) by (apply (CL5A.defined_vis _ M E 16 VE); exact HdefE).
    assert (DS : L5.defined Mv (sp - 1024) 1024) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) (firstn 14 (CC.cp_know G.cp0))).
    { cbn [firstn CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + eapply CL5.kunk_intro with (A := E) (N := 16); [ev_start | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DE].
      + eapply CL5.kwr_intro with (A := E) (N := 16); [ev_start | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DE].
      + eapply CL5.krange_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO CL SP1 S2 S3; lia].
      + eapply CL5.kalign_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | exact E8].
      + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 2 E); [exact U10 | clear; lia | clear - Q3 Q6; lia |].
        intros j Hj. apply CL5A.byte_vis; [exact (VSE j Hj) | exact (Esh j Hj)].
      + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := E) (N2 := 16); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in Q5; clear - Q5; lia].
      + eapply CL5.krange_intro with (v := code); [lin_eval; rw_atoms; clear; lia | clear - Hcode; lia | clear - Hcode; lia].
      + eapply CL5.kunk_intro with (A := sp - 1024) (N := 1024); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.kwr_intro with (A := sp - 1024) (N := 1024); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
      + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
      + eapply CL5.kdisj_intro with (A1 := sp - 1024) (N1 := 1024) (A2 := E) (N2 := 16); [ev_start | reflexivity | ev_start | reflexivity | clear - Q4 S2; lia]. }
    destruct SCVA.knc_ok as (KN1 & KR1 & KP1).
    assert (GB : forall b, 0 <= b < 2 -> PMLA.convcat_guard (hl_segs L) IC M b -> kentry_ok (hl_segs L) E0 Mv (KWord (SA (ELit 0) SCVA.GD) 1 (ELit b)) ).
    { intros b Hb (EG0 & _). unfold PMLA.u8 in EG0. rewrite HGD in EG0.
      eapply CL5A.kword8_intro with (A := SCVA.GD) (z := b); [ev_start | unfold SCVA.GD; clear; lia | unfold SCVA.GD; clear; lia | reflexivity | clear - Hb; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [unfold SCVA.GD; clear; lia | unfold SCVA.GD; clear; lia | exact (CL5A.visr_sub _ SCVA.GD 2 SCVA.GD 1 VG ltac:(clear; lia) ltac:(clear; lia)) | exact EG0]. }
    destruct Hi0 as [(-> & Hg)|(-> & Hg)].
    + change (nth 0%nat G.CPS G.cp0) with G.cp0. split; [exact (regs_ok_id R _ _)|]. unfold know_ok. rewrite <- (firstn_skipn 14 (CC.cp_know G.cp0)). apply Forall_app. split; [exact COMMON|].
      cbn [skipn CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      apply GB; [clear; lia|]. pose proof (EGof g M HG HLS) as HLS2. rewrite Hg in HLS2. exact HLS2.
    + change (nth 1%nat G.CPS G.cp0) with G.cp1. split; [rewrite KR1; exact (regs_ok_id R _ _)|]. unfold know_ok. rewrite <- (firstn_skipn 14 (CC.cp_know G.cp1)), KN1. apply Forall_app. split; [exact COMMON|].
      cbn [skipn CC.cp_know G.cp1]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      apply GB; [clear; lia|]. pose proof (EGof g M HG HLS) as HLS2. assert (J0 : PML.cbit g = 0) by (destruct Hg as [-> | ->]; reflexivity). rewrite J0 in HLS2. exact HLS2.
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite FFSnil, BLSnil. cbn [CH2.den map app CHA.denF length Z.of_nat Z.sub].
      split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + unfold XI. destruct Hi0 as [(-> & Hg)|(-> & Hg)].
      * split; [intros _; split; [exact Hg | intros a _; reflexivity]|]. split; [intros X0; exfalso; apply X0; reflexivity|].
        split; [intros X0; discriminate X0|]. split; [intros X0; discriminate X0|]. split; intros X0; discriminate X0.
      * split; [intros X0; discriminate X0|]. split; [intros _; exact Hg|]. split; [intros _ a _; reflexivity|].
        split; [intros X0; discriminate X0|]. split; intros X0; discriminate X0.
  - exact Hfp.
Qed.
End ConvEcOk.

