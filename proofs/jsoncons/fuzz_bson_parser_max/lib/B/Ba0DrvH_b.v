(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvA_b
  Ba0DrvHRead_b Ba0DrvStdio_b Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvLibL_b Ba0DrvLibInit_b Ba0DrvE_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanSoundK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MainPhaseA_b Ba0DrvMain_b Ba0DiagArmRefuse_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ShapeLaws AgentLib Spec BigintSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX_0. Context {fx : PropExec.FPState}.
(* [comment removed for export] *)
Definition rHR := Eval vm_compute in runA scr0 (SS 0xa7b58 srC0 [] knC0 70).
Definition srHR : list expr := Eval vm_compute in s_regs (fst (fst rHR)).
Definition knHR : list kentry := Eval vm_compute in kn_after rHR knC0.
(* [comment removed for export] *)
Definition srHE0 : list expr := Eval vm_compute in sr_upd (sr_after_call_j srHR (map ridx c_kept) 70) (ridx (Z_to_bv 5 10)) (ELit 18446744073709551615).
Definition knHE0 : list kentry := Eval vm_compute in keep_readEA MSO [(48%nat, 65536)] [] knHR.
(* [comment removed for export] *)
Definition rHE := Eval vm_compute in runA scr0 (SS 0xa7bec srHE0 [] knHE0 102).
Definition srHE : list expr := Eval vm_compute in s_regs (fst (fst rHE)).
Definition knHE : list kentry := Eval vm_compute in kn_after rHE knHE0.
End FPX_0.

(* [comment removed for export] *)
Lemma dot_itinerary_okA :
  (s_pc (fst (fst rHR)), snd (fst rHR), s_log (fst (fst rHR))) = (0x63390, [], [])
  /\ (s_pc (fst (fst rHE)), snd (fst rHE), s_log (fst (fst rHE))) = (0x633bc, [], [])
  /\ (nth 1 srHE (ELit 0), nth 2 srHE (ELit 0), nth 4 srHE (ELit 0), nth 8 srHE (ELit 0), nth 10 srHE (ELit 0), nth 11 srHE (ELit 0), nth 12 srHE (ELit 0))
     = (ELit 687464, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6765824, ELit 2, ELit 1293512, ELit 127251, EVar 2)
  /\ dg_kn_ok knHE = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma regs_lit_a0A : forall E sr R e, regs_ok E sr R -> edenot E e = getr R 10%bv -> regs_ok E (sr_upd sr (ridx 10%bv) e) R.
Proof.
  intros E sr R e HR He r. rewrite <- (regs_set_a0 E sr R (getr R 10%bv) e HR He r).
  destruct (bv_eqb r 10%bv) eqn:E10.
  - unfold bv_eqb in E10. apply Z.eqb_eq in E10. apply bv_eq in E10. subst r. rewrite getr_same by discriminate. reflexivity.
  - rewrite getr_other; [reflexivity|]. intros ->. unfold bv_eqb in E10. rewrite Z.eqb_refl in E10. discriminate.
Qed.

(* [comment removed for export] *)
Ltac name_stateH HRn HKn DIn :=
  lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?mc) _ =>
    match goal with H : regs_ok _ _ Rc |- _ => rename H into HRn end;
    match goal with H : know_ok _ _ (mrestrict _ Mc) _ |- _ => rename H into HKn end;
    match goal with H : dinv _ _ _ _ _ _ _ _ Mc mc |- _ => rename H into DIn end
  end.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvH.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hcells : incl RD_CELLS (asc_cells C).
  Variable fs0 : Fs.Fs.
  Variables p0 p1 can : word.
  Variable M0 : word -> option byte.                    (* [comment removed for export] *)
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Hypothesis Hfs : sc_fs scfg = true.
  (* [comment removed for export] *)
  Hypothesis P1lo : bv_unsigned sp0 <= bv_unsigned p1 /\ bv_unsigned p1 + 2 <= 2 ^ 47.
  Hypothesis P1str : rdn ASEGS M0 p1 2 = Some (dot_path ++ [Z_to_bv 8 0]).
  Variable LK0 : list fframe.
  Variable cr0 : credit.
  Variable A0 : list (Z * Z).
  Hypothesis Hcr0 : acredit_ok L cr0 65536.

  #[local] Abbreviation dinvA := (dinv ar HI sp0 M0).
  #[local] Abbreviation ENV0 := (ENVA []).

  (* [comment removed for export] *)
  Definition fds1d : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) FdDir.

  (* [comment removed for export] *)
  Definition read_err_kA (KE : TSet) : Prop :=
    forall vals R M (model : Model) A (A1 : Z),
      length vals = 102%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = p0 -> vals_ev vals 2 = p1 -> vals_ev vals 3 = can ->
      vals_ev vals 48 = Z_to_bv 64 A1 ->
      regs_ok (ENV0 vals) srHE R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A model) M) knHE ->
      dinvA [(A1, 65536)] LK0 (adebit L cr0 65536) A M model -> incl A0 A ->
      m_fds model = fds1d -> m_fs model = fs0 ->
      ablock_range L ar A1 65536 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x633bc) M (seg_rom ASEGS)) model) KE.

  #[using="C IL HIok Hsp Hal DL Hcells M0_def Hfs P1lo P1str Hcr0"] Theorem drv_dirA : forall KA KE R (model : Model) (tid : word),
    let vals := vals_mainA sp0 p0 p1 can tid R in
    regs_ok (ENV0 vals) sr_mainA R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model) M0) kn_mainA ->
    dinvA [] LK0 cr0 A0 M0 model -> m_fds model = fds0 -> m_fs model = fs0 ->
    open_err_kA scfg ar HI sp0 fs0 [] p1 M0 LK0 cr0 A0 KA -> read_err_kA KE -> KE [] ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b04) M0 (seg_rom ASEGS)) model) (t_alt2 KA KE).
  Proof.
    intros KA KE R model tid vals HR HK DI Hfds Hfs0 HKA HKE HKE0.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals_mainA; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1) by reflexivity.
    assert (P3 : vals_ev vals 3 = can) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 38%nat.
    name_stateH HRa HKa DIa.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite Hfds in F1. rewrite Hfs0 in F2.
    clear EQM EQH SBM HR HK DI Hfds Hfs0. clear model.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?mc) _ => rename Rc into Ra; rename Mc into Ma; rename mc into modela end.
    assert (Sr' : rdn ASEGS Ma p1 2 = Some (dot_path ++ [Z_to_bv 8 0])).
    { rewrite <- P1str. apply rdn_agree. intros j Hj. apply (di_above _ _ _ _ _ _ _ _ _ _ DIa). lia. }
    (* [comment removed for export] *)
    eapply (rz_openat_dot_lz ASEGS scfg _ _ _ modela ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - exact (di_halt _ _ _ _ _ _ _ _ _ _ DIa).
    - regv HRa (17%bv : reg). reflexivity.
    - regv HRa (10%bv : reg). apply bv_eq. reflexivity.
    - regv HRa (12%bv : reg). vm_compute. reflexivity.
    - exact Hfs.
    - regv HRa (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2.
      apply (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ _ _ _ _ DIa)); [lia|].
      intros k Hk. right. left. lia.
    - rewrite F1. reflexivity.
    - split; [cbn; lia|]. split; [cbn; intros [E0|[]]; apply (f_equal bv_unsigned) in E0; vm_compute in E0; lia|].
      regv HRa (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2. exact Sr'.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x12a8d8 + 4)%Z with 0x12a8dc%Z.
      lazymatch type of HRa with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HRa) as HR2 end.
      lazymatch type of HKa with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know ASEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HKa) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev [[]; []; []; []; []])) with (ENV0 (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])).
      + apply openat_errnos_rangeA. exact He.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENVA].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + exact HK2.
      + exact DIa.
      + exact F1.
      + exact F2.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x12a8d8 + 4)%Z with 0x12a8dc%Z.
      rewrite F1. change (alloc_fd fds0) with (Z_to_bv 64 3).
      set (model1 := with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) modela).
      assert (DI1 : dinvA [] LK0 cr0 A0 Ma model1).
      { apply (dinv_model scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ modela model1 DIa); [apply with_fds_vm|].
        unfold model1. rewrite with_fds_halted'. exact (di_halt _ _ _ _ _ _ _ _ _ _ DIa). }
      assert (HK1 : know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model1) Ma) knA) by exact HKa.
      assert (G1 : m_fds model1 = fds1d) by (unfold model1; apply with_fds_fds).
      assert (G2 : m_fs model1 = fs0) by (unfold model1; rewrite with_fds_fs; exact F2).
      pose proof (regs_set_a0 (ENV0 vals) _ _ (Z_to_bv 64 3) (ELit 3) HRa eq_refl) as HR1.
      clearbody model1. clear HRa HKa DIa F1 F2 Sr'. clear modela.
      (* [comment removed for export] *)
      drv_block0 HIok Hsp DL HR1 HK1 DI1 P0 scr0 38%nat.
      name_stateH HRb HKb DIb.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      clear EQM EQH SBM HR1 HK1 DI1 G1 G2. clear model1.
      lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?mc) _ => rename Rc into Rb; rename Mc into Mb; rename mc into modelb end.
      lazymatch type of HKb with know_ok _ _ _ ?kn =>
      eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ _ kn _ _ modelb [] LK0 cr0 A0 65536 (-128) [] [] 0xa7b58 KE) end;
        [ exact HRb | exact HKb
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; lia
        | exact P0
        | vm_compute; reflexivity
        | regv HRb (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
        | lia
        | reflexivity
        | regv HRb (10%bv : reg); reflexivity
        | lia
        | exact Hcr0
        | regv HRb (4%bv : reg); reflexivity
        | regv HRb (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DIb
        | intros i nb Hf; discriminate
        | intros v b Hf; discriminate
        | exact HKE0
        | ].
      (* [comment removed for export] *)
      intros R' M' model' A' u vals' E' HL' HA' HR' HK' DI' HRT HINC HBR HAP HSHB HAB HBLK HIMG. subst vals' E'.
      destruct (model_rt_fds _ _ HRT) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      set (vals1 := vals ++ junk_vals R') in *.
      change (Env (vals_ev vals1) (blobs_ev [[]; []; []; []; []])) with (ENV0 vals1) in HR', HK'.
      rewrite HL in HL', HA', HR', HK'. change (38 + 10)%nat with 48%nat in HA', HK'.
      change (sr_after_call_j _ (map ridx c_kept) 38) with srC0 in HR'.
      change (kn_blkA 48 65536 ++ keep_allocA (-128) 4096 [] [] _) with knC0 in HK'.
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q1 : vals_ev vals1 1 = p0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
      assert (Q2 : vals_ev vals1 2 = p1) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q3 : vals_ev vals1 3 = can) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
      pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Z1 & Z2 & Z3).
      clear HRb HKb DIb HAB HBLK HIMG HSHB HAP F1 F2 HRT. clear Rb Mb modelb.
      clearbody vals1.
      (* [comment removed for export] *)
      drv_block0 HIok Hsp DL HR' HK' DI' Q0 scr0 70%nat.
      name_stateH HRc HKc DIc.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      clear EQM EQH SBM HR' HK' DI' G1 G2. clear model' R' M'.
      lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?mc) _ => rename Rc into Rc0; rename Mc into Mc0; rename mc into modelc end.
      change (regs_ok (ENV0 vals1) srHR Rc0) in HRc.
      change (know_ok ASEGS (ENV0 vals1) (mrestrict (ahid A' modelc) Mc0) knHR) in HKc.
      (* [comment removed for export] *)
      eapply (aread_dir_site scfg L ar C IL HI HIok sp0 Hsp DL Hcells M0 vals1 _ srHR knHR Rc0 Mc0 modelc [(u, 65536)] LK0 (adebit L cr0 65536) A' 65536
                MSO [(48%nat, 65536)] [] 0xa7bec KE);
        [ exact HRc | exact HKc
        | rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
        | exact Q0 | vm_compute; reflexivity
        | regv HRc (2%bv : reg); cbn [edenot ev ENVA]; rewrite Q0; apply alu_add_w_litA
        | unfold MSO; lia | reflexivity
        | regv HRc (4%bv : reg); reflexivity
        | regv HRc (10%bv : reg); reflexivity
        | regv HRc (11%bv : reg); reflexivity
        | regv HRc (12%bv : reg); reflexivity
        | lia
        | regv HRc (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DIc
        | rewrite F1; unfold fds1d; vm_compute; reflexivity
        | intros i nb Hf; cbn in Hf;
          destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL'; lia|];
                                           rewrite HA', u_small by lia;
                                           exists 65536; split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
        | intros v b Hf; discriminate
        | ].
      intros R3 M3 model3 vals3 E3 HL3 HA3 HR3 HK3 DI3 HFD3 HFS3 HFRM. subst vals3 E3.
      rewrite HL' in HL3, HA3, HR3. change (38 + 32 + 10)%nat with 80%nat in HA3. change (38 + 32 + 32)%nat with 102%nat in HL3. change (38 + 32)%nat with 70%nat in HR3.
      set (vals2 := vals1 ++ junk_vals R3) in *.
      change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; []])) with (ENV0 vals2) in HR3, HK3.
      assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL'; lia); exact Q0).
      assert (W1 : vals_ev vals2 1 = p0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL'; lia); exact Q1).
      assert (W2 : vals_ev vals2 2 = p1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL'; lia); exact Q2).
      assert (W3 : vals_ev vals2 3 = can) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL'; lia); exact Q3).
      assert (W48 : vals_ev vals2 48 = Z_to_bv 64 u) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA').
      (* [comment removed for export] *)
      assert (HR4 : regs_ok (ENV0 vals2) srHE0 R3).
      { change srHE0 with (sr_upd (sr_after_call_j srHR (map ridx c_kept) 70) (ridx 10%bv) (ELit 18446744073709551615)).
        apply regs_lit_a0A; [exact HR3|]. cbn [edenot].
        rewrite (reg_val _ _ _ _ HR3). change (sr_get (sr_after_call_j srHR (map ridx c_kept) 70) 10%bv) with (EVar 80). cbn [edenot ev ENVA]. rewrite HA3. reflexivity. }
      change (keep_readEA MSO [(48%nat, 65536)] [] knHR) with knHE0 in HK3.
      assert (G1 : m_fds model3 = fds1d) by (rewrite HFD3; exact F1).
      assert (G2 : m_fs model3 = fs0) by (rewrite HFS3; exact F2).
      clear HRc HKc DIc HR3 HFRM HFD3 HFS3 F1 F2. clear Rc0 Mc0 modelc.
      clearbody vals2.
      (* [comment removed for export] *)
      drv_block0 HIok Hsp DL HR4 HK3 DI3 W0 scr0 102%nat.
      name_stateH HRd HKd DId.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?mc) _ => apply (HKE vals2 Rc Mc mc A' u) end; try assumption.
  Qed.
End DrvH.
End FPX_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition dg_readerr_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI sp0 M0, drv_ctxA scfg L C IL ar HI sp0 M0 -> forall fs0 p0 p1 can cr0 A0, drv_pathA sp0 M0 p1 dot_path ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    read_err_kA scfg L ar HI sp0 fs0 p0 p1 can M0 [] cr0 A0 (t_die (msg_read_error dot_path) fs0).

Theorem dg_dot_of : forall scfg (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics),
  drv_lib_layoutA Lay L -> drv_budgetA L Lay ->
  dg_openerr_stmt scfg L C IL -> dg_readerr_stmt scfg L C IL -> dg_dot_stmt scfg L C IL Lay LSt.
Proof.
  intros scfg L C IL Lay LSt DLL HBUD DG_OPENERR DG_READERR.
  unfold dg_dot_stmt, drv_main_on.
  intros Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs Hdot ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH.
  subst path.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hvsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
  assert (Hal : bv_unsigned sp mod 16 = 0) by (destruct Hvsp as (_ & _ & H3); exact H3).
  pose proof CONSTS as CONSTS'. destruct CONSTS as (ILY & HRD & Hkpm & Hlin & Hovh & HPR & HEX & _).
  assert (CTX : drv_ctxA scfg L C IL ar HI sp M0) by (constructor; try assumption).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp DL M0 _ _ _ _ _ _ DI) as (HOFF & _).
  assert (STRF : rdn ASEGS M0 p1 (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])) by (exact (rdn_of_mrestrict ASEGS _ M0 HOFF _ _ _ STR)).
  assert (Hnonul : ~ In (Z_to_bv 8 0) dot_path) by (cbn; intros [E0|[]]; apply (f_equal bv_unsigned) in E0; vm_compute in E0; lia).
  assert (PTH : drv_pathA sp M0 p1 dot_path) by (constructor; try assumption; cbn; lia).
  change (Z.of_nat (length dot_path)) with 1 in PLO.
  subst cr0.
  (* [comment removed for export] *)
  assert (Hcr : acredit_ok L (8192, 2 ^ 34) 65536).
  { destruct (dlla_credit_pos Lay L DLL 0 ltac:(lia)) as [CP1 CP2].
    pose proof (HBUD 0 ltac:(lia)) as (HB1 & HB2).
    unfold credA, adebit, acredit_ok, CAPk in *. cbn [fst snd] in *. rewrite Z.pow_0_r in HB2. nia. }
  destruct main_nb as (NB1 & NB2).
  unfold env_mainA in HR, HK.
  pose proof (regs_ok_nb _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB1 HR) as HR'.
  pose proof (know_ok_nb ASEGS _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB2 HK) as HK'.
  apply (@drv_dirA PropExec.fx0 scfg L ar C IL HI HIok sp Hsp Hal DL HRD fs p0 p1 can M0 M0def Hfs ltac:(lia) STRF [] (8192, 2 ^ 34) A0 Hcr
           (t_die (msg_cannot_open dot_path) fs) (t_die (msg_read_error dot_path) fs) R model tid HR' HK' DI FDS EFS).
  - exact (DG_OPENERR ar HI sp M0 CTX dot_path fs [] p1 (8192, 2 ^ 34) A0 PTH SAH).
  - exact (DG_READERR ar HI sp M0 CTX fs p0 p1 can (8192, 2 ^ 34) A0 PTH SAH).
  - unfold t_die. apply ShapeAlg.t_emit_has_nil.
Qed.
