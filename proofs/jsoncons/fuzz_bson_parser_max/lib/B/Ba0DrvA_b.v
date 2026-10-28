(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac drv_block_post HIok Hsp DL DI P0 bls Hbl HZ :=
  match goal with
  | EQM : mrestrict _ ?M' = mem_denot _ _ ?log, EQH : (forall a, _ = true -> ?M' a = _),
    HZn : lzinv _ _ _ ?model', SBM : same_but_materialized _ ?model' |- _ =>
      let D := fresh "DI" in
      pose proof (dinv_block _ _ _ _ _ _ HIok _ Hsp DL _ _ _ bls _ _ _ _ _ _ _ _ log P0 DI Hbl ltac:(vm_compute; reflexivity) EQM EQH HZn SBM) as D;
      clear HZ HZn;
      match goal with HKn : know_ok _ _ (mrestrict (ahid ?A ?model) M') _ |- _ => rewrite <- (ahid_sbm A model model' SBM) in HKn end
  end.
Ltac drv_block_post0 HIok Hsp DL DI P0 HZ :=
  match goal with
  | EQM : mrestrict _ ?M' = mem_denot _ _ ?log, EQH : (forall a, _ = true -> ?M' a = _),
    HZn : lzinv _ _ _ ?model', SBM : same_but_materialized _ ?model' |- _ =>
      let D := fresh "DI" in
      pose proof (dinv_block _ _ _ _ _ _ HIok _ Hsp DL _ _ _ (@nil (nat * Z)) _ _ _ _ _ _ _ _ log P0 DI (no_bls _) ltac:(vm_compute; reflexivity) EQM EQH HZn SBM) as D;
      clear HZ HZn;
      match goal with HKn : know_ok _ _ (mrestrict (ahid ?A ?model) M') _ |- _ => rewrite <- (ahid_sbm A model model' SBM) in HKn end
  end.
Ltac drv_block HIok Hsp DL HR HK DI P0 bls Hbl scr NX :=
  let HZ := fresh "HZ" in
  pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
  run_block_lz_with HR HK HZ asegs_wx FUELA STOPSA scr NX true;
  [ .. | drv_block_post HIok Hsp DL DI P0 bls Hbl HZ ].
Ltac drv_block0 HIok Hsp DL HR HK DI P0 scr NX :=
  let HZ := fresh "HZ" in
  pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
  run_block_lz_with HR HK HZ asegs_wx FUELA STOPSA scr NX true;
  [ .. | drv_block_post0 HIok Hsp DL DI P0 HZ ].

Lemma openat_errnos_rangeA : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvA.
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
  (* [comment removed for export] *)
  Variables a0s path : list byte.
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables p0 p1 can : word.
  Variable M0 : word -> option byte.                    (* [comment removed for export] *)
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hppl : openat_plain_name path = true.
  Hypothesis Hfs : sc_fs scfg = true.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis Hnonul : ~ In (Z_to_bv 8 0) path.
  (* [comment removed for export] *)
  Hypothesis P1lo : bv_unsigned sp0 <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 <= 2 ^ 47.
  Hypothesis P1str : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
  (* [comment removed for export] *)
  Variable LK0 : list fframe.
  Variable cr0 : credit.
  Variable A0 : list (Z * Z).
  Hypothesis Hcr0 : acredit_ok L cr0 65536.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).

  (* [comment removed for export] *)
  Definition ENVA (vals : list word) : env := Env (vals_ev vals) (blobs_ev [[]; []; []; []; fdata]).

  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  Definition fds1 : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition open_err_kA (KA : TSet) : Prop :=
    forall e vals R M (model : Model),
      1 <= e <= 4095 ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 -> vals_ev vals 38 = errno_ret e ->
      regs_ok (ENVA vals) (sr_upd srA (ridx 10) (EVar 38)) R ->
      know_ok ASEGS (ENVA vals) (mrestrict (ahid A0 model) M) knA ->
      dinvA [] LK0 cr0 A0 M model -> m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x12a8dc) M (seg_rom ASEGS)) model) KA.

  (* [comment removed for export] *)
  Definition file_kA (KF : TSet) : Prop :=
    forall vals R M (model : Model) A (A1 : Z),
      length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = p0 -> vals_ev vals 2 = p1 -> vals_ev vals 3 = can ->
      vals_ev vals 48 = Z_to_bv 64 A1 ->
      regs_ok (ENVA vals) srC0 R -> know_ok ASEGS (ENVA vals) (mrestrict (ahid A model) M) knC0 ->
      dinvA [(A1, 65536)] LK0 (adebit L cr0 65536) A M model -> incl A0 A ->
      m_fds model = fds1 -> m_fs model = fs0 ->
      ablock_range L ar A1 65536 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b58) M (seg_rom ASEGS)) model) KF.

  Lemma alu_add_w_litA : forall (x : word) k, alu64 ALU_ADD x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
  Proof.
    intros x k. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  Theorem drv_openA : forall KA KF R (model : Model) (tid : word),
    let vals := vals_mainA sp0 p0 p1 can tid R in
    regs_ok (ENVA vals) sr_mainA R -> know_ok ASEGS (ENVA vals) (mrestrict (ahid A0 model) M0) kn_mainA ->
    dinvA [] LK0 cr0 A0 M0 model -> m_fds model = fds0 -> m_fs model = fs0 ->
    open_err_kA KA -> file_kA KF -> KF [] ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b04) M0 (seg_rom ASEGS)) model) (t_alt2 KA KF).
  Proof.
    intros KA KF R model tid vals HR HK DI Hfds Hfs0 HKA HKF HKF0.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals_mainA; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1) by reflexivity.
    assert (P3 : vals_ev vals 3 = can) by reflexivity.
    clearbody vals.
    (* [comment removed for export] *)
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 38%nat.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite Hfds in F1. rewrite Hfs0 in F2.
    clear EQM EQH SBM HR HK DI Hfds Hfs0. clear model.
    (* [comment removed for export] *)
    assert (Sr' : rdn ASEGS M p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite <- P1str. apply rdn_agree. intros j Hj. apply (di_above _ _ _ _ _ _ _ _ _ _ DI0). lia. }
    (* [comment removed for export] *)
    eapply (rz_openat_file_lz ASEGS scfg _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - exact (di_halt _ _ _ _ _ _ _ _ _ _ DI0).
    - regv HR0 (17%bv : reg). reflexivity.
    - regv HR0 (10%bv : reg). apply bv_eq. reflexivity.
    - regv HR0 (12%bv : reg). vm_compute. reflexivity.
    - exact Hfs.
    - regv HR0 (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2.
      apply (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ _ _ _ _ DI0)); [lia|].
      intros k Hk. right. left. lia.
    - rewrite F1. reflexivity.
    - split; [exact Hplen|]. split; [exact Hnonul|].
      regv HR0 (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2. exact Sr'.
    - exact Hpne.
    - exact Hppl.
    - rewrite F2. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x12a8d8 + 4)%Z with 0x12a8dc%Z.
      lazymatch type of HR0 with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR0) as HR2 end.
      lazymatch type of HK0 with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know ASEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK0) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev [[]; []; []; []; fdata])) with (ENVA (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])).
      + apply openat_errnos_rangeA. exact He.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENVA].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + exact HK2.
      + exact DI0.
      + exact F1.
      + exact F2.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x12a8d8 + 4)%Z with 0x12a8dc%Z.
      rewrite F1. change (alloc_fd fds0) with (Z_to_bv 64 3).
      set (model1 := with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0).
      assert (DI1 : dinvA [] LK0 cr0 A0 M model1).
      { apply (dinv_model scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ model0 model1 DI0); [apply with_fds_vm|].
        unfold model1. rewrite with_fds_halted'. exact (di_halt _ _ _ _ _ _ _ _ _ _ DI0). }
      assert (HK1 : know_ok ASEGS (ENVA vals) (mrestrict (ahid A0 model1) M) knA) by exact HK0.
      assert (G1 : m_fds model1 = fds1) by (unfold model1; apply with_fds_fds).
      assert (G2 : m_fs model1 = fs0) by (unfold model1; rewrite with_fds_fs; exact F2).
      pose proof (regs_set_a0 (ENVA vals) _ _ (Z_to_bv 64 3) (ELit 3) HR0 eq_refl) as HR1.
      clearbody model1. clear HR0 HK0 DI0 F1 F2. clear model0.
      (* [comment removed for export] *)
      drv_block0 HIok Hsp DL HR1 HK1 DI1 P0 scr0 38%nat.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      clear EQM EQH SBM HR1 HK1 DI1 G1 G2 Sr'. clear model1.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
      eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ _ kn _ _ model [] LK0 cr0 A0 65536 (-128) [] [] 0xa7b58 KF) end;
        [ exact HR | exact HK
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; vm_compute; reflexivity
        | rewrite HL; lia
        | exact P0
        | vm_compute; reflexivity
        | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
        | lia
        | reflexivity
        | regv HR (10%bv : reg); reflexivity
        | lia
        | exact Hcr0
        | regv HR (4%bv : reg); reflexivity
        | regv HR (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DI
        | intros i nb Hf; discriminate
        | intros v b Hf; discriminate
        | exact HKF0
        | ].
      (* [comment removed for export] *)
      intros R' M' model' A' u vals' E' HL' HA' HR' HK' DI' HRT HINC HBR HAP HSHB HAB HBLK HIMG. subst vals' E'.
      destruct (model_rt_fds _ _ HRT) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      apply (HKF (vals ++ junk_vals R') R' M' model' A' u); try assumption.
      * rewrite HL', HL. reflexivity.
      * rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      * rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      * rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      * rewrite vals_ev_app_l by (rewrite HL; lia). exact P3.
      * rewrite <- HA'. rewrite HL. reflexivity.
      * rewrite HL in HR'. exact HR'.
      * rewrite HL in HK'. exact HK'.
  Qed.
End DrvA.
End FPX_1.
