(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the driver lemmas take the auxiliary-vector pointer (auxvp, start-up value slot 5), the new launch's stack window and the channel-reader fact, and recorded proofs that no longer check are replaced by text proofs from jsoncons/fuzz_bigint's and jsoncons/fuzz_bson_parser_max's driver files; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0DrvG.v, 484 lines within its lines 31-875. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.
Module Na0DrvA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
  Variables auxvp p1 can : word.
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
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x149d44) M (seg_rom ASEGS)) model) KA.

  (* [comment removed for export] *)
  Definition file_kA (KF : TSet) : Prop :=
    forall vals R M (model : Model) A (A1 : Z),
      length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 5 = auxvp -> vals_ev vals 2 = p1 -> vals_ev vals 3 = can ->
      vals_ev vals 48 = Z_to_bv 64 A1 ->
      regs_ok (ENVA vals) srC0 R -> know_ok ASEGS (ENVA vals) (mrestrict (ahid A model) M) knC0 ->
      dinvA [(A1, 65536)] LK0 (adebit L cr0 65536) A M model -> incl A0 A ->
      m_fds model = fds1 -> m_fs model = fs0 ->
      ablock_range L ar A1 65536 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaea80) M (seg_rom ASEGS)) model) KF.

  Lemma alu_add_w_litA : forall (x : word) k, alu64 ALU_ADD x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
  Proof.
    intros x k. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  Theorem drv_openA : forall KA KF R (model : Model) (tid a0p : word),
    let vals := vals_mainA sp0 a0p p1 can tid auxvp R in
    regs_ok (ENVA vals) sr_mainA R -> know_ok ASEGS (ENVA vals) (mrestrict (ahid A0 model) M0) kn_mainA ->
    dinvA [] LK0 cr0 A0 M0 model -> m_fds model = fds0 -> m_fs model = fs0 ->
    open_err_kA KA -> file_kA KF -> KF [] ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaea2c) M0 (seg_rom ASEGS)) model) (t_alt2 KA KF).
  Proof.
    intros KA KF R model tid a0p vals HR HK DI Hfds Hfs0 HKA HKF HKF0.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals_mainA; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 5 = auxvp) by reflexivity.
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
    - split; [exact Hplen|]. split; [exact Hnonul|]. split.
      { regv HR0 (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2.
        unfold TASK_SIZE. pose proof (proj2 P1lo). lia. }
      regv HR0 (11%bv : reg). cbn [edenot ev ENVA]. rewrite P2. exact Sr'.
    - exact Hpne.
    - exact Hppl.
    - rewrite F2. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x149d40 + 4)%Z with 0x149d44%Z.
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
      rewrite v_addi_pc4 by lia. change (0x149d40 + 4)%Z with 0x149d44%Z.
      rewrite F1. change (alloc_fd fds0) with (Z_to_bv 64 3).
      set (model1 := with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0).
      assert (DI1 : dinvA [] LK0 cr0 A0 M model1).
      { apply (dinv_model scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ model0 model1 DI0); [apply with_fds_vm| |apply with_fds_rdr].
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
      eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ _ kn _ _ model [] LK0 cr0 A0 65536 (-128) [] [] 0xaea80 KF) end;
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
End Na0DrvA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LibTail. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0126 () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_allc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic3iffK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01I46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega7EnvRing5PExpr02I47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltI47Corelib4Init9Datatypes6option00C47Corelib4Init3Nat3addI47Corelib4Init5Logic3and00K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addI47Corelib5Lists7ListDef6Forall00K46Stdlib9micromega=RingMicromega5Psatz07C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr07I46Stdlib9micromega6VarMap1t00K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfK69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7kn_blkAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib7Mh_01167DrvKitA8log_in_bC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2eq00K69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertK69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega=RingMicromega5Psatz05C47Corelib9RelationsDRelation_Definitions8relationC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib7Mh_00638SymExec23SX25s_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG6lp_atAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG4CAPkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3hzAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC46Stdlib9micromega;ZifyClasses7rew_iffc59OSSVerify5KrLib7Mh_01267Na0DrvG9hdr_valsAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvA4ENVAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclc59OSSVerify5KrLib7Mh_01267Na0DrvG4mdl3C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsc59OSSVerify5KrLib7Mh_01267Na0DrvG5credAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG:CAPk_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG:inv_block1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_01199Na0DrvLib:has_windowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvA>alu_add_w_litAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7reg_valC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupc59OSSVerify5KrLib7Mh_01267Na0DrvG<fds_lookup3AC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC56Stdlib5Arith8PeanoNat3Nat3eqbC59OSSVerify5KrLib7Mh_01199Na0DrvLib:sub_blockAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7find_nzC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC56Stdlib6ZArith4Znat5Nat2Z2idC59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead:keep_readAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC47Corelib4Init5Logic3notc59OSSVerify5KrLib7Mh_01267Na0DrvG>file_read_litAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG<length_readAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0105:RefReadLib:len_word_ZC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions?bv_add_unsignedc59OSSVerify5KrLib7Mh_01267Na0DrvG9fds_ins3AC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib7Mh_01059SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG8hdr_appAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_00638SymExec23SX25carryC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG2grC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG6relayVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_48C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_70C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6no_blsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_haltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib7Mh_01199Na0DrvLib8ahid_sbmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG>content_block0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC59OSSVerify5KrLib7Mh_01199Na0DrvLib;with_fds_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes@with_fds_halted'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib<with_fds_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib;with_fds_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive;regs_set_a0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG:credA_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9close_kgAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG:hdr_relayAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib7Mh_01267Na0DrvG>regs_ok_by_nthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib>kn_blkA_of_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7ksubl_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG;relay_know6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA;ksubl_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs4knGAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG<fds_remove3AC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive:v_addi_pc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK;rz_close_lzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG;block_nologC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib>src_stage_aaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLibAsrc_stage_app_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs;keep_allocAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib<model_rt_fdsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC49OSSVerify5KrLib7LibTail9rdn_app_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib<amemcpy_siteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead:aread_siteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG6rd_atAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega6VarMap4findK46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega6VarMap1t03C4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA:rz_run_lz2C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib9micromega:ZMicromega;ZArithProof00I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib7Mh_0119;Na0Drv_defs5FUELAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6STOPSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srGLAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srRA0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6knRf0AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8asegs_wxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srLPAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srRm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5knRm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6knRe0AC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6c_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead5STAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7IMG_W_AC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs3MSOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvA4fds0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srRDAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5knLPAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs4knRAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib7Mh_01059SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6cellCAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6knLP6AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs8knGbaseAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG<knGbaseA_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs<IMG_CLIENT_AC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_01267Na0DrvG;knLPA_splitC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List=length_firstnC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs8kn_blk2AC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init3Nat3minC59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:acredit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decc59OSSVerify5KrLib7Mh_01267Na0DrvG?know_LP_rangesAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_71C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib7Mh_01267Na0DrvG<sc_ltu_wantAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG<sc_eq_70_38AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG;want_x_valAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib7Mh_01267Na0DrvG9CAPk_lt10C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib7Mh_01267Na0DrvG;cap2_x_valAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLibBhzA_of_block_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG<lb_remove_2AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs;keepalloc_GC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib<src_blk_aaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib?src_blk_app_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG=lb_remove_hdAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG6CAPk_SC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib7Mh_01199Na0DrvLib:afree_siteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib<amalloc_siteC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6knLPpAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srGd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5knGd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srGc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5knGc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5knGb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6knLPgAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs4srPaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs7want_xAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lib_viewC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface7ll_heapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib7Mh_01167DrvKitA:kentry_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB=lla_td_localeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB:lla_localeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB<lla_init_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB:lla_td_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB=lla_td_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_guardC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry8auxv_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB?lib_init_factsAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface:auxv_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC59OSSVerify5KrLib7Mh_0116:As0DrvKitA@rdn_of_mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio:kimg_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio7vis_lowC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_0119;Na0DrvStdio9kword_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC59OSSVerify5KrLib7Mh_01167DrvKitA=kentry_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_auxvpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface>lib_init_factsC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0126=Na0DrvLibInit>drv_lib_cellsA00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB;lla_td_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lla_phdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_phentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_phnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_rw_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_initcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB>lla_init_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB5lla_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface5cellzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126=Na0DrvLibInit;locale_imgAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib7Mh_0119;Na0DrvStdio8img_cellC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC59OSSVerify5KrLib7Mh_01199Na0DrvLib8di_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio6rdn_trC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface7ll_phdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface8ll_phentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface8ll_phnumC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib7Mh_01199Na0DrvLib9dla_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8dla_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface;ll_init_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface:ll_td_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface9ll_td_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface<ll_td_localeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface9ll_localeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface<ll_td_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface8ll_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface8ll_auxvpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface=ll_init_cellsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC59OSSVerify5KrLib7Mh_0119;Na0DrvEntry:auxv_listAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126=Na0DrvLibInit:LIBINIT_KNC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c59OSSVerify5KrLib7Mh_0126=Na0DrvLibInit;LIBINIT_IMGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126=Na0DrvLibInit<INIT_CELLS_AC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA;asan_layout00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:vis_of_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL3CPlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3SCaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface7in_footC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB7in_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibLBnot_foot_off_imageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibLBnot_junk_off_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib=sub_blockA_hzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL;img_lib_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_clientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL@not_foot_of_holeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL@not_junk_of_holeC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint05K47Corelib4Init7Decimal4uint07K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01167DrvKitA:regions_ok01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL9IMG_LIB_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8IMG_RW_AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL9LIB_HOLESC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint01C59OSSVerify5KrLib7Mh_01199Na0DrvLib:wseg_stageC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9skipn_appI46Stdlib9micromega7EnvRing3Pol00I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr03K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib4Init3Nat3subc59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK<wv_loop_stmtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK5wv_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_bufC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib7Mh_0101=Na0DiagWritev3W64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphc59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK6wv_iovC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7wv_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK:wv_buf_lenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101=Na0DiagWritev8wv_ret_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned9keeps_butC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK8cs_not10C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC59OSSVerify5KrLib7Mh_0101=Na0DiagWritev8wv_ret_BC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK:wv_keep_csC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK8incl_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK;wv_keep_notC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK:wv_done_trC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA;sbm_lazy_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA=sbm_halted_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK8sbm_fds'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib7Mh_00368AsanAcctJsame_but_materialized_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:skipn_all2C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtC59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101=Na0DiagWritev:wv_body_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7W64_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC46Stdlib5Lists4List<length_skipnI46Stdlib;setoid_ring<Ring_polynom3Pol00c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7W64_hitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK;W64_rdn_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK;wv_buf_skipC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK9wv_buf_trC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK;rdn_frame_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK:wv_keep_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK:msteps_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101=Na0DiagWritev:wv_body_hiC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rK46Stdlib;setoid_ring<Ring_polynom5PExpr05I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega=RingMicromega3Op206C56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxI4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_0056<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I49OSSVerify5KrLib5BMode5BMode00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7pcE_af0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7pcE_b78C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7pcE_b84C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7pcE_af8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7WV_KEEPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK7pcE_b74C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>impl_ReflexiveI46Stdlib;setoid_ring<Ring_polynom3Mon00c59OSSVerify5KrLib7Mh_0126<Na0DiagLoopK9incl_bodyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX4esubC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5sx8FAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC9target_kAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib7Mh_01059SymDriveX<env_app_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC<content_visAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC8know_GLAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC;ltu_hdr_scAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5cfgFAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs9cfgF_valAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs>cfglen_x_cfgFAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs;sx8_x_sx8FAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<regs_ok_esubC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26adenotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC=content_byteAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC;krange_litAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs9plen_valAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC8kbyte48AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC4CFGAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs3PXAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs8STOPS_HAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5srHb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5knHb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs9scr_fallAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5knGLAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs9cfglen_xAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs4srHaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC3B0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC3B1AC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09c59OSSVerify5KrLib7Mh_01267Na0DrvC3PLAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC3B2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC9B0A_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC9B1A_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC9B2A_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC:CFGA_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs6sx8_xAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs6kn_bmAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs8knHb0_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs7kn_tgtAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs7plen_xAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs4srHbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5srT0AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5knT0AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs9knT0A_subC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityK69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond05C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesBPreOrder_Reflexivec59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knTcAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD6lh1_kAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC59OSSVerify5KrLib=SymExec2Sound4SX2S9rdn_skipnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9w_add_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD7callsFAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD;callsFA_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD?calls_x_callsFAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8know_TcAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD;relay_ok_bDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD:pl0_to_lhAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibLAregs_ok_upd_sameAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD6relayAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8lay_extAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8vals_hiAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD9relayA_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD9relayA_81C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD:relayA_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8lh_valsAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD;relayA_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD<relayA_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun=know_ok_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD6CALLSAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs8STOPS_TAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD7wseg_axC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knTeAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5srV0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knV0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knU0AC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorderK4ELinuxProcessSemantics5Riscv5Instr5aluop0:c59OSSVerify5KrLib7Mh_01267Na0DrvD8payloadAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs3TSOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs6srTm0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD9PLA_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD<CALLSA_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs8calls_xAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD9wseg_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD<payloadA_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4sr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4sr10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knTkAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs6knLH1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD4cr1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4sr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4sr11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126;Na0DrvHRead;keep_readEAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt3RDAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib?window_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead7rd_cellC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead9avoid_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct@rdn_mrestrict_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead5w_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcptAwrap_read_pre_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib7Mh_0119:Na0DrvRead5rd_M2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead6rd_MV2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0DrvHIcpt3RDEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib>ahid_same_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt9RDA_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead;rd_MV2_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead<rd_MV2_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0DrvHIcptFread_icpt_post_err_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0DrvHIcpt7RDE_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0DrvHIcpt9RDE_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt7RDA_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead;rd_M2_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_vmlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3CWAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib=vals_ev_junkAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib>window_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA?know_keep_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA<rz_msteps_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKBrz_read_dir_cnt_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0ReadIcpt4RIPLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101;Na0DrvHIcpt:EISDIR_RETC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126;Na0DrvHRead4TP_AC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06c59OSSVerify5KrLib7Mh_0126;Na0DrvHRead7ERRNO_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119:Na0DrvRead8RD_CELLSC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEc59OSSVerify5KrLib7Mh_0126;Na0DrvHRead:wseg_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib;c_kept_no0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126;Na0DrvHRead;IMG_NOERRNOC1?~~~~~~~~~~~~~~~".
Module Na0DrvG.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LibTail. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LibTail OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.RefReadLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefPrintfLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvG () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C47Corelib4Init5Peano2ltc59OSSVerify5KrLib7Mh_01267Na0DrvG6relayVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22ebC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_loC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7ksubl_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG<relayV_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA;ksubl_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun=know_ok_agreeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7kn_blkAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6knLP6AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs6cellCAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs8knGbaseAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib6ZArith4Zdiv;Zmod_uniqueK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem7mul_divC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3subC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7sub_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib7Mh_01267Na0DrvG>mod_of_decompZC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib=SymExec2Sound4SX2S7u_mul64C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I47Corelib7Numbers7BinNums1N00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes7nat_indc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_0105:RefReadLib?word_to_nat_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem2FsCfile_read_unguardedC46Stdlib5Lists4List<length_skipnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init3Nat3subC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z8eqb_reflC59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4bool02K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C59OSSVerify5KrLib=SymExec2Sound4SX2S>ridx_roundtripC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib=SymExec2Sound4SX2S:ridx_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib7Mh_01267Na0DrvG9hdr_valsAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegI47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes6option01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib7Mh_01267Na0DrvA4fds0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC56Stdlib6ZArith6BinInt1Z7pow_1_rC56Stdlib6ZArith6BinInt1Z9pow_add_rc59OSSVerify5KrLib7Mh_01267Na0DrvG4CAPkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib7Mh_01267Na0DrvG5credAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_b_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_b_overheadC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG:CAPk_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C47Corelib4Init9Datatypes3sndK46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx7aiob_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3hzAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLibBhzA_of_block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvA4ENVAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c59OSSVerify5KrLib7Mh_01267Na0DrvG;sub_as_addAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs7want_xAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuc59OSSVerify5KrLib7Mh_01267Na0DrvG;want_x_valAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c59OSSVerify5KrLib7Mh_01267Na0DrvG9mul2_litAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs7cap2_xAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5knLPAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init5Logic2or01c59OSSVerify5KrLib7Mh_01267Na0DrvG3CW0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_01167DrvKitA7find_nzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib7Mh_01199Na0DrvLib<img_w_clientC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK59OSSVerify5KrLib7Mh_01167DrvKitA:regions_ok01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7IMG_W_AC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs<IMG_CLIENT_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA8log_in_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG>regions_write0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01167DrvKitA:regions_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitAAmem_denot_frame_ZC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib7Mh_01267Na0DrvG<block_frame0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG6lp_atAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclc59OSSVerify5KrLib7Mh_01267Na0DrvG4mdl3C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injc59OSSVerify5KrLib7Mh_01267Na0DrvG8read_okAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG:loop_stepAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srLPAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsc59OSSVerify5KrLib7Mh_01267Na0DrvA4fds1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25carryC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_00638SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:sub_blockAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6no_blsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8ahid_sbmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG;block_nologC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG8loop_okAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG6rd_atAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG2grC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7pow_0_rc59OSSVerify5KrLib7Mh_01267Na0DrvG:hdr_relayAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7reg_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_38C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_48C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_70C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9relayV_71C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG>regs_ok_by_nthC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib7Mh_01199Na0DrvLib>kn_blkA_of_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG;relay_know6C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C69OSSVerify5KrLib7Mh_00638SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvA7file_kAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA:rz_run_lz2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs5srRDAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs5FUELAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6STOPSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs4srC0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs4knC0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8asegs_wxC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib7Mh_01267Na0DrvG;knLPA_splitC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gr (R : bvmap 5 word) (i : nat) : word := getr R (Z_to_bv 5 (Z.of_nat i)).
Definition relayV (vals : list word) (R : bvmap 5 word) (x38 x48 x70 : word) (ext : list word) : list word :=
  let z := Z_to_bv 64 0 in
  [vals_ev vals 0; vals_ev vals 1; vals_ev vals 2; vals_ev vals 3; vals_ev vals 4; vals_ev vals 5]
  ++ map (gr R) (seq 0 32)
  ++ [x38; z; z; z; z; z; z; z; z; z; x48]
  ++ [z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; z; x70]
  ++ ext.
Lemma relayV_len : forall vals R x38 x48 x70 ext, length (relayV vals R x38 x48 x70 ext) = (71 + length ext)%nat.
Proof. intros. reflexivity. Qed.
Lemma relayV_lo : forall vals R x38 x48 x70 ext j, (j < 6)%nat -> vals_ev (relayV vals R x38 x48 x70 ext) j = vals_ev vals j.
Proof. intros vals R x38 x48 x70 ext j Hj. do 6 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma relayV_38 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 38 = x38.
Proof. reflexivity. Qed.
Lemma relayV_48 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 48 = x48.
Proof. reflexivity. Qed.
Lemma relayV_70 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 70 = x70.
Proof. reflexivity. Qed.
Lemma relayV_71 : forall vals R x38 x48 x70 w ext, vals_ev (relayV vals R x38 x48 x70 (w :: ext)) 71 = w.
Proof. reflexivity. Qed.
Lemma relayV_agree : forall ebs vals R x38 x48 x70 ext,
  env_agree 6 (Env (vals_ev vals) ebs) (Env (vals_ev (relayV vals R x38 x48 x70 ext)) ebs).
Proof. intros. split; [|reflexivity]. intros n Hn. cbn [ev]. symmetry. apply relayV_lo. exact Hn. Qed.
(* [comment removed for export] *)
Lemma relay_know6 : forall ebs vals R x38 x48 x70 ext M kn kn6,
  know_ok ASEGS (Env (vals_ev vals) ebs) M kn -> ksubl_b kn kn6 = true -> kn_vars_lt 6 kn6 = true ->
  know_ok ASEGS (Env (vals_ev (relayV vals R x38 x48 x70 ext)) ebs) M kn6.
Proof.
  intros ebs vals R x38 x48 x70 ext M kn kn6 HK Hsub Hv.
  eapply (know_ok_agree ASEGS 6); [apply relayV_agree | exact Hv |].
  eapply ksubl_sound; [exact HK | exact Hsub].
Qed.

Lemma knLPA_split : knLPA = kn_blkA 48 65536 ++ knLP6A.
Proof. reflexivity. Qed.
Lemma knGbaseA_sub : ksubl_b (kn_blkA 48 65536 ++ cellCA :: knLP6A) knGbaseA = true.
Proof. vm_compute. reflexivity. Qed.
Lemma knLP6A_vars : kn_vars_lt 6 knLP6A = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod_of_decompZ : forall a b q r : Z, 0 < b -> 0 <= r < b -> a = b * q + r -> a mod b = r.
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma sub_as_addA : forall c l : Z, 0 <= l <= c -> c < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 c) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 l)) = Z_to_bv 64 (c - l).
Proof.
  intros c l Hl Hc. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
  rewrite (bv_wrap_small 64 l) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  destruct (Z.eq_dec l 0) as [->|Hnz].
  - rewrite Z.mul_0_r, Z.sub_0_r. cbn [Z.modulo Z.add]. rewrite Z.add_0_r. reflexivity.
  - rewrite (mod_of_decompZ ((2 ^ 64 - 1) * l) (2 ^ 64) (l - 1) (2 ^ 64 - l)) by lia.
    rewrite (mod_of_decompZ (c + (2 ^ 64 - l)) (2 ^ 64) 1 (c - l)) by lia.
    rewrite (mod_of_decompZ (c - l) (2 ^ 64) 0 (c - l)) by lia.
    reflexivity.
Qed.
Lemma mul2_litA : forall c : Z, 0 <= c -> 2 * c < 2 ^ 64 -> mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 c) = Z_to_bv 64 (2 * c).
Proof. intros c H0 H1. apply bv_eq. rewrite u_mul64. rewrite !u_small by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma firstn_app_skipnA : forall {X} (l : list X) (a b : nat), firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
  intros X l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma file_read_litA : forall data (off cnt : Z), 0 <= off < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data).
Proof. intros. rewrite file_read_unguarded, !word_to_nat_lit by lia. reflexivity. Qed.
Lemma length_readA : forall (data : list byte) (off cnt : Z), 0 <= off -> off <= Z.of_nat (length data) -> 0 <= cnt ->
  Z.of_nat (length (firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data))) = Z.min cnt (Z.of_nat (length data) - off).
Proof. intros. rewrite length_firstn, length_skipn. lia. Qed.
Lemma firstn_len_firstnA : forall {X} (l : list X) w, firstn (length (firstn w l)) l = firstn w l.
Proof.
  intros X l. induction l as [|x l IH]; intros w; [rewrite !firstn_nil; reflexivity|].
  destruct w as [|w]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.
Lemma lb_remove_2A : forall A2 n2 A n, A2 <> A -> lb_remove A [(A2, n2); (A, n)] = [(A2, n2)].
Proof.
  intros A2 n2 A n H. cbn [lb_remove fst]. replace (A2 =? A) with false by (symmetry; apply Z.eqb_neq; exact H).
  rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma regs_ok_by_nth : forall E sr R,
  (forall i, (0 < i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - assert (Hnz : ridx r <> 0%nat).
    { intros Hc. assert (r = 0%bv) by (rewrite <- (ridx_roundtrip r), Hc; apply bv_eq; reflexivity). subst r.
      rewrite bv_eqb_refl in Hr0. discriminate. }
    pose proof (H (ridx r) ltac:(pose proof (ridx_range r); lia)) as Hx. rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Lemma lb_remove_hdA : forall A n l, lb_remove A ((A, n) :: l) = l.
Proof. intros A n l. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma lb_remove_1A : forall A n, lb_remove A [(A, n)] = [].
Proof. intros A n. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvG.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hcells : incl RD_CELLS (asc_cells C).
  Hypothesis HCOST : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L.
  (* [comment removed for export] *)
  Variables a0s path : list byte.
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables auxvp p1 can : word.
  Variable M0 : word -> option byte.                    (* [comment removed for export] *)
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Variable LK0 : list fframe.
  Variable A0 : list (Z * Z).

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).

  (* [comment removed for export] *)
  Definition hdr_valsA (vals : list word) : Prop :=
    vals_ev vals 0 = sp0 /\ vals_ev vals 5 = auxvp /\ vals_ev vals 2 = p1 /\ vals_ev vals 3 = can.
  Lemma hdr_relayA : forall vals R x38 x48 x70 ext, hdr_valsA vals -> hdr_valsA (relayV vals R x38 x48 x70 ext).
  Proof. intros vals R x38 x48 x70 ext H. unfold hdr_valsA. rewrite !relayV_lo by lia. exact H. Qed.
  Lemma hdr_appA : forall vals ext, hdr_valsA vals -> (6 <= length vals)%nat -> hdr_valsA (vals ++ ext).
  Proof. intros vals ext H HL. unfold hdr_valsA. rewrite !vals_ev_app_l by lia. exact H. Qed.

  (* [comment removed for export] *)
  Definition mdl3 (model : Model) (off : Z) : Prop :=
    m_fds model = fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off)) /\ m_fs model = fs0.
  Lemma fds_lookup3A : forall e, fd_lookup (fd_insert fds0 (Z_to_bv 64 3) e) (Z_to_bv 64 3) = Some e.
  Proof. intros. reflexivity. Qed.
  Lemma fds_remove3A : forall e, fd_remove (fd_insert fds0 (Z_to_bv 64 3) e) (Z_to_bv 64 3) = fds0.
  Proof. intros. reflexivity. Qed.
  Lemma fds_ins3A : forall e e', fd_insert (fd_insert fds0 (Z_to_bv 64 3) e) (Z_to_bv 64 3) e' = fd_insert fds0 (Z_to_bv 64 3) e'.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition CAPk (k : Z) : Z := 65536 * 2 ^ k.
  Variables Kc Bc : Z.
  Hypothesis HKc : 0 <= Kc. Hypothesis HBc : 0 <= Bc.
  Definition credA (k : Z) (cr : credit) : Prop :=
    (10 - k) * hl_k_per_malloc L + Kc <= fst cr
    /\ hl_b_lin L * (2 ^ 27 - 2 * CAPk k) + (10 - k) * hl_b_overhead L + Bc <= snd cr.

  Lemma CAPk_S : forall k, 0 <= k -> CAPk (k + 1) = 2 * CAPk k.
  Proof. intros k Hk. unfold CAPk. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. Qed.
  Lemma CAPk_range : forall k, 0 <= k <= 10 -> 65536 <= CAPk k <= 67108864.
  Proof.
    intros k Hk. unfold CAPk. split.
    - assert (1 <= 2 ^ k) by (pose proof (Z.pow_le_mono_r 2 0 k); cbn in *; lia). lia.
    - pose proof (Z.pow_le_mono_r 2 k 10 ltac:(lia) ltac:(lia)) as H. change (2 ^ 10) with 1024 in H. lia.
  Qed.
  Lemma CAPk_lt10 : forall k, 0 <= k < 10 -> CAPk k <= 33554432.
  Proof. intros k Hk. unfold CAPk. pose proof (Z.pow_le_mono_r 2 k 9 ltac:(lia) ltac:(lia)) as H. change (2 ^ 9) with 512 in H. lia. Qed.
  Lemma credA_exit : forall k cr, 0 <= k <= 10 -> credA k cr -> Kc <= fst cr /\ Bc <= snd cr.
  Proof. intros k cr Hk [C1 C2]. pose proof (CAPk_range k Hk). destruct HCOST as (H1 & H2 & H3). nia. Qed.

  (* [comment removed for export] *)
  Lemma inv_block1 : forall LB LK cr A M model u n, dinvA LB LK cr A M model -> In (u, n) LB ->
    ablock_range L ar u n /\ defined M u n /\ hzA sp0 u n.
  Proof.
    intros LB LK cr A M model u n D Hin.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ _ _ _ _ D)) as (WF & _).
    destruct (WF (u, n) Hin) as (B & Df & _). cbn [fst snd] in B, Df. split; [exact B|]. split; [exact Df|].
    exact (hzA_of_block_range L ar IL sp0 DL _ _ B).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable K : TSet.
  Hypothesis HK0 : K [].

  (* [comment removed for export] *)
  Definition close_kgA (CAP : Z) (crC : credit) (KC : TSet) : Prop :=
    forall vals R M (model : Model) A (A1 : Z),
      length vals = 71%nat -> hdr_valsA vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
      regs_ok (ENVG vals) srGLA R ->
      (forall lo hi, lo <= LEN <= hi -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) (knGA lo hi)) ->
      rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      dinvA [(A1, CAP)] LK0 crC A M model -> incl A0 A ->
      m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x149d44) M (seg_rom ASEGS)) model) KC.

  (* [comment removed for export] *)
  Definition lp_atA (z : Z) : Prop := forall (k len A1 : Z) vals R M (model : Model) A cr,
      0 <= k <= 10 -> 0 <= len <= CAPk k -> len <= LEN -> LEN - len <= z ->
      length vals = 71%nat -> hdr_valsA vals ->
      vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 len ->
      regs_ok (ENVG vals) srLPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
      rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
      dinvA [(A1, CAPk k)] LK0 cr A M model -> incl A0 A -> mdl3 model len -> credA k cr ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaeab4) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition rd_atA (z : Z) : Prop := forall (k len want A1 : Z) vals R M (model : Model) A cr,
      0 <= k <= 10 -> 0 <= len < CAPk k -> len <= LEN -> LEN - len <= z ->
      want = Z.min (CAPk k - len) 65536 ->
      length vals = 72%nat -> hdr_valsA vals ->
      vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 len ->
      vals_ev vals 71 = Z_to_bv 64 want ->
      regs_ok (ENVG vals) srRDA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
      rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
      dinvA [(A1, CAPk k)] LK0 cr A M model -> incl A0 A -> mdl3 model len -> credA k cr ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x6a2b8) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition refuse_kA (KR : TSet) : Prop := forall (A1 : Z) vals R M (model : Model) A cr,
      length vals = 71%nat -> hdr_valsA vals ->
      vals_ev vals 38 = Z_to_bv 64 67108864 -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 67108864 ->
      regs_ok (ENVG vals) srLPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
      dinvA [(A1, 67108864)] LK0 cr A M model -> incl A0 A -> mdl3 model 67108864 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaeab4) M (seg_rom ASEGS)) model) KR.

  (* [comment removed for export] *)
  Hypothesis HKC : LEN < 67108864 -> forall CAP crC,
      65536 <= CAP <= 67108864 -> LEN < CAP -> Kc <= fst crC -> Bc <= snd crC -> close_kgA CAP crC K.
  Hypothesis HREF : 67108864 <= LEN -> refuse_kA K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac norm_srget := repeat match goal with |- context [sr_get ?sr ?r] =>
                      let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
  Ltac norm_nth := repeat match goal with |- context [nth ?i ?l (ELit 0)] =>
                      let x := eval vm_compute in (nth i l (ELit 0)) in change (nth i l (ELit 0)) with x end.
  Ltac relay1 HR :=
    norm_nth;
    first [ lia
          | reflexivity
          | rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA]; reflexivity
          | idtac ].
  Ltac relay_loop HR i :=
    first [ lia | let j := fresh "i" in destruct i as [|j]; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; relay1 HR | relay_loop HR j ] ].
  Ltac relay_regs HR := apply regs_ok_by_nth; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; relay_loop HR i.
  Ltac relay2 HR :=
    rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA];
    rewrite ?relayV_38, ?relayV_48, ?relayV_70, ?relayV_71; unfold gr;
    rewrite ?(reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA].
  Ltac regv1 HR := rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sc_eq_70_38A : forall vals M (len cap : Z) t,
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap ->
    0 <= len < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> Z.eqb len cap = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_EQ (EVar 70) (EVar 38)).
  Proof.
    intros vals M len cap t P70 P38 Hl Hc Ht. cbn [sc_denot branch_taken edenot ev ENVA]. rewrite P70, P38.
    unfold bv_eqb. rewrite !u_small by lia. exact Ht.
  Qed.
  Lemma want_x_valA : forall vals (len cap : Z),
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len <= cap -> cap < 2 ^ 64 ->
    edenot (ENVG vals) want_xA = Z_to_bv 64 (cap - len).
  Proof. intros vals len cap P70 P38 H1 H2. cbn [want_xA edenot ev ENVA]. rewrite P70, P38. apply sub_as_addA; lia. Qed.
  Lemma sc_ltu_wantA : forall vals M (len cap : Z) t,
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len <= cap -> cap < 2 ^ 64 ->
    Z.ltb (cap - len) 65536 = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_LTU want_xA (ELit 65536)).
  Proof.
    intros vals M len cap t P70 P38 H1 H2 Ht. cbn [sc_denot branch_taken].
    rewrite (want_x_valA vals len cap P70 P38 H1 H2). cbn [edenot]. unfold bv_ltu. rewrite !u_small by lia. exact Ht.
  Qed.
  Lemma cap2_x_valA : forall vals (cap : Z),
    vals_ev vals 70 = Z_to_bv 64 cap -> 0 <= cap -> 2 * cap < 2 ^ 64 ->
    edenot (ENVG vals) cap2_xA = Z_to_bv 64 (2 * cap).
  Proof. intros vals cap P70 H1 H2. cbn [cap2_xA edenot ev ENVA]. rewrite P70. apply mul2_litA; lia. Qed.

  Lemma know_LP_rangesA : forall vals M (len cap lo70 hi70 lo38 hi38 : Z),
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
    lo70 <= len <= hi70 -> lo38 <= cap <= hi38 ->
    know_ok ASEGS (ENVG vals) M knLPA ->
    know_ok ASEGS (ENVG vals) M (KRange (EVar 70) lo70 hi70 :: KRange (EVar 38) lo38 hi38 :: knLPA).
  Proof.
    intros vals M len cap lo70 hi70 lo38 hi38 P70 P38 Hl Hc H70 H38 HK.
    constructor; [|constructor; [|exact HK]]; cbn [kentry_ok edenot ev ENVA]; rewrite ?P70, ?P38, u_small by lia; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CW0 (a : Z) : Prop :=
    bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 \/ (exists lo hi, In (lo, hi) IMG_W_A /\ lo <= a < hi).
  Lemma regions_write0 : forall vals ebs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    regions_ok ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W_A [] E CW0 (fun _ => True).
  Proof.
    intros vals ebs E P0. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CW0. left. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. destruct (img_w_client sp0 lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4).
      split; [lia|]. split; [lia|]. intros a Ha. unfold CW0. right. exists lo, hi. auto.
    - intros lo hi [].
  Qed.
  Lemma block_frame0 : forall vals ebs A M M' (model : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    forall a, 0 <= a < 2 ^ 64 -> ~ CW0 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof.
    intros vals ebs A M M' model log E P0 Hlog EQM EQH a Ha HC.
    pose proof (regions_write0 vals ebs P0) as RG.
    destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
    assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
    rewrite E1, EQM.
    rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W_A _ CW0 (fun _ => True) [] RG _ log a Hlog Ha HC).
    unfold mrestrict. rewrite Hh. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma block_nolog : forall (E : env) A M M' (model : Model),
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) [] ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    forall a : word, M' a = M a.
  Proof.
    intros E A M M' model EQM EQH a. destruct (ahid A model a) eqn:Hh; [exact (EQH a Hh)|].
    cbn [mem_denot] in EQM. pose proof (f_equal (fun f => f a) EQM) as X. cbv beta in X. unfold mrestrict in X. rewrite Hh in X. exact X.
  Qed.
  (* [comment removed for export] *)
  Lemma content_block0 : forall vals ebs A M M' (model : Model) log (u n : Z) (m : nat) bs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    hzA sp0 u n -> Z.of_nat m <= n ->
    rdn ASEGS M (Z_to_bv 64 u) m = Some bs -> rdn ASEGS M' (Z_to_bv 64 u) m = Some bs.
  Proof.
    intros vals ebs A M M' model log u n m bs E P0 Hlog EQM EQH (Z1 & Z2 & Z3) Hm HC. pose proof Hsp as Hsp'.
    rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia.
    apply (block_frame0 vals ebs A M M' model log P0 Hlog EQM EQH); [lia|].
    intros [HS|(lo & hi & Hin & Hr)]; [lia|].
    destruct (img_w_client sp0 lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma read_okA : forall z, lp_atA (z - 1) -> rd_atA z.
  Proof.
    intros z IH. unfold rd_atA.
    intros k len want A1 vals R M model A cr Hk Hlen HlL Hz Hwant HL HV P38 P48 P70 P71 HR HK HC DI HINC (MF & MS) Hcr.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (CAPk_range k Hk) as HCk.
    destruct (inv_block1 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as (P0 & P1 & P2 & P3).
    assert (Hw : 1 <= want <= 65536 /\ want <= CAPk k - len) by lia.
    (* [comment removed for export] *)
    eapply (aread_site scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hcells M0 vals _ srRDA knLPA R M model [(A1, CAPk k)] LK0 cr A want path (Z_to_bv 64 len) fdata
              MSO [(48%nat, 65536)] [] 0xaeb14 K);
      [ exact HR | exact HK
      | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
      | exact P0 | vm_compute; reflexivity
      | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
      | unfold MSO; lia | reflexivity
      | regv HR (10%bv : reg); reflexivity
      | regv HR (11%bv : reg); reflexivity
      | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact P71
      | lia
      | regv HR (1%bv : reg); reflexivity
      | lia | reflexivity
      | exact DI
      | rewrite MF; apply fds_lookup3A
      | rewrite MS; exact Hfile
      | intros i nb Hf; cbn in Hf;
        destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                         rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
      | intros v b Hf; discriminate
      | ].
    intros R' M' model' bs vals' E' HL' HA' HR' HK' DI' HFD' HFS' HSRC HFRM. subst vals' E'.
    rewrite HL in HL', HA', HR'. change (72 + 10)%nat with 82%nat in HA'.
    change (sr_after_call_j srRDA (map ridx c_kept) 72) with srRA0 in HR'.
    change (keep_readA MSO [(48%nat, 65536)] [] knLPA) with knRA in HK'.
    assert (Ebs : bs = firstn (Z.to_nat want) (skipn (Z.to_nat len) fdata)) by (subst bs; apply file_read_litA; lia).
    assert (Hnb : Z.of_nat (length bs) = Z.min want (LEN - len)) by (rewrite Ebs; unfold LEN; apply length_readA; lia).
    clearbody bs. set (nb := Z.of_nat (length bs)) in *.
    rewrite len_word_Z in HA', HFD'. fold nb in HA', HFD'.
    assert (MF' : m_fds model' = fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + nb)))).
    { rewrite HFD', MF, fds_ins3A. f_equal. f_equal. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
    assert (MS' : m_fs model' = fs0) by (rewrite HFS'; exact MS).
    assert (HC1 : rdn ASEGS M' (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
    { rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HFRM; unfold MSO, STAGE; lia. }
    set (vals2 := vals ++ junk_vals R') in *.
    change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
    assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (XV : hdr_valsA vals2) by (subst vals2; apply hdr_appA; [exact HV | rewrite HL; lia]).
    assert (X38 : vals_ev vals2 38 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P38).
    assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
    assert (X70 : vals_ev vals2 70 = Z_to_bv 64 len) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    clear HR HK DI HC MF MS HFD' HFS' HFRM HDEF. clear M model.
    destruct (Z.eq_dec nb 0) as [Hz0 | Hnz].
    - (* [comment removed for export] *)
      assert (HlenL : len = LEN) by lia.
      assert (HKf : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model') M') knRf0A).
      { constructor; [|exact HK']. cbn [kentry_ok edenot ev ENVA]. rewrite HA', u_small by lia. lia. }
      clear HK'.
      drv_block0 HIok Hsp DL HR' HKf DI' X0 scr0 104%nat.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF' in F1. rewrite MS' in F2.
      assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
          apply (content_block0 vals2 _ A M' M model' lg A1 (CAPk k) (length fdata) fdata X0 ltac:(vm_compute; reflexivity) EQM EQH HZ) end; [unfold LEN in *; lia|].
        rewrite HlenL in HC1. unfold LEN in HC1. rewrite Nat2Z.id, firstn_all in HC1. exact HC1. }
      clear EQM EQH SBM HR' HKf DI' HC1 MF' MS' HSRC. clear M' model'.
      (* [comment removed for export] *)
      eapply (rz_close_lz ASEGS scfg _ _ M model ECALLW (Z_to_bv 64 3)); try apply is_ecall_ECALLW.
      + vm_compute. reflexivity.
      + exact (di_halt _ _ _ _ _ _ _ _ _ _ DI).
      + regv HR (17%bv : reg). reflexivity.
      + regv HR (10%bv : reg). reflexivity.
      + rewrite u_small by lia. lia.
      + rewrite F1. apply fds_lookup3A.
      + rewrite v_addi_pc4 by lia. change (0x149d40 + 4) with 0x149d44.
        rewrite F1, fds_remove3A.
        set (model2 := with_fds fds0 model).
        assert (DI2 : dinvA [(A1, CAPk k)] LK0 cr A M model2).
        { apply (dinv_model scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ model model2 DI); [apply with_fds_vm| |apply with_fds_rdr].
          unfold model2. rewrite with_fds_halted'. exact (di_halt _ _ _ _ _ _ _ _ _ _ DI). }
        assert (HK2 : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model2) M) (cellCA :: knRf0A)) by exact HK.
        assert (G1 : m_fds model2 = fds0) by (unfold model2; apply with_fds_fds).
        assert (G2 : m_fs model2 = fs0) by (unfold model2; rewrite with_fds_fs; exact F2).
        pose proof (regs_set_a0 (ENVG vals2) _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR3.
        clearbody model2. clear HR HK DI F1 F2. clear model.
        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
          set (valsG := relayV vals2 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
          pose proof (credA_exit k cr Hk Hcr) as [HX1 HX2];
          pose proof (HKC ltac:(lia) (CAPk k) cr ltac:(lia) ltac:(lia) HX1 HX2) as CL;
          unfold close_kgA in CL;
          apply (CL valsG Rc M model2 A A1)
        end.
        * reflexivity.
        * unfold valsG. apply hdr_relayA. exact XV.
        * unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact X48.
        * unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite X70. f_equal. lia.
        * unfold valsG, ENVA. relay_regs HR3.
        * intros lo hi Hlh. unfold knGA. constructor.
          -- cbn [kentry_ok edenot ev ENVA]. unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite X70, u_small by lia. lia.
          -- eapply ksubl_sound; [| exact knGbaseA_sub]. apply Forall_app. split.
             ++ apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsG _ [(A1, CAPk k)] LK0 cr A M model2 48%nat A1 (CAPk k) 65536 DI2);
                  [left; reflexivity | lia | | unfold valsG; rewrite relayV_lo by lia; exact X0].
                unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact X48.
             ++ unfold valsG, ENVA. eapply relay_know6; [exact HK2 | vm_compute; reflexivity | vm_compute; reflexivity].
        * exact HC2.
        * exact DI2.
        * exact HINC.
        * exact G1.
        * exact G2.
    - (* [comment removed for export] *)
      assert (HKe : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model') M') knRe0A).
      { constructor; [|exact HK']. cbn [kentry_ok edenot ev ENVA]. rewrite HA', u_small by lia. lia. }
      clear HK'.
      drv_block0 HIok Hsp DL HR' HKe DI' X0 scr0 104%nat.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF' in F1. rewrite MS' in F2.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
      { rewrite <- HC1. apply rdn_agree. intros j Hj. apply EQA. }
      assert (HSRC2 : rdn ASEGS M (Z_to_bv 64 STAGE) (Z.to_nat nb) = Some bs).
      { unfold nb. rewrite Nat2Z.id. rewrite <- HSRC. apply rdn_agree. intros j Hj. apply EQA. }
      clear EQM EQH EQA SBM HR' HKe DI' HC1 MF' MS' HSRC. clear M' model'.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
      eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R0 M model [(A1, CAPk k)] LK0 cr A A1 (CAPk k) (A1 + len) STAGE nb bs
                MSO [] [] 0xaeaac K) end end;
        [ exact HR | exact HK
        | rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
        | exact X0 | vm_compute; reflexivity
        | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
        | unfold MSO; lia | reflexivity
        | regv HR (10%bv : reg); cbn [edenot ev ENVA]; rewrite X48, X70, alu_add_Z; reflexivity
        | regv HR (11%bv : reg); reflexivity
        | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact HA'
        | lia
        | regv HR (4%bv : reg); reflexivity
        | regv HR (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DI
        | left; reflexivity | lia | lia
        | apply (src_stage_aacc scfg L ar IL HI sp0 Hsp DL ICok ILY _ _ _ _ _ _ _ STAGE nb (di_inv _ _ _ _ _ _ _ _ _ _ DI)); unfold STAGE; lia
        | unfold STAGE; lia | unfold STAGE; lia
        | apply (src_stage_app_rng L ar IL sp0 Hsp DL); unfold STAGE; lia
        | intros i Hi; left; unfold STAGE; lia
        | exact HSRC2
        | unfold STAGE; lia
        | intros i nb0 Hf; discriminate
        | intros v b Hf; discriminate
        | exact HK0
        | ].
      intros R2 M2 model2 vals' E' HL2 HR2 HK2 DI2 HRT2 HDST HBLK HIMG. subst vals' E'.
      rewrite HL' in HL2, HR2. change (72 + 32 + 32)%nat with 136%nat in HL2.
      change (sr_after_call_j _ (map ridx c_kept) (72 + 32)) with srRm0 in HR2.
      change (keep_allocA MSO 4096 [] [] _) with knRm0 in HK2.
      destruct (model_rt_fds _ _ HRT2) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      assert (HC3 : rdn ASEGS M2 (Z_to_bv 64 A1) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
      { replace (Z.to_nat (len + nb)) with (Z.to_nat len + length bs)%nat by lia.
        rewrite <- firstn_app_skipnA.
        replace (firstn (length bs) (skipn (Z.to_nat len) fdata)) with bs by (rewrite Ebs at 1; rewrite Ebs at 1; symmetry; apply firstn_len_firstnA).
        apply rdn_app_Z; [ | | lia | lia].
        - rewrite <- HC2. apply rdn_agree. intros j Hj. rewrite u_small by lia.
          apply HBLK; [lia | exists (A1, CAPk k); split; [left; reflexivity | cbn [fst snd]; lia] | lia].
        - rewrite Z2Nat.id by lia. unfold nb in HDST. rewrite Nat2Z.id in HDST. exact HDST. }
      set (vals3 := vals2 ++ junk_vals R2) in *.
      change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR2, HK2.
      assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
      assert (YV : hdr_valsA vals3) by (subst vals3; apply hdr_appA; [exact XV | rewrite HL'; lia]).
      assert (Y38 : vals_ev vals3 38 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X38).
      assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
      assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 len) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
      assert (Y82 : vals_ev vals3 82 = Z_to_bv 64 nb) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA').
      clear HR HK DI HC2 HSRC2 HDST HBLK HIMG F1 F2 HRT2. clear M model R0.
      (* [comment removed for export] *)
      drv_block0 HIok Hsp DL HR2 HK2 DI2 Y0 scr0 136%nat.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (HC4 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
      { rewrite <- HC3. apply rdn_agree. intros j Hj. apply EQA. }
      lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        set (valsL := relayV vals3 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
        apply (IH k (len + nb) A1 valsL Rc M model A cr)
      end.
      + lia.
      + lia.
      + lia.
      + lia.
      + reflexivity.
      + unfold valsL. apply hdr_relayA. exact YV.
      + unfold valsL. rewrite relayV_38. unfold gr. regv1 HR. exact Y38.
      + unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact Y48.
      + unfold valsL. rewrite relayV_70. unfold gr. regv1 HR. rewrite Y70, Y82, alu_add_Z. reflexivity.
      + unfold valsL, ENVA. relay_regs HR; try (relay2 HR; reflexivity).
      + rewrite knLPA_split. apply Forall_app. split.
        * apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsL _ [(A1, CAPk k)] LK0 cr A M model 48%nat A1 (CAPk k) 65536 DI);
            [left; reflexivity | lia | | unfold valsL; rewrite relayV_lo by lia; exact Y0].
          unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact Y48.
        * unfold valsL, ENVA. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
      + exact HC4.
      + exact DI.
      + exact HINC.
      + split; [exact F1 | exact F2].
      + exact Hcr.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_stepA : forall z, rd_atA z -> lp_atA z.
  Proof.
    intros z HRD. unfold lp_atA.
    intros k len A1 vals R M model A cr Hk Hlen HlL Hz HL HV P38 P48 P70 HR HK HC DI HINC HMD Hcr.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (CAPk_range k Hk) as HCk.
    destruct (inv_block1 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as (P0 & P1 & P2 & P3).
    destruct HCOST as (Hkpm & Hlin & Hovh).
    destruct (Z_lt_le_dec len (CAPk k)) as [Hlt | Hge].
    - (* [comment removed for export] *)
      pose proof (know_LP_rangesA vals _ len (CAPk k) 0 67108863 65536 67108864 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
      change (KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLPA) with knLPpA in HK1.
      clear HK. rename HK1 into HK.
      assert (TAIL : forall want R1 M1 (model1 : Model) (sc12 : expr),
                 want = Z.min (CAPk k - len) 65536 ->
                 regs_ok (ENVG vals) (sr_upd srPa (ridx 12) sc12) R1 -> edenot (ENVG vals) sc12 = Z_to_bv 64 want ->
                 know_ok ASEGS (ENVG vals) (mrestrict (ahid A model1) M1) knLPpA ->
                 (forall a : word, M1 a = M a) -> dinvA [(A1, CAPk k)] LK0 cr A M1 model1 -> mdl3 model1 len ->
                 srealizes ASEGS scfg (mkCfg (mkst R1 (Z_to_bv 64 0x6a2b8) M1 (seg_rom ASEGS)) model1) K).
      { intros want R1 M1 model1 sc12 Hwant HR1 H12 HK1 EQA DI1 HMD1.
        assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
        { rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
        set (valsR := relayV vals R1 (gr R1 21) (gr R1 9) (gr R1 19) [gr R1 12]).
        apply (HRD k len want A1 valsR R1 M1 model1 A cr); [lia | lia | lia | lia | exact Hwant | reflexivity | | | | | | | | exact HC1 | exact DI1 | exact HINC | exact HMD1 | exact Hcr].
        + unfold valsR. apply hdr_relayA. exact HV.
        + unfold valsR. rewrite relayV_38. unfold gr. regv1 HR1. exact P38.
        + unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
        + unfold valsR. rewrite relayV_70. unfold gr. regv1 HR1. exact P70.
        + unfold valsR. rewrite relayV_71. unfold gr. regv1 HR1. exact H12.
        + unfold valsR, ENVA. relay_regs HR1; try (relay2 HR1; reflexivity).
        + rewrite knLPA_split. apply Forall_app. split.
          * apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(A1, CAPk k)] LK0 cr A M1 model1 48%nat A1 (CAPk k) 65536 DI1);
              [left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact P0].
            unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
          * unfold valsR, ENVA. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity]. }
      destruct (Z_lt_le_dec (CAPk k - len) 65536) as [Hsmall | Hbig].
      + (* [comment removed for export] *)
        drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false; true] [] []) 71%nat.
        { apply (sc_ltu_wantA vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.ltb_lt; lia]. }
        { apply (sc_eq_70_38A vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
        apply (TAIL (CAPk k - len) R0 M1 model0 want_xA); [lia | exact HR0 | apply (want_x_valA vals len (CAPk k) P70 P38); lia | exact HK1
                                                         | exact (block_nolog _ _ _ _ _ EQM EQH) | exact DI0 |].
        destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). split; [rewrite F1; exact MF | rewrite F2; exact MS].
      + (* [comment removed for export] *)
        drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false; false] [] []) 71%nat.
        { apply (sc_ltu_wantA vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.ltb_ge; lia]. }
        { apply (sc_eq_70_38A vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
        apply (TAIL 65536 R0 M1 model0 (ELit 65536)); [lia | exact HR0 | reflexivity | exact HK1
                                                         | exact (block_nolog _ _ _ _ _ EQM EQH) | exact DI0 |].
        destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). split; [rewrite F1; exact MF | rewrite F2; exact MS].
    - (* [comment removed for export] *)
      assert (Heq : len = CAPk k) by lia.
      destruct (Z.eq_dec k 10) as [Hk10 | Hk10].
      + (* [comment removed for export] *)
        assert (HC10 : CAPk k = 67108864) by (rewrite Hk10; reflexivity).
        assert (Hl10 : len = 67108864) by lia.
        rewrite Hl10 in P70, HMD. rewrite HC10 in P38, DI.
        apply (HREF ltac:(lia) A1 vals R M model A cr); assumption.
      + (* [comment removed for export] *)
        pose proof (CAPk_lt10 k ltac:(lia)) as HC25.
        pose proof (know_LP_rangesA vals _ len (CAPk k) 65536 33554432 65536 33554432 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
        change (KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLPA) with knLPgA in HK1.
        clear HK. rename HK1 into HK.
        drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 71%nat.
        { apply (sc_eq_70_38A vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.eqb_eq; lia]. }
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). rewrite MF in F1. rewrite MS in F2.
        assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
        { rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
        clear EQM EQH EQA SBM HR HK DI HC MF MS HDEF. clear M model R.
        (* [comment removed for export] *)
        lazymatch type of HR0 with regs_ok _ ?sr _ => lazymatch type of HK1 with know_ok _ _ _ ?kn =>
        eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ sr kn R0 M1 model0 [(A1, CAPk k)] LK0 cr A (2 * CAPk k) MSO
                  [(48%nat, 65536)] [] 0xaead4 K) end end;
          [ exact HR0 | exact HK1
          | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
          | exact P0 | vm_compute; reflexivity
          | regv HR0 (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
          | unfold MSO; lia | reflexivity
          | regv HR0 (10%bv : reg); rewrite Heq in P70; apply (cap2_x_valA vals (CAPk k) P70); lia
          | lia
          | destruct Hcr as [Hc1 Hc2]; unfold acredit_ok; split; nia
          | regv HR0 (4%bv : reg); reflexivity
          | regv HR0 (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact DI0
          | intros i nb Hf; cbn in Hf;
            destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                             rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
          | intros v b Hf; discriminate
          | exact HK0 | ].
        intros R' M' model' A' u vals' E' HL' HA2 HR' HK' DI' HRT HINC' HBR2 HAP HSHB HAB HBLK HIMG. subst vals' E'.
        set (vals2 := vals ++ junk_vals R') in *.
        change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
        rewrite HL in HL', HA2, HR', HK'. change (71 + 10)%nat with 81%nat in HA2, HK'. change (71 + 32)%nat with 103%nat in HL'.
        destruct (model_rt_fds _ _ HRT) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
        pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U3). pose proof HBR2 as (_ & _ & U4 & _ & _).
        assert (NEQ : u <> A1).
        { specialize (HAP (A1, CAPk k) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
        assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (XV : hdr_valsA vals2) by (subst vals2; apply hdr_appA; [exact HV | rewrite HL; lia]).
        assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
        assert (X70 : vals_ev vals2 70 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); rewrite <- Heq; exact P70).
        (* [comment removed for export] *)
        apply Forall_app in HK' as [HKB HK'].
        assert (HKU : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A' model') M') knGb0).
        { change knGb0 with (kn_blk2A 81 ++ keepalloc_G knLPgA). apply Forall_app. split.
          - unfold kn_blk2A. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVA]; rewrite HA2, u_small by lia; lia.
          - exact HK'. }
        clear HK' HKB HK1 HR0.
        assert (HC2 : rdn ASEGS M' (Z_to_bv 64 A1) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- Heq, <- HC1. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply HBLK; [lia|].
          exists (A1, CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
        clear HC1 DI0 HBLK HIMG HAB F1 F2 HRT. clear M1 model0 R0.
        (* [comment removed for export] *)
        drv_block0 HIok Hsp DL HR' HKU DI' X0 scr0 103%nat.
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
        assert (HC3 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HC2. apply rdn_agree. intros j Hj. apply EQA. }
        clear EQM EQH EQA SBM HR' HKU DI' HC2 G1 G2 HSHB. clear M' model'.
        assert (HFL : length (firstn (Z.to_nat (CAPk k)) fdata) = Z.to_nat (CAPk k)) by (rewrite length_firstn; unfold LEN in HlL; lia).
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
        eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R M model [(u, 2 * CAPk k); (A1, CAPk k)] LK0
                  (adebit L cr (2 * CAPk k)) A' u (2 * CAPk k) u A1 (CAPk k) (firstn (Z.to_nat (CAPk k)) fdata) MSO [(48%nat, 65536)] [] 0xaeaf0 K) end end;
          [ exact HR | exact HK
          | rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
          | exact X0 | vm_compute; reflexivity
          | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
          | unfold MSO; lia | reflexivity
          | regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact HA2
          | regv HR (11%bv : reg); cbn [edenot ev ENVA]; exact X48
          | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact X70
          | lia
          | regv HR (4%bv : reg); reflexivity
          | regv HR (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact DI
          | left; reflexivity | lia | lia
          | apply (src_blk_aacc scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 (CAPk k) A1 (CAPk k) (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
          | lia | lia
          | apply (src_blk_app_rng scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 (CAPk k) A1 (CAPk k) (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
          | intros i Hi; right; exists (A1, CAPk k); split; [right; left; reflexivity | cbn [fst snd]; lia]
          | exact HC3
          | specialize (HAP (A1, CAPk k) ltac:(left; reflexivity)); cbn [fst snd] in HAP; lia
          | intros i nb Hf; cbn in Hf;
            destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL'; lia|];
                                             rewrite X48, u_small by lia; rewrite lb_remove_hdA; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
          | intros v b Hf; discriminate
          | exact HK0
          | ].
        intros R3 M3 model3 vals' E' HL3 HR3 HK3 DI3 HRT3 HDST HBLK3 HIMG3. subst vals' E'.
        rewrite HL' in HL3, HR3. change (103 + 32)%nat with 135%nat in HL3.
        change (sr_after_call_j _ (map ridx c_kept) 103) with srGc0 in HR3.
        change (keep_allocA MSO 4096 [(48%nat, 65536)] [] _) with knGc0 in HK3.
        destruct (model_rt_fds _ _ HRT3) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
        set (vals3 := vals2 ++ junk_vals R3) in *.
        change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR3, HK3.
        assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
        assert (YV : hdr_valsA vals3) by (subst vals3; apply hdr_appA; [exact XV | rewrite HL'; lia]).
        assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
        assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
        assert (Y81 : vals_ev vals3 81 = Z_to_bv 64 u) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
        clear HR HK DI HC3 HBLK3 HIMG3 F1 F2 HRT3. clear M model R.
        (* [comment removed for export] *)
        drv_block0 HIok Hsp DL HR3 HK3 DI3 Y0 scr0 135%nat.
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
        assert (HC4 : rdn ASEGS M (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HDST. apply rdn_agree. intros j Hj. apply EQA. }
        clear EQM EQH EQA SBM HR3 HK3 DI3 HDST G1 G2. clear M3 model3.
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
        eapply (afree_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals3 _ sr kn R M model [(u, 2 * CAPk k); (A1, CAPk k)] LK0
                  (adebit L cr (2 * CAPk k)) A' A1 (CAPk k) MSO [] [] 0xaeaf8 K) end end;
          [ exact HR | exact HK
          | rewrite HL3; vm_compute; reflexivity | rewrite HL3; vm_compute; reflexivity | rewrite HL3; lia
          | exact Y0 | vm_compute; reflexivity
          | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite Y0; apply alu_add_w_litA
          | unfold MSO; lia | reflexivity
          | right; left; reflexivity
          | regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact Y48
          | regv HR (4%bv : reg); reflexivity
          | regv HR (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact DI
          | intros i nb Hf; discriminate
          | intros v b Hf; discriminate
          | exact HK0 | ].
        intros R4 M4 model4 A4 vals' E' HL4 HR4 HK4 DI4 HRT4 HINC4 HAB4 HBLK4 HIMG4. subst vals' E'.
        rewrite (lb_remove_2A u (2 * CAPk k) A1 (CAPk k) NEQ) in DI4, HBLK4.
        rewrite HL3 in HL4, HR4. change (135 + 32)%nat with 167%nat in HL4.
        change (sr_after_call_j _ (map ridx c_kept) 135) with srGd0 in HR4.
        change (keep_allocA MSO 4096 [] [] _) with knGd0 in HK4.
        destruct (model_rt_fds _ _ HRT4) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
        set (vals4 := vals3 ++ junk_vals R4) in *.
        change (Env (vals_ev vals4) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals4) in HR4, HK4.
        assert (W0 : vals_ev vals4 0 = sp0) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y0).
        assert (WV : hdr_valsA vals4) by (subst vals4; apply hdr_appA; [exact YV | rewrite HL3; lia]).
        assert (W70 : vals_ev vals4 70 = Z_to_bv 64 (CAPk k)) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y70).
        assert (W81 : vals_ev vals4 81 = Z_to_bv 64 u) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y81).
        assert (HC5 : rdn ASEGS M4 (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HC4. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HBLK4; [lia|].
          exists (u, 2 * CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
        clear HR HK DI HC4 HBLK4 HIMG4 HAB4 F1 F2 HRT4. clear M model R.
        (* [comment removed for export] *)
        drv_block0 HIok Hsp DL HR4 HK4 DI4 W0 scr0 167%nat.
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
        assert (HC6 : rdn ASEGS M (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HC5. apply rdn_agree. intros j Hj. apply EQA. }
        (* [comment removed for export] *)
        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
          set (valsR := relayV vals4 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
          apply (HRD (k + 1) len 65536 u valsR Rc M model A4 (adebit L cr (2 * CAPk k)))
        end.
        * lia.
        * rewrite CAPk_S by lia. lia.
        * lia.
        * lia.
        * rewrite CAPk_S by lia. lia.
        * reflexivity.
        * unfold valsR. apply hdr_relayA. exact WV.
        * unfold valsR. rewrite relayV_38. unfold gr. regv1 HR. change (nth 21 srGd (ELit 0)) with cap2_xA.
          rewrite CAPk_S by lia. apply (cap2_x_valA vals4 (CAPk k) W70); lia.
        * unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
        * unfold valsR. rewrite relayV_70. unfold gr. regv1 HR. rewrite Heq. exact W70.
        * unfold valsR. rewrite relayV_71. unfold gr. regv1 HR. reflexivity.
        * unfold valsR, ENVA. relay_regs HR; try (relay2 HR; reflexivity).
        * rewrite knLPA_split. apply Forall_app. split.
          -- apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(u, 2 * CAPk k)] LK0 (adebit L cr (2 * CAPk k)) A4 M model 48%nat u (2 * CAPk k) 65536 DI);
               [left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact W0].
             unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
          -- unfold valsR, ENVA. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
        * rewrite Heq. exact HC6.
        * rewrite CAPk_S by lia. exact DI.
        * intros x Hx. apply HINC4. apply HINC'. apply HINC. exact Hx.
        * split; [exact F1 | exact F2].
        * destruct Hcr as [Hc1 Hc2]. unfold credA, adebit. cbn [fst snd]. rewrite CAPk_S by lia. split; nia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_okA : forall n : nat, lp_atA (Z.of_nat n).
  Proof.
    induction n as [|n IH].
    - apply loop_stepA. apply read_okA. unfold lp_atA. intros. exfalso. lia.
    - apply loop_stepA. apply read_okA. replace (Z.of_nat (Datatypes.S n) - 1) with (Z.of_nat n) by lia. exact IH.
  Qed.

  (* [comment removed for export] *)
  Variable cr0 : credit.
  Hypothesis Hcr0 : credA 0 (adebit L cr0 65536).

  Theorem drv_fileA : file_kA scfg L ar HI sp0 path fs0 fdata auxvp p1 can M0 LK0 cr0 A0 K.
  Proof.
    unfold file_kA.
    intros vals R M model A A1 HL P0 P1 P2 P3 P48 HR HK DI HINC MF MS HBR.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    assert (HV : hdr_valsA vals) by (unfold hdr_valsA; repeat split; assumption).
    change (Na0DrvA.ENVA fdata vals) with (ENVG vals) in HR, HK.
    (* [comment removed for export] *)
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 70%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF in F1. rewrite MS in F2.
    pose proof (read_okA (LEN + 1) ltac:(replace (LEN + 1 - 1) with (Z.of_nat (length fdata)) by (unfold LEN; lia); apply loop_okA)) as RD.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      set (valsR := relayV vals Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
      apply (RD 0 0 65536 A1 valsR Rc M1 model0 A (adebit L cr0 65536))
    end.
    - lia.
    - unfold CAPk. rewrite Z.pow_0_r. lia.
    - unfold LEN. lia.
    - unfold LEN. lia.
    - unfold CAPk. rewrite Z.pow_0_r. reflexivity.
    - reflexivity.
    - unfold valsR. apply hdr_relayA. exact HV.
    - unfold valsR. rewrite relayV_38. unfold gr. regv1 HR0. unfold CAPk. rewrite Z.pow_0_r. reflexivity.
    - unfold valsR. rewrite relayV_48. unfold gr. regv1 HR0. exact P48.
    - unfold valsR. rewrite relayV_70. unfold gr. regv1 HR0. reflexivity.
    - unfold valsR. rewrite relayV_71. unfold gr. regv1 HR0. reflexivity.
    - unfold valsR, ENVA. relay_regs HR0; try (relay2 HR0; reflexivity).
    - rewrite knLPA_split. apply Forall_app. split.
      + apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(A1, 65536)] LK0 (adebit L cr0 65536) A M1 model0 48%nat A1 65536 65536 DI0);
          [left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact P0].
        unfold valsR. rewrite relayV_48. unfold gr. regv1 HR0. exact P48.
      + unfold valsR, ENVA. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity].
    - reflexivity.
    - unfold CAPk. rewrite Z.pow_0_r. exact DI0.
    - exact HINC.
    - split; [exact F1 | exact F2].
    - exact Hcr0.
  Qed.
End DrvG.
End FPX_1.
End Na0DrvG.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.
Module Na0DrvLibInit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefPrintfLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvLibInit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Definition LIBINIT_KN : list kentry :=
  [KImg 65536 1409024; KImg 6889681 6889684; KImg 6889685 6896176; KImg 1422544 1422712; KImg 7028168 7028216;      (* [comment removed for export] *)
   KWord (SA (ELit 0) 7027520) 8 (EVar 3); KWord (SA (ELit 0) 6896184) 8 (ELit 6896184); KWord (SA (ELit 0) 6896216) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 6896368) 8 (EVar 3); KWord (SA (ELit 0) 6896336) 8 (ELit 7028168); KWord (SA (ELit 0) 7028120) 8 (EVar 5);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 7027536) 1 (ELit 0); KWord (SA (ELit 0) 7027540) 4 (ELit 0); KWord (SA (ELit 0) 7027544) 4 (ELit 2); KWord (SA (ELit 0) 7027552) 8 (ELit 7027560);
   KWord (SA (ELit 0) 7027560) 8 (ELit 0); KWord (SA (ELit 0) 7027568) 8 (ELit 1277044); KWord (SA (ELit 0) 7027824) 8 (ELit 648332);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 7027576) 8 (ELit 1277044); KWord (SA (ELit 0) 7027832) 8 (ELit 716372);
   KWord (SA (ELit 0) 7028115) 1 (ELit 0); KWord (SA (ELit 0) 7028336) 4 (ELit 0)].
(* [comment removed for export] *)
Definition LIBINIT_IMG : list (Z * Z) := [(65536, 1409024); (6889681, 6889684); (6889685, 6896176); (1422544, 1422712); (7028168, 7028216)].

(* [comment removed for export] *)
Definition INIT_CELLS_A : list (Z * Z * Z) :=
  [(7027536, 1, 0); (7027540, 4, 0); (7027544, 4, 2); (7027552, 8, 7027560); (7027560, 8, 0); (7027568, 8, 1277044); (7027824, 8, 648332);
   (7028115, 1, 0); (7028336, 4, 0); (7027576, 8, 1277044); (7027832, 8, 716372)].

(* [comment removed for export] *)
Record drv_lib_cellsA (Lay : lib_layoutA) : Prop := DRV_LIB_CELLSA {
  dlc_td_self : lla_td_self Lay = 0x693a38;  dlc_td_tid : lla_td_tid Lay = 0x693a58;  dlc_td_canary : lla_td_canary Lay = 0x693af0;
  dlc_td_locale : lla_td_locale Lay = 0x693ad0;  dlc_locale : lla_locale Lay = 0x6b3dc8;  dlc_guard : lla_guard Lay = 0x6b3b40;
  dlc_auxvp : lla_auxvp Lay = 0x6b3d98;  dlc_phdr : lla_phdr Lay = 0x10040;  dlc_phent : lla_phent Lay = 56;  dlc_phnum : lla_phnum Lay = 11;
  dlc_init_img : forall iv, In iv (lla_init_img Lay) -> exists lo hi, In (lo, hi) LIBINIT_IMG /\ lo <= fst iv /\ snd iv <= hi;
  (* [comment removed for export] *)
  dlc_rw_lo : lla_rw_lo Lay <= 0x15b690;
  dlc_initc : forall iv, In iv (lla_initc Lay) -> 0 <= fst iv /\ snd iv <= 0x6b6000 /\ (snd iv <= 0x15b690 \/ 0x15b778 <= fst iv) /\ (snd iv <= 0x6b4320 \/ 0x6b4720 <= fst iv)
                                                /\ (snd iv <= 0x6920d4 \/ 0x6920d5 <= fst iv);
  (* [comment removed for export] *)
  dlc_init_cells : lla_init_cells Lay = INIT_CELLS_A
}.

Lemma locale_imgA : forall k, (k < 6)%nat ->
  rdn ASEGS (fun _ => None) (Z_to_bv 64 (0x6b3dc8 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvLibInit ()) [] "p'0h02Hkh11kh24__p1h34__x1h43Hk0h57__arithh64__ffh78__varmaph85__with94cstrh:1xi001np;1p;2p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0p1005gp4p710R9p8P0p1006Gp4p710R0p8p1006dp4p70R:P1p8P:P2p8P:P3p8P:p1007TR;p4p710p8P:P;p4p7210p8P:P5p8P:P4p8P:P7p8P:P8p8p10081p4p710R:P3p8P:P7p8p1008Np4p70R:P1p8P:P2p8P:p1009<p4p7210p8P:P3p8P:p1009Xp4p7210p8P:P5p8P:P4p8P:P6p8P:P7p8P:p100:Gp4p7210p8P:P8p8P:p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R:P1p8P:P2p8P:P5p8P:P4p8P:P8p8p100=Ap4p710R:P3p8P:p100>Gp4p710R6p8P:P7p8P:P0p8P:p100>fp4p710R:p8p100?Ep4p710R0P6p8P0P7p8P0p100@Lp4p710p8P0P9p8P0P:p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P:P3p8P:P7p8g00B?R7j10Tg00B^R:j21Tg00C6j14Tg00C[j1LTg00D9j1KTg00D\j1FTg00E<j1VTg00E^j1BTg00F@j12Tg00Fej1<Tg00GCR3j1;Tg00Gcj2HTg00H@j2?Tg00Hfj2aTg00Inj2GTg00JPj2XTg00KCj3WTg00Kfj1ETg00LFj35Tg00Lfj2=Tg00M@R8j2DTg00M\j2:Tg00N9j4TTg00N`j1STg00OEj2ATg00Oaj2RTg00P?j1QTg00P]j1PTg00QHj2>Tg00Qkj2OTg00RNj4CTg00S9j6NTg00S]j2cTg00T?j2bTg00Tkj3@Tg00UEj3`Tg00Udj4_Tg00VVj4ITg00WGl<[Tg00Wll<\Tg00XQj7YTg00Y5j3]Tg00YXj8^Tf0R0#4#4p=9f6R4g00Z<R5f5R2f4R1f3R9f2R6':'?f1R;CI;@0p=Zf7P5P4%;6,H9,:1,?2P;CI;@0p=31:6;/:0p=6g00[QR4P4g00\0R5P5P7P3P3P9g00\NP6P;P0M<[p=7P4P5P:P3P8g00]2P2P1P9P6P;P0M<\p=UP;g00]TR2g00^3R8P8g00^SR3P0g00_3FYp=JA]5;0p=8P9P2P8P8P3P6P;P0G^p=Mg00_SR:#0R7#0R<#0R=#0R>#0R?#0R@,10RAP4g00`2RB#4#9RC#LRD#KRE#FRF#VRG%4C#9#LRH#K%BEURIPH%2B#4#2#4#2#2#9#2#2#2#2#4#2#2#2#9#2#4#9#<RJ%<CRC%;;RK'H%0@#0RLg00`WRM,?H,aL,GFRNFZ^0AP;11:@1XDM9WDMRD%EE95ED95ED95ED95ED95ED95ED95ED55E,GF,=GRFPGPIPHPJPCP:PLPNG3dW0%00R:/1@REP4PGPIPHPJPC%0;RDPLPNG3^0EP;117@PFPGPIPHPJPCP7PLPNG3dW0%0:R:/1@R7P4PGPIPHPJPC%0DREPLPNG3^07P;11<@PFPGPIPHPJPCP<PLPNG3dW0%0:R:/1@R<P4PGPIPHPJPC%0ER7PLPNG3^0<P;11=@PFPGPIPHPJPCP=PLPNG3dW0%0:R:/1@R=P4PGPIPHPJPC%07R<PLPNG3^0=P;11>@PFPGPIPHPJPCP>PLPNG3dW0%0:R:/1@R>P4PGPIPHPJPC%0<R=PLPNG3^0>P;11?@PFPGPIPHPJPCP?PLPNG3dW0%0:/1@%0=R:/1@%<BR?=6K??6???6??%2B#4#<RF'DR>P:1:0?X:5R:P:P:P:P:P:PKO1RAO1ROO1RPO1RQO1RRO1P:P=PRP:P<PQP:P7PPP:PEPOP:PDPAP:P;PK1=5KC7C7C7C7C7C7P@PF1=5FEUP0CTP>%S6%;6,AMp-0R>g00a5R@#E%F@1R5;%Q5%P5R@P51>5Mg00aa1O5BRBCC,J@%B8RKP@P51>5?R:,8B/8:/8:/8:/8:/8:g00bH1>5FCC,J@PKP@P2P8P8P3P9ENCMCM1c@3P0P6g00boR@g00cOR3'=1b06=@@3dA`5M;C_b6b7b8X35W21AM0A6;???6???6??/DFP9[[^35^2>P0PGPIPHPJPC%01#0#0#0#0#0PLPNG3%;1P;P6O4b5b9b4W0X14P0O1n0110000020111100P0O1W0X14P0O1n0110000020111100P0O1W0X14P0O1n0110000020111100P0O1W0X14P0O1n0110000020111100P0O1W0X14P0O1n0110000020111100P0O1W0X14P0O1n0110000020111100P0O1W0X14o"). Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibInit.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable M0 : word -> option byte.
  Variable Lay : lib_layoutA.
  Hypothesis LayL : lla_L Lay = L.
  Hypothesis DLC : drv_lib_cellsA Lay.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).

  Theorem lib_init_at_call : forall vals ebs kn LB LK cr A M (model : Model) (auxvp : word),
    know_ok ASEGS (Env (vals_ev vals) ebs) (mrestrict (ahid A model) M) kn ->
    forallb (fun K => existsb (kentry_eqb K) kn) LIBINIT_KN = true ->
    vals_ev vals 5 = auxvp ->
    dinvA LB LK cr A M model -> auxv_atA sp0 auxvp M0 ->
    exists av uid rnd tid canary hw, lib_init_factsA Lay ar av uid rnd tid canary hw M.
  Proof.
    intros vals ebs kn LB LK cr A M model auxvp HK HB P5 D
      (uidz & rnd & hwz & la & ph & entry & gidw & ae & PA & PE & PN & AB & AW & AU & AH & AR1 & AR2 & AP & AP8).
    assert (C27 : (27 <= StackLayout.auxv_count (StackLayout.la_rseq la))%nat)
      by (unfold StackLayout.auxv_count; destruct (StackLayout.la_rseq la); lia).
    pose proof Hsp as Hsp'. set (E := Env (vals_ev vals) ebs) in *. set (MV := mrestrict (ahid A model) M) in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as (HOFF & _).
    rewrite forallb_forall in HB.
    assert (KB : forall K, In K LIBINIT_KN -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
    assert (FULLR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M (Z_to_bv 64 a) n = Some bs)
      by (intros a n bs Hr; exact (rdn_of_mrestrict ASEGS _ M HOFF n _ bs Hr)).
    assert (NONE : forall lo hi, In (KImg lo hi) LIBINIT_KN -> hi <= 0x6b6000 -> forall i, 0 <= lo -> lo <= i < hi -> M (Z_to_bv 64 i) = None).
    { intros lo hi Hin Hhi i Hlo Hi. pose proof (kimg_clear E MV kn lo hi HK (KB _ Hin) i Hi) as X. unfold MV, mrestrict in X.
      rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ i D ltac:(lia)) in X. exact X. }
    assert (KW : forall a (w : nat) v, In (KWord (SA (ELit 0) a) w v) LIBINIT_KN -> 0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
                 rdn ASEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v))).
    { intros a w v Hin Ha Hw. apply FULLR. exact (kword_lit sp0 E MV kn a w v HK (KB _ Hin) Ha Hw). }
    pose proof (KW 7027520 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CG.
    pose proof (KW 6896184 8%nat (ELit 6896184) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CS.
    pose proof (KW 6896216 4%nat (EVar 4) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CT.
    pose proof (KW 6896368 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CC.
    pose proof (KW 6896336 8%nat (ELit 7028168) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CL.
    pose proof (KW 7028120 8%nat (EVar 5) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CA.
    assert (TR : 1 <= bv_unsigned (vals_ev vals 4) <= 4194303).
    { pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold LIBINIT_KN; cbn [In]; tauto)) as Hb.
      apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
      pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev E] in X. exact X. }
    cbn [edenot ev E] in CG, CS, CT, CC, CL, CA. rewrite P5 in CA.
    exists (bv_unsigned auxvp), uidz, rnd, (bv_unsigned (vals_ev vals 4)), (bv_unsigned (vals_ev vals 3)), hwz.
    destruct DLC as [d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 dimg _ _ dcells].
    unfold lib_init_factsA. split.
    2:{
      rewrite dcells, LayL, (dla_segs _ _ _ _ DL). unfold INIT_CELLS_A.
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027536 1%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027540 4%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027544 4%nat (ELit 2) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027552 8%nat (ELit 7027560) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027560 8%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027568 8%nat (ELit 1277044) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027824 8%nat (ELit 648332) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7028115 1%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7028336 4%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027576 8%nat (ELit 1277044) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 7027832 8%nat (ELit 716372) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
      apply Forall_nil. }
    unfold lib_init_facts. cbn [lib_view ll_heap heap_view OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface.hl_segs hl_sptop ll_init_img ll_td_self ll_td_tid ll_td_locale ll_locale ll_td_canary ll_guard ll_auxvp ll_init_cells].
    rewrite LayL, (dla_segs _ _ _ _ DL), (dla_sptop _ _ _ _ DL), d1, d2, d3, d4, d5, d6, d7. unfold cellz.
    rewrite !Z_to_bv_bv_unsigned.
    split. { intros iv a Hiv Ha. destruct (dimg iv Hiv) as (lo & hi & Hin & H1 & H2).
             unfold LIBINIT_IMG in Hin. cbn [In] in Hin.
             destruct Hin as [X|[X|[X|[X|[X|[]]]]]]; injection X as <- <-;
               [apply (NONE 65536 1409024) | apply (NONE 6889681 6889684) | apply (NONE 6889685 6896176) | apply (NONE 1422544 1422712) | apply (NONE 7028168 7028216)];
               first [lia | (unfold LIBINIT_KN; cbn [In]; tauto)]. }
    split; [exact CS|]. split; [exact CT|]. split; [lia|]. split; [exact CL|].
    split. { intros k Hk. apply (img_cell M _ 8%nat _ (locale_imgA k Hk)); [lia | cbn; lia|].
             intros i Hi. apply (NONE 7028168 7028216); [unfold LIBINIT_KN; cbn [In]; tauto | lia | lia | cbn in Hi; lia]. }
    split; [exact CC|]. split; [exact CG|]. split; [pose proof (bv_unsigned_in_range _ (vals_ev vals 3)) as X; change (bv_modulus 64) with (2 ^ 64) in X; lia|].
    split; [exact CA|]. split; [lia|]. split; [lia|].
    split; [exact AP8|].
    (* LPS 727298f3: the launch's whole vector ([LibIface.auxv_launch]), the
       main entry's [auxv_atA] carried up from [M0] by [di_above] *)
    split. { unfold auxv_launch. exists la, ph, entry, gidw, ae.
             cbn [lib_view ll_phdr ll_phent ll_phnum]. rewrite d8, d9, d10.
             split; [exact PA|]. split; [exact PE|]. split; [exact PN|]. split; [exact AB|].
             intros j Hj. unfold cellz. apply (rdn_tr M0 M _ 8%nat _ (AW j Hj)); [lia | cbn; lia|].
             intros i Hi. apply (di_above _ _ _ _ _ _ _ _ _ _ D). cbn in Hi. lia. }
    repeat split; try lia. apply Forall_nil.
  Qed.
End LibInit.
End FPX_1.

End Na0DrvLibInit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
Module Na0DrvLibL.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvLibL () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic7f_equalK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula06I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs<IMG_CLIENT_AC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL9IMG_LIB_AC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL9LIB_HOLESC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC59OSSVerify5KrLib=SymExec2Sound4SX2S8ridx_injC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib=SymExec2Sound4SX2S:nth_sr_updC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lib_viewC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface7in_footC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface7ll_footC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL9dlla_footC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib7Mh_0126:Na0DrvLibL@not_foot_of_holeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib7Mh_0092:LibIfaceAB7in_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lla_junkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL9dlla_junkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL@not_junk_of_holeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00908LibIface8ls_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_01199Na0DrvLib:has_windowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_stackC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_emptyC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_0092:LibIfaceAB:lla_creditC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB:lla_framesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ff_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface5ls_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7find_nzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib7Mh_01199Na0DrvLib:sub_blockAC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL9keep_libAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lla_leakC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00908LibIface:credit_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_haltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_minvC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLibBdinv_stack_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL:dlla_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib>window_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx7aiob_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lib_preA00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lib_postA00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB5lla_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lib_cfgAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB9lla_entryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL6dlla_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8dla_segsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL:dlla_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB6lla_gpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL7dlla_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6dla_tpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z7add_modK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04I46Stdlib;setoid_ring<Ring_polynom3Pol00C59OSSVerify5KrLib7Mh_01199Na0DrvLib9dla_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ff_rsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK46Stdlib;setoid_ring<Ring_polynom5PExpr03C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_01199Na0DrvLib6STKTOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8di_stkshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_0092:LibIfaceAB8lib_preA01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_01059SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib@aclient_scr_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibLBnot_foot_off_imageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibLBnot_junk_off_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLibDregs_preserved_keptAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_0126:Na0DrvLibLAregs_ok_upd_sameAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL3CPlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3SCaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL=regions_callLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:vis_of_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA?know_keep_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8di_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib9stksh_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8hish_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7di_hishC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLibBhzA_of_block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3hzAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126:Na0DrvLibL;img_lib_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_clientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dla_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_countC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr05C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses6mkapp2C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6c_keptC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA;asan_layout00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I46Stdlib;setoid_ring<Ring_polynom3Mon00C59OSSVerify5KrLib7Mh_01199Na0DrvLib;c_kept_no0AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8IMG_RW_AC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition IMG_LIB_A : list (Z * Z) :=
  [(0x10000, 0x158000); (0x15b4b8, 0x15c3a0); (0x6820d0, 0x692100); (0x692108, 0x692330); (0x6931f0, 0x693a5c); (0x693a60, 0x693aa8);      (* [comment removed for export] *)
   (0x693ab0, 0x693af8); (0x693b14, 0x693b28); (0x693b30, 0x6b3b50); (0x6b3d70, 0x6b4fb8); (0x6b4fc0, 0x6b6000)].      (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_HOLES : list (Z * Z) := [(0x692100, 0x692108); (0x692330, 0x6931f0); (0x6b3b50, 0x6b3d70); (0x693a5c, 0x693a60)].      (* [comment removed for export] *)
Definition keep_libA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so sc bls vbnd [] IMG_LIB_A IMG_RW_A kn.
Lemma img_lib_sub : forall lo hi, In (lo, hi) IMG_LIB_A ->
  (exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi') /\ 0x10000 <= lo /\ hi <= 0x6b6000 /\ lo <= hi
  /\ forall hl hh, In (hl, hh) LIB_HOLES -> hi <= hl \/ hh <= lo.
Proof.
  intros lo hi Hin. unfold IMG_LIB_A in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
    (split; [first [ (exists 0x10000, 0x158000; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x15b4b8, 0x15c3a0; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x6820d0, 0x693aa8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x693ab0, 0x693af8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x693b14, 0x693b28; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x693b30, 0x6b4fb8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x6b4fc0, 0x6b6000; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]) ] |]);
    (split; [lia|]); (split; [lia|]); (split; [lia|]);
    intros hl hh Hh; unfold LIB_HOLES in Hh; cbn [In] in Hh; repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]); destruct Hh |]).
  destruct Hin.
Qed.

(* [comment removed for export] *)
Record drv_lib_layoutA (Lay : lib_layoutA) (L : asan_layout) : Prop := DRV_LIB_LAYOUTA {
  dlla_L : lla_L Lay = L;
  dlla_entry : lla_entry Lay = 0xaeecc;
  dlla_gp : lla_gp Lay = 0x10800;
  dlla_stack : 4096 <= lla_stack Lay <= 2 ^ 20 /\ lla_stack Lay mod 8 = 0;      (* [comment removed for export] *)
  dlla_empty : lla_empty Lay = 0x6920e0;                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  dlla_foot : forall iv, In iv (lla_foot Lay) -> exists hl hh, In (hl, hh) LIB_HOLES /\ hl <= fst iv /\ snd iv <= hh;
  (* [comment removed for export] *)
  dlla_junk : forall iv, In iv (lla_junk Lay) -> exists hl hh, In (hl, hh) LIB_HOLES /\ hl <= fst iv /\ snd iv <= hh;
  dlla_credit_pos : forall n, 0 <= n -> 0 <= fst (lla_credit Lay n) /\ 0 <= snd (lla_credit Lay n);
  (* [comment removed for export] *)
  dlla_frames : forall k, In k [0; 1; 2; 3; 4; 5] -> 0 <= lla_leak Lay k /\ 4 * lla_leak Lay k + lla_frames Lay k <= ff_cap k
}.

(* [comment removed for export] *)
Lemma regs_ok_upd_sameA : forall E sr R (rd : reg) e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = getr R rd -> regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd e HR Hrd He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r. symmetry. exact He.
    + specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibSite.
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
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Variable Lay : lib_layoutA.
  Variable LSt : lib_statics.
  Hypothesis DLL : drv_lib_layoutA Lay L.
  Hypothesis LIok : lib_call_okA Lay ar scfg HI LSt.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation LV := (lib_view Lay ar).

  #[using="L sp0 Hsp DLL"] Lemma not_foot_of_hole : forall a, (forall hl hh, In (hl, hh) LIB_HOLES -> ~ (hl <= a < hh)) -> ~ in_foot LV a.
  Proof.
    intros a Hn (iv & Hin & Hr). cbn [lib_view ll_foot] in Hin. destruct (dlla_foot Lay L DLL iv Hin) as (hl & hh & Hh & H1 & H2).
    apply (Hn hl hh Hh). lia.
  Qed.
  #[using="L sp0 Hsp DLL"] Lemma not_foot_off_image : forall a, ~ (0x6820d0 <= a < 0x6b6000) -> ~ in_foot LV a.
  Proof.
    intros a Ha. apply not_foot_of_hole. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh.
    repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
  Qed.
  (* [comment removed for export] *)
  #[using="L sp0 Hsp DLL"] Lemma not_junk_of_hole : forall a, (forall hl hh, In (hl, hh) LIB_HOLES -> ~ (hl <= a < hh)) -> ~ in_junk Lay a.
  Proof.
    intros a Hn (iv & Hin & Hr). destruct (dlla_junk Lay L DLL iv Hin) as (hl & hh & Hh & H1 & H2).
    apply (Hn hl hh Hh). lia.
  Qed.
  #[using="L sp0 Hsp DLL"] Lemma not_junk_off_image : forall a, ~ (0x6820d0 <= a < 0x6b6000) -> ~ in_junk Lay a.
  Proof.
    intros a Ha. apply not_junk_of_hole. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh.
    repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
  Qed.

  (* [comment removed for export] *)
  Definition CPl (LBc : list (Z * Z)) (sp scr : Z) (H H' : word -> bool) (a : Z) : Prop :=
    (aclient L ar LBc [] sp scr a /\ ~ in_foot LV a /\ ~ in_junk Lay a) /\ H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false.

  #[using="scfg C IL HIok Hsp DL DLL"] Lemma regions_callL : forall vals ebs so scr bls vbnd LB LK LK' cr cr' A A' M M' model model',
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> 0 <= scr <= 2 ^ 21 ->
    ri_inv HI LB [] LK cr A M (vml_of model) -> ri_inv HI LB [] LK' cr' A' M' (vml_of model') ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
    regions_ok ASEGS 0 so scr bls vbnd [] IMG_LIB_A IMG_RW_A E
               (CPl LB (bv_unsigned sp0 + so) scr (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) scr).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0126 ()) ["FPX_1"; "LibSite"] "p'0h04__x1h14__x2h27__arithh36__sat4h46__sat5h56__sat6h68__varmaph75__with81zi001zh94__ffh:1Hh;4__p1h<4__x3h=6__sat7h>6__sat8h?2Hah@2hhhA2hlhB6__sat9hC1ahD4__p2hE6__sat1hF6__sat2hG6__sat3hH4__x4hI1bhJ2MxhK1dhL3hi'hM1mhN7__sat10hO1ihP2hihQ2lohR3lo'hS2HchT4__p3hU7__sat11hV4__x5hW4cstrhX3HinhY2HzhZ3caph[1fh\2nbh]2Hhh^1eh_1vh`1Aha2A'hb1Ehc2E1hd2HBhe2HHhf3HH'hg4HOLEhh3Hblhi2Hdhj2Hfhk4Hin'hl2Hmhm3Hnbhn4Hnotho4Hscrhp3Hsohq4Hsp'hr3Hvbhs2I1ht2I2hu2I3hv2IBhw2LBhx2LKhy3LK'hz1Mh{2M'h|2P0h}2S1h~2S2i013VISi022Y1i032Y2i042Y3i052Z1i062Z2i072Z3i083blsi092cri0:3cr'i0;3ebsi0<5modeli0=6model'i0>1oi0?1si0@3scri0A2soi0B4valsi0C4vbndi0D1pi0E1xp%0p%1p%2p&0p&1p;1p;2p;5p;3p;4p;8p;Dp;6p;7p;9p;:p;>p;Ep-1R0p104C9p4p710R1p9P0p104C\p4p710R2p9P0g001GR3p4p710R4p9P0p1001cR5p4p710p9P0P5p4p7210p9P0P5p4p73110p9P0p1002AR5p4p7210R6p9P0P5p4p710R5p9P0p10035p4p710R7p9P0g003eR8p4p710R9p9P0p104DHp4p710R:p9P0g005=R;p4p710p8P0g005TR<p4p710p8P0P<p4p7210p8P0p10061p4p710R=p8P0p1006Qp4p710R>p8p1006np4p70R?P1p8P?P2p8P?P4p8P?p1007^R@p4p710p8P?P@p4p7210p8P?P6p8P?P5p8P?P9p8P?P:p8p1008;p4p710R?P4p8P?P9p8p1008Xp4p70R?P1p8P?P2p8P?p1009Fp4p7210p8P?P4p8P?p1009bp4p7210p8P?P6p8P?P5p8P?P7p8P?P9p8P?p100:Qp4p7210p8P?P:p8P?p100;Ep4p7210p8p100;dp4p70P9p8p100<_p4p7210R?P1p8P?P2p8P?P6p8P?P5p8P?P:p8p100=Kp6051000R?P4p8P?p100>Qp4p710R7p8P?P9p8P?P>p8P?p1058Mp4p710R?p8p100?Op6051000R>P7p8P>P9p8P>p100@Vp4p710p8P>P=p8P>P?p8p100A8p4p710P9p8p100ASp4p70R>P1p8P>P2p8P>P6p8P>P5p8P>P9p8P>P:p8P?P4p8P?P9p8g00BIj17Tg00Bnj1mTg00CLk10KTg00Coj1HTg00DTj1DTg00Fkj1dTg00H3k11=Tg00GJk20XTg00J>k10zTg00Jik20YTg00KLk50lTg00Y>j3xTg014Pk20OTg00I[k10hTg00L0k20NTg00T>k205Tg00S^S00k20LTg00W8j2BTg04\^k10dTg00gTj2ATg00MEk10JTg00Xbj20Tg00Q[k10;Tg00S>j1rTg00g7k10[Tg00fWk21ATg00kMj2|Tg00l5j3~Tg013_k212Tg00E2j1pTg00UQj23Tg00f1j2GTg06Djj4{Tg00c7k10sTg00Yak10rTg00Zak20qTg00T[k20BTg00[Ck20pTg03=[k30oTg00[ok40nTg01<Sk10mj2gTg01Z;k20kTg06Ejj2yTg00h1j3JTg02_Ik10jTg04dKk80QTg01Ulk208Tg00lYk20PTg01Tkk50iTg00N>S01j21Tg00U5j24Tg02cQj2XTg01;_S02j2@Tg01<9j3vTg04^]j3WTg06FfmD0MTg01Whj4<Tg01[:j26k30wTg06Ggk50gj6VTg06Hbk20fk30HTg03;Qj2uTg00Z?k10eTP8j6UTg06I\k70@Tg059Ik20cTg06J[k20?Tg01bkj1KTg06KXk20>Tg04Z\k10bTg04[]k10aTg06LWk204Tg06M[k20<Tg06N\j3\TP;j3;Tg06O`k10`Tg06P_k10_Tg06Q_k10^Tg05UDS03j2hTP<k30ITg03DTk30UTg0634k51BTg06R_k20]Tg06Sik20\Tg06U3m91@Tg01>Lk30ZTg01:[k40ATg04a<k81>Tg01XCk41;Tg06V7k319Tg06W:m:18Tg06X;k517Tg06Y<k516Tg06Z=k215Tg06[Ek213Tg01WKk60WTg013:k10RTg03E1k211Tg06\Mk10VTg06\kk110Tg06]Ik10TTg06]gk10}Tg06^Dk10|Tg06^cm>0{TP3k60STg06_gmE0~Tg036>k30CTg0383j4oTg038^j7}Tg039Bk30yTg00Wbk414Tg03<Sk709Tg03:ek20FTg00XBk30ETg037Pk30xTg03=7j8zTg03?hk41:Tg03;ok60vTg03>:k60uTg03?Dk70tTf0R3#7#7p>00%H3#Hp=Z%H3#7p=R%73#7#7#7p=P%73#7#7#7#7#7#7#7p>07%73#Hp>03g03J5R</43p=M10<3p=8g03I8R;00X3p=_f1R8>0C;3p=Q20N;3p=bf2R9g03JSR?g03K2R4P4g03KRR:P;P8g03L2R>P3Cog03LYR5F}p=520Y;3p=`P9P?P4P4P:P;P8g03NkR6P3CoP5F}p=IB0y;83p=lP;P;P8P3H14p=EP;P8P6P3Cop>0=f3R6P?P4P4P:P9P8P?P4P4P:P3P5F}K09p>06g03R_R2g03ORR1-0F8<0E3p>1CB0C;8300F1p>1?B0x;83p=if4R=P?P4P4P:P6P?P4P4P:P;P9P>P8CoP5F}P3K09p=YP9P?P4P4P:P8P3K09p=aB0C;9800F1>0E23p=[B0E283p>0Dg03PZR1g03Q:R77J3p=s1098/13p=210<8/13p=NB0w983g045h5J1p=O1483,19p=91@83,@9p=fP6P?P4P4P:P9P8P3Gzp=eP;P9P8P3H1:p=:P8P?P4P4P:P3J0vp>02f5R@P?P4P4P:P=P?P4P4P:P6P9K09P8P3Gzp=?1083,19p=n143<p=k1483,19#Kp=cf6RAP@P=P6P91383EVp=^1198/13p=FP8P?P4P4P:P3J0up=q1A98/03p>0:PAP?P4P4P:P@P=P6P?P4P4P:P9P8P3GzGzp=j10691483'1p==P9P?P4P4P:P8P3K0tp=tPAP@P=1669P8P3EVp=LPAP@P=P61698P3EVp>011098/@3p=w1h;3p=TP@P?P4P4P:P=P?P4P4P:P;P6P>P9CoP5F}P8P3Gzp=S10691083'@p=C1098/13,16p=]P;P8P>P3Cop>1<1398/03p>0G1183,19p=>g03e9R>#7R5#7RB#7RC#7RD$00RE#mg03e^%mC$0KP0%H5RF#HRG#7g03f<RH%7FRI#HPH%H>RJ#HRK#Z#Z#Z#Z#Z#Z#R$00#P$07$07$07#DP;%HGRG#HPH%DEP;%R>#R#Z$03#R#P$07#DP;&00E#PRE#PRH#7$00#P#DP;%D5RL#Mp-0RM%8LPM%DGP;g03NLRN#dRO#dRP#_&1=;RQ%_OS0420X;NRO'QPQ&0z;RR20Y;<S05%b5R535PRP?P4P4P:I0lR?%`LRS%mG5x;-0O;&0h;RG%DDP;%dPRP#_PQ%bBPG%bJRD9IR5P?20N;>RT/l5PG1lTDPG%dPRP#_PQ%DEP;%DHP;%bKPG%dPRP#dRK#dRH#_PQ%_KPQ%_PPQ%dH#_PQ%bCPG%R>#R#P#R#P#Z$03#P#DRC#`PG%7J#bPG%7I#D-05LP;Q05=5RTP?A5RT5P?%HB#bPG%R>#R$03$00#R#P#Z$03#P#DR>,EC20L;;RB%8CPM%`>PG%bFPGfXRF$0KP0fWRI#DRJP;PJP;f[RHp,3sp0RP'BP;PJP;205LIP;fZRJ#`PG%mJ9x;SPGfURK#8PMfVRE-05LP;1QEKPQp,2arRU$0dS06/AHP;fTRV#8RWPMfYRX/QOPQA5RI5P?f_S07#`PGfSRY9IRVP?fbS08#`PGfdS09#8PMfkS0:9x;SPG1lTJPGPRQ07PR20=5VH06P?f]S0;/QOPQ%`IPGAIRTIRQP?fRRO=5RTP?f^S0<fKRZ55RP?fJR[fsR\$0J[P0205L[R0P;P0P;frS0=/0[PMP0P;fLR0fpS0>'AP;%80PMfOR]#8PMfQR^#8PMfMR_=5RTP?A5RT_P?%M0PM%8_PM&0;2R`-1C_%r2Ra&0[]P;%8ES0?PM21AI\#8PMfNRb-1?\P2PRPbPRQ05-0=5H06P?1iTbQ0=55RP?AIR\_P?%MJPM%8HPMPRPRQ05fvS0@Q0@=IRbDYP?1iDYPGf\S0A95RDP?A5RYTP?A5RbTP?PRPRfoRGPTPbDYP?fwS0B=5REP?fqS0C95R^P?AIRTFP?Q0C=aRQP?ffRQ,0>PMfPR2$0[P;fjRc/0bPM%M]PM%82PM%MYPMPWPM%MEPM%8IPMAaR2]P?p+01TS0D,|Lp+01VS0EfnR?P^[[p+01WS0FPO\G[PMQ0Fg03g>RWp+01XS0G=~L8UW?Q0FPO\W]?Q0GPY\W]?PM1AJ?P;Q0BQ0D+12P^\G\2Q0>PO[\^PMp+01`S0H,|Lp+01]S0IQ0:Pb[[p+01^S0JflS0KP][[PMQ0Jp+01dRd=~L8VWW?Q0JP]\W]?p+01_P2\W]?PMQ0DQ0I;[`-0DVPag03IVRe10C8S0L%p8S0M,39S0N/0>g03W2S0OP=p+020S0P/G6P9C{#s[[]M^K;^JQPMf~S0Q,|Lp+01cS0RQ08fES0S[[fcS0TfFRf[\dPMp+01CS0U=~L8VWX?dPf\W^?dp+01eS0VfGRd\W]?PMp+01ES0W,|Lp+01gS0XfeS0YPd[[p+01hS0ZfHRg\Q[PMQ0Zp+01IS0[=~L8VWW?Q0ZPg\W]?p+01iS0\fIRh\W]?PMp+01JRi,|Lp+01kS0]fhRjPh[[p+01lRkfiRlP[[[PMp+01NRm=~L8VWX?kP[\W^?kp+01mS0^PZ\W]?PMf;RWf:RLPLf9RnPnf8RoPof7RpQ0SfDRqPqfCRrPnPoPoPpP`Pa&0s;Rs&0r;Rtp+01[S0_p+01FS0`55R20qR:R:P3P920B1720p39#sdB0o;<8H0nR7b9b6b7PJP3b2bEbFbGb3b4b5b=b>POp+01PR1#rp+02:S0a#r\e1313P;1A83P;20Le;#rS0bQ0b%rBS0cg04?RRu#rS0dQ0dg042mS0eQ0eQ0cQ0cp+01DS0fQ0Wg0427S0gQ0gfBRv$0mfAS0h+0kg046Hp+02MS0i1y3N'BP;Q0V1gqN;JP10r<92jr10vi,Nvp,2HIRif?Rw&0;uRxf>Ryf<RzPLPo&0jAR{L0QPif@R|PxPyPzPLPoP{L0Q&0J;S0jQ0S-08820P;3S0k3JR{p,1LR}PUPqp+02VS0l1g09'BP8I0i[^\;^Oep+02W1g_9'B/08\{^I;^_ep,3HspS0mfmS0n,1mp+02PS0o,43PMp+02XS0p/G8p+01oS0q1019PM1Xg6,@3PM1@63PMp+01nS0r,4@,N@Q02PAP6P6P3Avo@3XSpP3O1Q02PA1XbnP@P31X2WR{=vo39WLpXSpP3O11X]LAWo{39WLpWSP3O1n200100000021000010000X:=P3O1n200100000021000010000P9AOgqAAOdrAp,4scfgS0sP}PUp,1CS0tp,2ILS0uPip,4HIokR{PPp,2DLS0vP_PxP0P[PgPfPqPof=R~P9P3ND0MQ0sP}PUQ0tQ0uPiP{PPQ0vP_PxPZPhPdQ0SPrPoPzP9P3ND0MC<aXS8W?aaaaaXC;%83R{Q0\793p+02QS0t,48p+01ORi/081Xf83fp+02YS0s/G9S0w9OvyQ0hQ0w7O~'1[[^C;Q0OPNPZPhPdPf&0;eS0wg06`hS0xg06aiS0yPLQ0SP[Ph16|z16wWI0g20f[hQ0rPPQ0rp+02TS0zQ0p/B3S0{Q0{/0132WIPJPXPXPFPFPIPIPEPEPKPKPVP`Pa1u;8S0{PtPRQ0C&0e4R4Q0CCeP:P7b9b6b7X0;p+02ZS0|Q0E,03723p+02[S0}Q0F,08728[^0;P3p+022Q0mO2b2bEbFbGb3b4b51g_NS0~PoEUp+02SS1010ni72nePJPXPXPFPFPIPIPEQ0:PcPcPlPFPIPIPEp+01QS11Pa1u;9RN?:8sS12PtPRPRQ0lp+02aS13#m9x;S95R5P4PRPRp+02b#m9x;S-0O;=5RT202R=S14P4PRPRp+02US151iT5Q0lDYE?E?P:P7b9b6b7X0;X1;X;M%88S0lp+01\S167n8f|S17?286p+01RS181A96S19%86S1:32[[^0;^1;^;MP310V<POPVPwP|O5b2bEbFbGb3b4b5b=b>Q0W1AZh%8h32eQ0rPPQ0rp+01G%k3S1;7231Ab0S1</08?c8bPhPbP_16q|S1=16rwS1>Q0}/B6P9F^[[^8;WI13k3S1?P;P}PUPdPxP0PZP3K0@PMp,3LayS1@00cUS1A00?8#KPMQ1@00>9#KS1BPMp+02\S1C/G6p+023S1D1XZ=PMQ0E,4@PM10CAPMQ0s,4pPM11A@R<PM10Yn?cnKPM&0b}S1E/0L&0a}S1F,4L204}L#K3F20<xLQ0q?\GLA;u3xS1G&0`3S1H&0_3$0^S1I;\W'1X[u,huA;B3OB0I;;3S1JB0U;;3S1K;\W'1XIB,hB3f3fPMQ0P/0W?F@8PMp+01SS0P%k~72~PlPjPjfgRSPSPQPQQ0YfzS1LfyS1MQ1MfxS1NPSPQPQQ0Yp+01bS1OPaQ12PtPRPRp+02>S1PQ14P4PRPRQ0Z202R@S1QP4202RAS1RQ0I5aR,qRE?E?P:P7b9b6b7X0;X1;X;MXDMXTMp+01aS1S?289p+030S1T?28=1396S1Up+02nS1V59Ag03faS1W[[[^0;^1;^;M^DM^TMP3Pwp+01HS1X%kdPdp+02CPnPhO7b2bEbFbGb3b4b5b=b>Q1W\<B0:HXw?cwH11yAAO^_WAO20W'1PyPA1@6=P;p+02<S1YQ13>0:3|?FLAX8;Q0:PcPcPlPlPjPjPSQ17f{R<P<Q1LPlPjPjPSP<Q1LQ1OQ1O00D`S1Z+0DPa1u;=S1[?:9s1u;6S1\7:8S1]PtPRPRPRp+02gS1^,iDP5p+02fS1_DY,qRP4PRQ0RP4PRPRQ1RQ0]P4PRPRPk202RpS1`P4PRQ1OPRp+02eS1ap+02I+0=H06PRPRp+02dQ1^'iQ1ap+02@S1bDY,qR5aRE?E?FjP:P7b9b6b7X0;X1;X<;XH;X;MXDMQ19P8P8P9C=Q1W[p+01fS19%k9729p+021,09S1c,1Ap+036S1d?26op+033S1e13=@S1f60:=Q1fQ1D'413=AS1D/ApQ1fQ1fQ1DC=Q1W[3F[[[[^0;^1;^<;^H;^;M^DMP3p+01KS1DQ0]Q09PQP[p+02FS1gPLPzP0Q0mO:b2bEbFbGb3b4b5b=b>bBQ06P}PUQ0uPPQ0vI1BEU9v6=5WLPyeP~Pz20]w820\w8C<C<Q0hPwQ0:PcPcPlPlPjPjPSQ17P<P<Q1LQ0BQ0@Q0@fuS0BQ0:PcPcPlp+02^Q1Pp+02cQ1^;[`3[PaQ12PtPRQ0HP4PRQ1XP4Q0_FjP:P7b9b6b7X0;X1;Q1O%k8728p+031Q0^,08S06728Q1UQ1Up+02HS1h'4'N[[^0;^1;P3PZp+02GP~P_O4b2bEbFbGb3b4b5b=b>bBbNQ0:PcPcPlPlPjPjPSQ17P<P<Q1LPlPjPjPSP`PaQ12PtPRPRQ1bQ14P4Q1QQ0HQ1R5tR5tRE?P:P7b9b6b7X0;X1;X;MXDMXTMQ0R?289Q1V1389S0R60:8=f=@[^0;^1;^;M^DM^TMP3PrP|%khPhp+02ES1VPWO6b2bEbFbGb3b4b5b=b>O3C<PEPHPJP^P_1620PwFLeWnaWYaaaaaaaaaaaaaX8;Q0~PoEUQ0`Q1;7231A_ZS1;/08?c8_PgP_P0Q1>16vyS0`PzP9F^[[^8;eQ0rPPQ0rQ1;143_S0H723PgP_P0Q1>Q0`Q0|/B9S1;/38S1iEVQ1i:0H_0'@[^8;WIQ1?P;B0H0Z3PMQ1<P9P9PbC=PhPbP_Q1=Q1>P9EVQ0<Q0;Q0;Q0AQ0APHPHPJPJPXPXPFP`PaQ1]PtPRPR1i5DQ1555RQ15=IR5P4PRPRQ10/iDp+01jS1]Q1]Q105IRDYE?P:P7b9b6b7X0;X1;X<;XH;1A89P6P6P8C=Q0R/A6138=S1]Q1]Q0RC=[^0;^1;^<;^H;P3PLPVPEp+026S1]PpO5b2bEbFbGb3b4b5P8e7W8WYaaX8;Q0~PoEU1A0[P3P3P0C=PdP0PZQ0`Q0hP~13W8S0`K01Q0`:0H0Z'@[^8;eQ0p1gb3'BS0`P;p+02B/03PMQ10/08PM1363P;Q1V=w39PMp+01US1<,08PMQ1cPM1198PMQ0j208n^20P;@3JP}PUQ0uPPQ0vP2PnPAPyPLPAP3O3N91@B0ZPnAQ01PnP9A9{3nPVPXPF16]ZS1c16b[S1?P~P8F^[^8;,1=P3Q01PnPoA9{3~PFQ0;Q0A16Y]S1i16ObS1jQ0hP8F^[^8;,1oP3PdPrPwPnO3%M|10|31Er3=;BJP}PUPrP3H0A'13FXZ;#TQ03P;Q0h#MQ0h/03S1k1Eq3=;BHP}PUPqP3H0A'13FXZ;A9{3vQ0;Q08faS1l16FVS1mPIPY13f8K01[^8;,1~P3%Mr?nr3PM1Ed8PBP}PUPgP9H0APM13h6P;Q1l9;B9PMQ1C=w8hPM109kPMB0I;;@P;116@PM1169PM11n8Q01PLP9A9{32Q0:Q0>PGPQQ08Q0YQ1l'6S1n13V8FL[^8;,1ZP3Q01PLPzA9{3VPGftRJP\PcPQQ0Y,6lS1o13F8FL[^8;,1]P3P}PUQ0uPPQ0vPXPrP3L1>B0ZPXrQ01PXPLA9{3XPJQ1MQ1NPGQ0:16?cQ0;/38FL[^8;,1VP3Q01PvQ0hQ0;99{3Q1Nf}S1pQ17P\PGQ0=/6?Q1l/38FL[^8;,1FP3PHf`S1q99{3P<p+01AS1rp+01@S1sQ0@Q0='6S1tQ0BQ0C'6S1uQ09P8F^[^8;PiPmPmp+01MRJPJp+01LS1vQ1vQ1Dp+01YS1wQ0GQ0GQ0FPJQ1vQ1vQ1DQ1gPaQ1\9:N8PtPRPRp+03ES1xp+02=S1yP4PRPRQ1QQ1YP4Q1xp+02]S1z55RE?ESP:P7b9b6b7X0;X1;X<;X;M1338S1xp+03OS1{,A9'0Q0o9n=6Q1Up+02kS1|'0[[^0;^1;^<;^;MP3Q0ip+02hS1}PjQ0:PXP?O6b2b3b4b5b=b>bBbNbUQ0T/33P;1X<3PMP}PUQ17Pxp+01BS1~Q1rP8K0@PMQ1A00?9#KPMQ1@00>6#KPMp+03QS20/G=Q1}p+03K,4@PMp+02J/0APMP_PpPpB0U;;Y,3_C=PM11@=PM%8LS21?9LcQ0_p+01ZS22Q22Q1wQ1wQ0GQ0GQ0FQ0FQ0EQ0EQ1<Q0\Q0Zp+03JS0Zp+03IS0\p+03NS23Q04'Q'QQ0\p+03HS04Q23p+03SS24'Q'Qp+03GS23Q1aQ23Q0ZQ0\Q24'Q'Q;[`3[3[3[Pa1u;@?:@s?:9sQ1[9:s6S0\7:8S24PtPRQ1}P4PRQ04,lTS25Q1_55RQ1h5tRP4PRPRQ05p+03MS265IRQ26Q0455RP4PRQ26,lTQ1_55RQ1h5tRP4PRPRPRp+037S1hPDQ1`DYP4PRPRQ23p+03RS1`p+02NS1_DY,qRFjE?FjP:P7b9b6b7X0;X1;X<;XH;XV;X;MQ0l?986S27138@Q26p+03^P8CC%M@?n@A136AQ1{p+03`S1{P6CCp+03d?2AnPC13@AS26Q26p+03bC=Q1W[[[[[[^0;^1;^<;^H;^V;^;MP3p+028S26Q1qP\Q1ePrQ0@PoQ0SPOQ0YQ0mO;b2b3b4b5b=b>bBbNA2CL=Q1W[PBQ1X9;B3Q1JPzQ1JQ1K'3,4zC]XIBPIPVP6PdQ16Q0_Q0_Q22Q22Q1wQ1wQ0GQ0GQ0FQ0FQ0Ep+02RS0FPaQ0\9:N8PtPRQ1^P4PRPRQ1RPRp+03LS0\01<DH06P4PRPRPTQ20p+02lDYFjP:P7b9b6b7X0;X1;X<;XH;X;MQ27An@=6P9Q1UQ1U139=C=[[^0;^1;^<;^H;^;MP3%M\P\Q1qPrQ0@PoPOO7b2b3b4b5b=b>bBP6eC<H1;PL11L6Q0UQ0Q;OpQ1~Q1p;Op'1PLP6Q1a/0zQ0t,4zQ1D/0z?czJ3FQ1E/0zQ1F,4zS1U204}z#KS0G3F20<xzQ1aQ19;\zQ1GQ1HQ1I;\~'1X[u,huQ0[9;B3Q1JQ1K;\~'1XIB,hB'@3f3f=vW3PnPo20]z820\z8C<C<Q0=PzQ0IQ16Q16Q0_Q0_Q22Q22Q1wQ0XQ19Q19Q0VQ0_Q22Q22Q1wQ0ZQ1^p+03PS0VQ1e;[`3[PaQ1[9:s9Q1\7:8PtPRPRp+03ZQ049IR5P4PRPRQ20#`PTP4PRPRQ25p+02LS25P4PRPRQ1Rp+02KS04P4Q0iE?ESESE?P:P7b9b6b7X0;X1;X<;XH;X;MQ27Q0V/08Q1{,A=:0G9@Q139np@Q1fQ1fp+03<S13'4'N[[[[^0;^1;^<;^H;^;MP3Q0}Q0@Q1dPfQ1MPWP0PSQ17O9b2b3b4b5b=b>bBbNbU1@@WAW@W35WAO3C<Q1XPJQ1vQ0UQ0QQ1~Q1p'6PzFLebvaWYaaaaaaaaaaX8;C<Z04qZ03qP8P3O2n2001000000121000000X:~Z02HP8P3O2n2001000000121000000b:XdwXXzP8P3O2n2001000000121000000X:@XmzP8P3O2n2001000000121000000W:aaaaaaaaaaXZ;P8P3O2n200100000012110E000c0?Z07WZ06WP8P3O2n2001000000121000000X:@Z05WP8P3O2n2001000000121000000b:WjaaaaaX\;aaaXOeQ0j2088hQ0k3JQ0|1y~9'BS1p/381439S1X,1{P[P]PbQ0SQ0h'6S0hQ1=Q1C1yw='BP8F^[^8;72k[^\;^OeeP9Q0j2088gQ0k3JQ1p/08[^I;^_eeQ0rPPQ0rQ0w9;e3S1pQ1;Q0|1g28'BS0|Q0|p+029S0k'3Q0a99{3P[P]PbQ0hQ1=Q1C1gO6'BP8F^[^8;72k32[^OeWIQ0`P;Q0w9;e8Q1WQ0qQ0a,39Q0^p+02;99{3PZP2P]16fvS0wQ0hP=P8F^[^8;32729P3n010000000W:aXOeQ0~PoEUQ1pQ0s1yz8'BS0sQ0sQ26'3Q0]Q0k99{3PhPbP_Q1=Q1>Q0}1yy6'BP8F^[^8;3252W[^OeeQ1b/03PMQ10,03PMQ06PMP@P3P3P6C=P0P^P2PdPrQ0wP8FL[^C;PM1E@6Q0x5;BB19A=31E83S0wg04@PS065;BS10P8Po10A3C]XL;#TXR;#TP6PAP=Q0wg06bj5;BR{108nS1p9wp9[^@;^A;C]7>@Q01Q10Q1p10p33>XL;#TXR;#TPoP9P8PLCC\{^@;^A;92p@9>A=%8oS1p10n3S0}?93pP2PKPVPZPd16[fP8FL[^C;7>=P3Q10P8PWQ0}C]XL;#TXR;#TQ03P;Q10P8Pz10L3C]XL;#TXR;108yS0}9wz9\{^@;^A;92Wn9>Lo10~3S1>?93WPVPXPFQ1cQ1?P8EV[^C;,1o,Nz[P3Q10Q0}10z33>XL;#TQ03P;1E93S03Q065;BP9PwQ1>C]XL;P|P9P8PvCC\{^@;^A;92w~9>yzQ1k?93wPFQ0;Q0AQ1iQ1jP8EV[^C;,1z,N|[P31E=3Q065;BPM10|892@vPM1183Q01P9P8Q0SPfP9P8PgCC\{^@;^A;72r9>qvPdP3P3Q0SC=Q0<Q0TQ08PXPKQ1mP8FL[^C;,1v,Nf[P3Q0110Wg10fpP[P9P8P0CC\{^@;^A;92hd9>gfPZP3P3PhC=Q08PSPQQ0;PXQ0A/6FP8FL[^C;,1f,N[[P310~[10hLP_P9P8P]CC\{^@;^A;920[9>ZhQ01P0P[P_PZPbP9P8P2CC\{^@;^A;C]Q0H92]3PQQ0:PcQ1lQ0;Q1qQ0A'6P8FL[^C;,1[,NbP3P_P2PbP^P9P8PYCC\{^@;^A;C]Q01PbPOP9P8PVCC\{^@;^A;92^]PYP3P3P^C=PcPGP?Q1nQ09Q1qP8K01[^C;,1b,NOP3PKP9P8PICC\{^@;^A;92VOQ0110KYPEP9P8PFCC\{^@;^A;Q0?PIP3P3PKC=P?P\Q0=Q1oPjQ09P8K01[^C;7>OP310IKPXP9P8PHCC\{^@;^A;%8X11KVQ0WQ0fQ0fQ0UQ0UQ1~Q1~Q1rQ1rQ1sQ1sQ0QP`PaQ0{PtPRQ0]P4Q1}CeP:P7b9b6b7X0;Q1T/03Q0l[^0;P3Q1qP|O2b2b3b4b5b=b>bBPKPVQ0WQ0fQ0fQ0UQ0UQ1~Q1~Q1rPiPmPmPJQ0UQ1~Q1~Q1rP`PaQ0{PtPRPRPTQ0FP4Q0o95RTESP:P7b9b6b7X0;p+03C,03Q1z,08[^0;P3Q1qPyO2b2b3b4b5b=b>bBbNbUQ1A00?3#KPMQ1E/08Q1F,48204}8#K3FPMQ1B,18PMp+02mRK/06PMp+03FRX/G=Q1zP}PUQ0BPxQ1LQ1MP@K0@PMQ0z/0AQ1b,4AQ1M/0A?cA<3FPM20<xpQ15Q0E;\pQ1GQ1HQ1I;\o'1X[u,huQ1N9;B3Q1JQ1K;\o'1XIB,hB'@3fPM1@A3PMQ0TPnPnQ1lC=PyP9P8P3O3Q0YP9P8PSCCQ0210Q6109j10=w?cw6P310S=Q0EQ1<Q1<Q0DQ0DQ0PQ0PQ18Q18Q11Q11P1Q25PaQ1\?:6sRu?:6s9:N8PtPRPRp+03;RxPTP4PRPRQ1QAIR5xP4Q13Q1R5aR,qRE?ESP:P7b9b6b7X0;X1;X<;X;MXDM10931496Rx,1=A296AQ1W[[[^0;^1;^<;^;M^DMP314dWQ0C/0dPGPdPzPpP~O7b2b3b4b5b=b>bBW:P3O1106lQ0EQ1<Q1<Q0DQ0DQ0PQ0PQ18Q18Q11Q11P1Q25PaA:u8s?:6NPtPRPRPDp+03ARuP4PRPRA5Ru5RIQ1QP4Q1RQ0\5aR,qRE?ESP:P7b9b6b7X0;X1;X<;X;MXDM10891068RO/1=11AxQ1W[[[^0;^1;^<;^;M^DMP310zd14dGQ0CPWPdPpP~O7b2b3b4b5b=b>bBW:P3O1n200100000021000010000c0>X]{X@;XA;109~?c~8^]{^@;^A;11@oQ0@Q0=;OAQ0BQ0C;OA'1P@Po1X<W1@=9P;p+035103zQ1UQ0G3FX8;P;PX14z3Q0G5FoX8;A9pWX204}W#KQ11P1P1PiPiPmPmPJPJQ1vQ1vQ1DQ16PaA:s6NQ1\9:s67:8RXPtPRQ26P4PRp+027R{P4PRQ1]P4Q0kp+025Rd5aRCeFjP:P7b9b6b7X0;X1;X<;Q1X9283RxQ0V,06p+03@/06PuP6P6Q1`C=[[[^0;^1;^<;P3PcQ0KPvPoPgP0O6b2b3b4b5b=b>bBP}PUQ0uPPQ0vPFPVPWPbQ11P1P1PiPiPmPmPJPJQ1vQ1vQ1DQ0JPaQ24PtPRPRPIQ139IR5P4PRPRQ13PDP4PRPRPTPuP4Q1hQ235aRESESE?P:P7b9b6b7X0;X1;X<;XH;XV;A9O8=10@6109@P6P=P=P@C=[[[^0;^1;^<;^H;^V;P3PcQ0KPHPvQ07PoP2P^O8b2b3b4b5b=b>bBN:18C<Q1FP}PUQ0uPPQ0vI17EUQ1EP}PUQ0uPPQ0vI16EU9vn69W=93WP@ePLQ1@00>W#K215W3213W3C<C<PQPWQ11P1P1PiPiPmPmPJQ0_Q22Q22Q1wPiPmPmPJQ0JPaPXPtPRQ0aP4PRQ0kP4PRQ26P4Q1]CeFjP:P7b9b6b7X0;X1;X<;Q1`,06p+03B/06Q1:?96K[[\x^0;^1;^<;P3Q0KP?PqPLP[PbO6b2b3b4b5b=b>bBbNbUQ11P1P1PiPiPmPmPJPJQ1vQ1vQ1DQ1gPaA:s9N9:s8PtPRPRQ14Q0pP4PRQ26P4Q1]Q1Q5tRCeE?P:P7b9b6b7X0;X1;X;MXDMA9938Q20,09Q1`,49/@@[[^0;^1;^;M^DMP3Q04Q0U/Xv7wvQ0K/0vPcPvPoPgO6b2b3b4b5b=b>bBO3C<P<Q1rQ1sQ1tQ1uPWEVeaW?aaaaaaaaaXC;C<C<WgWuP8P3O2n2001000000121000000W:Xt2P8P3O2n2001000000121000000W:XsbP8P3O2n2001000000121000000W:W~W}P8P3O2n2001000000121000000X:=Xk=P8P3O2n2001000000121000000W:aaXL;P8P3O2n200100000012110E000W:XR;P8P3O2n200100000012110E000W:P8P3O2n2001000000121000000bCWXaaaXP;aXQ;Q0wQ0x5;B%89R2108kRkQ1X9263P[P]PbQ0hQ1=P8EV[^C;3>[^P;^Q;eAJ;C3PMQ03&0;B5;BPMAJ;>8PM1E=99JB{PMQ0q,06PM1EA=Q0y5;BQ02P9P=Q1pQ1610W8Q0N/0LQ0OP=Q1a/G6P9C{#s[[^Me^K;]J7>9P3PBP;Q00P;P;P;P3P3n200110D000120100100X^BQ1Y1EnpP3J0WP@PBP;Q00P;P;P;P3P8n200110D000120100100X^BQ1y1ELoP8J0WPnP;PCQ0lQ1O10=8Q0N/0|Q0OP=Q1|/G6P9C{#sR|[[^Me^K;]J7>o\nXQ;P;P>Q1bP3Q26Q1OQ0LQ0N/0=P|[[^Me^K;]JC]XP;p+02?Q1s/1lPjPSPSPQPQQ0YQ0YQ09Q09Q0TQ0TQ08P`PaPsPtQ05Q1_55RP:P7b9b6b7Q1VP3b2bEbFbGb3b4b5Q1sPlQ0AQ1SQ1^/G3Q1PQ1}/B3P;10C6Q0M>0G=>&0R9%p9#8Q0>PGPGP?P?Q0nQ0nQ0KQ1LQ1MQ1MQ1NP?Q0nQ0nQ0KQ1ZPaA:N9s9:s8PtPRPRQ05Q0tP4PRPRQ0t,lTQ0FP4PRP{P4Q1<CeESESP:P7b9b6b7X0;X1;Q0lQ0R/0>R{10C9Q1:Q25796[[[^0;^1;P3%pzPwPnPLPWO5b2bEbFbGb3b4b5b=b>bW-11@AJ;6@Q0OPp1GKCP@g06ck$0V$10$0T$0T$0V$0}$0|P6PCP>20B;C20B;>&0R6RK%p6#8RpQ0YbWg06dIP;PA10C3RCX8;PKPpQ0CQ0>Q0>PGPGP?P?Q0nQ0nQ0KQ0KQ0:P`PaQ0{PtPRPdP4PdCeP:P7b9R7b6b7X0;Q0L\C^0;P3PyPLO2b2bEbFbGb3b4b5bWP=P3EUP;PA%p=>0G3>X8;PKPpQ0CQ0>Q0>PGPGP?P?Q0nQ0nQ0KQ0KQ0:P`PaQ12PtP7b6b7X0;X1;Q1x/0>P{[^0;^1;P3%pWPyPnO3b2bEbFbGb3b4b5bWP=P3EUN>0{aWlWiXMeaaXK;WJC<C<PWP3J0SX:oPzP3J0SX:LP3O1b:P3O1b:Xc6P3O1Q1WQ21Q0J10~8Q0N/0zQ0OP=Q1^/G6P9C{#s[[^Me^K;]J7>=P3n010000000X:@P3O1n200100000021100010000WXaaaaXP;aXQ;Q0wQ0y5;BQ0E10@8Q0N/0@Q0OP=p+02_/G6P9C{#s[[^Me^K;]J9>2k[^P;^Q;eNE0~c01bqWrWhWfWeWoWpW|abbY0=Y0<W{WzWaW`Y0:Y09WyWxWwY0CY08aZ0@;aZ0A;Y0;Y0Baaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.

  (* [comment removed for export] *)
  #[using="C IL HIok Hsp Hal DL M0_def DLL LIok"] Lemma alib_site : forall vals ebs sr kn R M (model : Model) LB LK cr A g so stk bls vbnd (ptr ra : Z) (payload : list byte) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 21 <= so <= 0 -> so mod 16 = 0 -> lla_stack Lay <= stk <= 2 ^ 21 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 47 -> ra mod 2 = 0 ->
    getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x693b00 ->
    getr R 10 = Z_to_bv 64 ptr -> getr R 11 = Z_to_bv 64 (Z.of_nat (length payload)) -> Z.of_nat (length payload) < 2 ^ 26 ->
    ((length payload = 0%nat /\ ptr = lla_empty Lay) \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB)) ->
    rdn ASEGS M (Z_to_bv 64 ptr) (length payload) = Some payload ->
    credit_le (lla_credit Lay (Z.of_nat (length payload))) cr ->
    (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k LK) + lla_frames Lay k <= ff_cap k) ->
    ls_ok LSt g M ->
    dinvA LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall (fx' : PropExec.FPState) R' M' (model' : Model) g' cr' LK' A',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_upd (sr_after_call_j sr (map ridx c_kept) (length vals)) (ridx 10) (ELit 0)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_libA so stk bls vbnd kn) ->
       dinvA LB LK' cr' A' M' model' -> model_rt model model' -> incl A A' ->
       (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) ->
       ls_ok LSt g' M' ->
       credit_le (credit_sub cr (lla_credit Lay (Z.of_nat (length payload)))) cr' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_LIB_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaeecc) M (seg_rom ASEGS)) model) K.
Proof.
    intros vals ebs sr kn R M model LB LK cr A g so stk bls vbnd ptr ra payload K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal Hstk R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hroom Hls DI Hbl Hvb HK0 CONT.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined scfg L ar C HI HIok sp0 Hsp M0 M0_def _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'. destruct (dlla_stack Lay L DLL) as ((ST1 & ST2) & ST3).
    set (sp := bv_unsigned sp0 + so) in *.
    assert (WDEF : forall a, bv_unsigned sp0 - 6144513 <= a < bv_unsigned sp0 -> M (Z_to_bv 64 a) <> None)
      by (exact (window_defined sp0 Hsp vals ebs (ahid A model) M kn HK Hiw P0)).
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & (B4096 & TOPEQ & _ & _) & TOP47 & _).
    pose proof (LIok fx g LB [] LK cr A sp ptr ra payload R M model K) as MS.
    unfold lib_cfgA in MS. rewrite (dlla_L Lay L DLL), (dla_segs L ar IL sp0 DL), (dlla_entry Lay L DLL) in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *)
      constructor; rewrite ?(dlla_L Lay L DLL), ?(dla_segs L ar IL sp0 DL), ?(dla_tp L ar IL sp0 DL), ?(dlla_gp Lay L DLL); try assumption.
      + split; [exact Hra | exact Hra2].
      + (* [comment removed for export] *)
        rewrite (dla_sptop L ar IL sp0 DL). unfold sp.
        split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros i Hi. apply WDEF. lia.
        * intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlo|Hhi].
          -- apply WDEF. lia.
          -- replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
      + intros f [].
      + (* [comment removed for export] *)
        intros j Hj. apply (di_stksh _ _ _ _ _ _ _ _ _ _ DI). unfold STKTOP, in_shadow_of, S, SB. rewrite (dla_sptop L ar IL sp0 DL) in *.
        set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
        replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        unfold sp in *. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      intros fx' g' R' M' model' cr' LK' A' POST HRT HINC Hh' HMI' HLEAK HH'.
      destruct POST as [Qa0 Qregs Qcr Qframe Qscr Qgrows Qstk Qls].
      rewrite ?(dlla_L Lay L DLL) in *.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (FR : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB [] sp stk a -> ~ in_foot LV a /\ ~ in_junk Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hc [Hf Hj]. apply Qframe; [exact Ha | | exact Hf | exact Hj]. apply (aclient_scr_mono L ar sp0 Hsp LB [] sp stk (lla_stack Lay) a); [lia | exact Hc]. }
      assert (ABOVE : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. apply FR; [lia | | split; [apply not_foot_off_image | apply not_junk_off_image]; lia]. unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp. lia. }
      apply (CONT fx' R' M' model' g' cr' LK' A' HL'); try assumption.
      + (* [comment removed for export] *)
        apply regs_ok_upd_sameA; [| discriminate | cbn [edenot]; symmetry; exact Qa0].
        apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA sp0 Hsp R R' Qregs) c_kept_no0A).
      + (* [comment removed for export] *)
        unfold keep_libA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so stk bls vbnd [] IMG_LIB_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPl LB sp stk (ahid A model) (ahid A' model')) (SCa sp stk)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
        * eapply (regions_callL (vals ++ junk_vals R') ebs so stk bls vbnd LB LK LK' cr cr' A A' M M' model model');
            [exact P0' | lia | lia | exact HH | exact HH' | | ].
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha ((HC & HF) & V1 & V2). unfold mrestrict. rewrite V1, V2. apply FR; assumption.
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH') by (unfold sp in *; lia).
          destruct (Z_lt_le_dec a (sp - lla_stack Lay)) as [Hlo|Hhi].
          -- rewrite Qframe; [apply WDEF; unfold sp in *; lia | unfold sp in *; lia | | apply not_foot_off_image; unfold sp in *; lia | apply not_junk_off_image; unfold sp in *; lia].
             unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp in *. lia.
          -- replace a with (sp - lla_stack Lay + (a - (sp - lla_stack Lay))) by ring. apply Qscr. lia.
      + (* [comment removed for export] *)
        apply DINV; [exact HH' | exact HMI' | exact Hh' | | | | rewrite (model_rt_rdr _ _ HRT); exact (di_rdr _ _ _ _ _ _ _ _ _ _ DI)].
        * intros a Ha. rewrite (ABOVE a Ha). exact (di_above _ _ _ _ _ _ _ _ _ _ DI a Ha).
        * intros x Hx. destruct (stksh_rng scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ x HH Hx) as (XR & XC).
          unfold STKTOP, in_shadow_of, S, SB in Hx. rewrite (dla_sptop L ar IL sp0 DL) in Hx.
          set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
          replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) in Hx by ring.
          destruct (Z_lt_le_dec x (S (sp - lla_stack Lay))) as [Hlo|Hhi].
          -- unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ _ _ _ _ DI x ltac:(unfold STKTOP, in_shadow_of, S, SB; rewrite (dla_sptop L ar IL sp0 DL); fold mx;
                   replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring; exact Hx)) | lia | | split; [apply not_foot_off_image | apply not_junk_off_image]; lia].
             unfold aclient. right. right. right. right. left. exact XC.
          -- replace x with (S (sp - lla_stack Lay) + (x - S (sp - lla_stack Lay))) by ring. apply Qstk.
             rewrite (dla_sptop L ar IL sp0 DL). fold mx. unfold S, SB in *.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             unfold sp in *. lia.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        * intros x Hx. pose proof (hish_rng L ar IL sp0 Hsp DL x Hx) as XR. unfold byte_at.
          rewrite FR; [exact (di_hish _ _ _ _ _ _ _ _ _ _ DI x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx | split; [apply not_foot_off_image | apply not_junk_off_image]; lia].
      + intros a Ha Hb. apply FR; [exact Ha | left; exact Hb |].
        destruct Hb as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _). destruct (WF b Hb) as (HBR & _).
        pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3). split; [apply not_foot_off_image | apply not_junk_off_image]; lia.
      + intros lo hi a Hin Ha. destruct (img_lib_sub lo hi Hin) as ((lo' & hi' & Hin' & S1 & S2) & I1 & I2 & I3 & HOLE).
        apply FR; [lia | | split; [apply not_foot_of_hole | apply not_junk_of_hole]; intros hl hh Hhol; destruct (HOLE hl hh Hhol); lia].
        unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL). split; [lia|].
        apply (dla_client L ar IL sp0 DL lo' hi' a Hin'). lia.
  Qed.
End LibSite.
End FPX_1.

End Na0DrvLibL.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
Module Na0DiagLoopK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0RegionPoisoned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0DiagWritev.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation rom := (seg_rom ASEGS).

(* [comment removed for export] *)
Definition WV_KEEP : list reg := [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%bv.

Lemma wv_keep_cs : forall r, In r WV_KEEP -> In r callee_saved.
Proof. intros r Hr. unfold WV_KEEP in Hr. unfold callee_saved. cbn [In] in *. tauto. Qed.
Lemma wv_keep_not : forall r, In r WV_KEEP -> ~ In r [1; 18; 19; 20; 22]%bv.
Proof.
intros r Hr. unfold WV_KEEP in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hr.
Qed.
Lemma wv_keep_of : forall Lr R R', keeps_but Lr R R' -> incl Lr [1; 18; 19; 20; 22]%bv -> forall r, In r WV_KEEP -> getr R' r = getr R r.
Proof. intros Lr R R' KB Hi r Hr. apply KB; [exact (wv_keep_cs r Hr)|]. intros X. exact (wv_keep_not r Hr (Hi r X)). Qed.

Lemma sbm_fds' : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sbm_rdr : forall m m', same_but_materialized m m' -> m_channel_reader m' = m_channel_reader m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.

Lemma rdn_skipn_Z : forall (M : word -> option byte) a n bs k,
  rdn ASEGS M (Z_to_bv 64 a) (Z.to_nat n) = Some bs -> 0 <= k <= n -> 0 <= a ->
  rdn ASEGS M (Z_to_bv 64 (a + k)) (Z.to_nat (n - k)) = Some (skipn (Z.to_nat k) bs).
Proof.
intros M a n bs k Hr Hk Ha.
pose proof (Mh_0038.SeqExec.rdn_skipn ASEGS M (Z.to_nat n) (Z_to_bv 64 a) bs (Z.to_nat k) Hr ltac:(lia)) as X.
replace (Z.to_nat (n - k)) with (Z.to_nat n - Z.to_nat k)%nat by lia.
replace (Z_to_bv 64 (a + k)) with (Z_to_bv 64 a + nat_to_word (Z.to_nat k))%bv; [exact X|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. rewrite Z2Nat.id by lia.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac cs_in := unfold callee_saved; cbn [In]; repeat first [left; reflexivity | right].
Lemma cs_not10 : forall r : reg, In r callee_saved -> r <> 10%bv.
Proof. intros r Hr ->. unfold callee_saved in Hr. cbn [In] in Hr. repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]). exact Hr. Qed.
Lemma incl_body : incl ([18; 20; 22]%bv : list reg) [1; 18; 19; 20; 22]%bv.
Proof. intros r Hr. cbn [In] in *. tauto. Qed.
Lemma incl_ret : incl ([1; 19]%bv : list reg) [1; 18; 19; 20; 22]%bv.
Proof. intros r Hr. cbn [In] in *. tauto. Qed.
Ltac cs_out := let X := fresh in intros X; cbn [In] in X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.

(* [comment removed for export] *)
Lemma pcE_af0 : v_addi (Z_to_bv 64 0x13f6ac) 4 = (1308336%bv : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b78 : v_addi (Z_to_bv 64 0x13f734) 4 = (1308472%bv : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_af8 : (1308344%bv : word) = Z_to_bv 64 0x13f6b8.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b84 : (1308484%bv : word) = Z_to_bv 64 0x13f744.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b74 : (1308468%bv : word) = Z_to_bv 64 0x13f734.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rdn_frame_w : forall (MV MV' : word -> option byte) a (n : nat) bs,
  rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> MV' x = MV x) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs.
Proof.
intros MV MV' a n bs Hr Ha Hn FR. rewrite <- Hr. apply rdn_agree. intros j Hj. rewrite (u64_lit a) by lia. apply FR. rewrite u64_lit by lia. lia.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

Section Loop.
  Variable H : word -> bool.
  Variable A : list (Z * Z).
  Hypothesis HH : H_off_segments ASEGS H.
  Variable lazy : list (word * word).
  Hypothesis HLC : lazy_cover H lazy A.
  Hypothesis HAwf : A_wf A.
  Variables f fd : Z.
  Hypothesis Hfd : 0 < fd < 2 ^ 31.
  Variables qlo qhi : Z.          (* [comment removed for export] *)
  Hypothesis Hq : 0 <= qlo /\ qlo <= qhi /\ qhi + 16 <= 2 ^ 47.
  Hypothesis Hf : 0 <= f /\ (f + 124 <= qlo \/ qhi + 16 <= f + 120) /\ f + 124 < 2 ^ 63.
  Hypothesis NLq : forall x, qlo <= x < qhi -> page_in_ranges (page_base_of x) lazy = false.
  Variable K : TSet.
  Hypothesis HK0 : K [].

  (* [comment removed for export] *)
  #[using="HH HLC HAwf"] Lemma msteps_vis : forall R (pc : word) M R' (pc' : word) MV' (model : Model) T,
    m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
    msteps ASEGS (mkst R pc (mrestrict H M) rom) (mkst R' pc' MV' rom) ->
    (forall a : word, mrestrict H M a <> None -> MV' a <> None) ->
    (forall M' (model' : Model), MInv A model' -> same_but_materialized model model' ->
        mrestrict H M' = MV' ->
        (forall a : word, MV' a = mrestrict H M a -> M' a = M a) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        srealizes ASEGS scfg (mkCfg (mkst R' pc' M' rom) model') T) ->
    srealizes ASEGS scfg (mkCfg (mkst R pc M rom) model) T.
Proof.
intros R pc M R' pc' MV' model T HL HI Hh MS GR KONT.
apply (rz_msteps_lz ASEGS scfg H A R pc M R' pc' MV' model T HH asegs_wx ltac:(rewrite HL; exact HLC) HAwf HI Hh MS).
intros model' HI' SBM VIS. apply (KONT _ model' HI' SBM VIS).
- intros a Ha. unfold munrestrict. destruct (H a) eqn:E; [reflexivity|]. rewrite Ha. unfold mrestrict. rewrite E. reflexivity.
- intros a Ha. unfold munrestrict. destruct (H a) eqn:E; [exact Ha|]. apply GR. unfold mrestrict. rewrite E. exact Ha.
Qed.

  (* [comment removed for export] *)
  Definition wv_pc (s : bool) : word := if s then Z_to_bv 64 0x13f6ac else Z_to_bv 64 0x13f734.
  Definition wv_regs (s : bool) (R : bvmap 5 word) (q c rem : Z) : Prop :=
    getr R 17%bv = Z_to_bv 64 66 /\ getr R 10%bv = Z_to_bv 64 fd /\ getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 c
    /\ getr R 9%bv = Z_to_bv 64 f /\ getr R 18%bv = Z_to_bv 64 c /\ getr R 22%bv = Z_to_bv 64 rem
    /\ getr R (if s then 19%bv else 20%bv) = Z_to_bv 64 q.

  (* [comment removed for export] *)
  Definition wv_buf (MV : word -> option byte) (b l : Z) (bs : list byte) : Prop :=
    0 <= b /\ 0 <= l /\ b + l <= 2 ^ 47 /\ (l = 0 \/ b + l <= qlo \/ qhi <= b)
    /\ rdn ASEGS MV (Z_to_bv 64 b) (Z.to_nat l) = Some bs
    /\ (forall x, b <= x < b + l -> page_in_ranges (page_base_of x) lazy = false).

  (* [comment removed for export] *)
  Definition wv_iov (MV : word -> option byte) (q c b1 l1 b2 l2 : Z) (bs1 bs2 : list byte) : Prop :=
    qlo <= q /\ q + 16 * c <= qhi /\ (c = 1 \/ c = 2)
    /\ rdn ASEGS MV (Z_to_bv 64 q) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b1))
    /\ rdn ASEGS MV (Z_to_bv 64 (q + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 l1))
    /\ store_ok ASEGS MV (Z_to_bv 64 q) (Z.to_nat (16 * c)) = true
    /\ wv_buf MV b1 l1 bs1
    /\ (c = 1 -> l2 = 0 /\ bs2 = [])
    /\ (c = 2 -> rdn ASEGS MV (Z_to_bv 64 (q + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b2))
                 /\ rdn ASEGS MV (Z_to_bv 64 (q + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 l2))
                 /\ wv_buf MV b2 l2 bs2 /\ 1 <= l1 + l2).

  #[using="f Hq Hf"] Lemma wv_buf_tr : forall MV MV' b l bs, wv_buf MV b l bs ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) -> wv_buf MV' b l bs.
Proof.
intros MV MV' b l bs (B1 & B2 & B3 & B4 & B5 & B6) FR. repeat split; try assumption.
rewrite <- B5. apply rdn_agree. intros j Hj. rewrite u64_lit by lia. apply FR; lia.
Qed.

  #[using="f Hq Hf"] Lemma wv_buf_skip : forall MV b l bs k, wv_buf MV b l bs -> 0 <= k <= l -> wv_buf MV (b + k) (l - k) (skipn (Z.to_nat k) bs).
Proof.
intros MV b l bs k (B1 & B2 & B3 & B4 & B5 & B6) Hk. repeat split; try lia.
- exact (rdn_skipn_Z MV b l bs k B5 Hk B1).
- intros x Hx. apply B6. lia.
Qed.

  Definition wv_done (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
    forall R' M' (model' : Model),
      MInv A model' -> same_but_materialized model model' ->
      (forall r, In r WV_KEEP -> getr R' r = getr R r) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> mrestrict H M' (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      (forall a : word, mrestrict H M a <> None -> mrestrict H M' a <> None) ->
      srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x13f6b8) M' rom) model') K.

  #[using="Type"] Lemma wv_done_tr : forall R M model R1 M1 model1, wv_done R M model ->
    same_but_materialized model model1 ->
    (forall r, In r WV_KEEP -> getr R1 r = getr R r) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> mrestrict H M1 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M1 a <> None) ->
    (forall a : word, mrestrict H M a <> None -> mrestrict H M1 a <> None) ->
    wv_done R1 M1 model1.
Proof.
intros R M model R1 M1 model1 D SBM KR F1 F2 G1 G2 R' M' model' MI SBM' KR' F1' F2' G1' G2'.
apply (D R' M' model' MI (same_but_materialized_trans _ _ _ SBM SBM')).
- intros r Hr. rewrite (KR' r Hr). exact (KR r Hr).
- intros a Ha Hn. rewrite (F1' a Ha Hn). exact (F1 a Ha Hn).
- intros a Ha Hn. rewrite (F2' a Ha Hn). exact (F2 a Ha Hn).
- intros a Ha. exact (G1' a (G1 a Ha)).
- intros a Ha. exact (G2' a (G2 a Ha)).
Qed.

  #[using="Type"] Lemma W64_out : forall (M : word -> option byte) a v (x : word), 0 <= a -> a + 8 <= 2 ^ 64 -> ~ (a <= bv_unsigned x < a + 8) -> W64 M a v x = M x.
Proof.
intros M a v x Ha Hb Hn. unfold W64. destruct (Z_lt_le_dec (bv_unsigned x) a) as [Lt|Ge].
- apply wbytes_below; [rewrite u64_lit by lia; rewrite length_N_to_le_bytes; lia | rewrite u64_lit by lia; exact Lt].
- apply wbytes_above. rewrite u64_lit by lia. rewrite length_N_to_le_bytes. lia.
Qed.
  #[using="Type"] Lemma W64_hit : forall (M : word -> option byte) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> rdn ASEGS (W64 M a v) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Proof. intros M a v Ha Hb. unfold W64. apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. Qed.
  #[using="Type"] Lemma W64_rdn_out : forall (M : word -> option byte) a v x (n : nat) bs, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= x -> x + Z.of_nat n <= 2 ^ 64 ->
    (x + Z.of_nat n <= a \/ a + 8 <= x) -> rdn ASEGS M (Z_to_bv 64 x) n = Some bs -> rdn ASEGS (W64 M a v) (Z_to_bv 64 x) n = Some bs.
Proof.
intros M a v x n bs Ha Hb Hx Hn Hd Hr. rewrite <- Hr. apply rdn_agree. intros j Hj. rewrite u64_lit by lia.
apply W64_out; [exact Ha | exact Hb |]. rewrite u64_lit by lia. lia.
Qed.

  (* [comment removed for export] *)
  Definition wv_loop_stmt (n : nat) : Prop :=
    forall (s : bool) R M (model : Model) q c b1 l1 b2 l2 bs1 bs2,
      (length (bs1 ++ bs2) <= n)%nat ->
      m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
      fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
      m_channel_reader model = true ->
      wv_regs s R q c (l1 + l2) ->
      wv_iov (mrestrict H M) q c b1 l1 b2 l2 bs1 bs2 ->
      l1 + l2 <= 2 ^ 30 ->
      rdn ASEGS (mrestrict H M) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
      wv_done R M model ->
      srealizes ASEGS scfg (mkCfg (mkst R (wv_pc s) M rom) model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).

  #[using="Type"] Lemma wv_buf_len : forall MV b l bs, wv_buf MV b l bs -> length bs = Z.to_nat l.
Proof. intros MV b l bs (_ & _ & _ & _ & B5 & _). exact (rdn_length _ _ _ _ _ B5). Qed.

  (* [comment removed for export] *)
  #[using="HH HLC HAwf Hfd Hq Hf HK0"] Lemma wv_after : forall (n : nat), (forall m, (m < n)%nat -> wv_loop_stmt m) ->
    forall (s : bool) R M (model : Model) q c b1 l1 b2 l2 bs1 bs2 (k : nat),
      (length (bs1 ++ bs2) <= n)%nat -> (k <= length (bs1 ++ bs2))%nat -> (1 <= k)%nat \/ l1 + l2 = 0 ->
      m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
      fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
      m_channel_reader model = true ->
      wv_regs s R q c (l1 + l2) ->
      wv_iov (mrestrict H M) q c b1 l1 b2 l2 bs1 bs2 ->
      l1 + l2 <= 2 ^ 30 ->
      rdn ASEGS (mrestrict H M) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
      wv_done R M model ->
      srealizes ASEGS scfg (mkCfg (mkst (regupd R 10%bv (Z_to_bv 64 (Z.of_nat k))) (v_addi (wv_pc s) 4) M rom) model)
                (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K).
  Proof.
    intros n IH s R M model q c b1 l1 b2 l2 bs1 bs2 k Hn Hk Hk1 HL HI Hh FD RDR RG IOV H30 HFD DONE.
    destruct RG as (G17 & G10 & G11 & G12 & G9 & G18 & G22 & Gq).
    destruct IOV as (Q1 & Q2 & Hc & C0 & C8 & SOK & BUF1 & HC1 & HC2).
    pose proof (wv_buf_len _ _ _ _ BUF1) as LEN1.
    assert (LEN2 : length bs2 = Z.to_nat l2 /\ 0 <= l2).
    { destruct Hc as [->| ->]; [destruct (HC1 eq_refl) as (-> & ->); split; [reflexivity | lia]|].
      destruct (HC2 eq_refl) as (_ & _ & BUF2 & _). split; [exact (wv_buf_len _ _ _ _ BUF2) | exact (proj1 (proj2 BUF2))]. }
    destruct LEN2 as (LEN2 & Hl2). pose proof BUF1 as (Hb1 & Hl1 & Hb1l & _).
    assert (LEN : Z.of_nat (length (bs1 ++ bs2)) = l1 + l2) by (rewrite length_app, LEN1, LEN2; lia).
    set (R1 := regupd R 10%bv (Z_to_bv 64 (Z.of_nat k))).
    assert (R1k : getr R1 10%bv = Z_to_bv 64 (Z.of_nat k)) by (unfold R1; apply getr_same; intros X; discriminate X).
    assert (R1o : forall r : reg, r <> 10%bv -> getr R1 r = getr R r) by (intros r Hr; unfold R1; apply getr_other; exact Hr).
    assert (Hq' : 0 <= q /\ q + 32 < 2 ^ 63) by lia.
    (* [comment removed for export] *)
    assert (RET : exists R2, msteps ASEGS (mkst R1 (v_addi (wv_pc s) 4) (mrestrict H M) rom)
                     (mkst R2 (if Z.eqb (Z.of_nat k) (l1 + l2) then Z_to_bv 64 0x13f6b8 else Z_to_bv 64 0x13f744) (mrestrict H M) rom)
                   /\ getr R2 10%bv = Z_to_bv 64 (Z.of_nat k) /\ getr R2 19%bv = Z_to_bv 64 q
                   /\ (forall r, In r callee_saved -> ~ In r [1; 19]%bv -> getr R2 r = getr R r)).
    { rewrite <- pcE_af8, <- pcE_b84. destruct s; cbn [wv_pc] in *; [rewrite pcE_af0 | rewrite pcE_b78].
      - destruct (wv_ret_A (mrestrict H M) rom q (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' R1 R1k ltac:(rewrite R1o by (intros X; discriminate X); exact G22))
          as (R2 & MS & V10 & KB).
        exists R2. split; [exact MS|]. split; [exact V10|]. split.
        + rewrite (KB 19%bv ltac:(cs_in) ltac:(cs_out)). rewrite R1o by (intros X; discriminate X). exact Gq.
        + intros r Hr Hn'. rewrite (KB r Hr) by (intros X; apply Hn'; cbn [In] in *; tauto). apply R1o. exact (cs_not10 r Hr).
      - destruct (wv_ret_B (mrestrict H M) rom q (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' R1 R1k ltac:(rewrite R1o by (intros X; discriminate X); exact G22)
                    ltac:(rewrite R1o by (intros X; discriminate X); exact Gq)) as (R2 & MS & V10 & V19 & KB).
        exists R2. split; [exact MS|]. split; [exact V10|]. split; [exact V19|].
        intros r Hr Hn'. rewrite (KB r Hr Hn'). apply R1o. exact (cs_not10 r Hr). }
    destruct RET as (R2 & MS2 & V10 & V19 & KB2).
    apply (msteps_vis R1 _ M R2 _ (mrestrict H M) model _ HL HI Hh MS2 (fun a Ha => Ha)).
    intros M2 model2 HI2 SBM2 VIS2 FRM2 GRM2.
    assert (EQ2 : forall a, M2 a = M a) by (intros a; apply FRM2; reflexivity).
    assert (DONE2 : wv_done R2 M2 model2).
    { apply (wv_done_tr R M model R2 M2 model2 DONE SBM2).
      - intros r Hr. apply KB2; [exact (wv_keep_cs r Hr)|]. intros X. exact (wv_keep_not r Hr (incl_ret r X)).
      - intros a _ _. apply EQ2.
      - intros a _ _. rewrite VIS2. reflexivity.
      - exact GRM2.
      - intros a Ha. rewrite VIS2. exact Ha. }
    assert (HL2 : m_vm_lazy model2 = lazy) by (rewrite (sbm_lazy_eq _ _ SBM2); exact HL).
    assert (Hh2 : m_halted model2 = None) by (rewrite (sbm_halted_eq _ _ SBM2); exact Hh).
    assert (FD2 : fd_lookup (m_fds model2) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd))) by (rewrite (sbm_fds' _ _ SBM2); exact FD).
    assert (RDR2 : m_channel_reader model2 = true) by (rewrite (sbm_rdr _ _ SBM2); exact RDR).
    destruct (Z.eqb_spec (Z.of_nat k) (l1 + l2)) as [E|NE].
    - (* [comment removed for export] *)
      rewrite skipn_all2 by lia. cbn [map].
      apply (srz_conseq ASEGS scfg _ K); [|apply t_eq_sym; apply t_emit_nil_eq; exact HK0].
      apply (DONE2 R2 M2 model2 HI2 (same_but_materialized_refl _)); auto.
    - (* [comment removed for export] *)
      assert (Hk1' : (1 <= k)%nat) by (destruct Hk1 as [?|Z0]; [assumption | lia]).
      assert (NPOS : (0 < n)%nat) by lia.
      assert (R2o : forall r : reg, In r callee_saved -> ~ In r [1; 19]%bv -> getr R2 r = getr R r) by exact KB2.
      assert (V18 : getr R2 18%bv = Z_to_bv 64 c) by (rewrite (R2o 18%bv ltac:(cs_in) ltac:(cs_out)); exact G18).
      assert (V22 : getr R2 22%bv = Z_to_bv 64 (l1 + l2)) by (rewrite (R2o 22%bv ltac:(cs_in) ltac:(cs_out)); exact G22).
      assert (V9 : getr R2 9%bv = Z_to_bv 64 f) by (rewrite (R2o 9%bv ltac:(cs_in) ltac:(cs_out)); exact G9).
      assert (Hf' : 0 <= f /\ (f + 124 <= q \/ q + 32 <= f + 120) /\ f + 124 < 2 ^ 63) by lia.
      destruct (Z_le_gt_dec (Z.of_nat k) l1) as [LO|HI'].
      + (* [comment removed for export] *)
        assert (SOK16 : store_ok ASEGS (mrestrict H M) (Z_to_bv 64 q) 16 = true).
        { apply (store_ok_sub ASEGS _ (Z_to_bv 64 q) _ (Z.to_nat (16 * c))); [rewrite u64_lit by lia; lia | exact SOK | lia | rewrite u64_lit by lia; lia]. }
        destruct (wv_body_lo (mrestrict H M) rom f q c (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' b1 l1 fd Hf' ltac:(lia) HFD ltac:(lia) ltac:(lia)
                    R2 ltac:(lia) Hb1 ltac:(lia) C0 C8 SOK16 V10 V19 V18 V22 V9 ltac:(lia))
          as (R3 & MS3 & W17 & W10 & W11 & W12 & W20 & W18 & W22 & KB3).
        rewrite pcE_b84, pcE_b74 in MS3.
        set (MV3 := W64 (W64 (mrestrict H M) q (b1 + Z.of_nat k)) (q + 8) (l1 - Z.of_nat k)) in *.
        assert (FR3f : forall x : word, ~ (q <= bv_unsigned x < q + 16) -> MV3 x = mrestrict H M x).
        { intros x Hx. unfold MV3. rewrite !W64_out; [reflexivity | | | | | |]; lia. }
        assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV3 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)).
        { intros a Ha Hna. apply FR3f. rewrite u64_lit by lia. lia. }
        assert (GR3 : forall a : word, mrestrict H M a <> None -> MV3 a <> None).
        { intros a Ha. unfold MV3, W64. apply wbytes_grows. apply wbytes_grows. exact Ha. }
        rewrite <- VIS2 in MS3. 
        apply (msteps_vis R2 _ M2 R3 _ MV3 model2 _ HL2 HI2 Hh2 MS3 ltac:(rewrite VIS2; exact GR3)).
        intros M3 model3 HI3 SBM3 VIS3 FRM3 GRM3.
        assert (IHn : wv_loop_stmt (n - 1)) by (apply IH; lia).
        replace (skipn k (bs1 ++ bs2)) with (skipn k bs1 ++ bs2).
        2:{ rewrite skipn_app. replace (k - length bs1)%nat with 0%nat by lia. reflexivity. }
        replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia.
        apply (IHn false R3 M3 model3 q c (b1 + Z.of_nat k) (l1 - Z.of_nat k) b2 l2).
        * rewrite length_app, length_skipn, Nat2Z.id. rewrite length_app in Hn. lia.
        * rewrite (sbm_lazy_eq _ _ SBM3); exact HL2.
        * exact HI3.
        * rewrite (sbm_halted_eq _ _ SBM3); exact Hh2.
        * rewrite (sbm_fds' _ _ SBM3); exact FD2.
        * rewrite (sbm_rdr _ _ SBM3); exact RDR2.
        * unfold wv_regs. replace (l1 - Z.of_nat k + l2) with (l1 + l2 - Z.of_nat k) by ring. repeat split; try assumption.
          rewrite (KB3 9%bv ltac:(cs_in) ltac:(cs_out)). exact V9.
        * rewrite VIS3. unfold wv_iov. split; [exact Q1|]. split; [exact Q2|]. split; [exact Hc|].
          split; [unfold MV3; apply W64_rdn_out; [lia | lia | lia | cbn; lia | cbn; lia | apply W64_hit; lia]|].
          split; [unfold MV3; apply W64_hit; lia|].
          split; [apply (store_ok_mono ASEGS _ (mrestrict H M) MV3); [exact GR3 | exact SOK]|].
          split; [apply (wv_buf_tr (mrestrict H M) MV3); [apply wv_buf_skip; [exact BUF1 | lia] | exact FR3]|].
          split; [exact HC1|].
          intros Hc2. destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). 
          split; [apply (rdn_frame_w _ MV3 _ _ _ C16); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia]|].
          split; [apply (rdn_frame_w _ MV3 _ _ _ C24); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia]|].
          split; [exact (wv_buf_tr _ MV3 _ _ _ BUF2 FR3) | lia].
        * lia.
        * rewrite VIS3. apply (rdn_frame_w _ MV3 _ _ _ HFD); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia].
        * apply (wv_done_tr R2 M2 model2 R3 M3 model3 DONE2 SBM3).
          -- exact (wv_keep_of _ R2 R3 KB3 incl_body).
          -- intros a Ha Hna. apply FRM3. rewrite VIS2. apply FR3; assumption.
          -- intros a Ha Hna. rewrite VIS3, VIS2. apply FR3; assumption.
          -- exact GRM3.
          -- intros a Ha. rewrite VIS3. apply GR3. rewrite <- VIS2. exact Ha.
      + (* [comment removed for export] *)
        assert (Hc2 : c = 2) by (destruct Hc as [Hc|Hc]; [destruct (HC1 Hc) as (Z0 & _); lia | exact Hc]).
        destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). pose proof BUF2 as (Hb2 & _ & Hb2l & _). subst c.
        assert (SOK16 : store_ok ASEGS (mrestrict H M) (Z_to_bv 64 (q + 16)) 16 = true).
        { apply (store_ok_sub ASEGS _ (Z_to_bv 64 q) _ (Z.to_nat (16 * 2))); [rewrite u64_lit by lia; lia | exact SOK | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; lia]. }
        destruct (wv_body_hi (mrestrict H M) rom f q 2 (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' l1 fd Hf' ltac:(lia) HFD b2 l2
                    R2 eq_refl ltac:(lia) ltac:(lia) Hb2 ltac:(lia) C8 C16 C24 SOK16 V10 V19 V18 V22 V9 ltac:(lia))
          as (R3 & MS3 & W17 & W10 & W11 & W12 & W20 & W18 & W22 & KB3).
        rewrite pcE_b84, pcE_b74 in MS3.
        set (d := Z.of_nat k - l1) in *.
        set (MV3 := W64 (W64 (mrestrict H M) (q + 16) (b2 + d)) (q + 24) (l2 - d)) in *.
        assert (FR3f : forall x : word, ~ (q + 16 <= bv_unsigned x < q + 32) -> MV3 x = mrestrict H M x).
        { intros x Hx. unfold MV3. rewrite !W64_out; [reflexivity | | | | | |]; lia. }
        assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV3 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)).
        { intros a Ha Hna. apply FR3f. rewrite u64_lit by lia. lia. }
        assert (GR3 : forall a : word, mrestrict H M a <> None -> MV3 a <> None).
        { intros a Ha. unfold MV3, W64. apply wbytes_grows. apply wbytes_grows. exact Ha. }
        rewrite <- VIS2 in MS3.
        apply (msteps_vis R2 _ M2 R3 _ MV3 model2 _ HL2 HI2 Hh2 MS3 ltac:(rewrite VIS2; exact GR3)).
        intros M3 model3 HI3 SBM3 VIS3 FRM3 GRM3.
        assert (IHn : wv_loop_stmt (n - 1)) by (apply IH; lia).
        replace (skipn k (bs1 ++ bs2)) with (skipn (Z.to_nat d) bs2 ++ []).
        2:{ assert (E1 : skipn k bs1 = []) by (apply skipn_all2; lia). rewrite app_nil_r, skipn_app, E1. cbn [app]. f_equal. unfold d. lia. }
        apply (IHn false R3 M3 model3 (q + 16) 1 (b2 + d) (l2 - d) 0 0).
        * rewrite app_nil_r, length_skipn. rewrite length_app in Hn. unfold d. lia.
        * rewrite (sbm_lazy_eq _ _ SBM3); exact HL2.
        * exact HI3.
        * rewrite (sbm_halted_eq _ _ SBM3); exact Hh2.
        * rewrite (sbm_fds' _ _ SBM3); exact FD2.
        * rewrite (sbm_rdr _ _ SBM3); exact RDR2.
        * unfold wv_regs. replace (l2 - d + 0) with (l1 + l2 - Z.of_nat k) by (unfold d; ring). repeat split; try assumption.
          rewrite (KB3 9%bv ltac:(cs_in) ltac:(cs_out)). exact V9.
        * rewrite VIS3. unfold wv_iov. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
          split; [unfold MV3; apply W64_rdn_out; [lia | lia | lia | cbn; lia | cbn; lia | apply W64_hit; lia]|].
          split; [replace (q + 16 + 8) with (q + 24) by ring; unfold MV3; apply W64_hit; lia|].
          split; [apply (store_ok_mono ASEGS _ (mrestrict H M) MV3); [exact GR3 | exact SOK16]|].
          split; [apply (wv_buf_tr (mrestrict H M) MV3); [apply wv_buf_skip; [exact BUF2 | unfold d; lia] | exact FR3]|].
          split; [intros _; split; reflexivity | intros X; discriminate X].
        * unfold d. lia.
        * rewrite VIS3. apply (rdn_frame_w _ MV3 _ _ _ HFD); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia].
        * apply (wv_done_tr R2 M2 model2 R3 M3 model3 DONE2 SBM3).
          -- exact (wv_keep_of _ R2 R3 KB3 incl_body).
          -- intros a Ha Hna. apply FRM3. rewrite VIS2. apply FR3; assumption.
          -- intros a Ha Hna. rewrite VIS3, VIS2. apply FR3; assumption.
          -- exact GRM3.
          -- intros a Ha. rewrite VIS3. apply GR3. rewrite <- VIS2. exact Ha.
  Qed.

  #[using="Type"] Lemma fetch_wv_pc : forall s, fetch_word ASEGS (wv_pc s) = Some ECALLW.
Proof. intros [|]; vm_compute; reflexivity. Qed.

  #[using="HH HLC HAwf Hfd Hq Hf NLq HK0"] Theorem wv_loop : forall n, wv_loop_stmt n.
  Proof.
    intros n. induction n as [n IH] using lt_wf_ind.
    intros s R M model q c b1 l1 b2 l2 bs1 bs2 Hn HL HI Hh FD RDR RG IOV H30 HFD DONE.
    pose proof RG as (G17 & G10 & G11 & G12 & G9 & G18 & G22 & Gq).
    pose proof IOV as (Q1 & Q2 & Hc & C0 & C8 & SOK & BUF1 & HC1 & HC2).
    pose proof BUF1 as (Hb1 & Hl1 & Hb1l & _ & RD1 & NL1).
    pose proof (wv_buf_len _ _ _ _ BUF1) as LEN1.
    assert (NLI : forall m, m <= qhi - q -> nolazy_rng (m_vm_lazy model) (Z_to_bv 64 q) m).
    { intros m Hm j Hj. rewrite HL, u64_lit by lia. apply NLq. lia. }
    assert (UQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply u64_lit; lia).
    assert (C0f := rdn_of_mrestrict ASEGS H M HH _ _ _ C0). assert (C8f := rdn_of_mrestrict ASEGS H M HH _ _ _ C8).
    assert (RD1f := rdn_of_mrestrict ASEGS H M HH _ _ _ RD1).
    destruct Hc as [Hc1|Hc2].
    - (* [comment removed for export] *)
      destruct (HC1 Hc1) as (-> & ->). subst c. rewrite app_nil_r in *. rewrite Z.add_0_r in *.
      destruct (Z.eq_dec l1 0) as [Z0|NZ].
      + (* [comment removed for export] *)
        subst l1. assert (bs1 = []) by (apply length_zero_iff_nil; exact LEN1). subst bs1.
        eapply (rz_writev1_zero_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1));
          [apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
          | exact C0f | rewrite UQ; exact C8f | rewrite UQ; unfold TASK_SIZE; lia | rewrite u64_lit by lia; unfold TASK_SIZE; lia | apply NLI; lia |].
        pose proof (wv_after n IH s R M model q 1 b1 0 b2 0 [] [] 0%nat) as X. cbn [app skipn Z.of_nat] in X. rewrite Z.add_0_r in X.
        apply X; try assumption; try lia.
      + eapply (rz_writev1_wall_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs1 K);
          [apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact RDR | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
          | exact C0f | rewrite UQ; exact C8f | unfold word_to_nat; rewrite u64_lit by lia; exact RD1f
          | rewrite UQ; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia | apply NLI; lia
          | intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL1; lia | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia | exact HK0 |].
        intros k Hk1 Hk2.
        pose proof (wv_after n IH s R M model q 1 b1 l1 b2 0 bs1 [] k) as X. rewrite app_nil_r, Z.add_0_r in X.
        apply X; try assumption; try lia.
    - (* [comment removed for export] *)
      destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). subst c.
      pose proof BUF2 as (Hb2 & Hl2 & Hb2l & _ & RD2 & NL2).
      assert (C16f := rdn_of_mrestrict ASEGS H M HH _ _ _ C16). assert (C24f := rdn_of_mrestrict ASEGS H M HH _ _ _ C24).
      assert (RD2f := rdn_of_mrestrict ASEGS H M HH _ _ _ RD2).
      eapply (rz_writev2_wall_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 b2) (Z_to_bv 64 l2) bs1 bs2 K);
        [apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact RDR | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
        | exact C0f | rewrite UQ; exact C8f | rewrite UQ; exact C16f | rewrite UQ; exact C24f
        | unfold word_to_nat; rewrite u64_lit by lia; exact RD1f | unfold word_to_nat; rewrite u64_lit by lia; exact RD2f
        | rewrite UQ; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia
        | apply NLI; lia
        | intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL1; lia
        | intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL2; lia
        | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; lia | exact HK0 |].
      intros k Hk1 Hk2.
      apply (wv_after n IH s R M model q 2 b1 l1 b2 l2 bs1 bs2 k); try assumption. left; exact Hk1.
  Qed.
End Loop.
End FPX_1.
End Na0DiagLoopK.
Module Na0DrvC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LibTail. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LibTail OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.RefReadLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefPrintfLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvC_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_00387SeqExec7rdn_nthC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib=SymExec2Sound4SX2S9w_add_natC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib7Mh_01267Na0DrvC;w2le1_byteAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib7Mh_01267Na0DrvC3B0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC3B1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC3B2AC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib7Mh_01267Na0DrvC4CFGAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5cfgFAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094<RefPrintfLib9alu_add_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs9cfgF_valAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive8blobs_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs>cfglen_x_cfgFAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvA4ENVAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK46Stdlib9micromega5Tauto8GFormula03K4ELinuxProcessSemantics5Riscv5Instr5aluop01c59OSSVerify5KrLib7Mh_01267Na0DrvC9B0A_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC9B1A_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC:CFGA_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs9cfglen_xAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib7Mh_01267Na0DrvG:inv_block1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3hzAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_01199Na0DrvLib6di_invC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_01199Na0DrvLib:vis_of_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6to_natK69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8iff_reflK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib7Mh_01059SymDriveX:flat_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC=content_byteAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZK69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvG_defs4knGAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symc59OSSVerify5KrLib7Mh_01267Na0DrvC8kbyte48AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC;krange_litAC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I46Stdlib5Lists4List6Exists00I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5knGLAC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma w2le1_byteA : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
Proof.
  intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256 in Hx.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma content_byteA : forall M (A : Z) (data : list byte) j,
  rdn ASEGS M (Z_to_bv 64 A) (length data) = Some data -> (j < length data)%nat ->
  0 <= A -> A + Z.of_nat (length data) < 2 ^ 64 ->
  rdn ASEGS M (Z_to_bv 64 (A + Z.of_nat j)) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j data (Z_to_bv 8 0))))).
Proof.
  intros M A data j Hc Hj HA HA2.
  pose proof (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.rdn_nth ASEGS M (length data) _ data j Hc Hj) as H.
  rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byteA. exact H.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvC.
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
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables auxvp p1 can : word.
  Variable M0 : word -> option byte.
  Variable LK0 : list fframe.
  Variable A0 : list (Z * Z).
  Variable CAP : Z.
  Hypothesis HCAP : 65536 <= CAP <= 67108864.
  Variable crC : credit.
  Hypothesis HLEN : Z.of_nat (length fdata) < CAP.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).

  (* [comment removed for export] *)
  Definition B0A : Z := bv_unsigned (nth 0 fdata (Z_to_bv 8 0)).
  Definition B1A : Z := bv_unsigned (nth 1 fdata (Z_to_bv 8 0)).
  Definition B2A : Z := bv_unsigned (nth 2 fdata (Z_to_bv 8 0)).
  Definition CFGA : Z := (B0A + 256 * B1A) mod 32768.
  Definition PLA : Z := LEN - 6 - CFGA.
  Lemma B0A_range : 0 <= B0A < 256.
  Proof. clear HLEN. unfold B0A. pose proof (bv_unsigned_in_range _ (nth 0 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
  Lemma B1A_range : 0 <= B1A < 256.
  Proof. clear HLEN. unfold B1A. pose proof (bv_unsigned_in_range _ (nth 1 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
  Lemma B2A_range : 0 <= B2A < 256.
  Proof. clear HLEN. unfold B2A. pose proof (bv_unsigned_in_range _ (nth 2 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
  Lemma CFGA_range : 0 <= CFGA < 32768.
  Proof. clear HLEN. unfold CFGA. apply Z.mod_pos_bound. lia. Qed.

  (* [comment removed for export] *)
  Definition target_kA (KT : TSet) : Prop :=
    forall vals R M (model : Model) A (A1 : Z),
      length vals = 81%nat -> hdr_valsA sp0 auxvp p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
      vals_ev vals 71 = Z_to_bv 64 B0A -> vals_ev vals 72 = Z_to_bv 64 B1A -> vals_ev vals 73 = Z_to_bv 64 CFGA ->
      vals_ev vals 79 = Z_to_bv 64 PLA -> vals_ev vals 80 = Z_to_bv 64 B2A ->
      regs_ok (ENVG vals) srT0A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knT0A ->
      rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      dinvA [(A1, CAP)] LK0 crC A M model -> incl A0 A ->
      m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaecfc) M (seg_rom ASEGS)) model) KT.

  (* [comment removed for export] *)
  Lemma ltu_hdr_scA : forall vals M t,
    vals_ev vals 70 = Z_to_bv 64 LEN -> vals_ev vals 71 = Z_to_bv 64 B0A -> vals_ev vals 72 = Z_to_bv 64 B1A ->
    Z.ltb LEN (CFGA + 6) = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_xA (ELit 6))).
  Proof.
    intros vals M t P70 P71 P72 Ht. pose proof B0A_range as R0. pose proof B1A_range as R1. pose proof CFGA_range as RC.
    cbn [sc_denot branch_taken].
    change (edenot (ENVG vals) (EAlu ALU_ADD cfglen_xA (ELit 6))) with (alu64 ALU_ADD (edenot (ENVG vals) cfglen_xA) (Z_to_bv 64 6)).
    change (edenot (ENVG vals) (EVar 70)) with (vals_ev vals 70).
    unfold ENVA. rewrite cfglen_x_cfgFA, P70, P71, P72, cfgF_valA by lia. fold CFGA.
    rewrite alu_add_Z. unfold bv_ltu. rewrite !u_small by (unfold LEN in *; lia). exact Ht.
  Qed.

  (* [comment removed for export] *)
  Lemma content_visA : forall LK cr A M model (u n : Z) (m : nat) bs,
    dinvA [(u, n)] LK cr A M model -> Z.of_nat m <= n ->
    rdn ASEGS M (Z_to_bv 64 u) m = Some bs -> rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 u) m = Some bs.
  Proof.
    intros LK cr A M model u n m bs D Hm HC. pose proof Hsp as Hsp'.
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ D (or_introl eq_refl)) as (_ & _ & (Z1 & Z2 & Z3)).
    rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia. unfold mrestrict.
    rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (u + Z.of_nat j) (di_inv _ _ _ _ _ _ _ _ _ _ D) ltac:(lia)); [reflexivity|].
    right. right. exists (u, n). split; [left; reflexivity | cbn [fst snd]; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma kbyte48A : forall vals MV (A1 : Z) (k : Z) (v : nat),
    vals_ev vals 48 = Z_to_bv 64 A1 -> hzA sp0 A1 CAP ->
    rdn ASEGS MV (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    0 <= k -> (Z.to_nat k < length fdata)%nat ->
    vals_ev vals v = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat k) fdata (Z_to_bv 8 0))) ->
    kentry_ok ASEGS (ENVG vals) MV (KWord (SA (EVar 48) k) 1 (EVar v)).
  Proof.
    intros vals MV A1 k v P48 (Z1 & Z2 & Z3) HC Hk Hkl Pv. pose proof Hsp as Hsp'.
    cbn [kentry_ok]. split; [lia|]. split.
    - apply flat_intro; cbn [edenot ev ENVA]; rewrite ?P48, ?u_small by lia; lia.
    - unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVA]. rewrite P48, Pv, u_small by lia.
      replace (A1 + k) with (A1 + Z.of_nat (Z.to_nat k)) by lia. apply content_byteA; [exact HC | exact Hkl | lia | lia].
  Qed.
  Lemma krange_litA : forall vals MV (v : nat) (x lo hi : Z),
    vals_ev vals v = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> lo <= x <= hi ->
    kentry_ok ASEGS (ENVG vals) MV (KRange (EVar v) lo hi).
  Proof. intros vals MV v x lo hi Pv Hx Hr. cbn [kentry_ok edenot ev ENVA]. rewrite Pv, u_small by lia. lia. Qed.

  Lemma know_GLA : forall vals MV (A1 : Z),
    length vals = 73%nat -> vals_ev vals 48 = Z_to_bv 64 A1 -> hzA sp0 A1 CAP ->
    rdn ASEGS MV (Z_to_bv 64 A1) (length fdata) = Some fdata -> (6 <= length fdata)%nat ->
    vals_ev vals 71 = Z_to_bv 64 B0A -> vals_ev vals 72 = Z_to_bv 64 B1A ->
    know_ok ASEGS (ENVG vals) MV (knGA 6 67108863) ->
    know_ok ASEGS (ENVG vals) MV knGLA.
  Proof.
    intros vals MV A1 HL P48 HZ HC H6 P71 P72 HK. pose proof B0A_range as R0. pose proof B1A_range as R1.
    unfold knGLA, kn_hdrA. apply Forall_app. split; [|exact HK].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    - eapply kbyte48A; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P71].
    - eapply kbyte48A; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P72].
    - eapply krange_litA; [exact P71 | lia | lia].
    - eapply krange_litA; [exact P72 | lia | lia].
  Qed.

  Ltac drv_blockH0 HIok Hsp DL HR HK DI P0 scr NX :=
    let HZ := fresh "HZ" in
    pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
    run_block_lz_with HR HK HZ asegs_wx FUELA STOPS_HA scr NX true;
    [ .. | drv_block_post0 HIok Hsp DL DI P0 HZ ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem hdr_okA : 6 + CFGA <= LEN -> forall KT, target_kA KT -> KT [] ->
    close_kgA scfg ar HI sp0 fs0 fdata auxvp p1 can M0 LK0 A0 CAP crC KT.
  Proof.
    intros Hok KT HKT HKT0. unfold close_kgA.
    intros vals R M model A A1 HL HV P48 P70 HR HK HC DI HINC G1 G2.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as (P0 & P1 & P2 & P3).
    pose proof B0A_range as HB0r. pose proof B1A_range as HB1r. pose proof B2A_range as HB2r. pose proof CFGA_range as HCr.
    assert (ELEN : LEN = Z.of_nat (length fdata)) by reflexivity.
    assert (Hge : (6 <= length fdata)%nat) by lia.
    specialize (HK 6 67108863 ltac:(lia)).
    (* [comment removed for export] *)
    set (vals1 := vals ++ [Z_to_bv 64 B0A; Z_to_bv 64 B1A]).
    assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
    assert (YV : hdr_valsA sp0 auxvp p1 can vals1) by (subst vals1; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
    pose proof YV as (Y0 & _).
    assert (Y48 : vals_ev vals1 48 = Z_to_bv 64 A1) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
    assert (Y70 : vals_ev vals1 70 = Z_to_bv 64 LEN) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Y71 : vals_ev vals1 71 = Z_to_bv 64 B0A).
    { subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    assert (Y72 : vals_ev vals1 72 = Z_to_bv 64 B1A).
    { subst vals1. replace 72%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    pose proof (env_app_regs vals [Z_to_bv 64 B0A; Z_to_bv 64 B1A] _ srGLA R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals [Z_to_bv 64 B0A; Z_to_bv 64 B1A] _ _ (knGA 6 67108863) ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK0.
    fold vals1 in HR1, HK0. change (Env (vals_ev vals1) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals1) in HR1, HK0.
    pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI ltac:(lia) HC) as HCV.
    pose proof (know_GLA vals1 _ A1 HL1 Y48 HZ HCV Hge Y71 Y72 HK0) as HK1.
    clear HR HK HK0 HCV.
    (* [comment removed for export] *)
    drv_blockH0 HIok Hsp DL HR1 HK1 DI Y0 scr_fallA 73%nat.
    { apply (ltu_hdr_scA vals1 _ false Y70 Y71 Y72). apply Z.ltb_ge. lia. }
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
    assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (length fdata) = Some fdata).
    { rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
    clear EQM EQH EQA SBM HR1 HK1 DI HC G1 G2 HDEF. clear M model R.
    (* [comment removed for export] *)
    set (ext := [Z_to_bv 64 CFGA; sx8FA (Z_to_bv 64 B1A);
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (2 + CFGA)) fdata (Z_to_bv 8 0)));
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (3 + CFGA)) fdata (Z_to_bv 8 0)));
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (4 + CFGA)) fdata (Z_to_bv 8 0)));
                 Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (5 + CFGA)) fdata (Z_to_bv 8 0)))]).
    set (vals2 := vals1 ++ ext).
    assert (HL2 : length vals2 = 79%nat) by (subst vals2 ext; rewrite length_app, HL1; reflexivity).
    assert (WV : hdr_valsA sp0 auxvp p1 can vals2) by (subst vals2; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL1; lia); exact YV).
    pose proof WV as (W0 & _).
    assert (W48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y48).
    assert (W70 : vals_ev vals2 70 = Z_to_bv 64 LEN) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y70).
    assert (W71 : vals_ev vals2 71 = Z_to_bv 64 B0A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y71).
    assert (W72 : vals_ev vals2 72 = Z_to_bv 64 B1A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y72).
    assert (WX : forall i, (i < 6)%nat -> vals_ev vals2 (73 + i) = nth i ext (Z_to_bv 64 0)).
    { intros i Hi. subst vals2. replace (73 + i)%nat with (length vals1 + i)%nat by (rewrite HL1; reflexivity).
      rewrite vals_ev_app_r. reflexivity. }
    pose proof (WX 0%nat ltac:(lia)) as W73. pose proof (WX 1%nat ltac:(lia)) as W74.
    pose proof (WX 2%nat ltac:(lia)) as W75. pose proof (WX 3%nat ltac:(lia)) as W76.
    pose proof (WX 4%nat ltac:(lia)) as W77. pose proof (WX 5%nat ltac:(lia)) as W78.
    cbn [nth ext Nat.add] in W73, W74, W75, W76, W77, W78. clear WX.
    (* [comment removed for export] *)
    pose proof (env_app_regs vals1 ext _ srHa _ ltac:(rewrite HL1; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals1 ext _ _ knGLA ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK0.
    fold vals2 in HR1, HK0. change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR1, HK0.
    assert (Ecfg : edenot (ENVG vals2) cfglen_xA = edenot (ENVG vals2) (EVar 73)).
    { unfold ENVA. rewrite cfglen_x_cfgFA, W71, W72, cfgF_valA by lia. fold CFGA. symmetry. exact W73. }
    assert (Esx8 : edenot (ENVG vals2) sx8_xA = edenot (ENVG vals2) (EVar 74)).
    { unfold ENVA. rewrite sx8_x_sx8FA, W72. symmetry. exact W74. }
    pose proof (regs_ok_esub _ _ _ _ _ Esx8 (regs_ok_esub _ _ _ _ _ Ecfg HR1)) as HR2.
    lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRb : regs_ok Ex srHb0 Rx) by (exact HR2) end.
    clear HR HR1 HR2.
    (* [comment removed for export] *)
    pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI0 ltac:(lia) HC1) as HCV.
    assert (HKb : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) knHb0).
    { rewrite knHb0_eq. unfold kn_bmA. apply Forall_app. split; [|exact HK0].
      assert (PXv : edenot (ENVG vals2) PXA = Z_to_bv 64 (A1 + CFGA)).
      { cbn [edenot ev ENVA PXA]. rewrite W48, W73. apply alu_add_Z. }
      assert (KB : forall (j : Z) (v : nat), 2 <= j <= 5 ->
                vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (j + CFGA)) fdata (Z_to_bv 8 0))) ->
                kentry_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) (KWord (SA PXA j) 1 (EVar v))).
      { intros j v Hj Pv. cbn [kentry_ok]. split; [lia|]. split.
        - unfold flat, estart. cbn [a_base a_off]. rewrite PXv, u_small by lia. lia.
        - unfold adenot, v_addi. cbn [a_base a_off]. rewrite PXv, u_small by lia.
          change (edenot (ENVG vals2) (EVar v)) with (vals_ev vals2 v). rewrite Pv.
          replace (A1 + CFGA + j) with (A1 + Z.of_nat (Z.to_nat (j + CFGA))) by lia.
          apply content_byteA; [exact HCV | lia | lia | lia]. }
      constructor; [eapply krange_litA; [exact W73 | lia | lia]|].
      constructor; [apply (KB 2); [lia | exact W75]|].
      constructor; [apply (KB 3); [lia | exact W76]|].
      constructor; [apply (KB 4); [lia | exact W77]|].
      constructor; [apply (KB 5); [lia | exact W78]|].
      assert (BR : forall (v : nat) k, vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth k fdata (Z_to_bv 8 0))) ->
                 kentry_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) (KRange (EVar v) 0 255)).
      { intros v k Pv. pose proof (bv_unsigned_in_range _ (nth k fdata (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
        eapply krange_litA; [exact Pv | lia | lia]. }
      constructor; [exact (BR _ _ W75)|]. constructor; [exact (BR _ _ W76)|].
      constructor; [exact (BR _ _ W77)|]. constructor; [exact (BR _ _ W78)|]. constructor. }
    clear HK HK0.
    (* [comment removed for export] *)
    drv_blockH0 HIok Hsp DL HRb HKb DI0 W0 scr0 79%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
    { rewrite <- HC1. apply rdn_agree. intros j Hj. apply EQA. }
    pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI ltac:(lia) HC2) as HCV2.
    clear EQM EQH EQA SBM HRb HKb DI0 HC1 HCV F1 F2. clear M1 model0 R0.
    (* [comment removed for export] *)
    set (ext2 := [Z_to_bv 64 PLA; Z_to_bv 64 B2A]).
    set (vals3 := vals2 ++ ext2).
    assert (HL3 : length vals3 = 81%nat) by (subst vals3 ext2; rewrite length_app, HL2; reflexivity).
    assert (V79 : vals_ev vals3 79 = Z_to_bv 64 PLA).
    { subst vals3. rewrite <- HL2, <- (Nat.add_0_r (length vals2)). rewrite vals_ev_app_r. reflexivity. }
    assert (V80 : vals_ev vals3 80 = Z_to_bv 64 B2A).
    { subst vals3. replace 80%nat with (length vals2 + 1)%nat by (rewrite HL2; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    pose proof (env_app_regs vals2 ext2 _ srHb _ ltac:(rewrite HL2; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals2 ext2 _ _ knHb0 ltac:(rewrite HL2; vm_compute; reflexivity) HK) as HK0.
    fold vals3 in HR1, HK0. change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR1, HK0.
    assert (TV : hdr_valsA sp0 auxvp p1 can vals3) by (subst vals3; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL2; lia); exact WV).
    assert (T70 : vals_ev vals3 70 = Z_to_bv 64 LEN) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W70).
    assert (T71 : vals_ev vals3 71 = Z_to_bv 64 B0A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W71).
    assert (T72 : vals_ev vals3 72 = Z_to_bv 64 B1A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W72).
    assert (T73 : vals_ev vals3 73 = Z_to_bv 64 CFGA) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W73).
    assert (T48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W48).
    assert (Epl : edenot (ENVG vals3) plen_xA = edenot (ENVG vals3) (EVar 79)).
    { unfold ENVA. rewrite (plen_valA LEN CFGA vals3 _ ltac:(lia) ltac:(unfold LEN in *; lia) T70 T73). symmetry. exact V79. }
    pose proof (regs_ok_esub _ _ _ _ _ Epl HR1) as HR2.
    lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRt : regs_ok Ex srT0A Rx) by (exact HR2) end.
    clear HR HR1 HR2.
    assert (HKt : know_ok ASEGS (ENVG vals3) (mrestrict (ahid A model) M) knT0A).
    { eapply ksubl_sound; [|exact knT0A_sub]. apply Forall_app. split; [|exact HK0]. unfold kn_tgtA.
      constructor; [eapply krange_litA; [exact T73 | lia | lia]|].
      constructor; [eapply krange_litA; [exact V79 | unfold PLA, LEN in *; lia | unfold PLA, LEN in *; lia]|].
      constructor; [eapply kbyte48A; [exact T48 | exact HZ | exact HCV2 | lia | cbn; lia | exact V80]|].
      constructor; [eapply krange_litA; [exact V80 | lia | lia]|]. constructor. }
    clear HK HK0.
    apply (HKT vals3 R M model A A1 HL3 TV T48 T70 T71 T72 T73 V79 V80 HRt HKt HC2 DI HINC G1 G2).
  Qed.


End DrvC.
End FPX_1.
End Na0DrvC.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
Module Na0DrvD_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvC_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvD_defs () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00638SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knTcAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8kn_afterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7ksubl_bC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs;relay_ok_bAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00638SymExec23SX25s_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4spxAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5srLBAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4rT00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4rT10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4rT01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4rT11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knTeAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4sr01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs6srTm0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs6knLH1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knV0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs3rVAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs3rUAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knU0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4sr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4sr10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs4srVAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5rLB1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs6flag1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs6knLc1AC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS_TA : list Z := 0xaedb4 :: 0xaeba0 :: STOPSA.
Definition runTA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_TA scr ss [].

(* [comment removed for export] *)
Definition knTcA (clo chi plo phi : Z) : list kentry := KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: knT0A.
Definition rT00 := Eval vm_compute in runTA scr0 (SS 0xaecfc srT0A [] (knTcA 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runTA scr0 (SS 0xaecfc srT0A [] (knTcA 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runTA scr0 (SS 0xaecfc srT0A [] (knTcA 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runTA scr0 (SS 0xaecfc srT0A [] (knTcA 1 32767 1 67108857) 81).
Definition sr00 : list expr := Eval vm_compute in s_regs (fst (fst rT00)).
Definition sr01 : list expr := Eval vm_compute in s_regs (fst (fst rT01)).
Definition sr10 : list expr := Eval vm_compute in s_regs (fst (fst rT10)).
Definition sr11 : list expr := Eval vm_compute in s_regs (fst (fst rT11)).
Definition calls_xA : expr := Eval vm_compute in nth 21 sr11 (ELit 0).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_case_entryA (K : kentry) : bool :=
  existsb (kentry_eqb K) [KRange (EVar 73) 0 0; KRange (EVar 73) 1 32767; KRange (EVar 79) 0 0; KRange (EVar 79) 1 67108857].
Definition uncaseA (kn : list kentry) : list kentry := List.filter (fun K => negb (is_case_entryA K)) kn.
Definition knTeA : list kentry := Eval vm_compute in uncaseA (kn_after rT11 (knTcA 1 32767 1 67108857)).
(* [comment removed for export] *)
Definition TSO : Z := -208.
Definition knTkA : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knTeA.

(* [comment removed for export] *)
Definition srTm0A : list expr := Eval vm_compute in sr_upd sr11 (ridx 21) (EVar 81).
Definition srU0A : list expr := Eval vm_compute in sr_after_call_j srTm0A (map ridx c_kept) 82.
Definition knU0A : list kentry := Eval vm_compute in kn_blk2A 92 ++ knTkA.
Definition rUA := Eval vm_compute in runTA scr0 (SS 0xaed60 srU0A [] knU0A 114).
Definition srUA : list expr := Eval vm_compute in s_regs (fst (fst rUA)).
(* [comment removed for export] *)
Definition srV0A : list expr := Eval vm_compute in sr_after_call_j srUA (map ridx c_kept) 114.
Definition knV0A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knU0A.
Definition rVA := Eval vm_compute in runTA scr0 (SS 0xaed74 srV0A [] knV0A 146).
Definition srVA : list expr := Eval vm_compute in s_regs (fst (fst rVA)).

(* [comment removed for export] *)
Definition spxA (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition knLH1A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knTkA.
Definition srLHA : list expr :=
  [ELit 0; EVar 85; spxA (-208); ELit 67584; ELit 6896384; EVar 86; EVar 87; EVar 88;
   EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
   EVar 83; EVar 84; ELit 6889680; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 97; EVar 98; EVar 99; EVar 100].
(* [comment removed for export] *)
Definition shared_posA : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_bA (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLHA (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_posA.

(* [comment removed for export] *)
Definition rLB1A := Eval vm_compute in runTA scr0 (SS 0xaedb4 srLHA [] knLH1A 102).
Definition srLBA : list expr := Eval vm_compute in s_regs (fst (fst rLB1A)).
Definition knLc1A : list kentry := Eval vm_compute in kn_after rLB1A knLH1A.
Definition flag1A : list sentry := [SE (SA (ELit 0) 0x6920d4) 1 (ELit 1)].
Definition flag0A : list sentry := [SE (SA (ELit 0) 0x6920d4) 1 (ELit 0)].
(* [comment removed for export] *)
Definition LIBSTK : Z := 1048576.
Definition srLr0A : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLBA (map ridx c_kept) 102) (ridx 10) (ELit 0).

Lemma tgt_itinerary_okA :
  (s_pc (fst (fst rT00)), s_pc (fst (fst rT10)), s_pc (fst (fst rT01)), s_pc (fst (fst rT11))) = (0xaedb4, 0xaedb4, 0x80740, 0x80740)
  /\ ksubl_b (kn_after rT00 (knTcA 0 0 0 0)) knTeA = true /\ ksubl_b (kn_after rT01 (knTcA 0 0 1 67108857)) knTeA = true
  /\ ksubl_b (kn_after rT10 (knTcA 1 32767 0 0)) knTeA = true /\ ksubl_b (kn_after rT11 (knTcA 1 32767 1 67108857)) knTeA = true
  /\ sr_upd sr01 (ridx 21) (EVar 81) = srTm0A
  /\ ksubl_b knTeA knLH1A = true /\ ksubl_b knV0A knLH1A = true /\ kn_after rVA knV0A = knV0A /\ kn_after rUA knU0A = knU0A
  /\ relay_ok_bA (sr_upd sr00 (ridx 21) (EVar 81)) = true /\ relay_ok_bA (sr_upd sr10 (ridx 21) (EVar 81)) = true /\ relay_ok_bA srVA = true
  /\ kn_vars_lt 82 knLH1A = true /\ sr_vars_lt 82 srTm0A = true
  /\ (s_pc (fst (fst rUA)), snd (fst rUA), s_log (fst (fst rUA))) = (0x7ebb8, [], [])
  /\ (s_pc (fst (fst rVA)), snd (fst rVA), s_log (fst (fst rVA))) = (0xaedb4, [], [])
  /\ (s_pc (fst (fst rLB1A)), s_log (fst (fst rLB1A))) = (0xaeecc, flag1A)
  /\ kn_after rLB1A knLH1A = knLc1A
  /\ (nth 10 srLBA (ELit 0), nth 11 srLBA (ELit 0), nth 1 srLBA (ELit 0), nth 2 srLBA (ELit 0)) = (EVar 82, EVar 79, ELit 0xaedc8, spxA (-208)).
Proof.
vm_compute. repeat split; reflexivity. Qed.
End FPX_1.

End Na0DrvD_defs.
Module Na0DrvE_defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvC_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvD_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvLibL.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvE_defs () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z03K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5summEC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib7Mh_01167DrvKitA:kentry_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC59OSSVerify5KrLib7Mh_01056SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8kn_afterC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs4srPAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs3rPAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5rLB1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs4knPAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs4rQtAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs4rQfAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5knQ0AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7ksubl_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs6knLH2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5knQ2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5rLB2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5srLBAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs6knLc2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs4rP2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5knP2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5rSt2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5rSf2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs6srSf2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs6srSt2AC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib7Mh_01058SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs;keep_allocAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs4rT1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5srM1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5rT2fAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5rT2tAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6c_keptC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5srF2AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs3MSOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5knM1AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs5knF2AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvE_defs4rT3AC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition IMG_PF_A : list (Z * Z) :=
  [(0x10000, 0x158000); (0x15b4b8, 0x15b690); (0x15b778, 0x15c3a0); (0x6820d0, 0x693aa8); (0x693ab0, 0x693af8); (0x693b14, 0x693b28);
   (0x693b30, 0x6b4318); (0x6b4728, 0x6b4fb8); (0x6b4fc0, 0x6b6000)].
Definition keep_pfA (so : Z) (bls : list (nat * Z)) (kn : list kentry) : list kentry := kn_keep 0 so 3232 bls [] [] IMG_PF_A IMG_RW_A kn.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition PSO : Z := -288.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition knLr0A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLc1A.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition rPA := Eval vm_compute in runTA scr0 (SS 0xaedc8 srLr0A [] knLr0A 134).
Definition srPA : list expr := Eval vm_compute in s_regs (fst (fst rPA)).
Definition knPA : list kentry := Eval vm_compute in kn_after rPA knLr0A.
(* [comment removed for export] *)
Definition srQ0A : list expr := Eval vm_compute in sr_after_call_j srPA (map ridx c_kept) 134.
Definition knQ0A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knPA.
(* [comment removed for export] *)
Definition rQtA := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xaeec0 srQ0A [] knQ0A 166).
Definition rQfA := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xaeec0 srQ0A [] knQ0A 166).

Definition summE (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), length (s_log (fst (fst r)))).

Lemma loop_itinerary_okA :
  summE rPA = (0x6a2d4, [SCStoreOk (SA (ELit 0) 0x6920d4) 1], 134%nat, 10%nat)      (* [comment removed for export] *)
  /\ snd (fst rLB1A) = [SCStoreOk (SA (ELit 0) 0x6920d4) 1]                              (* [comment removed for export] *)
  /\ (nth 1 srPA (ELit 0), nth 2 srPA (ELit 0), nth 10 srPA (ELit 0), nth 11 srPA (ELit 0), nth 19 srPA (ELit 0))
     = (ELit 0xaeec0, EAlu ALU_ADD (EVar 0) (ELit (-288)), ELit 86406, EAlu ALU_ADD (EVar 0) (ELit (-264)), ELit 0)
  (* [comment removed for export] *)
  /\ forallb (fun K => existsb (kentry_eqb K) knPA)
       [KWr (SA (EVar 0) (-6144513)) (6144513); KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1409024; KWord (SA (ELit 0) 7027520) 8 (EVar 3)] = true
  /\ sr_vars_lt 134 srPA = true /\ kn_vars_lt 134 knPA = true
  /\ (s_pc (fst (fst rQtA)), snd (fst rQtA), s_log (fst (fst rQtA))) = (0xaedb4, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst rQfA)), snd (fst rQfA), s_log (fst (fst rQfA))) = (0x8073c, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (nth 1 (s_regs (fst (fst rQfA))) (ELit 0), nth 10 (s_regs (fst (fst rQfA))) (ELit 0)) = (ELit 0xaedf4, EVar 83)
  /\ kn_after rQtA knQ0A = knQ0A /\ kn_after rQfA knQ0A = knQ0A.
Proof.
vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knLH2A : list kentry := Eval vm_compute in filter (kentry_vars_lt 81) knQ0A.
Definition rLB2A := Eval vm_compute in runTA scr0 (SS 0xaedb4 srLHA [] knLH2A 102).
Definition knLc2A : list kentry := Eval vm_compute in kn_after rLB2A knLH2A.      (* [comment removed for export] *)
Definition knLr2A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLc2A.
Definition rP2A := Eval vm_compute in runTA scr0 (SS 0xaedc8 srLr0A [] knLr2A 134).
Definition knP2A : list kentry := Eval vm_compute in kn_after rP2A knLr2A.
Definition knQ2A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knP2A.
(* [comment removed for export] *)
Definition rSt2A := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xaeec0 srQ0A [] knLH2A 166).
Definition rSf2A := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xaeec0 srQ0A [] knLH2A 166).
Definition srSt2A : list expr := Eval vm_compute in s_regs (fst (fst rSt2A)).
Definition srSf2A : list expr := Eval vm_compute in s_regs (fst (fst rSf2A)).
(* [comment removed for export] *)
Definition srF1A : list expr := Eval vm_compute in sr_after_call_j srSf2A (map ridx c_kept) 166.
Definition knF1A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knLH2A.
Definition rT1A := Eval vm_compute in runTA scr0 (SS 0xaedf4 srF1A [] knF1A 198).
Definition srM1A : list expr := Eval vm_compute in s_regs (fst (fst rT1A)).
Definition knM1A : list kentry := Eval vm_compute in kn_after rT1A knF1A.
(* [comment removed for export] *)
Definition rT2fA := Eval vm_compute in runA (SCR [false] [] []) (SS 0xaeba0 srM1A [] knM1A 198).
Definition rT2tA := Eval vm_compute in runA (SCR [true] [] []) (SS 0xaeba0 srM1A [] knM1A 198).
Definition srF2A : list expr := Eval vm_compute in sr_after_call_j (s_regs (fst (fst rT2fA))) (map ridx c_kept) 198.
Definition knF2A : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] (kn_after rT2fA knM1A).
(* [comment removed for export] *)
Definition rT3A := Eval vm_compute in runA scr0 (SS 0xaec28 srF2A [] knF2A 230).

Lemma loop2_itinerary_okA :
  ksubl_b knQ0A knLH2A = true /\ ksubl_b knQ2A knLH2A = true /\ kn_vars_lt 81 knLH2A = true
  /\ summE rLB2A = summE rLB1A /\ s_regs (fst (fst rLB2A)) = srLBA /\ kn_after rLB2A knLH2A = knLc2A
  /\ summE rP2A = (0x6a2d4, [SCStoreOk (SA (ELit 0) 0x6920d4) 1], 134%nat, 10%nat) /\ s_regs (fst (fst rP2A)) = srPA
  /\ forallb (fun K => existsb (kentry_eqb K) knP2A)
       [KWr (SA (EVar 0) (-6144513)) (6144513); KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1409024; KWord (SA (ELit 0) 7027520) 8 (EVar 3)] = true
  /\ (s_pc (fst (fst rSt2A)), snd (fst rSt2A), s_log (fst (fst rSt2A))) = (0xaedb4, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst rSf2A)), snd (fst rSf2A), s_log (fst (fst rSf2A))) = (0x8073c, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (nth 1 srSf2A (ELit 0), nth 10 srSf2A (ELit 0), nth 21 srSt2A (ELit 0)) = (ELit 0xaedf4, EVar 83, EAluw ALU_ADD (EVar 81) (ELit (-1)))
  /\ kn_after rSt2A knLH2A = knLH2A /\ kn_after rSf2A knLH2A = knLH2A.
Proof.
vm_compute. repeat split; reflexivity. Qed.

Lemma tail_itinerary_okA :
  summE rT1A = (0xaeba0, [], 198%nat, 0%nat) /\ nth 2 srM1A (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit (-128))
  /\ (s_pc (fst (fst rT2fA)), snd (fst rT2fA), s_log (fst (fst rT2fA))) = (0x8073c, [SCBr false BC_LT (EVar 74) (ELit 0)], [])
  /\ (s_pc (fst (fst rT2tA)), snd (fst rT2tA), s_log (fst (fst rT2tA))) = (0x8073c, [SCBr true BC_LT (EVar 74) (ELit 0)], [])
  /\ (nth 1 (s_regs (fst (fst rT2fA))) (ELit 0), nth 10 (s_regs (fst (fst rT2fA))) (ELit 0)) = (ELit 0xaec28, EVar 48)
  /\ (nth 1 (s_regs (fst (fst rT2tA))) (ELit 0), nth 10 (s_regs (fst (fst rT2tA))) (ELit 0)) = (ELit 0xaec28, EVar 48)
  /\ sr_after_call_j (s_regs (fst (fst rT2tA))) (map ridx c_kept) 198 = srF2A
  /\ ksubl_b (keep_allocA MSO 4096 [] [] (kn_after rT2tA knM1A)) knF2A = true
  /\ summE rT3A = (0x137cc8, [], 230%nat, 0%nat)
  /\ (nth 1 (s_regs (fst (fst rT3A))) (ELit 0), nth 2 (s_regs (fst (fst rT3A))) (ELit 0), nth 4 (s_regs (fst (fst rT3A))) (ELit 0), nth 10 (s_regs (fst (fst rT3A))) (ELit 0))
     = (ELit 1275140, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 6896384, ELit 0).
Proof.
vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
End Na0DrvE_defs.
Module Na0DrvD.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefPrintfLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvC_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvD_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvLibL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvD () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C46Stdlib5Lists4List:nth_firstnC46Stdlib5Lists4List8app_nth1I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC47Corelib4Init5Logic6eq_symC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List8app_nth2C47Corelib4Init3Nat3addC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C46Stdlib5Lists4List:length_appC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula07C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD9ridx_litAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib7Mh_01267Na0DrvD8lay_extAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8len_layAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD6relayAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8vals_loAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8vals_hiAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22ebC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib7Mh_01267Na0DrvD9relayA_81C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphc59OSSVerify5KrLib7Mh_01267Na0DrvD9relayA_loC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib5Lists4List2Inc59OSSVerify5KrLib7Mh_01267Na0DrvD;relay_ok_bDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC47Corelib4Init9Datatypes9andb_propC59OSSVerify5KrLib=SymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses8or_morphK46Stdlib9micromega5Tauto8GFormula02c59OSSVerify5KrLib7Mh_01267Na0DrvD;sr_get_natAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD<relayA_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun<edenot_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG>regs_ok_by_nthC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5srLHAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD;shared_posDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib7Mh_01267Na0DrvC3B2AC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegI47Corelib4Init5Logic4True00c59OSSVerify5KrLib7Mh_01267Na0DrvD6CALLSAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC:CFGA_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC4CFGAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvC3PLAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List<length_skipnc59OSSVerify5KrLib7Mh_01267Na0DrvD8payloadAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD7callsFAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5zseqAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs8in_zseqAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions5bv_eqK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD;callsFA_tabC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_01267Na0DrvA4ENVAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knTcAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119<Na0DrvC_defs5knT0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD9PLA_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib7Mh_01267Na0DrvD6lh1_kAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG9hdr_valsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_0126:Na0DrvLibLAregs_ok_upd_sameAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvG:inv_block1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib3hzAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD:relayA_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD8lh_valsAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive8blobs_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD;relayA_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA7ksubl_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA;ksubl_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun=know_ok_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs5knTeAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib7Mh_01267Na0DrvA4fds0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD<payloadA_lenC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0126<Na0DrvD_defs6knLH1AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01267Na0DrvD4cr1AC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma wseg_init : wseg_ok ASEGS (Z_to_bv 64 0x6920d0) 1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvD ()) [] "p;2p;1p;3p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0p1005gp4p710R9p8P0p1006Gp4p710R0p8p1006dp4p70R:P1p8P:P2p8P:P3p8P:p1007TR;p4p710p8P:P;p4p7210p8P:P5p8P:P4p8P:P7p8P:P8p8p10081p4p710R:P3p8P:P7p8p1008Np4p70R:P1p8P:P2p8P:p1009<p4p7210p8P:P3p8P:p1009Xp4p7210p8P:P5p8P:P4p8P:P6p8P:P7p8P:p100:Gp4p7210p8P:P8p8P:p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R:P1p8P:P2p8P:P5p8P:P4p8P:P8p8p100=Ap4p710R:P3p8P:p100>Gp4p710R6p8P:P7p8P:P0p8P:p100>fp4p710R:p8p100?Ep4p710R0P6p8P0P7p8P0p100@Lp4p710p8P0P9p8P0P:p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P:P3p8P:P7p8g00B?j29Tg00BYj13Tg00C7j11Tg00C\j12Tg00DAj18Tg00D_j27Tg00EEj14Tg00Edj35Tg00Fbj36Tf0#2#2p=0g00G<R7g00G\R:'9g00H<g00IQR3#0#0#0#3%13#2#1#0#1#0#1#2#0#0#1#1#2#1#0#0#8'7g00J6#435=67:do"). Qed.
(* [comment removed for export] *)
Lemma wseg_ax : wseg_ok ASEGS (Z_to_bv 64 0x6b3b50) 544 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvD ()) [] "p;2p;1p;3p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0p1005gp4p710R9p8P0p1006Gp4p710R0p8p1006dp4p70R:P1p8P:P2p8P:P3p8P:p1007TR;p4p710p8P:P;p4p7210p8P:P5p8P:P4p8P:P7p8P:P8p8p10081p4p710R:P3p8P:P7p8p1008Np4p70R:P1p8P:P2p8P:p1009<p4p7210p8P:P3p8P:p1009Xp4p7210p8P:P5p8P:P4p8P:P6p8P:P7p8P:p100:Gp4p7210p8P:P8p8P:p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R:P1p8P:P2p8P:P5p8P:P4p8P:P8p8p100=Ap4p710R:P3p8P:p100>Gp4p710R6p8P:P7p8P:P0p8P:p100>fp4p710R:p8p100?Ep4p710R0P6p8P0P7p8P0p100@Lp4p710p8P0P9p8P0P:p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P:P3p8P:P7p8g00B?j2:Tg00BYj15Tg00C7j12Tg00C\j13Tg00DAj19Tg00D_j28Tg00Edj36Tg00Fbj37Tg00EEj10Tf0R7#3#3p=4%07#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00G<R7g00G\R:':g00H<g00IQR3#4#4#4#5%23#3#2#3#2#2#4#2#2#2#3#2#2#3#2#3#2#4#4#9'8g00J6#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#136=77:do"). Qed.
(* [comment removed for export] *)
Ltac entry_store :=
  cbn [sc_denot]; unfold adenot, v_addi; cbn [a_base a_off edenot];
  lazymatch goal with |- store_ok _ _ _ ?n = true =>
    first [ apply (store_ok_window ASEGS _ (Z_to_bv 64 0x6b3b50) _ 544%nat n 0x6b3b50 0x6b3d70);
              first [exact wseg_ax | reflexivity | lia | (vm_compute; intuition discriminate) | (rewrite u_small by lia; lia)]
          | apply (store_ok_window ASEGS _ (Z_to_bv 64 0x6920d0) _ 1%nat 1%nat 0x6920d0 0x6920d1);
              first [exact wseg_init | reflexivity | lia | (vm_compute; intuition discriminate)] ]
  end.

(* [comment removed for export] *)
Ltac drv_blockT0 HIok Hsp DL HR HK DI P0 scr NX :=
  let HZ := fresh "HZ" in
  pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
  run_block_lz_with HR HK HZ asegs_wx FUELA STOPS_TA scr NX true;
  [ .. | drv_block_post0 HIok Hsp DL DI P0 HZ ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vals_loA : forall (vals ext : list word) (n j : nat),
  (n <= length vals)%nat -> (j < n)%nat -> vals_ev (firstn n vals ++ ext) j = vals_ev vals j.
Proof.
  intros vals ext n j Hn Hj. unfold vals_ev. rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
Lemma vals_hiA : forall (vals ext : list word) (n i : nat),
  (n <= length vals)%nat -> vals_ev (firstn n vals ++ ext) (n + i) = nth i ext (Z_to_bv 64 0).
Proof.
  intros vals ext n i Hn. unfold vals_ev. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (n + i - Nat.min n (length vals))%nat with i by lia. reflexivity.
Qed.
Lemma len_layA : forall (vals ext : list word) n, (n <= length vals)%nat -> length (firstn n vals ++ ext) = (n + length ext)%nat.
Proof. intros. rewrite length_app, length_firstn. lia. Qed.
Lemma ridx_litA : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sr_get_natA : forall sr n, (0 < n < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat n)) = nth n sr (ELit 0).
Proof.
  intros sr n Hn. unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_litA by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lay_extA (vals : list word) (R : bvmap 5 word) (W : word) : list word :=
  [vals_ev vals 81; getr R 9; getr R 18; getr R 19; getr R 1; getr R 5; getr R 6; getr R 7;
   getr R 10; getr R 11; getr R 12; getr R 13; getr R 14; getr R 15; getr R 16; getr R 17;
   getr R 28; getr R 29; getr R 30; getr R 31; W].
Definition relayA (vals : list word) (R : bvmap 5 word) (W : word) : list word := firstn 81 vals ++ lay_extA vals R W.

Lemma relayA_len : forall vals R W, (81 <= length vals)%nat -> length (relayA vals R W) = 102%nat.
Proof. intros. unfold relayA. rewrite len_layA by lia. reflexivity. Qed.
Lemma relayA_lo : forall vals R W j, (81 <= length vals)%nat -> (j < 81)%nat -> vals_ev (relayA vals R W) j = vals_ev vals j.
Proof. intros. unfold relayA. apply vals_loA; lia. Qed.
Lemma relayA_81 : forall vals R W, (81 <= length vals)%nat -> vals_ev (relayA vals R W) 81 = vals_ev vals 81.
Proof.
  intros vals R W H. unfold relayA.
  change (vals_ev (firstn 81 vals ++ lay_extA vals R W) 81) with (vals_ev (firstn 81 vals ++ lay_extA vals R W) (81 + 0)).
  rewrite vals_hiA by lia. reflexivity.
Qed.
Lemma relayA_101 : forall vals R W, (81 <= length vals)%nat -> vals_ev (relayA vals R W) 101 = W.
Proof.
  intros vals R W H. unfold relayA.
  change (vals_ev (firstn 81 vals ++ lay_extA vals R W) 101) with (vals_ev (firstn 81 vals ++ lay_extA vals R W) (81 + 20)).
  rewrite vals_hiA by lia. reflexivity.
Qed.
Lemma relayA_agree : forall ebs vals R W, (82 <= length vals)%nat ->
  env_agree 82 (Env (vals_ev vals) ebs) (Env (vals_ev (relayA vals R W)) ebs).
Proof.
  intros ebs vals R W HL. split; [|reflexivity]. intros n Hn. cbn [ev].
  destruct (Nat.eq_dec n 81) as [->|Hne]; [symmetry; apply relayA_81; lia | symmetry; apply relayA_lo; lia].
Qed.

(* [comment removed for export] *)
Definition shared_posD : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_bD (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLHA (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_posD.

Lemma relayA_regs : forall ebs vals sr R W,
  (82 <= length vals)%nat -> relay_ok_bD sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  regs_ok (Env (vals_ev (relayA vals R W)) ebs) srLHA R.
Proof.
  intros ebs vals sr R W HL Hokb HR.
  unfold relay_ok_bD in Hokb. rewrite forallb_forall in Hokb.
  assert (SH : forall i, In i shared_posD -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot (Env (vals_ev (relayA vals R W)) ebs) (nth i srLHA (ELit 0))).
  { intros i Hi. pose proof (Hokb i Hi) as H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1.
    rewrite <- H1. rewrite <- (edenot_agree 82 _ _ _ (relayA_agree ebs vals R W HL) H2).
    assert (Hi32 : (0 < i < 32)%nat) by (unfold shared_posD in Hi; cbn in Hi; lia).
    rewrite (HR (Z_to_bv 5 (Z.of_nat i))), sr_get_natA by exact Hi32. reflexivity. }
  apply regs_ok_by_nth. intros i Hi.
  assert (JK : forall r k, nth r srLHA (ELit 0) = EVar (81 + k) -> nth k (lay_extA vals R W) (Z_to_bv 64 0) = getr R (Z_to_bv 5 (Z.of_nat r)) ->
               getr R (Z_to_bv 5 (Z.of_nat r)) = edenot (Env (vals_ev (relayA vals R W)) ebs) (nth r srLHA (ELit 0))).
  { intros r k Hr Hk. rewrite Hr. cbn [edenot ev]. unfold relayA. rewrite vals_hiA by lia. symmetry. exact Hk. }
  do 32 (destruct i as [|i]; [first [lia | apply SH; cbn; tauto | eapply JK; reflexivity] |]). lia.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvD.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables p0 p1 can : word.
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Variable LK0 : list fframe.
  Variable A0 : list (Z * Z).
  (* [comment removed for export] *)
  Variable CAP : Z.
  Hypothesis HCAP : 65536 <= CAP <= 67108864.
  Variable crC : credit.
  Hypothesis HLEN : Z.of_nat (length fdata) < CAP.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).
  Let CFG : Z := CFGA fdata.
  Let PL : Z := PLA fdata.
  Let B2 : Z := B2A fdata.
  Let target_k := target_kA scfg ar HI sp0 fs0 fdata p0 p1 can M0 LK0 A0 CAP crC.

  (* [comment removed for export] *)
  Hypothesis Hok : 6 + CFG <= LEN.
  (* [comment removed for export] *)
  Hypothesis Hcr1 : 0 < PL -> acredit_ok L crC PL.

  Definition CALLSA : Z := if CFG =? 0 then 1 else B2 mod 4 + 1.
  Definition payloadA : list byte := skipn (Z.to_nat (6 + CFG)) fdata.
  (* [comment removed for export] *)
  Definition cr1A : credit := if PL =? 0 then crC else adebit L crC PL.

  #[using="sp0 LEN PL"] Lemma CALLSA_range : 1 <= CALLSA <= 4.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvD ()) ["FPX_1"; "DrvD"] "p'0h07__arithh14__ffh28__varmaph35__with42Hah56__sat1h66__sat2h74__x1h81Hh96__sat3h:6__sat4h;6__sat5h<6__sat6h=1bi001bh>6heq_B2p;2p;1p;3p;4p;8p;7p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0p1005gp4p710R9p8P0p1006Gp4p710R0p8p1006dp4p70R:P1p8P:P2p8P:P3p8P:p1007TR;p4p710p8P:P;p4p7210p8P:P5p8P:P4p8P:P7p8P:P8p8p10081p4p710R:P3p8P:P7p8p1008Np4p70R:P1p8P:P2p8P:p1009<p4p7210p8P:P3p8P:p1009Xp4p7210p8P:P5p8P:P4p8P:P6p8P:P7p8P:p100:Gp4p7210p8P:P8p8P:p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R:P1p8P:P2p8P:P5p8P:P4p8P:P8p8p100=Ap6051000R:P3p8P:p100>Gp4p710R6p8P:P7p8P:P0p8P:p100>fp4p710R:p8p100?Ep6051000R0P6p8P0P7p8P0p100@Lp4p710p8P0P9p8P0P:p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P:P3p8P:P7p8g01>Bj2XTg00DAj17Tg00C\j14Tg019Vj2?Tg00oHj2@Tg00QXj21Tg00S;j23Tg00C7j18Tg01goj2FTg00PUj25Tg01hWj2BTg01i4j3ATg00WVj1WTg00L4j1UTg00Y4j1TTg00Z0j1MTg00ZNj1LTg013Gj29Tg00]Mj2JTg00B?j2=Tg00]oj2ITg00Fbj3<Tg00^[j3GTg00_:j4HTg00[\j4;Tg01iXj3ETg01j?j1KTg01k7j2>Tg00BYj1DTg01:Yj2CTg00XVj2NTg00[9j2OTg00\kj1PTg012Aj3QTg00dkj8RTg00ccj7STg00dGj7VTg00jRR7f0R:'1p=0g00enR3f1R8g00loP:C;p=6P8g00hSR0g00i2R4P4g00iRR5P:g00j2FSp=2f2R2P0P4P4P5P8P:FVp=:p,3CFG/X7g00G<R1P1g00IQR9#7R6P1P3P:P6p,2B2R;%49R<#4R=#7R>'?R?/@6n0100000020000R@'111@>'3P:%7<R@%8<#8#8#8#7R<'FRA157@%0<1B@<RB,57[[RC%0@RDg01khREAA@<8UW4R<%0B\E^4DRDg00k0RE#WRB%UERE%T3R@%M3RF%L3RG1936RH/6H,2G193>RI,6H,2G3:1JG5RJP:P2g00G\RK,=11I:2=<1KdAG378CHRKb1b2b31166116>'3P:b0b5b6PAPCP<PDPBPEP@PFP31937R@g00mVR1PIC;,2GPJPKb1b2b3157>P:b0b5b69E;>%0?R715?>'3p,5fdata#KR2,=3A<3;2R2eP2PAPCP<PD1>;>%0;%0>P7[[%4=#4R=#4#4#Dp,3sp0'CR7%7=R='>%07%0=1?7=#0[[PBPE1N38PFPGP0P4P4P51O39R9,6@,2GP3P9P1PIC;,2G5:G%P4AQ39HR9,6H,2G169I,2G5:GGRPJPKb1b2b3X73%0:15:>'31@86R8,16118>'3[^73P:P?f6O2b0b9b:b;b<b>b8n0110000020001b=g01lDR?,1611?>'3eo"). Qed.
  #[using="sp0 Hsp CAP HCAP HLEN LEN CFG B2 Hok"] Lemma PLA_range : 0 <= PL <= 67108857.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvD ()) ["FPX_1"; "DrvD"] "h02Hah14__p1h24__p2h34__x1h44__x2h54__x3h61Hh77__arithh84__ffh96__sat1h:6__sat2h;8__varmaph<5__with=4cstrp;2p;1p;3p;4p;7p;6p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0g005gR9p4p710R:p8P0p1006Gp4p710R0p8p1006dp4p70R;P1p8P;P2p8P;P3p8P;p1007TR<p4p710p8P;P<p4p7210p8P;P5p8P;P4p8P;P7p8P;P8p8p10081p4p710R;P3p8P;P7p8p1008Np4p70R;P1p8P;P2p8P;p1009<p4p7210p8P;P3p8P;p1009Xp4p7210p8P;P5p8P;P4p8P;P6p8P;P7p8P;p100:Gp4p7210p8P;P8p8P;p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R;P1p8P;P2p8P;P5p8P;P4p8P;P8p8p100=Ap6051000R;P3p8P;p100>Gp4p710R6p8P;P7p8P;P0p8P;p100>fp4p710R;p8p100?Ep6051000R0P6p8P0P7p8P0p100@Lp4p710p8P0P:p8P0P;p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P;P3p8P;P7p8g01m?j2gTg01n>j1fTg00C\j10Tg00DAj12Tg00PUj2<Tg00S;j28Tg00BYj1OTg00KQj1LTP9j2JTg00R4j1ITg00OXj1HTg01goj2dTg01hWj2^Tg01i4j3ZTg00EEj1=Tg00Toj2:Tg00VAj3ATg00Vjj2VTg00WVj1UTg00X6j3TTg00L4j1STg00XVj2RTg00Y4j1NTg00YRj4CTg00Z0j1MTg00ZNj1KTg013Gj2;Tg00[9j2?Tg00\kj1PTg00C7j13Tg012Aj3QTg00[\j4ETg012dj3GTg00]Mj2eTg00B?j2cTg00]oj2bTg00Fbj3_Tg00^[j3]Tg00_:j4\Tg00oHj2[Tg00QXj26Tg00oej2FTg01o7j1YTg00ccj7XTg00c?j6`Tg00dGj7aTg00dkj8WTg00jRR9f0R7'6p=1%07#0#0#0p=9%37#3#3#3p=5g00enR;f1R3g00loP7CEp=7P3g00hSR8g00i2R0P0g00iRR4P7g00j2FXp=4P3P8P0P0P4P7E`p=Bf2R5P8P0P0P4P3P7Fap=@%07#0p=Df3R2P8P0P0P4P5P3P7GWp=>p,3sp0p,5fdataR8'g%f8R1#1g00IQR:#0R6#0R<#0R=#9#9#9R>#2,<1R?'8%O=#L/J8R=#I%H=R=#1%26R@%56#2RA'd1<9@%1A1^@ARB,<9[[%1@RCg01khRDAZ@A3UW0%1B\D^0Cp-0RCg00k0RDg00J6RB#=RA#=R@#=#=,:;1:;@1:;A1:;B5A;5A;5A;g00k\'V%UD3T%SDP;P;1R;2P5%N;RDCCP3PDCC%M;%K;RD1;;9RB1?;6R6'7,4Df5RA,BD5@D%P0R0PD%3:R@#0#2RE,;;RF=Q;61?;:R:'7,4DP0PDP;P:g00mV1?;<R<CE,4DP0PDf6,BD%0>R>#D#9#9#2RG,;;,7<,4D5@DP0AG;:F=G;6R6,7B,4D%3@#5#5#5#5#5#D#3#2R@,;;,76,4D5@DC>C>C>C>1eD4P7P5g00G<RDg00G\R4'c1b75=_D4dA];93C\b8b;b<X3;X4;X5;X1CW2%13/821[E5/63f4R3,<5f716AG'81F3E/FARA#116A@'8[[[[^3;^4;^5;^1C^2CP7%2>p,3CAPR>'6P?P>P1P=P3p,3Hokp,4HLENp,4HCAPO9b7b9b:b=b6%Y8R8#1168@'8eo"). Qed.
  #[using="sp0 Hsp B2"] Lemma payloadA_len : length payloadA = Z.to_nat PL.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvD ()) ["FPX_1"; "DrvD"] "h01xh12Hah24__p1h34__p2h44__p3h54__x1h64__x2h74__x3h84__x4h94__x5h:1nh;1Hh<2H1h=2H2h>2H3h?7__arithh@4__ffhA6__sat4hB6__sat5hC8__varmaphD5__withE4cstrhF1mhG1yhH2z1hI2z2hJ2z3p&0p;1p;2p;3p;<p;4p;6p;Bp;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0g003]R7p4p710R8p9P0p1004;p4p710R9p9P0p10053p4p710p8P0p1005JR:p4p710p8P0P:p4p7210p8P0g005gR:p4p710R;p8P0p1006Gp4p710R0p8p1006dp4p70R<P1p8P<P2p8P<P3p8P<p1007TR=p4p710p8P<P=p4p7210p8P<P5p8P<P4p8P<P8p8P<P9p8p10081p4p710R<P3p8P<P8p8p1008Np4p70R<P1p8P<P2p8P<p1009<p4p7210p8P<P3p8P<p1009Xp4p7210p8P<P5p8P<P4p8P<P6p8P<P8p8P<p100:Gp4p7210p8P<P9p8P<p100;;p4p7210p8p100;Zp4p70P8p8p100<Up4p7210R<P1p8P<P2p8P<P5p8P<P4p8P<P9p8p100=Ap6051000R<P3p8P<g01ooR6p4p710R=p8P<P8p8P<P0p8P<g020MR<p4p710R0p8p100?Ep6051000R>P=p8P>P8p8P>p100@Lp4p710p8P>P;p8P>P0p8p100@np4p710P8p8p100AIp4p70R>P1p8P>P2p8P>P5p8P>P4p8P>P8p8P>P9p8P0P3p8P0P8p8g00C\j1KTg00BYj1jTg00KQj1aTP:j2UTg00C7j1?Tg00DAj1ITg00oHj2MTg0196R:j1ETg00o1j2VTg00Fbj35j1WTg01m?j2_Tg01n>j1\Tg00PUj2[Tg00S;j20Tg00OXR8j1STg00oej23Tg010_j2kTg011Bj3iTg00B?j2FTg00bZl<cTg00R4j1bTg011_j2NTg00SVj2BTg01goj2`Tg01hWj2^Tg01i4j3]Tg00EEj1ATg00Toj2<Tg00T0k105Tg00TNk204Tg00UXj3TTg00WVk103Tg00L4k102Tg00Y4j1xTg00XVj2LTg00YRj4OTg00Z0j1vTg00ZNj1uTg013Gj2XTg00[9j2DTg012dj3RTg00[\j4GTg00\kj1pTg012Aj3oTg00]Mj2lTg00]oj2mTg00^[j3nTg00_:j4hTg00_lj4qTg01o7j1rTP6j3gTP<j3sTP7j6tTg00QXj2ZTg010Bj2fTg01=0l<wTg00b4lBdTg00VAj3yTg00Vjj2zTg00X6j3{Tg00ccj7|Tg00dGj7}Tg00\Gj7~Tg00c?k600Tg00dkk801Tf0R7#K#Kp=9g00jRR</Z7p=C1f<7p=;g00enR6f1R0;57p=4P6g00eOR3P6P6P:f4R:P8f3R9g01=Uf2R>P0P7M<wp=YP3P3P3P6P6P6g015aP8P8P8f6R4g016Af5R5P:P9P>P0P7MBdp=e1[<7p=71Z7<p==A567<p=>Ay607p=1g00k\,z7p=:g00k0R2?{07p=6P0g00hSR1g00i2R;P;g00iRR=P7g00j2F|p=2P6P0g00lHP7CGp=@P>P1P;P;P=P0P7F}p=8P6P0g00loP7CGp=HP>P1P;P;P=P0P7F~p=QP0P1P;P;P=P7J00p=PP9P1P;P;P=P>P0P7L01p=JP3g00IQR1#KR?#9R@#j#aRAp,5fdataRB'URC%?1RD#KRE#IRFp,3CFG'M#ERG'Vp,2PL#ERH9537X:3p,3sp0/_B%\BRI#C%9@#9#9#9#9#9#I,[IR@'01MFIRJ#ERK,VCRL%SCRM/3F/3IRN#ERO553%;JRP,3M#;RQ%;NRR'4P3P6%W3P8%W6%S0%S7'4A53071k073iXG3X03PLPQ1307#;XF6X:6PCPM1F6MPKPPP7X06RK%;7X06RQPJPJ1F6JDYFePOPRPKPQPNPN1F6NDYM<c%bC%CM1N<N%7N14RN'0%=N%>R'0'BPRP61N<J%7JRR14PJ'0%=J%>P'0'BPPP613M7RP,N<%7P%;PRJ/4P'0%=P%>J'0'B13M0#;P6%I?RJ%??RP#?#?#?#IRN'`%7J%CN1^JNRC#7[[%CJRQg01khRKA]JN0UW1%CC\K^1Qp-0RQg00J6RK#A#ARC#ARN#ARJ#ARO#A,<6R81<6JRJ1<6NRN'1'1#:RS&051-046RT1<6ORO5T6RU1<6CRC1<6KRK'1RV'1RW#:AT6TC/1KRK,1O#:AT6TJRT/1N,18#:118W#:11JV,1U#:11TK,1O#:&032'6'6'6'6'6'6,6S'6&022P6P6%x6P>1L6:COP0P61L69P51L65COCO%v6%u6R2P61X6<RSg00mVRO1D6PRP%?D,D6RD5R6RTCG,221D61R1/@T,225821HTS,221@1S,225825Q2%p;R;P2f7RT,P21X6FRK1D6ERE5o6RU,@D,225821HUS,22f8RU,P25825Q2P;P2P6PSPOAR6PK=R6ERKCG,221D6?R?/@K,225821HKS,221@?S,225825Q2P;P21HSE,22f9,P2582P;1@1?,22CJCJCJCJ1l2=P7P>g00G<R2g00G\R='F1m7>=52=dAn6<0Chb@bCbDX56X66X76X86X96X2QX3QW413>:R>#7147>'0%=>%>7'0'B1MF:R>,45,04%=>/0T'B13:F/35RF#7149F'0%=F%>9'0'B%C4f:RF'014:5[[[[^56^66^76^86^96^2Q^3Q^4QP7P@%>5PRP5PIPMPTP9P:P4PUPFO<b?bAbBbJb>bIb=bHb<bECqb;%rB#E953LeAgAGB,UAAsAGBEtg020n,UA=53Heo"). Qed.

  (* [comment removed for export] *)
  Definition lh_valsA (vals : list word) (A1 PTR OWN k : Z) : Prop :=
    length vals = 102%nat /\ hdr_valsA sp0 p0 p1 can vals
    /\ vals_ev vals 48 = Z_to_bv 64 A1 /\ vals_ev vals 70 = Z_to_bv 64 LEN
    /\ vals_ev vals 73 = Z_to_bv 64 CFG /\ vals_ev vals 79 = Z_to_bv 64 PL
    /\ vals_ev vals 81 = Z_to_bv 64 k /\ vals_ev vals 82 = Z_to_bv 64 PTR /\ vals_ev vals 83 = Z_to_bv 64 OWN.

  (* [comment removed for export] *)
  Definition blk_factsA (A1 PTR OWN : Z) (LB : list (Z * Z)) : Prop :=
    ablock_range L ar A1 CAP /\
    ((PL = 0 /\ PTR = 0x6920e0 /\ OWN = 0 /\ LB = [(A1, CAP)])
     \/ (0 < PL /\ PTR = OWN /\ ablock_range L ar OWN PL /\ blocks_apart OWN PL [(A1, CAP)] /\ LB = [(OWN, PL); (A1, CAP)])).

  (* [comment removed for export] *)
  Definition lh1_kA (K : TSet) : Prop :=
    forall (fx' : PropExec.FPState) vals R M (model : Model) A (A1 PTR OWN : Z) LB,
      lh_valsA vals A1 PTR OWN CALLSA ->
      regs_ok (ENVG vals) srLHA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLH1A ->
      blk_factsA A1 PTR OWN LB ->
      rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      rdn ASEGS M (Z_to_bv 64 PTR) (length payloadA) = Some payloadA ->
      dinvA LB LK0 cr1A A M model -> incl A0 A ->
      m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R (Z_to_bv 64 0xaedb4) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition callsFA (v80 : word) : word :=
    edenot (Env (fun n => match n with 80%nat => v80 | _ => Z_to_bv 64 0 end) (blobs_ev [])) calls_xA.
  #[using="Type"] Lemma calls_x_callsFA : forall vals bl, edenot (Env (vals_ev vals) (blobs_ev bl)) calls_xA = callsFA (vals_ev vals 80).
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvD ()) ["FPX_1"; "DrvD"] "h02blh14valsp;1p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0p1005gp4p710R9p8P0p1006Gp4p710R0p8p1006dp4p70R:P1p8P:P2p8P:P3p8P:p1007TR;p4p710p8P:P;p4p7210p8P:P5p8P:P4p8P:P7p8P:P8p8p10081p4p710R:P3p8P:P7p8p1008Np4p70R:P1p8P:P2p8P:p1009<p4p7210p8P:P3p8P:p1009Xp4p7210p8P:P5p8P:P4p8P:P6p8P:P7p8P:p100:Gp4p7210p8P:P8p8P:p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R:P1p8P:P2p8P:P5p8P:P4p8P:P8p8p100=Ap6051000R:P3p8P:p100>Gp4p710R6p8P:P7p8P:P0p8P:p100>fp4p710R:p8p100?Ep6051000R0P6p8P0P7p8P0p100@Lp4p710p8P0P9p8P0P:p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P:P3p8P:P7p8g00C\j11Tg00BYj15Tg00KQj14Tg00L4j13Tg00a9j28Tg021kj17Tg00B?j26Tg00EEj10Tf0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2g00IQ#1#1#1R7#1#1#1#5#4R:#3%57#4#3#3f1g00J6#2#2#2#2#2'8#7,6:W0W1o"). Qed.
  #[using="Type"] Lemma callsFA_tab : forallb (fun b => Z.eqb (bv_unsigned (callsFA (Z_to_bv 64 b))) (b mod 4 + 1)) (zseqA 256) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvD ()) ["FPX_1"; "DrvD"] "h01bp;2p;1p;3p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0p1005gp4p710R9p8P0p1006Gp4p710R0p8p1006dp4p70R:P1p8P:P2p8P:P3p8P:p1007TR;p4p710p8P:P;p4p7210p8P:P5p8P:P4p8P:P7p8P:P8p8p10081p4p710R:P3p8P:P7p8p1008Np4p70R:P1p8P:P2p8P:p1009<p4p7210p8P:P3p8P:p1009Xp4p7210p8P:P5p8P:P4p8P:P6p8P:P7p8P:p100:Gp4p7210p8P:P8p8P:p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R:P1p8P:P2p8P:P5p8P:P4p8P:P8p8p100=Ap6051000R:P3p8P:p100>Gp4p710R6p8P:P7p8P:P0p8P:p100>fp4p710R:p8p100?Ep6051000R0P6p8P0P7p8P0p100@Lp4p710p8P0P9p8P0P:p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P:P3p8P:P7p8g00B?j2>Tg00C\j12Tg00BYj18Tg00D_j24Tg021kj1=Tg01:Yj2;Tg00DAj13Tg019Vj27Tg00oHj25Tg01>Bj26Tg022gj19Tg01Wlj3:Tg00Fbj3<Tg00EEj10Tf0R7#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00G<R:g00G\R3'>g00enR8g00IQR0#2#2R4#2#2#2#2#8R51457#=';%34,77%30'5'6X08g00J6#1#1#1#1#1#1#1#1#93:=<:3do"). Qed.
  #[using="sp0 fdata LEN CFG PL B2"] Lemma callsFA_val : forall b, 0 <= b < 256 -> callsFA (Z_to_bv 64 b) = Z_to_bv 64 (b mod 4 + 1).
  Proof.
    intros b Hb. pose proof callsFA_tab as T. rewrite forallb_forall in T.
    specialize (T b (proj2 (in_zseqA 256 b) ltac:(cbn; lia))). apply Z.eqb_eq in T.
    apply bv_eq. rewrite T. symmetry. apply u_small. pose proof (Z.mod_pos_bound b 4 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 Hsp CAP HCAP HLEN LEN B2 Hok"] Lemma know_TcA : forall vals M clo chi plo phi,
    vals_ev vals 73 = Z_to_bv 64 CFG -> vals_ev vals 79 = Z_to_bv 64 PL ->
    clo <= CFG <= chi -> plo <= PL <= phi ->
    know_ok ASEGS (ENVG vals) M knT0A -> know_ok ASEGS (ENVG vals) M (knTcA clo chi plo phi).
  Proof.
    intros vals M clo chi plo phi P73 P79 HC HP HK. pose proof (CFGA_range sp0 fdata) as RC. pose proof PLA_range as RP.
    unfold knTcA. constructor; [|constructor; [|exact HK]]; cbn [kentry_ok edenot ev ENVA].
    - rewrite P73, u_small by (subst CFG; lia). lia.
    - rewrite P79, u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="fx C IL HIok Hsp DL HCAP target_k"] Lemma pl0_to_lhA : forall K (fx' : PropExec.FPState) vals1 srX R' M' (model' : Model) A (A1 : Z),
    lh1_kA K ->
    length vals1 = 82%nat -> hdr_valsA sp0 p0 p1 can vals1 ->
    vals_ev vals1 48 = Z_to_bv 64 A1 -> vals_ev vals1 70 = Z_to_bv 64 LEN -> vals_ev vals1 73 = Z_to_bv 64 CFG ->
    vals_ev vals1 79 = Z_to_bv 64 PL -> vals_ev vals1 81 = Z_to_bv 64 CALLSA ->
    regs_ok (ENVG vals1) srX R' -> relay_ok_bD (sr_upd srX (ridx 21) (EVar 81)) = true ->
    nth 9 srX (ELit 0) = ELit 0x6920e0 -> nth 18 srX (ELit 0) = ELit 0 ->
    edenot (ENVG vals1) (nth 21 srX (ELit 0)) = Z_to_bv 64 CALLSA ->
    know_ok ASEGS (ENVG vals1) (mrestrict (ahid A model') M') knTeA ->
    rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata ->
    PL = 0 -> dinvA [(A1, CAP)] LK0 crC A M' model' -> incl A0 A -> m_fds model' = fds0 -> m_fs model' = fs0 ->
    srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xaedb4) M' (seg_rom ASEGS)) model') K.
  Proof.
    intros K fx' vals1 srX R' M' model' A A1 HLH HL1 WV W48 W70 W73 W79 V81 HR' Hrel H9 H18 H20 HK' HC1 HPL0 DI HINC F1 F2.
    pose proof Hsp as Hsp'.
    assert (Hpay : payloadA = []).
    { pose proof payloadA_len as X. rewrite HPL0 in X. destruct payloadA; [reflexivity | discriminate]. }
    assert (HR2 : regs_ok (ENVG vals1) (sr_upd srX (ridx 21) (EVar 81)) R').
    { apply regs_ok_upd_sameA; [exact HR' | discriminate |].
      rewrite (HR' (21%bv : reg)). change (sr_get srX (21%bv : reg)) with (nth 21 srX (ELit 0)). rewrite H20.
      cbn [edenot ev ENVA]. exact V81. }
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & _ & _).
    set (valsL := relayA vals1 R' (Z_to_bv 64 0)).
    apply (HLH fx' valsL R' M' model' A A1 0x6920e0 0 [(A1, CAP)]).
    - (* [comment removed for export] *)
      unfold lh_valsA, hdr_valsA in *. subst valsL. rewrite (relayA_len vals1 R' _ ltac:(lia)), relayA_81 by lia.
      rewrite !(relayA_lo vals1 R' _) by lia.
      repeat split; try tauto; try assumption.
      + unfold relayA. change 82%nat with (81 + 1)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
        rewrite (HR' (9%bv : reg)). change (sr_get srX (9%bv : reg)) with (nth 9 srX (ELit 0)). rewrite H9. reflexivity.
      + unfold relayA. change 83%nat with (81 + 2)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
        rewrite (HR' (18%bv : reg)). change (sr_get srX (18%bv : reg)) with (nth 18 srX (ELit 0)). rewrite H18. reflexivity.
    - (* [comment removed for export] *)
      subst valsL. eapply (relayA_regs _ vals1 _ R' _ ltac:(lia)); [exact Hrel | exact HR2].
    - (* [comment removed for export] *)
      subst valsL. eapply (know_ok_agree ASEGS 82); [apply relayA_agree; lia | vm_compute; reflexivity |].
      eapply ksubl_sound; [exact HK' | vm_compute; reflexivity].
    - split; [exact HBR|]. left. repeat split; lia.
    - exact HC1.
    - rewrite Hpay. reflexivity.
    - unfold cr1A. rewrite (proj2 (Z.eqb_eq PL 0) HPL0). exact DI.
    - exact HINC.
    - exact F1.
    - exact F2.
  Qed.

  #[using="C IL HIok ICok Hsp Hal DL M0_def HCAP HLEN Hok Hcr1"] Theorem drv_targetA : forall K, lh1_kA K -> K [] -> target_k K.
  Proof.
    intros K HLH HK0. unfold target_k, target_kA.
    intros vals R M model A A1 HL HV P48 P70 P71 P72 P73 P79 P80 HR HK HC DI HINC F1 F2.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & _ & HZ). pose proof HZ as (Q1 & Q2 & Q4).
    pose proof (CFGA_range sp0 fdata) as HCr. pose proof PLA_range as HPr. pose proof (B2A_range sp0 fdata) as HB2r. pose proof CALLSA_range as HKr.
    assert (ELEN : LEN = Z.of_nat (length fdata)) by reflexivity.
    assert (EPL : PL = LEN - 6 - CFG) by reflexivity.
    fold CFG in P73, HCr. fold PL in P79. fold B2 in P80, HB2r. fold LEN in P70.
    pose proof HV as (P0 & _).
    assert (HPAY0 : rdn ASEGS M (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA).
    { unfold payloadA. rewrite length_skipn.
      pose proof (rdn_skipn ASEGS M (length fdata) (Z_to_bv 64 A1) fdata (Z.to_nat (6 + CFG)) HC ltac:(lia)) as X.
      rewrite w_add_nat, u_small in X by lia.
      replace (A1 + Z.of_nat (Z.to_nat (6 + CFG))) with (A1 + 6 + CFG) in X by lia. exact X. }
    (* [comment removed for export] *)
    set (vals1 := vals ++ [Z_to_bv 64 CALLSA]).
    assert (HL1 : length vals1 = 82%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
    assert (V81 : vals_ev vals1 81 = Z_to_bv 64 CALLSA).
    { subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
    assert (VL : forall j x, (j < 81)%nat -> vals_ev vals j = x -> vals_ev vals1 j = x).
    { intros j x Hj Hx. subst vals1. rewrite vals_ev_app_l by (rewrite HL; exact Hj). exact Hx. }
    assert (WV : hdr_valsA sp0 p0 p1 can vals1) by (subst vals1; apply (hdr_appA sp0 fdata); [exact HV | rewrite HL; lia]).
    pose proof WV as (W0 & _).
    pose proof (VL 48%nat _ ltac:(lia) P48) as W48. pose proof (VL 70%nat _ ltac:(lia) P70) as W70.
    pose proof (VL 73%nat _ ltac:(lia) P73) as W73. pose proof (VL 79%nat _ ltac:(lia) P79) as W79. pose proof (VL 80%nat _ ltac:(lia) P80) as W80.
    pose proof (env_app_regs vals [Z_to_bv 64 CALLSA] _ srT0A R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know ASEGS vals [Z_to_bv 64 CALLSA] _ _ knT0A ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
    fold vals1 in HR1, HK1. change (Env (vals_ev vals1) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals1) in HR1, HK1.
    clear HR HK. rename HR1 into HR.
    clearbody vals1. clear VL HL HV P0 P48 P70 P71 P72 P73 P79 P80 vals.
    (* [comment removed for export] *)
    assert (HCALLS : CALLSA = (if CFG =? 0 then 1 else B2 mod 4 + 1)) by reflexivity.
    assert (Ecx : (CFG =? 0) = false -> edenot (ENVG vals1) calls_xA = Z_to_bv 64 CALLSA).
    { intros E. unfold ENVA. rewrite calls_x_callsFA, W80, callsFA_val by lia. rewrite HCALLS, E. reflexivity. }
    (* [comment removed for export] *)
    assert (POST : forall M' (model' : Model) log,
               log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W_A log = true ->
               mrestrict (ahid A model) M' = mem_denot (ENVG vals1) (mrestrict (ahid A model) M) log ->
               (forall a, ahid A model a = true -> M' a = M a) ->
               same_but_materialized model model' ->
               rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata
               /\ rdn ASEGS M' (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA
               /\ m_fds model' = fds0 /\ m_fs model' = fs0).
    { intros M' model' log Hlog EQM EQH SBM. destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      split; [|split; [|split; [exact G1 | exact G2]]].
      - apply (content_block0 sp0 Hsp fdata vals1 _ A M M' model log A1 CAP (length fdata) fdata W0 Hlog EQM EQH HZ ltac:(lia) HC).
      - apply (content_block0 sp0 Hsp fdata vals1 _ A M M' model log (A1 + 6 + CFG) (CAP - 6 - CFG) (length payloadA) payloadA W0 Hlog EQM EQH);
          [unfold hzA in *; lia | rewrite payloadA_len; lia | exact HPAY0]. }
    destruct (Z.eq_dec PL 0) as [HPL0 | HPLp].
    - (* [comment removed for export] *)
      destruct (CFG =? 0) eqn:ECFG.
      + (* [comment removed for export] *)
        pose proof (know_TcA vals1 _ 0 0 0 0 W73 W79 ltac:(apply Z.eqb_eq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
        drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
        1-4: entry_store.
        lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
          destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & _ & G1 & G2) end.
        eapply (pl0_to_lhA K fx vals1 sr00 R0 M1 model0 A A1 HLH HL1 WV W48 W70 W73 W79 V81 HR0);
          [ vm_compute; reflexivity | reflexivity | reflexivity | cbn [nth sr00 edenot]; rewrite HCALLS; reflexivity
          | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPL0 | exact DI0 | exact HINC | exact G1 | exact G2 ].
      + (* [comment removed for export] *)
        pose proof (know_TcA vals1 _ 1 32767 0 0 W73 W79 ltac:(apply Z.eqb_neq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
        drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
        1-4: entry_store.
        lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
          destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & _ & G1 & G2) end.
        eapply (pl0_to_lhA K fx vals1 sr10 R0 M1 model0 A A1 HLH HL1 WV W48 W70 W73 W79 V81 HR0);
          [ vm_compute; reflexivity | reflexivity | reflexivity | change (nth 21 sr10 (ELit 0)) with calls_xA; apply Ecx; reflexivity
          | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPL0 | exact DI0 | exact HINC | exact G1 | exact G2 ].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (TAILm : forall srX R' M' (model' : Model),
                 regs_ok (ENVG vals1) srX R' -> sr_upd srX (ridx 21) (EVar 81) = srTm0A ->
                 edenot (ENVG vals1) (nth 21 srX (ELit 0)) = Z_to_bv 64 CALLSA ->
                 know_ok ASEGS (ENVG vals1) (mrestrict (ahid A model') M') knTeA ->
                 rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata ->
                 rdn ASEGS M' (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA ->
                 dinvA [(A1, CAP)] LK0 crC A M' model' -> m_fds model' = fds0 -> m_fs model' = fs0 ->
                 srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x80740) M' (seg_rom ASEGS)) model') K).
      2:{ destruct (CFG =? 0) eqn:ECFG.
          - pose proof (know_TcA vals1 _ 0 0 1 67108857 W73 W79 ltac:(apply Z.eqb_eq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
            drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
            1-4: entry_store.
            lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
              destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & HPAY1 & G1 & G2) end.
            apply (TAILm sr01 _ _ _ HR0); [vm_compute; reflexivity | cbn [nth sr01 edenot]; rewrite HCALLS; reflexivity
              | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPAY1 | exact DI0 | exact G1 | exact G2].
          - pose proof (know_TcA vals1 _ 1 32767 1 67108857 W73 W79 ltac:(apply Z.eqb_neq in ECFG; lia) ltac:(lia) HK1) as HK. clear HK1.
            drv_blockT0 HIok Hsp DL HR HK DI W0 scr0 82%nat.
            1-4: entry_store.
            lazymatch goal with EQM : mrestrict _ _ = mem_denot _ _ ?log |- _ =>
              destruct (POST _ _ log ltac:(vm_compute; reflexivity) EQM EQH SBM) as (HC1 & HPAY1 & G1 & G2) end.
            apply (TAILm sr11 _ _ _ HR0); [vm_compute; reflexivity | change (nth 21 sr11 (ELit 0)) with calls_xA; apply Ecx; reflexivity
              | eapply ksubl_sound; [exact HK1 | vm_compute; reflexivity] | exact HC1 | exact HPAY1 | exact DI0 | exact G1 | exact G2]. }
      clear POST HC HPAY0 HK1 HR DI F1 F2. clear M model R.
      intros srX R M model HR1 HsrX H20 HK HC1 HPAY1 DI G1 G2.
      assert (HR2 : regs_ok (ENVG vals1) srTm0A R).
      { rewrite <- HsrX. apply regs_ok_upd_sameA; [exact HR1 | discriminate |].
        rewrite (HR1 (21%bv : reg)). change (sr_get srX (21%bv : reg)) with (nth 21 srX (ELit 0)). rewrite H20.
        cbn [edenot ev ENVA]. exact V81. }
      clear HR1 HsrX H20.
      (* [comment removed for export] *)
      eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals1 _ srTm0A knTeA R M model [(A1, CAP)] LK0 crC A PL TSO
                [(48%nat, 65536)] [] 0xaed60 K);
        [ exact HR2 | exact HK
        | rewrite HL1; vm_compute; reflexivity | rewrite HL1; vm_compute; reflexivity | rewrite HL1; lia
        | exact W0 | vm_compute; reflexivity
        | regv HR2 (2%bv : reg); cbn [edenot ev ENVA]; rewrite W0; apply alu_add_w_litA
        | unfold TSO; lia | reflexivity
        | regv HR2 (10%bv : reg); cbn [edenot ev ENVA]; exact W79
        | lia
        | apply Hcr1; lia
        | regv HR2 (4%bv : reg); reflexivity
        | regv HR2 (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DI
        | intros i nb Hf; cbn in Hf;
          destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL1; lia|];
                                           rewrite W48, u_small by lia; exists CAP; split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
        | intros v b Hf; discriminate
        | exact HK0 | ].
      intros R' M' model' A' u vals' E' HL' HA2 HR' HK' DI' HRT HINC' HBR2 HAP HSHB HAB HBLK HIMG. subst vals' E'.
      set (vals2 := vals1 ++ junk_vals R') in *.
      change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
      rewrite HL1 in HL', HA2, HR', HK'. change (82 + 10)%nat with 92%nat in HA2, HK'. change (82 + 32)%nat with 114%nat in HL'.
      destruct (model_rt_fds _ _ HRT) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U3). pose proof HBR2 as (_ & _ & U4 & _ & _).
      assert (NEQ : u <> A1).
      { specialize (HAP (A1, CAP) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
      assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W0).
      assert (XV : hdr_valsA sp0 p0 p1 can vals2) by (subst vals2; apply (hdr_appA sp0 fdata); [exact WV | rewrite HL1; lia]).
      assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W48).
      assert (X73 : vals_ev vals2 73 = Z_to_bv 64 CFG) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W73).
      assert (X79 : vals_ev vals2 79 = Z_to_bv 64 PL) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact W79).
      (* [comment removed for export] *)
      apply Forall_app in HK' as [HKB HK'].
      assert (HKU : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A' model') M') knU0A).
      { change knU0A with (kn_blk2A 92 ++ knTkA). apply Forall_app. split.
        - unfold kn_blk2A. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVA]; rewrite HA2, u_small by lia; lia.
        - exact HK'. }
      clear HK' HKB HK HR2.
      (* [comment removed for export] *)
      assert (HC2 : rdn ASEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC1. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply HBLK; [lia|].
        exists (A1, CAP). split; [left; reflexivity|]. cbn [fst snd]. lia. }
      assert (HPAY2 : rdn ASEGS M' (Z_to_bv 64 (A1 + 6 + CFG)) (length payloadA) = Some payloadA).
      { rewrite <- HPAY1. apply rdn_agree. intros k Hk. rewrite payloadA_len in Hk. rewrite u_small by lia. apply HBLK; [lia|].
        exists (A1, CAP). split; [left; reflexivity|]. cbn [fst snd]. lia. }
      clear HC1 HPAY1 DI HBLK HIMG HAB G1 G2 HRT. clear M model R.
      (* [comment removed for export] *)
      drv_blockT0 HIok Hsp DL HR' HKU DI' X0 scr0 114%nat.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      assert (HC3 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC2. apply rdn_agree. intros j Hj. apply EQA. }
      assert (HPAY3 : rdn ASEGS M (Z_to_bv 64 (A1 + 6 + CFG)) (Z.to_nat PL) = Some payloadA).
      { rewrite <- payloadA_len, <- HPAY2. apply rdn_agree. intros j Hj. apply EQA. }
      clear EQM EQH EQA SBM HR' HKU DI' HC2 HPAY2 F1 F2 HSHB. clear M' model'.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
      eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R M model [(u, PL); (A1, CAP)] LK0
                (adebit L crC PL) A' u PL u (A1 + 6 + CFG) PL payloadA TSO [(48%nat, 65536)] [] 0xaed74 K) end end;
        [ exact HR | exact HK
        | rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
        | exact X0 | vm_compute; reflexivity
        | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
        | unfold TSO; lia | reflexivity
        | regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact HA2
        | regv HR (11%bv : reg); cbn [edenot ev ENVA]; rewrite X48, X73, !alu_add_Z; f_equal; lia
        | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact X79
        | lia
        | regv HR (4%bv : reg); reflexivity
        | regv HR (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DI
        | left; reflexivity | lia | lia
        | apply (src_blk_aacc scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 CAP (A1 + 6 + CFG) PL (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
        | lia | lia
        | apply (src_blk_app_rng scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 CAP (A1 + 6 + CFG) PL (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
        | intros i Hi; right; exists (A1, CAP); split; [right; left; reflexivity | cbn [fst snd]; lia]
        | exact HPAY3
        | specialize (HAP (A1, CAP) ltac:(left; reflexivity)); cbn [fst snd] in HAP; lia
        | intros i nb Hf; cbn in Hf;
          destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL'; lia|];
                                           rewrite X48, u_small by lia; rewrite lb_remove_hdA; exists CAP; split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
        | intros v b Hf; discriminate
        | exact HK0
        | ].
      intros R3 M3 model3 vals' E' HL3 HR3 HK3 DI3 HRT3 HDST HBLK3 HIMG3. subst vals' E'.
      rewrite HL' in HL3, HR3. change (114 + 32)%nat with 146%nat in HL3.
      change (sr_after_call_j _ (map ridx c_kept) 114) with srV0A in HR3.
      change (keep_allocA TSO 4096 [(48%nat, 65536)] [] _) with knV0A in HK3.
      destruct (model_rt_fds _ _ HRT3) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      set (vals3 := vals2 ++ junk_vals R3) in *.
      change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR3, HK3.
      assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
      assert (YV : hdr_valsA sp0 p0 p1 can vals3) by (subst vals3; apply (hdr_appA sp0 fdata); [exact XV | rewrite HL'; lia]).
      assert (Y92 : vals_ev vals3 92 = Z_to_bv 64 u) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
      assert (YL : forall j, (j < 82)%nat -> vals_ev vals3 j = vals_ev vals1 j).
      { intros j Hj. subst vals3 vals2. rewrite !vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, HL1; lia). reflexivity. }
      assert (HC4 : rdn ASEGS M3 (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC3. apply rdn_agree. intros k Hk. rewrite u_small by lia. apply HBLK3; [lia | | ].
        - exists (A1, CAP). split; [right; left; reflexivity|]. cbn [fst snd]. lia.
        - specialize (HAP (A1, CAP) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
      clear HR HK DI HC3 HPAY3 HBLK3 HIMG3 G1 G2 HRT3. clear M model R.
      (* [comment removed for export] *)
      drv_blockT0 HIok Hsp DL HR3 HK3 DI3 Y0 scr0 146%nat.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      assert (HC5 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { rewrite <- HC4. apply rdn_agree. intros j Hj. apply EQA. }
      assert (HPAY5 : rdn ASEGS M (Z_to_bv 64 u) (length payloadA) = Some payloadA).
      { rewrite payloadA_len, <- HDST. apply rdn_agree. intros j Hj. apply EQA. }
      (* [comment removed for export] *)
      set (valsL := relayA vals3 R (Z_to_bv 64 0)).
      apply (HLH fx valsL R M model A' A1 u u [(u, PL); (A1, CAP)]).
      + unfold lh_valsA, hdr_valsA in *. subst valsL. rewrite (relayA_len vals3 R _ ltac:(lia)), relayA_81 by lia.
        rewrite !(relayA_lo vals3 R _) by lia. rewrite !YL by lia.
        repeat split; try tauto; try assumption.
        * unfold relayA. change 82%nat with (81 + 1)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
          regv HR (9%bv : reg). cbn [edenot ev ENVA]. exact Y92.
        * unfold relayA. change 83%nat with (81 + 2)%nat. rewrite vals_hiA by lia. cbn [nth lay_extA].
          regv HR (18%bv : reg). cbn [edenot ev ENVA]. exact Y92.
      + subst valsL. eapply (relayA_regs _ vals3 _ R _ ltac:(lia)); [|exact HR]. vm_compute; reflexivity.
      + subst valsL. eapply (know_ok_agree ASEGS 82); [apply relayA_agree; lia | vm_compute; reflexivity |].
        eapply ksubl_sound; [exact HK | vm_compute; reflexivity].
      + split; [exact HBR|]. right. split; [lia|]. split; [reflexivity|]. split; [exact HBR2|]. split; [exact HAP | reflexivity].
      + exact HC5.
      + exact HPAY5.
      + unfold cr1A. replace (PL =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact DI.
      + intros x Hx. apply HINC'. apply HINC. exact Hx.
      + exact G1.
      + exact G2.
  Qed.

End DrvD.
End FPX_1.

End Na0DrvD.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr.
Module Na0DrvFreeNull.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceANull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section FreeNull.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis FNULL : afree_null_spec L ar scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  #[local] Notation dinvA := (dinv ar HI sp0 M0).

  Lemma afree_null_site : forall vals ebs sr kn R M (model : Model) LB LK cr A so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true -> (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2%bv = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10%bv = Z_to_bv 64 0 -> getr R 4%bv = Z_to_bv 64 0x693b00 -> getr R 1%bv = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    dinvA LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) A',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_allocA so 4096 bls vbnd kn) ->
       dinvA LB LK cr A' M' model' -> model_rt model model' -> incl A A' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x8073c) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined scfg L ar C HI HIok sp0 Hsp M0 M0_def _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr L ar IL sp0 DL) as (SC1 & SC2 & SC3).
    pose proof (FNULL fx R M model LB FF LK cr A K) as MS.
    rewrite (dla_segs L ar IL sp0 DL), (dla_free L ar IL sp0 DL), (dla_tp L ar IL sp0 DL) in MS. rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia.
      eapply (astack_ok_of_window L ar IL HI sp0 Hsp Hal DL vals ebs (ahid A model) M kn so); eauto; lia.
    - intros R' M' model' A' HP HPRES HRT HINC HMI' HH'.
      rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (CLI : forall a, aclient L ar LB FF (bv_unsigned sp0 + so) 4096 a -> aclient L ar LB FF (bv_unsigned sp0 + so) (hl_scr_free L) a)
        by (intros a; apply (aclient_scr_mono L ar sp0 Hsp); lia).
      apply (CONT R' M' model' A' HL'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA sp0 Hsp R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) unfold keep_allocA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPa L ar LB FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
        * eapply (regions_callA scfg L ar C IL HI HIok sp0 Hsp DL (vals ++ junk_vals R') ebs so 4096 bls vbnd LB LB LB FF FF LK LK cr cr A A' M M' model model');
            [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
          -- intros a Ha. exact Ha.
          -- intros a Ha; exact Ha.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH') by lia.
          destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_free L)) as [Hlo|Hhi].
          -- rewrite PR1; [apply (window_defined sp0 Hsp vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
             unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
          -- apply PR2. lia.
      + (* [comment removed for export] *)
        apply (dinv_call scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LB LB LK LK cr cr A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_free L) DI ltac:(lia)); assumption.
      + (* [comment removed for export] *) intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
      + intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
      + intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL).
        split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client L ar IL sp0 DL lo hi a Hin' Ha)].
  Qed.
End FreeNull.
End FPX_1.

End Na0DrvFreeNull.
Module Na0DrvHRead.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0RegionPoisoned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0AsanMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0ReadIcpt OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0DrvHIcpt OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DrvHRead () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic6eq_indC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List:Proper_mapC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_01267Na0DrvGAfirstn_app_skipnAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List:firstn_nilc59OSSVerify5KrLib7Mh_01267Na0DrvGBfirstn_len_firstnAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition TP_A : Z := 0x693b00.
Definition ERRNO_A : Z := 0x693a5c.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_NOERRNO : list (Z * Z) :=
  [(0x10000, 0x158000); (0x15b4b8, 0x15c3a0); (0x6820d0, 0x693a5c); (0x693a60, 0x693aa8); (0x693ab0, 0x693af8); (0x693b14, 0x693b28); (0x693b30, 0x6b4fb8);
   (0x6b4fc0, 0x6b6000)].
Definition keep_readEA (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 2200 bls vbnd [] IMG_NOERRNO IMG_RW_A kn.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvReadDir.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hcells : incl RD_CELLS (asc_cells C).
  Variable M0 : word -> option byte.

  #[local] Abbreviation dinvA := (dinv ar HI sp0 M0).

  Lemma wseg_errno : wseg_ok ASEGS (Z_to_bv 64 0x693a5c) 4 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DrvHRead ()) ["FPX_1"; "DrvReadDir"] "p;2p;1p;3p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?p4p710R3p9P0p1001[R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p10029R4p4p7210R5p9P0P4p4p710R4p9P0p1002mp4p710R6p9P0p1003]p4p710R7p9P0p1004;p4p710R8p9P0p10053p4p710p8P0p1005JR9p4p710p8P0P9p4p7210p8P0p1005gp4p710R9p8P0p1006Gp4p710R0p8p1006dp4p70R:P1p8P:P2p8P:P3p8P:p1007TR;p4p710p8P:P;p4p7210p8P:P5p8P:P4p8P:P7p8P:P8p8p10081p4p710R:P3p8P:P7p8p1008Np4p70R:P1p8P:P2p8P:p1009<p4p7210p8P:P3p8P:p1009Xp4p7210p8P:P5p8P:P4p8P:P6p8P:P7p8P:p100:Gp4p7210p8P:P8p8P:p100;;p4p7210p8p100;Zp4p70P7p8p100<Up4p7210R:P1p8P:P2p8P:P5p8P:P4p8P:P8p8p100=Ap6051000R:P3p8P:p100>Gp4p710R6p8P:P7p8P:P0p8P:p100>fp4p710R:p8p100?Ep6051000R0P6p8P0P7p8P0p100@Lp4p710p8P0P9p8P0P:p8p100@np4p710P7p8p100AIp4p70R0P1p8P0P2p8P0P5p8P0P4p8P0P7p8P0P8p8P:P3p8P:P7p8g00B?j29Tg00BYj14Tg00C7j10Tg00C\j12Tg00DAj18Tg00D_j27Tg00EEj13Tg00Edj35Tg00Fbj36Tf0#2#2p=1g00G<R7g00G\R:'9g00H<g00IQR3#1#1#1#4%03#2#0#1#0#1#0#0#0#2#0#1#0#2#0#0#0#1#8'7g00J6#3#3#3#335=67:do"). Qed.

  Lemma aread_dir_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (cnt : Z) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 4 = Z_to_bv 64 TP_A ->
    getr R 10 = Z_to_bv 64 3 -> getr R 11 = Z_to_bv 64 STAGE -> getr R 12 = Z_to_bv 64 cnt -> 1 <= cnt <= 65536 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    dinvA LB LK cr A M model ->
    fd_lookup (m_fds model) (Z_to_bv 64 3) = Some FdDir ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    (forall R' M' (model' : Model),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = Z_to_bv 64 18446744073709551615 ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A model') M') (keep_readEA so bls vbnd kn) ->
       dinvA LB LK cr A M' model' ->
       m_fds model' = m_fds model -> m_fs model' = m_fs model ->
       (forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 + so - 2200 <= a < bv_unsigned sp0 + so) -> ~ (ERRNO_A <= a < ERRNO_A + 4) ->
                  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x6a2b8) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A cnt so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R4 R10 R11 R12 Hcnt R1 Hra Hra2 DI Hfd Hbl Hvb CONT.
    pose proof Hsp as Hsp'. unfold STAGE, TP_A, ERRNO_A in *.
    set (s := bv_unsigned sp0 + so) in *. set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    destruct (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HOFF & HLC & HAWF & _ & _). fold H in HOFF, HLC.
    assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by (unfold s; lia).
    assert (WOK : store_ok ASEGS MV (Z_to_bv 64 (s - 2200)) 2200 = true).
    { replace (s - 2200) with (bv_unsigned sp0 + (so - 2200)) by (unfold s; ring).
      apply (window_store_ok sp0 vals ebs MV kn (so - 2200) 2200 HK Hiw P0); lia. }
    assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x6b6000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) -> H (Z_to_bv 64 a) = false)
      by (intros a Ha Hc; exact (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha Hc)).
    assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply VIS; unfold s in Hx; lia. }
    assert (VST : forall x : word, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead.STAGE <= bv_unsigned x < OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead.STAGE + 65536 -> H x = false).
    { intros x Hx. unfold OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead.STAGE in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply VIS; lia. }
    assert (CV : forall a n v, In (a, n, v) RD_CELLS ->
                 rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
    { intros a n v Hin. unfold MV, H. rewrite rdn_mrestrict_eq; [exact (rd_cell scfg L ar C IL HI HIok sp0 DL Hcells _ _ _ _ _ _ _ a n v HH Hin)|].
      apply (avoid_img scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ a (Z.to_nat n) HH);
        unfold RD_CELLS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]); destruct Hin. }
    (* [comment removed for export] *)
    destruct (wrap_read_pre_run MV (seg_rom ASEGS) (Z_to_bv 64 s) (Z_to_bv 64 ra) s 3 0x6820d0 cnt
                ltac:(apply u_small; lia) Hs WOK ltac:(lia) ltac:(lia) ltac:(lia)) with (regs := R)
      as (Ra & RUN1 & A17 & A10 & A11 & A12 & _ & _ & _ & _ & A2 & A1 & A8 & A9 & A18 & A19 & A20 & KB1).
    1: { rewrite <- (w_lit 0x160758 (0x160758%bv : word) eq_refl). exact (CV 0x160758 1 1 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: { rewrite <- (w_lit 0x158bf0 (0x158bf0%bv : word) eq_refl). exact (CV 0x158bf0 8 0x14f76c ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: exact R10. 1: exact R11. 1: exact R12. 1: exact R2. 1: exact R1.
    rewrite (w_lit 0x6a2b8 (0x6a2b8%bv : word) eq_refl).
    apply (rz_msteps_lz ASEGS scfg H A R _ M Ra _ _ model K HOFF asegs_wx HLC HAWF HMI Hh RUN1).
    intros model1 MI1 SBM1 EQV1.
    destruct (sbm_fds _ _ SBM1) as (F1 & F2).
    (* [comment removed for export] *)
    eapply (rz_read_dir_cnt_lz ASEGS scfg Ra _ _ model1 ECALLW (Z_to_bv 64 3) cnt K); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - rewrite (sbm_halted_eq _ _ SBM1). exact Hh.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - rewrite F1. exact Hfd.
    - exact A12.
    - lia.
    - rewrite A11, u_small by lia. unfold TASK_SIZE. lia.
    - replace (v_addi (0x149d40%bv : word) 4) with (0x149d44%bv : word) by (apply bv_eq; reflexivity).
      set (raw := Z_to_bv 64 ra) in *.
      set (R2' := regupd Ra 10 (errno_ret EISDIR)).
      assert (Hbs : Z.of_nat (length (@nil byte)) <= 65536) by (cbn; lia).
      change (munrestrict H M (RDA MV raw s R)) with (rd_M2 H M s raw R []).
      set (M2 := rd_M2 H M s raw R []).
      set (MV2 := rd_MV2 H M s raw R []).
      assert (EL1 : m_vm_lazy model1 = m_vm_lazy model) by exact (sbm_lazy_eq _ _ SBM1).
      assert (EH1 : ahid A model1 = H) by (unfold H; apply ahid_same_lazy; exact EL1).
      assert (Hh1 : m_halted model1 = None) by (rewrite (sbm_halted_eq _ _ SBM1); exact Hh).
      (* [comment removed for export] *)
      pose proof (RDA_slots (mrestrict H M) raw s Hs R) as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6 & SL7).
      assert (T1 : rdn ASEGS MV2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 raw)) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 8) by lia; exact SL1).
      assert (T2 : rdn ASEGS MV2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 16) by lia; exact SL2).
      assert (T3 : rdn ASEGS MV2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 24) by lia; exact SL3).
      assert (T4 : rdn ASEGS MV2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr R 18))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 32) by lia; exact SL4).
      assert (T5 : rdn ASEGS MV2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr R 19))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 40) by lia; exact SL5).
      assert (T6 : rdn ASEGS MV2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr R 20))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 48) by lia; exact SL6).
      assert (T7 : rdn ASEGS MV2 (Z_to_bv 64 (s - 2136)) 8 = Some (word_to_le_bytes 8 (0x6c4e4%bv : word))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 2136) by lia; exact SL7).
      assert (Hret : ret_ok raw) by (apply ret_ok_even; unfold raw; rewrite u_small by lia; exact Hra2).
      assert (Q4 : getr R2' 4 = Z_to_bv 64 0x693b00).
      { unfold R2'. rewrite getr_other by discriminate. rewrite (KB1 4%bv); [exact R4 | cbv; tauto | cbv; intuition discriminate]. }
      destruct (read_icpt_post_err_run (seg_rom ASEGS) raw s 0x693b00 Hs ltac:(lia) Hret R R2' MV2) as (R3 & RUN3 & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB3).
      1: { unfold R2'. rewrite getr_same by discriminate. apply bv_eq. vm_compute. reflexivity. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A2. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A1. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A8. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A20. }
      1: exact Q4.
      1: { apply (store_ok_mono ASEGS _ (mrestrict H M) MV2); [exact (rd_MV2_grows H M s raw R []) | exact WOK]. }
      1: { apply (store_ok_window ASEGS _ (Z_to_bv 64 0x693a5c) (Z_to_bv 64 (0x693b00 - 164)) 4%nat 4%nat 0x693a5c 0x693a60);
             first [exact wseg_errno | reflexivity | lia | (rewrite u_small by lia; lia)]. }
      1: exact T7. 1: exact T1. 1: exact T2. 1: exact T3. 1: exact T4. 1: exact T5. 1: exact T6.
      set (M3' := RDE s 0x693b00 MV2) in *.
      assert (MI1' : MInv A model1) by exact MI1.
      apply (rz_msteps_lz ASEGS scfg H A R2' _ M2 R3 _ M3' model1 K HOFF asegs_wx ltac:(rewrite EL1; exact HLC) HAWF MI1' Hh1 RUN3).
      intros model3 MI3 SBM3 EQV3.
      set (M3 := munrestrict H M2 M3') in *.
      assert (OUT3 : forall x : word, ~ (s - 2200 <= bv_unsigned x < s) -> ~ (0x693a5c <= bv_unsigned x < 0x693a60) -> M3' x = MV2 x).
      { intros x N1 N2. unfold M3'. apply RDE_out; lia. }
      assert (GR3 : mem_grows MV2 M3') by (unfold M3'; apply RDE_grows).
      (* [comment removed for export] *)
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (s - 2200 <= a < s) -> ~ (0x693a5c <= a < 0x693a5c + 4) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N1 N2. unfold M3, munrestrict.
        assert (E2 : M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { unfold M2, rd_M2. cbn [wbytes]. unfold munrestrict. destruct (H (Z_to_bv 64 a)) eqn:Hx; [reflexivity|].
          rewrite (RDA_out (mrestrict H M) raw s Hs R (Z_to_bv 64 a)) by (rewrite u_small by lia; lia). unfold mrestrict. rewrite Hx. reflexivity. }
        destruct (H (Z_to_bv 64 a)) eqn:Hx; [exact E2|].
        rewrite OUT3 by (rewrite u_small by lia; lia). unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact E2. }
      assert (GRW : forall x : word, M x <> None -> M3 x <> None).
      { intros x Hd. unfold M3, munrestrict.
        assert (E2 : M2 x <> None) by (unfold M2; apply (rd_M2_grows H M s raw R []); exact Hd).
        destruct (H x) eqn:Hx; [exact E2|]. apply GR3. unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact E2. }
      assert (EV3 : vml_of model3 = vml_of model) by (rewrite (sbm_vml _ _ SBM3); exact (sbm_vml _ _ SBM1)).
      assert (Hh3 : m_halted model3 = None) by (rewrite (sbm_halted_eq _ _ SBM3); exact Hh1).
      assert (EH3 : ahid A model3 = H) by (rewrite (ahid_sbm A model1 model3 SBM3); exact EH1).
      assert (DI3 : dinvA LB LK cr A M3 model3).
      { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M3 model model3 DI); [ | exact GRW | exact EV3 | exact MI3 | exact Hh3 | rewrite (sbm_rdrA _ _ SBM3); exact (sbm_rdrA _ _ SBM1)].
        intros a Ha NC. apply FRM; [exact Ha | |]; intros Hr; apply NC; unfold CWA.
        - right. left. unfold s in Hr. lia.
        - right. right. exists 0x6820d0, 0x693aa8. split; [unfold IMG_W_A; cbn [In]; tauto | lia]. }
      assert (HL' : length (vals ++ junk_vals R3) = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R3) 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (KEPT : forall r : reg, In r c_kept -> getr R3 r = getr R r).
      { assert (KK : forall r : reg, In r callee_saved -> ~ In r OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0ReadIcpt.RIPL -> getr R3 r = getr R r).
        { intros r Hr Hn'. rewrite (KB3 r Hr Hn'). unfold R2'. rewrite getr_other; [exact (KB1 r Hr Hn')|].
          intros ->. clear - Hr. cbv in Hr. intuition discriminate. }
        intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
        - rewrite O2, R2. reflexivity.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - exact O8.
        - exact O9.
        - exact O18.
        - exact O19.
        - exact O20.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate. }
      apply (CONT R3 M3 model3 HL').
      + rewrite (vals_ev_junkA vals R3 10) by lia. exact O10.
      + exact (regs_after_keeps vals ebs sr R R3 c_kept Hsv HR KEPT c_kept_no0A).
      + (* [comment removed for export] *) rewrite EH3. unfold keep_readEA.
        pose proof (env_app_know ASEGS vals (junk_vals R3) ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 2200 bls vbnd [] IMG_NOERRNO IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R3)) ebs)
                  (fun a => H (Z_to_bv 64 a) = false /\ ~ (s - 2200 <= a < s) /\ ~ (0x693a5c <= a < 0x693a5c + 4))
                  (fun a => s - 2200 <= a < s)
                  _ MV (mrestrict H M3) _ _ kn HK1).
        * constructor; cbn [ev]; rewrite ?P0'.
          -- lia.
          -- lia.
          -- intros z Hz Hnot. split; [apply VIS; lia|]. unfold s. split; lia.
          -- intros z Hz. right. unfold s. lia.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & SBk). rewrite vals_ev_app_l by exact Hi32.
             pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ SBk) as (Z1 & Z2 & Z3).
             destruct SBk as (cap & Hnb & Hin & HB).
             split; [lia|]. intros z Hz. split; [|unfold s; split; lia].
             apply VIS; [lia|]. right. right. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin | cbn [fst snd]; lia].
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros i [].
          -- intros lo hi Hin. unfold IMG_NOERRNO in Hin. cbn [In] in Hin.
             repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; (split; [apply VIS; lia | unfold s; split; lia])|]).
             destruct Hin.
          -- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
             intros Mx d m Hd Hm.
             apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x6820d0) (Z_to_bv 64 d) 65536%nat m 0x6820d0 0x6920d0);
               first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
        * intros a Ha (V1 & N1 & N2). unfold MV, mrestrict. rewrite V1. apply FRM; assumption.
        * intros a Ha. unfold mrestrict. rewrite (VFR (Z_to_bv 64 a)) by (rewrite u_small by (unfold s in Ha; lia); exact Ha).
          apply GRW. apply (window_defined sp0 Hsp vals ebs H M kn HK Hiw P0). unfold s in Ha. lia.
      + exact DI3.
      + rewrite (proj1 (sbm_fds _ _ SBM3)). exact F1.
      + rewrite (proj2 (sbm_fds _ _ SBM3)). exact F2.
      + exact FRM.
  Qed.
End DrvReadDir.
End FPX_1.

End Na0DrvHRead.
