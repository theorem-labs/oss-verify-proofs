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
  Ba0DrvStdio_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanSoundK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MainPhaseA_b Ba0DrvMain_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ShapeLaws AgentLib Spec BigintSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Existing Instance PropExec.fx0.

Lemma In_firstnA : forall {X} (l : list X) n x, In x (firstn n l) -> In x l.
Proof. intros X l n x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H. Qed.

Section OpenFail.
  Variable scfg : SpuriousCfg.
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
  Variable path : list byte.
  Variable fs0 : Fs.Fs.
  Variables p0 p1 can : word.
  Variable M0 : word -> option byte.
  Hypothesis Hfs : sc_fs scfg = true.
  Hypothesis Hnonul : ~ In (Z_to_bv 8 0) path.
  Hypothesis Hplen131 : Z.of_nat (length path) <= 131071.
  Hypothesis P1lo : bv_unsigned sp0 <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 <= 2 ^ 47.
  Hypothesis P1str : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
  Variable LK0 : list fframe.
  Variable cr0 : credit.
  Variable A0 : list (Z * Z).

  #[local] Abbreviation dinvA := (dinv ar HI sp0 M0).
  #[local] Abbreviation ENV0 := (ENVA []).

  (* [comment removed for export] *)
  #[using="L C IL HIok Hsp Hal DL P1lo P1str"] Lemma of_blockAA : forall T R (model : Model) (tid : word),
    let vals0 := vals_mainA sp0 p0 p1 can tid R in
    regs_ok (ENV0 vals0) sr_mainA R -> know_ok ASEGS (ENV0 vals0) (mrestrict (ahid A0 model) M0) kn_mainA ->
    dinvA [] LK0 cr0 A0 M0 model -> m_fds model = fds0 -> m_fs model = fs0 ->
    (forall vals R' M (model' : Model),
       length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 ->
       regs_ok (ENV0 vals) srA R' -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model') M) knA ->
       dinvA [] LK0 cr0 A0 M model' -> m_fds model' = fds0 -> m_fs model' = fs0 ->
       rdn ASEGS M p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x12a8d8) M (seg_rom ASEGS)) model') T) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b04) M0 (seg_rom ASEGS)) model) T.
  Proof.
    intros T R model tid vals HR HK DI Hfds Hfs0 CONT.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals_mainA; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1) by reflexivity.
    clearbody vals.
    drv_block0 HIok Hsp DL HR HK DI P0 scr0 38%nat.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite Hfds in F1. rewrite Hfs0 in F2.
    apply (CONT vals); try assumption.
    rewrite <- P1str. apply rdn_agree. intros j Hj. apply (di_above _ _ _ _ _ _ _ _ _ _ DI0). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="path"] Lemma after_openat_failA : forall KA e vals R M (model : Model),
    open_err_kA scfg ar HI sp0 fs0 [] p1 M0 LK0 cr0 A0 KA ->
    1 <= e <= 4095 ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 ->
    regs_ok (ENV0 vals) srA R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model) M) knA ->
    dinvA [] LK0 cr0 A0 M model -> m_fds model = fds0 -> m_fs model = fs0 ->
    srealizes ASEGS scfg (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x12a8d8) 4) M (seg_rom ASEGS)) model) KA.
  Proof.
    intros KA e vals R M model HKA He HL P0 P2 HR HK DI F1 F2.
    rewrite v_addi_pc4 by lia. change (0x12a8d8 + 4)%Z with 0x12a8dc%Z.
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know ASEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
    change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev [[]; []; []; []; []])) with (ENV0 (vals ++ [errno_ret e])) in HR2, HK2.
    eapply (HKA e (vals ++ [errno_ret e])).
    - exact He.
    - rewrite length_app, HL. reflexivity.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
    - rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
    - rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENVA].
      rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - exact HK2.
    - exact DI.
    - exact F1.
    - exact F2.
  Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok Hsp Hal DL Hnonul P1lo P1str"] Theorem open_fail_nofileA : forall KA R (model : Model) (tid : word),
    let vals0 := vals_mainA sp0 p0 p1 can tid R in
    (4096 <= length path)%nat \/ path = [] \/ (path <> [] /\ openat_plain_name path = true /\ fs_lookup fs0 path = None) ->
    regs_ok (ENV0 vals0) sr_mainA R -> know_ok ASEGS (ENV0 vals0) (mrestrict (ahid A0 model) M0) kn_mainA ->
    dinvA [] LK0 cr0 A0 M0 model -> m_fds model = fds0 -> m_fs model = fs0 ->
    open_err_kA scfg ar HI sp0 fs0 [] p1 M0 LK0 cr0 A0 KA ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b04) M0 (seg_rom ASEGS)) model) KA.
  Proof.
    intros KA R model tid vals0 Hcase HR HK DI Hfds Hfs0 HKA.
    apply (of_blockAA KA R model tid HR HK DI Hfds Hfs0).
    clear HR HK DI Hfds Hfs0. clear vals0 model R.
    intros vals R M model HL P0 P2 HR HK DI F1 F2 Sr.
    assert (A17 : getr R 17 = Z_to_bv 64 56) by (regv HR (17%bv : reg); reflexivity).
    assert (A10 : getr R 10 = AT_FDCWD) by (regv HR (10%bv : reg); apply bv_eq; reflexivity).
    assert (A12 : Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z) by (regv HR (12%bv : reg); vm_compute; reflexivity).
    assert (A11 : getr R 11 = p1) by (regv HR (11%bv : reg); cbn [edenot ev ENVA]; exact P2).
    assert (HF : fetch_word ASEGS (Z_to_bv 64 0x12a8d8) = Some ECALLW) by (vm_compute; reflexivity).
    assert (Hh : m_halted model = None) by exact (di_halt _ _ _ _ _ _ _ _ _ _ DI).
    assert (Hnl : nolazy_rng (m_vm_lazy model) (getr R 11) 4096).
    { rewrite A11. apply (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [lia|].
      intros k Hk. right. left. lia. }
    destruct Hcase as [Hlong | [Hemp | (Hne & Hppl & Hlk)]].
    - (* [comment removed for export] *)
      eapply (rz_openat_toolong_lz ASEGS scfg R _ M model ECALLW HF is_ecall_ECALLW Hh A17 A10 A12 Hnl (firstn 4096 path)).
      + rewrite A11.
        replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
          by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
        apply (rdn_firstn ASEGS M (length path + 1)); [exact Sr | lia].
      + intros Hin. apply Hnonul. eapply In_firstnA. exact Hin.
      + apply (after_openat_failA KA ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
    - (* [comment removed for export] *)
      eapply (rz_openat_empty_lz ASEGS scfg R _ M model ECALLW HF is_ecall_ECALLW Hh A17 A10 A12 Hnl).
      + split; [cbn; lia|]. split; [intros [] |]. rewrite A11.
        rewrite Hemp in Sr. exact Sr.
      + apply (after_openat_failA KA ENOENT vals); try assumption. unfold ENOENT. lia.
    - (* [comment removed for export] *)
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      { eapply (rz_openat_toolong_lz ASEGS scfg R _ M model ECALLW HF is_ecall_ECALLW Hh A17 A10 A12 Hnl (firstn 4096 path)).
        + rewrite A11.
          replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
            by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
          apply (rdn_firstn ASEGS M (length path + 1)); [exact Sr | lia].
        + intros Hin. apply Hnonul. eapply In_firstnA. exact Hin.
        + apply (after_openat_failA KA ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia. }
      eapply (rz_openat_absent_lz ASEGS scfg R _ M model ECALLW HF is_ecall_ECALLW Hh A17 A10 A12 Hnl path).
      + split; [lia|]. split; [exact Hnonul|]. rewrite A11. exact Sr.
      + exact Hne.
      + exact Hppl.
      + rewrite F2. exact Hlk.
      + apply (after_openat_failA KA ENOENT vals); try assumption. unfold ENOENT. lia.
  Qed.
End OpenFail.

(* [comment removed for export] *)
Theorem dg_nofile_of_openerr : forall scfg (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics),
  dg_openerr_stmt scfg L C IL -> dg_nofile_stmt scfg L C IL Lay LSt.
Proof.
  intros scfg L C IL Lay LSt DG_OPENERR.
  unfold dg_nofile_stmt, drv_main_on.
  intros Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs Hcase ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hvsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
  assert (Hal : bv_unsigned sp mod 16 = 0) by (destruct Hvsp as (_ & _ & H3); exact H3).
  pose proof CONSTS as CONSTS'. destruct CONSTS as (ILY & HRD & Hkpm & Hlin & Hovh & HPR & HEX & _).
  assert (CTX : drv_ctxA scfg L C IL ar HI sp M0) by (constructor; try assumption).
  assert (Hnonul : ~ In (Z_to_bv 8 0) path).
  { destruct Hva as (_ & _ & _ & Hnn & _). inversion Hnn as [|x l _ Hn2]; subst. inversion Hn2 as [|y l2 Hy _]; subst. exact Hy. }
  assert (Hplen131 : Z.of_nat (length path) <= 131071).
  { destruct Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l _ Hf2]; subst. inversion Hf2 as [|y l2 Hy _]; subst. exact Hy. }
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp DL M0 _ _ _ _ _ _ DI) as (HOFF & _).
  assert (STRF : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0])) by (exact (rdn_of_mrestrict ASEGS _ M0 HOFF _ _ _ STR)).
  assert (PTH : drv_pathA sp M0 p1 path) by (constructor; assumption).
  destruct main_nb as (NB1 & NB2).
  unfold env_mainA in HR, HK.
  pose proof (regs_ok_nb _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB1 HR) as HR'.
  pose proof (know_ok_nb ASEGS _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB2 HK) as HK'.
  apply (open_fail_nofileA scfg L ar C IL HI HIok sp Hsp Hal DL path fs p0 p1 can M0 Hnonul ltac:(lia) STRF [] cr0 A0
           (t_die (msg_cannot_open path) fs) R model tid); try assumption.
  - destruct Hcase as [H1|[H2|[Hnd Hlk]]]; [left; exact H1 | right; left; exact H2 |].
    destruct (list_byte_eqb path []) eqn:Hemp; [right; left; apply list_byte_eqb_iffA; exact Hemp|].
    right. right. split; [intros E; apply list_byte_eqb_iffA in E; rewrite E in Hemp; discriminate Hemp|]. split; [|exact Hlk].
    destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|p' l' [Hsl Hdd] _]; subst.
    unfold openat_plain_name, path_is_dirref. rewrite Hsl, Hdd.
    lazymatch goal with |- context [path_eqb path ?d] => destruct (path_eqb path d) eqn:E; [|reflexivity] end.
    exfalso. apply Hnd. apply path_eqb_eq in E. rewrite E. reflexivity.
  - exact (DG_OPENERR ar HI sp M0 CTX path fs [] p1 cr0 A0 PTH SAH).
Qed.
