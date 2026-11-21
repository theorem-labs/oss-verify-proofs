(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (model0, model1g, open_err_branch and file_seg2_kont_g written out from their encoded forms, model0 now carrying the launch's vDSO and model1g the vDSO reservation, with model1g_resv added; the argv pointers taken from the entry draw; the path read also proved to end below TASK_SIZE; below_win and file_seg1's below-window proof use sp0 - 6144512, the floor of the stack the launch maps (was sp0 - 8388608)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX ShapeLaws MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame MemcpyLib Hoare MemSplit.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_call U_exit_base U_stdio_defs U_exit U_memcpy_base U_memcpy U_startup U_main_entry.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_open_defs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Export P_lim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_main_open () : Init.string Init.list := ["OSSVerify.KrLib.BB.SymExec2.SX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.BB.SymExec2.SX2.sentry"; "Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Stdlib.Lists.List.forallb"; "entry_win_b"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.BB.SymExec2.SX2.ev"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.mem_denot"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.with_tid"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "OSSVerify.KrImg.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "OSSVerify.KrLib.P.P_lim.LIM"; "OSSVerify.KrLib.BB.Amb.mkProcInputC"; "OSSVerify.KrLib.BB.Amb.mkModelC"; "Pilot.fds1g"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.BB.SymRun.vals_ev"; "OSSVerify.KrLib.BB.SymDriveX.log_below_b"; "Pilot.above_sp0"; "Pilot.ENV"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_errnos"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "OSSVerify.KrLib.U.U_main_entry.p0"; "OSSVerify.KrLib.U.U_main_entry.p1"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.regs_ok"; "OSSVerify.KrLib.BB.SymExec2.SX2.sr_upd"; "OSSVerify.KrLib.U.U_main_open_defs.srA"; "OSSVerify.KrLib.BB.SymExec2.SX2.ridx"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.BB.SymExec2.SX2.EVar"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.know_ok"; "OSSVerify.KrLib.U.U_main_open_defs.knA"; "OSSVerify.KrLib.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Pilot.model0"; "OSSVerify.KrLib.U.U_main_open_defs.srB0"; "Pilot.below_win"; "Pilot.model1g"; "OSSVerify.KrLib.Lib.Shape.TSet"; "Pilot.open_err_branch"; "Pilot.file_seg2_kont"; "OSSVerify.KrLib.Lib.Shape.t_alt2"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_win_b (spi : nat) (K : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb K k && Z.leb (k + Z.of_nat w) 0
  | _ => false
  end.

Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L3477398674.18 L53649095585.18L55373802897.1800000R00h01<S1E1k1w3spi1K3He23He32HK4Hsp14Hsp2S1E1k1w3spi1K1x3He22HxS1E1k1w3spi3He34Hsp2". (* [comment removed for export] *)
Lemma mem_denot_below : ltac2:(CDefT.buildp (gd_tbl_P_main_open ()) "PE,$0.PM,P,(1.&40.)(2.(1.&8.))Plog,(3.$4.)Pspi,$5.PK,$6.Px,(1.&40.)P,(7.$8.(9.$4.(:.R3.R2.)R4.)$;.)P,(<.(=.(>.+2.+28.))R3.)P,(<.(>.+2.+29.)(?.&40.(10.R8.R5.)))P,(11.(?.&40.(10.R9.R6.))(>.+2.+3?.))P,(11.(?.&40.R5.)(12.(?.&40.(10.R:.R7.))R6.))(7.(2.(1.&8.))(13.R;.R:.R9.R6.)A1.R:.R6.)")
(* [comment removed for export] *).
Proof.
  intros E M log spi K x Hb HK Hsp1 Hsp2 Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  destruct b as [z|i| | | | | |]; cbn [entry_win_b] in He; try discriminate.
  apply andb_prop in He as [He1 He3]. apply andb_prop in He1 as [He1 He2].
  apply Nat.eqb_eq in He1. subst i. apply Z.leb_le in He2. apply Z.leb_le in He3.
  pose proof (u64_range x) as Hxr.
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. left. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Pilot.
  Context {AMB : Amb}.
  Context {LM : Lim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) := ltac2:(CDefT.buildp (gd_tbl_P_main_open ()) "(14.(15.(1.&40.)$16.)(17.(1.&40.)$16.(18.&40.=)(19.(18.&40.=)))(14.(15.(1.&40.)$16.)(17.(1.&40.)$16.(18.&40.+1.)(19.(18.&40.+1.)))(14.(15.(1.&40.)$16.)(17.(1.&40.)$16.(18.&40.+2.)(19.(18.&40.+2.)))(1:.(15.(1.&40.)$16.)))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  (* 08b1429: [Run.init_config] starts from the launch's vDSO run, which the ambient
     record carries ([Amb.a_vdso]) *)
  Definition model0 : Model :=
    with_tid tid (with_vdso a_vdso (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp0 (@LIM LM) (mkProcInputC [a0s; path] envv fs0 stdin0))).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  (* plain text (was serialised).  At 08b1429 [init_model] reserves the
     image's segments and then the launch's vDSO/vvar pair
     ([State.init_reserved]); the start-up keeps that ledger, so the model
     after it does too (BB/Amb.v [init_model_C]). *)
  Definition model1g (fd3 : FdEntry) : Model :=
    @mkModelC AMB (fds1g fd3)
      (mkVmMapsFull (init_reserved (segments_reserved Ubsan.M.loaded_segments) mbase sp0 (@a_kernel AMB))
                    [] [] brk brk (@LIM LM) mbase sp0)
      stdin0 fs0 None (Some tid) None.
  #[using="Type"] Lemma model1g_resv (fd3 : FdEntry) :
    vm_reserved (m_vmmaps (model1g fd3))
    = segments_reserved Ubsan.M.loaded_segments
      ++ vdso_reserved (m_kernel (model1g fd3)) (vdso_top (m_vmmaps (model1g fd3))).
  Proof.
    change (vdso_top (m_vmmaps (model1g fd3)))
      with (vdso_top (m_vmmaps (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp0 (@LIM LM)
                                           (@mkProcInputC AMB [] [] fs0 stdin0)))).
    rewrite vdso_top_init_model. reflexivity.
  Qed.
  Definition fds1 : list (word * FdEntry) := fds1g (FdFile path (Z_to_bv 64 0)).
  Definition model1 : Model := model1g (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  (* [comment removed for export] *)
  Definition below_win (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned a < bv_unsigned sp0 - 6144512)%Z -> M a = mem0 a.

  
  (* [comment removed for export] *)
        #[using="Type"] Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L20218684591.34L41668126075.34L53393235032.3400000J00_014S3sp04path5Hplen1a2Ha4SPloS3sp04path5Hplen4SPloS3sp04path5Hplen1a2Ha". (* [comment removed for export] *)
  #[using="Hvsp Hplen"] Lemma above_sp0_block : ltac2:(CDefT.buildp (gd_tbl_P_main_open ()) "Pvals,(3.(1.&40.))Plog,(3.$4.)PM,P,(1.&40.)(2.(1.&8.))P,(7.(1.&40.)(26.R3.#0.)Vsp0,)P,(7.$8.(27.#0.+7>000.R3.)$;.)P,(28.R3.)(28.(13.(29.R6.)R4.R5.))")
(* [comment removed for export] *).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x7e000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  
  #[using="Type"] Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof. exact (alloc_fd_init _ _ _). Qed.
  #[using="Type"] Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac refresh_above vals P0 HA :=
    lazymatch type of HA with above_sp0 ?Mo =>
      lazymatch goal with EQ : ?Mn = mem_denot _ Mo ?log |- _ =>
        let HA' := fresh "HA" in
        pose proof (above_sp0_block vals log Mo P0 ltac:(vm_compute; reflexivity) HA) as HA';
        rewrite <- EQ in HA'; clear HA EQ; rename HA' into HA
      end
    end.
  (* [comment removed for export] *)
  Ltac name_state R M :=
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into R; rename Mn into M end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  #[using="a0s Hva"] Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    ddestruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="a0s Hva"] Lemma path_noslash : path_has_slash path = false /\ path_eqb path dotdot_path = false.
  Proof.
    ddestruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs; subst. assumption.
  Qed.


  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop := (forall e : Z, (forall vals : (list word), (forall R : (bvmap (5)%N word), (forall M : (word -> (option byte)), ((In e openat_errnos) -> (((length vals) = (39)%nat) -> (((vals_ev vals (0)%nat) = sp0) -> (((vals_ev vals (38)%nat) = (errno_ret e)) -> (((vals_ev vals (1)%nat) = (p0 a0s path envv rd)) -> (((vals_ev vals (2)%nat) = (p1 a0s path envv rd)) -> (((vals_ev vals (5)%nat) = tid) -> ((regs_ok (ENV vals) (sr_upd srA (ridx (10%bv : bv 5)) (EVar (38)%nat)) R) -> ((know_ok RSEGS (ENV vals) M knA) -> ((forall x : word, ((Z.le (bv_unsigned sp0) (bv_unsigned x)) -> ((M x) = (mem0 x)))) -> (realizes RSEGS (mkCfg (mkst R (Z_to_bv (64)%N 0x4729c%Z) M (seg_rom RSEGS)) model0) KA))))))))))))))).

  (* [comment removed for export] *)
  Definition file_seg2_kont_g (fd3 : FdEntry) (KB : TSet) : Prop := (forall vals : (list word), (forall R : (bvmap (5)%N word), (forall M : (word -> (option byte)), (((length vals) = (38)%nat) -> (((vals_ev vals (0)%nat) = sp0) -> (((vals_ev vals (1)%nat) = (p0 a0s path envv rd)) -> (((vals_ev vals (2)%nat) = (p1 a0s path envv rd)) -> (((vals_ev vals (5)%nat) = tid) -> ((regs_ok (ENV vals) srB0 R) -> ((know_ok RSEGS (ENV vals) M knA) -> ((above_sp0 M) -> ((below_win M) -> (realizes RSEGS (mkCfg (mkst R (Z_to_bv (64)%N 0x4729c%Z) M (seg_rom RSEGS)) (model1g fd3)) KB))))))))))))).
  Definition file_seg2_kont : TSet -> Prop := file_seg2_kont_g (FdFile path (Z_to_bv 64 0)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L11800014584.51L22307226813.39L22973606012.50L22973606012.53L29670166300.47L30224815755.51L34927224505.49L34929503351.47L36107553247.50L36107553247.53L38841990246.51L41663852402.50L41663852402.53L41665739397.46L4419303106.51 L50387686011.46L51594537528.51L54438946794.51L63382998904.46L64160615017.51L67502449517.51L7374777705.47 L7377053607.49 00000D00X01501R02<02P02d03803Z04<04Y05605S06006M07707T07h08M08a09509I09]S4path5Hplen4vals2HLS4path5Hplen4vals2HLS3sp04path5Hplen4vals2HL1x2HxS3sp04path5Hplen4vals2HL1x2HxS3sp03a0s4path4envv5Hplen4SPhi4vals2HL3ShiS4path5Hplen4vals2HLS4path5Hplen4vals2HLS4path5Hplen4vals2HLS3sp04path5Hplen4SPlo4vals2HL1x2HxS3sp04path5Hplen4SPlo4vals2HL1x2HxS3sp04path5Hplen4SPhi4vals2HLS3sp04path5Hplen4SPlo4vals2HLS3sp04path5Hplen4SPlo4vals2HLS3sp04path5Hplen4SPlo4vals2HLS3sp04path5Hplen4SPlo4vals2HLS3sp03a0s4path4envv5Hplen4SPlo4vals2HL3SloS3sp04path5Hplen4vals2HL1x2HxS4path5Hplen4vals2HLS3sp03a0s4path4envv5Hplen4vals2HL3SloS4path5Hplen4vals2HLS4path5Hplen4vals2HLS4path5Hplen4vals2HLS4path5Hplen4vals2HL". (* [comment removed for export] *)
  #[using="rd fdata Hva Hve Hvsp Htid ME Hfile Hpne Hpnd Hplen"] Lemma file_seg1 : ltac2:(CDefT.buildp (gd_tbl_P_main_open ()) "PKA,$43.PKB,$43.P,(44.R2.)P,(45.R2.)(3:.$1>.(3;.(3<.$3=.Vregs0,(18.&40.+1=24<.)Vmem0,(3>.$1>.))$3?.)(46.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros KA KB HKA HKB.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s path envv tid rd regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv tid rd regs0) with (ENV (vals0 sp0 a0s path envv tid rd regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid rd regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; apply vals0_length).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 a0s path envv rd) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 a0s path envv rd) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    ddestruct (main_str sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 a0s path envv rd) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0x7e000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | pose proof (u64_range (cat_argv_ptr (ed_top rd) [a0s; path] envv a_execfn 1)); lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_file RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [exact Hplen|]. split; [apply path_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. split; [exact Sr'|].
      (* LPS revision: read_cstr refuses a byte at or above TASK_SIZE; the path ends below the stack top *)
      pose proof (main_str_top sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as HT.
      cbn [nth] in HT. unfold p1, TASK_SIZE. lia.
    - exact Hpne.
    - exact Hpnd.
    - exact (proj1 path_noslash).
    - exact (proj2 path_noslash).
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x47298 + 4)%Z with 0x4729c%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x7e000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x47298 + 4)%Z with 0x4729c%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x7e000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      assert (HB : below_win M).
      { intros x Hx. rewrite EQM. apply (mem_denot_below (ENV vals) mem0 _ 0%nat (-6144512));
          [vm_compute; reflexivity | lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
      eapply (HKB vals); try eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

End Pilot.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
