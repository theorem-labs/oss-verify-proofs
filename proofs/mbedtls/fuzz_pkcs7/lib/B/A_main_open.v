(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape Mem Cells Step ZBridge HeapIface Asn1Aux Arr SysStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StreamSim StoreOk MemcpyLib ShapeLaws SymDriveX LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_main_file.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow AUnw NodesA NodesA2 SymDriveA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals ARestrict A_code_67000_68000 A_code_68000_69000 A_code_96000_97000 A_code_dd000_de000 A_code_de000_df000 A_code_e8000_e9000              A_exit_base A_exit_lib A_exit_defs A_exit_front1 A_unreg_globals A_tailkit_defs A_oomtail A_rip A_icpt_read A_main_tails.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import ATopContract A_main_inv A_main_loop A_main_fin A_main_hdr A_main_target.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance Lib.PropExec.fx0.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P016871b195cdef9f 0 2 1 1 23 1P017b887c3cde6564 0 2 0 1 22 1P02044bfcb0e4619b 0 2 1 1 28 1P024f60e7f3ea1163 0 2 0 1 19 1P031f480d592a1a81 0 2 0 1 22 1P03a890d90cafa976 0 2 1 1 23 1P0590268d314c65f1 0 2 1 1 23 1P062349ceb55cd452 0 2 0 1 19 1P066a190eb1bce505 0 2 0 1 18 1P075bccde76daffb7 0 2 1 1 23 1P0840328b56345304 0 2 0 1 22 1P0871cb75474b793d 0 2 1 1 23 1P09b6c2ccd78cd395 0 2 1 1 23 1P0a816dd1ef6a6d27 0 2 0 1 19 1P0e16fd452f86be41 0 2 1 1 28 1P0ece76c2c25331db 0 2 0 1 19 1P108857e925f7b905 0 2 0 1 24 1P1096b6d3c86ca793 0 2 1 1 23 1P1260ba42926f16a9 0 2 0 1 19 1P12835ea965f946a0 0 2 0 1 19 1P137c17406e18678d 0 2 0 1 19 1P139008fbc1fbcd24 0 2 0 1 19 1P1775b5b3e4973f39 0 2 0 1 19 1P177fde0709d835c2 0 2 1 1 23 1P18160c3709a13986 0 2 0 1 22 1P193f98c6aad43cd5 0 2 0 1 19 1P19c1d90a9467eb91 0 2 0 1 19 1P1bf2297e971c8e47 0 2 1 1 23 1P1c330912bf8c03bf 0 2 0 1 19 1P1d57407d8829ce08 0 2 0 1 22 1P1f3b64cf6719f36d 0 2 0 1 19 1P20517585afe67e3f 0 2 1 1 23 1P225f912916f4346d 0 2 0 1 19 1P22786ee05ff8796a 0 2 0 1 28 1P23b8d0c89ef4503f 0 2 0 1 22 1P25af0d014c5cfac0 0 2 0 1 22 1P26429e1c9c4ca913 0 2 1 1 23 1P2644180a1266fcae 0 2 0 1 22 1P26549721956d93f9 0 2 1 1 28 1P269ec732ba4f2592 0 2 0 1 18 1P2737987423dc1ae8 0 2 0 1 19 1P27e6816ff9b01440 0 2 0 1 19 1P287dccde944ac5d3 0 2 1 1 23 1P28a9a24f6706feb8 0 2 1 1 23 1P2af56ef03ec510ef 0 2 0 1 19 1P2c734fdc225d865b 0 2 0 1 18 1P2ca8f59bf8a4fb11 0 2 0 1 19 1P2d43ae06676443a5 0 2 0 1 24 1P2dc2e28f350bbc62 0 2 0 1 19 1P2e95f06ad5c93ed1 0 2 0 1 19 1P2ee8113eb8ccdc8c 0 2 0 1 19 1P2f18f308148cd529 0 2 0 1 22 1P2fc2550124ca63e8 0 2 1 1 23 1P315a5b2c9e7fbe89 0 2 1 1 23 1P352915ec52890a28 0 2 0 1 18 1P3784f4d69e5827ea 0 2 0 1 22 1P37bafffe8fb4cf83 0 2 0 1 19 1P37d7da5588951e9a 0 2 0 1 19 1P38595b65d45b82fd 0 2 1 1 28 1P3a28ab9ab88b47a7 0 2 0 1 19 1P3a52754c276c794d 0 2 1 1 23 1P3a9c6c4241d42959 0 2 1 1 23 1P3ad21c01da32d0f2 0 2 1 1 23 1P3eb8943349a3284c 0 2 1 1 23 1P3f3d2f118171d560 0 2 0 1 17 1P3f562e3a413b802c 0 2 1 1 23 1N01d6455f8d2c937dN02d66cb8fad7039dN08ff2dd1e483a27fN0b0d259a53fa56baN0e502025cee89a32N0f2d3f871072f51bN10141be87e95b817N10d003c0b3096500N128a71faae1ae835N1568074d64734baaN1b9edabe5df08a1cN2227f759e382d1c7N2496c6d7466f8172N25ecb3c210042839N290e7557955b34c1N2a902a6f8b4b1571N2aecac28b11ed9ebN2ed80f7ef24b4e95N316eb5cd8cbf6431N3270bb07367dd853N38c098c4963c8257N39c704e456eb35b0N3ad3e4ebe473c850N3dedb8a3953856e1"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_main_open () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Open.O1_post"; "Open.MREGS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "Open.O2_post"; "Open.OREGS"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.B.A_main_loop.LREGSA"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mrd"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.tail_memA"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.drv_static"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.ZIMG_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.ZIMG_HI"; "rtc_zone"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Open.near_HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.app"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_cannot_open"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Open.MENTRY"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "RocqVerifyHarness.AgentSubmission.B.A_main_inv.files_pristine"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_P"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "Open.ATOPEN"; "Open.EREGS"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_addi"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "RocqVerifyHarness.AgentSubmission.B.A_main_loop.after_loop_stmtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.hfresh"; "LinuxProcessSemantics.LinuxProcessSem.State.with_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_insert"; "RocqVerifyHarness.AgentSubmission.B.A_main_hdr.FDS2"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_fd"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFile"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_opened"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.LibA.NodesA2.path_atA"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.dot_path"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_read_error"; "LinuxProcessSemantics.LinuxProcessSem.State.FdDir"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_opened_dir"; "Open.UREGS"; "Open.UFRAME"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_usage"; "Open.usage_stmtA"; "Open.MENTRYU"].

#[local] Unset Lia Cache.

Lemma bytes_at_of_rdn : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$3.Pbs,(4.(0.&8.))P,(5.(1.(4.(0.&8.)))(6.$7.R4.(8.&40.R3.)R2.)(9.(4.(0.&8.))R1.))P,(:.=R4.)P,(:.(;.R5.(<.R4.))(=.+2.+40.))(>.$7.R7.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs H Ha Hn.
  - cbn in H. injection H as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - rewrite rdn_unfold in H. destruct (mrd asegs m (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate].
    change (Z_to_bv 64 a) with (wa a) in H. rewrite wa_succ in H. unfold wa in H.
    destruct (rdn asegs m (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Er; [|discriminate]. injection H as <-.
    pose proof (IH (a + 1) r Er ltac:(lia) ltac:(lia)) as (_ & _ & B).
    pose proof (IH (a + 1) r Er ltac:(lia) ltac:(lia)) as (_ & LB & _).
    split; [lia|]. split; [cbn [length]; lia|]. intros [|i] Hi; cbn in Hi.
    + rewrite Z.add_0_r. unfold wa. exact Eb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. cbn [nth_error]. apply B. lia.
Qed.
Lemma ro_cell8_of_rdn : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pv,(0.&40.)P,(5.(1.(4.(0.&8.)))(6.$7.R3.(8.&40.R2.)#8.)(9.(4.(0.&8.))(?.#8.R1.)))P,(:.=R3.)P,(:.(;.R4.+8.)(=.+2.+40.))(10.$7.R6.R5.(11.$12.(13.R4.)(14.$12.)))")
(* [comment removed for export] *).
Proof.
  intros m a v H Ha Hn. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  exact (bytes_at_of_rdn m a 8 _ H Ha Hn).
Qed.

Lemma swrap32_neg_errno : forall e, 1 <= e <= 4095 -> bv_swrap 32 (18446744073709551616 - e + 0) = - e.
Proof.
  intros e He. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N N.sub Z.pow_pos Pos.iter Z.mul Pos.mul].
  Z.div_mod_to_equations. lia.
Qed.
Lemma zbv_neg_errno : forall e, (Z_to_bv 64 (- e) : word) = Z_to_bv 64 (18446744073709551616 - e).
Proof. intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zminus_mod_idemp_l. reflexivity. Qed.

(* [comment removed for export] *)
Definition rtc_zone (a : Z) : Prop := (0x0f1000 <= a < 0x10b380) \/ (0x19b380 <= a < 0x19c350) \/ (0x63c080 <= a < 0x63c084).
Definition rtc_compl : list ivl := [(0, 0x0f1000); (0x10b380, 0x19b380); (0x19c350, 0x63c080); (0x63c084, 2^64)].
Lemma asan_rtc_agree : forall m m', asan_rtc m -> (forall a, rtc_zone a -> m' (wa a) = m (wa a)) -> asan_rtc m'.
Proof.
  intros m m' [RC PR] AG.
  assert (MU : munch rtc_compl m m').
  { intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
    apply AG. unfold rtc_compl in Hx. cbn in Hx. unfold rtc_zone. lia. }
  split.
  - apply Forall_forall. intros [[a n] v] Hin.
    pose proof (proj1 (Forall_forall _ _) RC _ Hin) as H. unfold rtc_holds in *.
    assert (B : 0 <= a /\ ((0x0f1000 <= a /\ a + 8 <= 0x10b380) \/ (0x19b380 <= a /\ a + 8 <= 0x19c350) \/ (0x63c080 <= a /\ a + 1 <= 0x63c084 /\ n = 1%nat))).
    { unfold rtc_cells in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; subst; cbn; lia |]). destruct Hin. }
    eapply ro_cells_transport; [exact H | exact MU |].
    assert (SZ : (Z.of_nat (cells_size [rtc_mkcell n v]) <= 8)%Z /\ (n = 1%nat -> cells_size [rtc_mkcell n v] = 1%nat)).
    { destruct n as [|[|[|[|[|n]]]]]; cbn; split; intros; try lia; try discriminate; reflexivity. }
    pose proof (Nat2Z.is_nonneg (cells_size [rtc_mkcell n v])).
    destruct B as [B0 [B|[B|(B1 & B2 & ->)]]]; [| | rewrite (proj2 SZ eq_refl)]; unfold rtc_compl; cbn [disjoint_from fst snd]; lia.
  - intros a Ha. rewrite AG; [apply PR; exact Ha|].
    unfold rtc_prist, rtc_pristine, AGLOB_LO, AGLOB_HI in Ha. unfold rtc_zone.
    assert (B : (0x0f1520 <= a < 0x0f5cc0) \/ (0x0f5df0 <= a < 0x0f6b50) \/ (0x0fa400 <= a < 0x0fa460) \/ (0x0fa780 <= a < 0x106340)).   (* [comment removed for export] *)
    { repeat (apply Exists_cons in Ha; destruct Ha as [Ha | Ha]; [cbn in Ha; lia|]). inversion Ha. }
    lia.
Qed.

Section Open.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Variable HID : artD asegs R HIA.
  Let AL := arl_AL R.
  Let L := arl_L R.
  #[local] Existing Instance L.   (* [comment removed for export] *)
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis GSB : al_gsb AL = 0x1099f8.
  Hypothesis HMALLOC : arl_malloc R = 0x69480.
  Hypothesis HFREE : arl_free R = 0x6947c.
  Hypothesis HMEMCPY : arl_memcpy_i R = 0x67db8.
  Hypothesis HTP : arl_tp R = 0x63ca90.
  Hypothesis HIMGCS : forall h, A_unreg_globals.img_cs AL (hcs asegs R HIA h).
  Variable SI : sinv (arl_L R).
  Hypothesis SIFP : forall a, ~ outside (si_fp SI) a -> 0x63c0a0 <= a < 0x63c180.

  Variable sp0 : word.
  Hypothesis SPlo : 0x7fff80000000 <= bv_unsigned sp0.       (* [comment removed for export] *)
  Hypothesis SPhi : bv_unsigned sp0 <= 0x800000000000.       (* [comment removed for export] *)
  Hypothesis SPal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis STKLO : arl_stklo R = bv_unsigned sp0 - 8388608.
  Variables (path : list byte) (pathp : word) (fs0 : Fs).
  Variables (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Variables (TOP STKHI V0 : Z).
  Hypothesis HTOPlo : bv_unsigned sp0 - 48 <= TOP.
  Hypothesis HSTKHI : bv_unsigned sp0 <= STKHI.
  Hypothesis STKHI8 : STKHI mod 8 = 0.
  Hypothesis STKHImax : STKHI <= 2^47.
  Hypothesis HV0 : V0 + 2^29 <= AVOL_SPLIT.      (* [comment removed for export] *)
  Let HV0M : V0 + 2^29 <= AVOL_MAX.                (* [comment removed for export] *)
  Proof. pose proof HV0 as H. unfold AVOL_SPLIT, AVOL_MAX in *. clear - H. lia. Qed.
  Variable FR0 : Z.                          (* [comment removed for export] *)
  Hypothesis HFR0 : FR0 <= FR_MAX.

  Let msp : Z := bv_unsigned sp0 - 128.     (* [comment removed for export] *)
  Let esp : Z := bv_unsigned sp0 - 48.      (* [comment removed for export] *)

  Ltac done_regs := apply evtA_done; unfold mkR; repeat (first [ reflexivity | lia | progress f_equal ]).
  Ltac solve_condb :=
    cbn [negb]; unfold bv_eqb, bv_ltu; rewrite ?bv_lts_zero_r; rewrite ?unsigned_lit by lia;
    repeat (first [ apply (proj2 (Bool.negb_true_iff _)) | apply (proj2 (Bool.negb_false_iff _)) ]);
    first [ reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
          | apply Z.leb_le; lia | apply Z.leb_gt; lia ].
  Ltac ifc b :=
    lazymatch goal with
    | |- ?EV (MS ?R ?F (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_condb]
    end.
  Ltac reg_lit pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  Ltac norm_getr_in H :=
    repeat match type of H with
    | context [getr (TNode ?a ?b ?c) ?r] =>
        let p := eval vm_compute in (bv_key r) in
        let v := eval cbn [tget] in (match tget p (TNode a b c) with Some v => v | None => w0 end) in
        change (getr (TNode a b c) r) with v in H
    end.

  (* [comment removed for export] *)
  Definition MREGS (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (argc : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "(15.(8.&40.+>0::8.)(8.&40.Vesp,)(8.&40.+10800.)(8.&40.+63<:90.)O=.O<.O;.(8.&40.(;.(16.&40.Vsp0,)+8.))(8.&40.O1.)(8.&40.O1.)(8.&40.(;.(16.&40.Vsp0,)+8.))(8.&40.(;.(;.(16.&40.Vsp0,)(17.+8.O1.))+10.))O:.O9.O8.O7.O6.(8.&40.+970>0.)(8.&40.(;.(;.(16.&40.Vsp0,)(17.+8.O1.))+10.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)O5.O4.O3.O2.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Let FRAMEA := A_main_loop.FRAMEA sp0.

  (* [comment removed for export] *)
  Lemma wseg_rs : wseg_ok asegs (Z_to_bv 64 RS) (Z.to_nat RSN) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma rs_wr_at : forall m, wr_at asegs m RS RSN.
  Proof.
    intros m. split; [unfold RS; lia|]. split; [unfold RS, RSN; lia|]. intros i Hi.
    assert (SO : store_ok asegs m (Z_to_bv 64 (RS + i)) 1 = true).
    { eapply (store_ok_window asegs m (Z_to_bv 64 RS) (Z_to_bv 64 (RS + i)) (Z.to_nat RSN) 1%nat RS (RS + RSN));
        [reflexivity | reflexivity | unfold RS, RSN; lia | exact wseg_rs
        | rewrite unsigned_lit by (unfold RS, RSN in *; lia); unfold RS, RSN in *; lia
        | rewrite unsigned_lit by (unfold RS, RSN in *; lia); unfold RS, RSN in *; lia]. }
    pose proof (store_ok_wview asegs m (Z_to_bv 64 (RS + i)) 1%nat 0%nat SO ltac:(lia)) as WV.
    rewrite unsigned_lit in WV by (unfold RS, RSN in *; lia). rewrite Z.add_0_r in WV. exact WV.
  Qed.

  (* [comment removed for export] *)
  Definition O1_post (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Lms',$18.(19.(4.(0.&8.))Lpad,(4.(0.&8.))(19.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(1:.(5.$18.R3.(1;.(15.(8.&40.+97120.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)O=.O<.O;.(8.&40.+2.)(8.&40.+2.)Vpathp,(8.&40.=)(8.&40.(;.(16.&40.Vsp0,)+20.))O:.O9.O8.O7.O6.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)O5.O4.O3.O2.)(1<.&5.(0.&40.))(8.&40.+>141<.)(8.&20.=)(1=.(0.&40.))R1.(1>.$7.)))(1:.(1?.(11.(20.$2.$2.)(21.$2.$2.(22.VR,)Vesp,)(14.(20.$2.$2.)))O1.R1.)(1:.(23.$7.O1.R1.)(1:.(24.$7.R1.)(1:.(25.$7.R1.(22.VR,)Vmsp,)(26.$7.R1.Vmsp,A1.VFRAMEA,R2.))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition CS0 (lo hi x : Z) : Prop := lo <= x < hi \/ 0x65cad0 <= x < 0x65cad8.
  Definition CS1 (lo hi x : Z) : Prop := lo <= x < hi \/ 0x65cad0 <= x < 0x65cad8 \/ 0x63c9ec <= x < 0x63c9f0.
  Lemma cs0_ok : forall lo hi, arl_stklo R <= lo -> hi <= bv_unsigned sp0 -> cs_ok AL (CS0 lo hi).
  Proof.
    intros lo hi Hlo Hhi.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (EG & ELO & EHI & EGS).
    pose proof SPlo as SL. pose proof SPhi as SH. pose proof STKLO as SK.
    unfold cs_ok, CS0, shadow_of. rewrite ASB, EG, EGS. clear - Hlo Hhi SL SH SK.
    split; [| split; [| split]].
    - intros c Hc. rewrite SK in Hlo. Z.div_mod_to_equations. lia.
    - intros i Hi. rewrite SK in Hlo. lia.
    - intros c i Hc Hi. rewrite SK in Hlo. Z.div_mod_to_equations. lia.
    - lia.
  Qed.
  Lemma cs1_ok : forall lo hi, arl_stklo R <= lo -> hi <= bv_unsigned sp0 -> cs_ok AL (CS1 lo hi).
  Proof.
    intros lo hi Hlo Hhi.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (EG & ELO & EHI & EGS).
    pose proof SPlo as SL. pose proof SPhi as SH. pose proof STKLO as SK.
    unfold cs_ok, CS1, shadow_of. rewrite ASB, EG, EGS. clear - Hlo Hhi SL SH SK.
    split; [| split; [| split]].
    - intros c Hc. rewrite SK in Hlo. Z.div_mod_to_equations. lia.
    - intros i Hi. rewrite SK in Hlo. lia.
    - intros c i Hc Hi. rewrite SK in Hlo. Z.div_mod_to_equations. lia.
    - lia.
  Qed.

  Lemma O1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))P,(25.$7.R1.(22.VR,)Vesp,)P,(24.$7.R2.)P,(27.R10.(22.VR,)(28.Vesp,(22.VR,)))P,(26.$7.R4.(;.(16.&40.Vsp0,)+10.)(11.$12.(13.Vpathp,)(14.$12.)))P,(27.R12.(;.(16.&40.Vsp0,)+10.)+8.)(29.$7.VAL,R13.(2:.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)(1;.(2;.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R6.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros * ST MI SCS AV ACS. unfold O1_post, MREGS. cbv delta [FRAMEA]. unfold A_main_loop.FRAMEA. subst msp esp.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(arl_stklo R, bv_unsigned sp0 - 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.                                          (* [comment removed for export] *)
    carve_frame 80%nat ST. try replace (bv_unsigned sp0 - 48 + -80) with (bv_unsigned sp0 + -128) in * by lia.
    try replace (bv_unsigned sp0 + -48 + -80) with (bv_unsigned sp0 + -128) in * by lia.
    replace (bv_unsigned sp0 - 48) with (bv_unsigned sp0 + -48) in MU by lia.
    do 9 zstep.                                     (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    replace (bv_unsigned sp0 + 8 * 2 + 16) with (bv_unsigned sp0 + 32) by lia.
    zstep.                                          (* [comment removed for export] *)
    zstep. zstep. zstep.                            (* [comment removed for export] *)
    replace (bv_unsigned sp0 - 128) with (bv_unsigned sp0 + -128) by lia.
    finish. all: try eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition OREGS (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "(15.O11.O10.(8.&40.+10800.)(8.&40.+63<:90.)O?.O>.O=.(8.&40.+2.)(8.&40.+2.)O<.O;.O:.O9.O8.O7.O6.O5.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)O4.O3.O2.O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition O2_post (t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Lms',$18.(19.(4.(0.&8.))Lj16,(4.(0.&8.))(19.(4.(0.&8.))Lj48,(4.(0.&8.))(19.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(1:.(5.$18.R4.(1;.(15.(8.&40.+>149<.)(8.&40.(;.Vmsp,-60.))(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,O=.O<.(8.&40.=)(8.&40.+65<:=0.)(8.&40.-64.)Vpathp,(8.&40.+8000.)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.+38.)Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)O5.O4.O3.O2.)(1<.&5.(0.&40.))(8.&40.+>;5:8.)(8.&20.=)(1=.(0.&40.))R1.(1>.$7.)))(1:.(1?.(11.(20.$2.$2.)(21.$2.$2.(22.VR,)Vmsp,)(14.(20.$2.$2.)))O1.R1.)(1:.(23.$7.O1.R1.)(1:.(24.$7.R1.)(1:.(25.$7.R1.(22.VR,)(;.Vmsp,-60.))(26.$7.R1.(;.Vmsp,-60.)(11.$12.(2<.#10.R3.)(11.$12.(13.Vcan,)(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+97120.))(11.$12.(13.O;.)(11.$12.(13.O:.)(11.$12.(13.O9.)(11.$12.(13.O8.)(11.$12.(13.O7.)(11.$12.(13.O6.)(14.$12.)))))))))))))))))))))")
(* [comment removed for export] *).

  Lemma O2_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))P,(25.$7.R1.(22.VR,)Vmsp,)P,(24.$7.R2.)P,(27.R11.(22.VR,)(28.Vmsp,(22.VR,)))P,(2=.R4.)P,(10.$7.R5.+65<:=0.(11.$12.(13.Vcan,)(14.$12.)))P,(27.R14.+65<:=0.+8.)(29.$7.VAL,R15.(2>.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)(1;.(2?.(8.&40.+97120.)(8.&40.Vmsp,)R14.R13.R12.Vpathp,(8.&40.=)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)(1<.&5.(0.&40.))(8.&40.+>141<.)(8.&20.=)(1=.(0.&40.))R7.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    clear HMALLOC HFREE HMEMCPY HTP HFR0 HV0M HV0 SPal STKHI8 STKHImax HTOPlo HSTKHI.   (* [comment removed for export] *)
    pose proof (art_alwf _ _ HIA : al_wf AL) as ALWF. pose proof (cs0_ok (arl_stklo R) msp ltac:(lia) ltac:(subst msp; pose proof SPlo; lia)) as CSOK.
    intros * ST MI SCS RTC CAN CCS. unfold O2_post, OREGS. subst msp.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    assert (GSB0 : al_gsb AL = 0x1099f8) by (destruct IMG' as (_ & _ & _ & G); exact G). clear GSB.   (* [comment removed for export] *)
    pose proof SPlo as SL. pose proof SPhi as SH. pose proof STKLO as SK.
    apply (evtA_cs_mono asegs AL (CS0 (arl_stklo R) (bv_unsigned sp0 - 128)) CS); [| intros x Hx; destruct Hx as [Hx|Hx]; [apply SCS | apply CCS]; clear - Hx; lia ].
    assert (SCS0 : crange (CS0 (arl_stklo R) (bv_unsigned sp0 - 128)) (arl_stklo R) (bv_unsigned sp0 - 128 - arl_stklo R)) by (intros x Hx; unfold CS0; left; lia).
    assert (CCS0 : crange (CS0 (arl_stklo R) (bv_unsigned sp0 - 128)) 0x65cad0 8) by (intros x Hx; unfold CS0; right; lia).
    clear SCS CCS.
    pose proof (munch_refl [(arl_stklo R, bv_unsigned sp0 - 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (asan_rtc_cell m 0x0f6ae0 8%nat 0x65cad0 RTC ltac:(unfold rtc_cells; cbn [In]; tauto)) as GOTC. cbn [rtc_mkcell] in GOTC.
    carve_frame 96%nat ST.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x0eb5a8] [] 80%N). lx_tree.
    try replace (bv_unsigned sp0 - 128) with (bv_unsigned sp0 + -128) in * by lia.
    try replace (bv_unsigned sp0 + -224) with (bv_unsigned sp0 + -128 + -96) in * by lia.
    apply evtA_done. eexists _, [], _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma O3_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pj16,(4.(0.&8.))Pfa2,(0.&40.)Pfa3,(0.&40.)Pfa4,(0.&40.)Pfa5,(0.&40.)Pfa6,(0.&40.)Pfa7,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))P,(26.$7.R1.(;.Vmsp,-60.)(11.$12.(2<.#10.R8.)(11.$12.(13.Vcan,)(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+97120.))(11.$12.(13.R7.)(11.$12.(13.R6.)(11.$12.(13.R5.)(11.$12.(13.R4.)(11.$12.(13.R3.)(11.$12.(13.R2.)(14.$12.)))))))))))))P,(27.R17.(28.Vmsp,+60.)+60.)P,(10.$7.R3.+65<:=0.(11.$12.(13.Vcan,)(14.$12.)))P,(27.R19.+65<:=0.+8.)(29.$7.VAL,R1:.Lms',$18.(19.(0.&40.)La1',(0.&40.)(19.(0.&40.)La2',(0.&40.)(5.$18.R3.(1;.(15.(8.&40.+97134.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,R1<.R1;.(8.&40.+2.)(8.&40.+2.)(8.&40.+10000.)R2.R1.(8.&40.+3.)R17.R16.R15.R14.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.+3.)(8.&40.+10000.)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R13.R12.R11.R10.)(1<.&5.(0.&40.))(8.&40.+69480.)(8.&20.=)(1=.(0.&40.))R8.(1>.$7.)))))(1;.(15.(8.&40.+>149<.)(8.&40.(;.Vmsp,-60.))(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,R19.R18.(8.&40.=)(8.&40.+65<:=0.)(8.&40.+3.)R17.R16.R15.R14.R13.R12.R11.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R10.R?.R>.R=.)(1<.&5.(0.&40.))(8.&40.+>;5:<.)(8.&20.=)(1=.(0.&40.))R5.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros * FR SCS CAN CCS. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    replace (bv_unsigned sp0 - 128 + -96) with (bv_unsigned sp0 + -224) in * by lia.
    zstep.                                          (* [comment removed for export] *)
    zstep. zstep. zstep.                            (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    zstep.                                          (* [comment removed for export] *)
    ifc false.
    zstep.                                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.              (* [comment removed for export] *)
    zstep.                                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
    match goal with |- ?g => idtac "O3END" g end.
    apply evtA_done. eexists _, _. unfold mkR. repeat (first [ reflexivity | lia | progress f_equal ]).
  Qed.

  (* [comment removed for export] *)
  Lemma O3n_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pj16,(4.(0.&8.))Pje,(4.(0.&8.))Pfa2,(0.&40.)Pfa3,(0.&40.)Pfa4,(0.&40.)Pfa5,(0.&40.)Pfa6,(0.&40.)Pfa7,(0.&40.)Pe,$2.Pm,P,(0.&40.)(1.(0.&8.))P,(1:.(:.+1.R2.)(:.R2.+???.))P,(26.$7.R2.(;.Vmsp,-60.)(11.$12.(2<.#10.R;.)(11.$12.(13.Vcan,)(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+97120.))(11.$12.(13.R9.)(11.$12.(13.R8.)(11.$12.(13.R7.)(11.$12.(13.R6.)(11.$12.(13.R5.)(11.$12.(13.R4.)(14.$12.)))))))))))))P,(27.R1:.(28.Vmsp,+70.)+70.)P,(10.$7.R4.+65<:=0.(11.$12.(13.Vcan,)(14.$12.)))P,(27.R1<.+65<:=0.+8.)P,(25.$7.R6.(22.VR,)(;.Vmsp,-60.))P,(26.$7.R7.+63<9><.(11.$12.(2<.#4.R?.)(14.$12.)))P,(24.$7.R8.)(29.$7.VAL,R20.Lms',$18.(19.(0.&40.)La1',(0.&40.)(19.(0.&40.)La2',(0.&40.)(19.(4.(0.&8.))Lj8,(4.(0.&8.))(19.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(1:.(5.$18.R5.(1;.(15.(8.&40.+97120.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,R24.R23.(8.&40.+2.)(8.&40.+2.)(8.&40.-1.)R4.R3.(8.&40.(28.+10000000000000000.R?.))R1?.R1>.R1=.R1<.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R1;.R1:.R19.R18.)(1<.&5.(0.&40.))(8.&40.+97370.)(8.&20.=)(1=.(0.&40.))R1.(1>.$7.)))(1:.(1?.(11.(20.$2.$2.)(21.$2.$2.(22.VR,)Vmsp,)(11.(20.$2.$2.)(21.$2.$2.+63<9><.+63<9?0.)(14.(20.$2.$2.))))R>.R1.)(1:.(23.$7.R>.R1.)(1:.(24.$7.R1.)(25.$7.R1.(22.VR,)Vmsp,)))))))))(1;.(15.(8.&40.+>149<.)(8.&40.(;.Vmsp,-60.))(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,R1?.R1>.(8.&40.=)(8.&40.+65<:=0.)(8.&40.(28.+10000000000000000.R:.))R1=.R1<.R1;.R1:.R19.R18.R17.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R16.R15.R14.R13.)(1<.&5.(0.&40.))(8.&40.+>;5:<.)(8.&20.=)(1=.(0.&40.))R9.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    clear HMALLOC HFREE HMEMCPY HTP HFR0 HV0M HV0 SPal STKHI8 STKHImax HTOPlo HSTKHI.   (* [comment removed for export] *)
    pose proof (art_alwf _ _ HIA : al_wf AL) as ALWF. pose proof (cs0_ok (msp - 112) msp ltac:(subst msp; pose proof SPlo; pose proof STKLO; lia) ltac:(subst msp; pose proof SPlo; lia)) as CSOK.
    intros * He FR SCS CAN CCS ST ERR MI. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    assert (GSB0 : al_gsb AL = 0x1099f8) by (destruct IMG' as (_ & _ & _ & G); exact G). clear GSB.
    pose proof SPlo as SL. pose proof SPhi as SH. pose proof STKLO as SK.
    replace (bv_unsigned sp0 - 128 + -96) with (bv_unsigned sp0 + -224) in * by lia.
    replace (bv_unsigned sp0 - 128 - 112) with (bv_unsigned sp0 + -240) in * by lia.
    apply (evtA_cs_mono asegs AL (CS0 (bv_unsigned sp0 + -240) (bv_unsigned sp0 - 128)) CS); [| intros x Hx; destruct Hx as [Hx|Hx]; [apply SCS | apply CCS]; clear - Hx; lia ].
    assert (SCS0 : crange (CS0 (bv_unsigned sp0 + -240) (bv_unsigned sp0 - 128)) (bv_unsigned sp0 + -240) 112) by (intros x Hx; unfold CS0; left; lia).
    assert (CCS0 : crange (CS0 (bv_unsigned sp0 + -240) (bv_unsigned sp0 - 128)) 0x65cad0 8) by (intros x Hx; unfold CS0; right; lia).
    clear SCS CCS.
    pose proof (munch_refl [(arl_stklo R, bv_unsigned sp0 - 128); (0x63c9ec, 0x63c9f0)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x097370] [] 80%N). lx_tree.
    (* [comment removed for export] *)
    all: try (lazymatch goal with Hn : 0 <= - zlow 64 (- ?ee) + _ |- _ => exfalso; clear - Hn He; unfold zlow in Hn; Z.div_mod_to_equations; lia end).
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      repeat (lazymatch goal with Hc : rw_cells _ mx (bv_unsigned sp0 + ?k) ?cs, STq : stk _ mx _ (bv_unsigned sp0 + ?k') |- _ =>
                constr_eq k k'; let z := eval cbv in (Z.of_nat (cells_size cs)) in
                release_frame Hc STq (bv_unsigned sp0 + k + z) end) end.
    replace (bv_unsigned sp0 + -240 + 112) with (bv_unsigned sp0 - 128) in * by lia.
    replace (bv_unsigned sp0 + -128) with (bv_unsigned sp0 - 128) in * by lia.
    replace (- e + 18446744073709551616) with (18446744073709551616 - e) in * by lia.
    apply evtA_done. eexists _, _, [], _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma O4_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pbuf,$2.Pm,P,(0.&40.)(1.(0.&8.))P,(1:.(30.=R2.)(30.R2.(=.+2.+2?.)))(29.$7.VAL,R12.Lms',$18.(5.$18.R1.(1;.(31.Vsp0,Vpathp,(8.&40.+97134.)R12.R11.R10.(8.&40.+62<140.)R?.R>.R=.R<.R;.R:.R9.(8.&40.R4.)R8.R7.R6.R5.R4.=+10000.)(1<.&5.(0.&40.))(8.&40.+971:<.)(8.&20.=)(1=.(0.&40.))R3.(1>.$7.)))(1;.(15.(8.&40.+97134.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)R11.R10.R?.(8.&40.+2.)(8.&40.+2.)(8.&40.R3.)R>.R=.R<.R;.R:.R9.R8.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.+3.)(8.&40.+10000.)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R7.R6.R5.R4.)(1<.&5.(0.&40.))(8.&40.+97134.)(8.&20.=)(1=.(0.&40.))R2.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros * HB. unfold LREGSA, RS. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. ifc false.                               (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    zstep. try (ifc true).                          (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    done_regs.
  Qed.

  (* [comment removed for export] *)
  Lemma O4n_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))(29.$7.VAL,R10.Lms',$18.(5.$18.R1.(1;.(15.(8.&40.+97134.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)R10.R?.R>.(8.&40.+2.)(8.&40.+2.)(8.&40.=)R=.R<.R;.R:.R9.R8.R7.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.+3.)(8.&40.+10000.)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R6.R5.R4.R3.)(1<.&5.(0.&40.))(8.&40.+97388.)(8.&20.=)(1=.(0.&40.))R2.(1>.$7.)))(1;.(15.(8.&40.+97134.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)R?.R>.R=.(8.&40.+2.)(8.&40.+2.)(8.&40.=)R<.R;.R:.R9.R8.R7.R6.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.+3.)(8.&40.+10000.)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R5.R4.R3.R2.)(1<.&5.(0.&40.))(8.&40.+97134.)(8.&20.=)(1=.(0.&40.))R1.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros *. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_defined : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$3.P,Pi,$2.P,(1:.(:.=R1.)(30.R1.(<.R2.)))(32.(5.(1.(0.&8.))(33.$7.R5.(34.(;.R4.R2.)))(1=.(0.&8.))))P,(:.=R3.)P,(:.(;.R4.(<.R3.))(=.+2.+40.))(19.(4.(0.&8.))Lbs,(4.(0.&8.))(5.(1.(4.(0.&8.)))(6.$7.R7.(8.&40.R6.)R5.)(9.(4.(0.&8.))R1.)))")
(* [comment removed for export] *).
  Proof.
    intros m a n. revert a. induction n as [|n IH]; intros a H Ha Hn; [exists []; reflexivity|].
    rewrite rdn_unfold. destruct (mrd asegs m (Z_to_bv 64 a)) as [b|] eqn:Eb.
    - change (Z_to_bv 64 a) with (wa a). rewrite wa_succ. unfold wa.
      destruct (IH (a + 1) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia) ltac:(lia) ltac:(lia)) as [r Hr].
      rewrite Hr. eexists. reflexivity.
    - exfalso. apply (H 0 ltac:(lia)). rewrite Z.add_0_r. unfold wa. exact Eb.
  Qed.
  Lemma errno_cell : forall m, exists je, rw_cells asegs m 0x63c9ec [CB 4 je].
  Proof.
    intros m.
    destruct (rdn_defined m 0x63c9ec 4) as [bs Hbs]; [| lia | lia |].
    { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
      unfold mrd, wa. destruct C as [-> | [-> | [-> | ->]]]; (destruct (m _); [discriminate | vm_compute; discriminate]). }
    exists bs. pose proof (rdn_length _ _ _ _ _ Hbs) as L0. split; [split; [cbn; exact (conj L0 I) |] |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (bytes_at_of_rdn m 0x63c9ec 4 bs Hbs ltac:(lia) ltac:(lia)).
    - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply (wview_6d5 sp0 [] m (wa (0x63c9ec + i))). unfold wa. rewrite unsigned_lit by lia. lia.
  Qed.

  Let HRTC : forall m, arl_rtc R m -> asan_rtc m := hd_rtc _ _ _ HID.
  Let DRVS : forall a, drv_static a -> cstatic R a := hd_static _ _ _ HID.
  Let HM_LOWSH : forall h LB LF m, HM asegs R HIA h LB LF m -> mapped m 0x7fffa000 0x800d3000 := hd_lowsh _ _ _ HID.
  Let HM_ZIMG := A_main_loop.HM_ZIMG R HIA ASB.

  (* [comment removed for export] *)
  Theorem tail_rebuild0 : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Psp,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pm',Px,(0.&40.)(1.(0.&8.))P,(35.R3.R2.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,Pa,$2.P,(36.R1.)(5.(1.(0.&8.))A1.R4.(34.R2.)A1.R5.(34.R2.))P,Pa,$2.P,(36.R1.)P,(32.(5.(1.(0.&8.))(37.$7.R6.(34.R2.))(1=.(0.&8.))))(32.(5.(1.(0.&8.))(37.$7.R6.(34.R3.))(1=.(0.&8.))))P,Pa,$2.P,(1:.(:.(38.R7.)R1.)(30.R1.(39.R7.)))(5.(1.(0.&8.))A1.R6.(8.&40.R2.)A1.R7.(8.&40.R2.))P,Pa,$2.P,(1:.(:.$3:.R1.)(30.R1.$3;.))(5.(1.(0.&8.))A1.R7.(8.&40.R2.)A1.R8.(8.&40.R2.))P,Pa,$2.P,(3<.R1.)(5.(1.(0.&8.))A1.R8.(34.R2.)A1.R9.(34.R2.))P,Pa,$2.P,(1:.(:.+7???:000.R1.)(30.R1.+800=3000.))(5.(1.(0.&8.))A1.R9.(34.R2.)A1.R:.(34.R2.))P,(24.$7.R8.)P,(25.$7.R9.(28.(16.&40.R;.)+1000.)(16.&40.R;.))(35.R<.R:.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)")
(* [comment removed for export] *).
  Proof.
    intros sp m m' TM AG WV SH ZI RT MP MI ST. pose proof (u64_range sp) as SPR.
    destruct TM as [WIN RO ERR CAN RTC ZIm ZS STK MI0 TID LOCK MTID ATEXIT NL COMP MAPPED GLOB FIN FOUT FLG INCB].
    assert (MU : munch drv_compl m m').
    { intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
      apply AG. apply (proj1 (outside_drv_compl (bv_unsigned x) ltac:(lia))). exact Hx. }
    assert (RW : forall A cs, rw_cells asegs m A cs ->
                 (0x0fa460 <= A /\ A + Z.of_nat (cells_size cs) <= 0x0fa780) \/ (A = 0x106390 /\ cells_size cs = 1%nat) \/ (0x63c180 <= A /\ A + Z.of_nat (cells_size cs) <= 0x63c9ec) \/ (0x63cae8 <= A /\ A + Z.of_nat (cells_size cs) <= 0x65cd50) \/ (0x63c050 <= A /\ A + Z.of_nat (cells_size cs) <= 0x63c080) ->
                 rw_cells asegs m' A cs).
    { intros A cs H DS. eapply rw_cells_transport_w; [exact H | exact MU | intros a Ha; apply WV; unfold drv_static; lia |].
      unfold drv_compl. cbn [disjoint_from fst snd]. lia. }
    split.
    - intros a Ha. pose proof (proj1 (proj2 (proj2 ST) (bv_unsigned a) Ha)) as W. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
    - intros a Ha. apply mem_inv_text_noneA; [exact MI | exact Ha].
    - intros a Ha. change (Z_to_bv 64 a) with (wa a). rewrite AG; [apply ERR; exact Ha | unfold drv_static; lia].
    - eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | exact CAN].
    - eapply asan_rtc_agree; [exact RTC | exact RT].
    - intros a Ha. rewrite ZI by exact Ha. apply ZIm. exact Ha.
    - intros a Ha. rewrite SH by exact Ha. apply ZS. exact Ha.
    - exact ST.
    - exact MI.
    - exact TID.
    - apply RW; [exact LOCK | cbn; lia].
    - apply RW; [exact MTID | cbn; lia].
    - destruct ATEXIT as (jp & jq & jf & AT). exists jp, jq, jf. unfold atexit_cells in *.
      apply RW; [exact AT | cbn; lia].
    - eapply ro_cells_transport; [exact NL | exact MU |]. unfold drv_compl. cbn [disjoint_from fst snd cells_size csize]. lia.
    - apply RW; [exact COMP | cbn; lia].
    - intros x Hx. rewrite MP by exact Hx. apply MAPPED. exact Hx.
    - destruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals.
      repeat split; (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
    - destruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
      repeat split; (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
    - destruct FOUT as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
      repeat split; (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
    - apply RW; [exact FLG | cbn; lia].
    - apply RW; [exact INCB | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma tail_errno : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))P,(35.(8.&40.Vmsp,)R2.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(1?.(11.(20.$2.$2.)(21.$2.$2.(22.VR,)Vmsp,)(11.(20.$2.$2.)(21.$2.$2.+63<9><.+63<9?0.)(14.(20.$2.$2.))))R3.R2.)P,(23.$7.R4.R3.)P,(24.$7.R4.)P,(25.$7.R5.(22.VR,)Vmsp,)(35.(8.&40.Vmsp,)R6.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)")
(* [comment removed for export] *).
  Proof.
    intros m m' TM MU WM MI ST. pose proof (u64_range sp0) as SPR.
    assert (AGz : forall a, 0 <= a < 2^64 -> (a < arl_stklo R \/ msp <= a) -> (a < 0x63c9ec \/ 0x63c9f0 <= a) -> m' (wa a) = m (wa a)).
    { intros a H0 H1 H2. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
    eapply tail_rebuild0; [exact TM | | | | | | | exact MI |]; rewrite ?unsigned_lit by (cbv delta [msp]; lia).
    - intros a Ha. apply AGz; unfold drv_static in Ha; rewrite ?STKLO; cbv delta [msp]; lia.
    - intros a Ha W0. apply WM. exact W0.
    - intros a Ha. unfold SSH_LO, SSH_HI in Ha. rewrite unsigned_lit in Ha by (cbv delta [msp]; lia). change (Z_to_bv 64 a) with (wa a). apply AGz; rewrite ?STKLO; cbv delta [msp] in *; lia.
    - intros a Ha. unfold ZIMG_LO, ZIMG_HI in Ha. change (Z_to_bv 64 a) with (wa a). apply AGz; rewrite ?STKLO; cbv delta [msp]; lia.
    - intros a Ha. unfold rtc_zone in Ha. apply AGz; rewrite ?STKLO; cbv delta [msp]; lia.
    - intros a Ha. apply AGz; rewrite ?STKLO; cbv delta [msp]; lia.
    - eapply (proj2 (stk_split asegs m' (arl_stklo R) (msp - 4096) msp ST ltac:(rewrite STKLO; cbv delta [msp]; lia))).
  Qed.

  (* [comment removed for export] *)
  Lemma sshad_munch_far : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PW,(4.$3=.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.Phi,$2.P,(3>.$7.VAL,R4.R2.R1.)P,(1?.R6.R5.R4.)P,(23.$7.R6.R5.)P,Pg,$2.P,(:.R6.R1.)P,(:.(;.R2.+8.)R6.)(3?.R;.(40.VAL,R3.)+1.)(3>.$7.VAL,R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' lo hi (S0 & S1 & SS) MU WM DJ. split; [exact S0|]. split; [exact S1|].
    intros g G1 G2 G3. eapply rw_cells_transport; [exact (SS g G1 G2 G3) | exact MU | exact WM | cbn [cells_size csize]; apply DJ; lia].
  Qed.

  (* [comment removed for export] *)
  Record MENTRY (m : mem) (mo : Model) (h : HST asegs R HIA) : Prop := MKME {
    me_hm : HM asegs R HIA h [] [] m;
    me_hk : HK asegs R HIA h mo;
    me_htop : htop asegs R HIA h = TOP;
    me_hstkhi : hstkhi asegs R HIA h = STKHI;
    me_vol : havol asegs R HIA h + 402392064 <= V0;           (* [comment removed for export] *)
    me_fr : hfr asegs R HIA h + 63 <= FR0;                      (* [comment removed for export] *)
    me_fresh : forall c, hfresh _ _ _ HID h c;                  (* [comment removed for export] *)
    me_tail : tail_memA (Z_to_bv 64 msp) m can tid wp0 rp0 wp1 rp1;
    me_files : files_pristine m;
    me_sshad : sshad asegs AL m (arl_stklo R) STKHI;                       (* [comment removed for export] *)
    me_si : si_P SI m;
    me_stk : stk asegs m (arl_stklo R) esp;
    me_argv1 : rw_cells asegs m (bv_unsigned sp0 + 16) [C8 pathp];               (* [comment removed for export] *)
    me_path : bytes_at asegs m (bv_unsigned pathp) (path ++ [Z_to_bv 8 0]);    (* [comment removed for export] *)
    me_pathnz : ~ In (Z_to_bv 8 0) path;
    me_pathok : path_has_slash path = false /\ path_eqb path dotdot_path = false;   (* [comment removed for export] *)
    me_pathlo : bv_unsigned sp0 + 40 <= bv_unsigned pathp;
    me_pathhi : bv_unsigned pathp + Z.of_nat (length path) + 16 <= STKHI;
    me_fds : m_fds mo = FDS2;
    me_fs : m_fs mo = fs0;
    me_pathlen : Z.of_nat (length path) <= 131071                            (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Definition near_HM (h : HST asegs R HIA) (LB : list blk) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "(19.P,(0.&40.)(1.(0.&8.))Lm0,P,(0.&40.)(1.(0.&8.))(1:.(41.$7.VR,VHIA,O3.O2.(14.$42.)R1.)(1:.(1?.(11.(20.$2.$2.)(21.$2.$2.(22.VR,)Vmsp,)(11.(20.$2.$2.)(21.$2.$2.+63<9><.+63<9?0.)(14.(20.$2.$2.))))R1.O1.)(23.$7.R1.O1.))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition openfail_stmtA : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(45.R1.(14.$42.)R3.)P,(46.$7.VR,VHIA,R2.R3.)P,(5.$2.(47.$7.VR,VHIA,R3.)VTOP,)P,(5.$2.(48.$7.VR,VHIA,R4.)VSTKHI,)P,(24.$7.R7.)P,(35.(8.&40.Vmsp,)R8.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(25.$7.R9.(22.VR,)Vmsp,)P,(3>.$7.VAL,R:.(22.VR,)VSTKHI,)P,(>.$7.R;.(16.&40.Vpathp,)(49.(0.&8.)Vpath,(11.(0.&8.)(8.&8.=)(14.(0.&8.)))))P,(32.(4:.(0.&8.)(8.&8.=)Vpath,))P,(:.(;.(16.&40.Vsp0,)+28.)(16.&40.Vpathp,))P,(:.(;.(;.(16.&40.Vpathp,)(<.(4;.(0.&8.)Vpath,)))+10.)VSTKHI,)P,(5.(1.$4<.)(4=.(4>.R>.)(8.&40.+2.))(9.$4<.(4?.(8.&40.+2.))))P,(5.$50.(51.R?.)Vfs0,)P,(:.(<.(4;.(0.&8.)Vpath,))+1????.)(52.$7.(53.(1;.(15.(8.&40.+97120.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,R1?.R1>.(8.&40.+2.)(8.&40.+2.)(8.&40.-1.)R1=.R1<.R1;.R1:.R19.R18.R17.Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R16.R15.R14.R13.)(1<.&5.(0.&40.))(8.&40.+97370.)(8.&20.=)(1=.(0.&40.))R12.(1>.$7.))R11.)(54.(55.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Hypothesis OPENFAIL : openfail_stmtA.

  (* [comment removed for export] *)
  Lemma to_openat : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)PT,$56.P,(57.R4.R3.R2.)P,Pm2,P,(0.&40.)(1.(0.&8.))Pj16,(4.(0.&8.))Ppad,(4.(0.&8.))Pmo2,$43.P,(41.$7.VR,VHIA,R7.(14.$42.)(14.$42.)R4.)P,(46.$7.VR,VHIA,R8.R2.)P,(58.R:.R3.)P,(24.$7.R7.)P,(35.(8.&40.Vmsp,)R8.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(59.R9.)P,(3>.$7.VAL,R:.(22.VR,)VSTKHI,)P,(5:.(5;.VR,)VSI,R;.)P,(25.$7.R<.(22.VR,)(;.Vmsp,-60.))P,(26.$7.R=.(;.Vmsp,-60.)(11.$12.(2<.#10.R<.)(11.$12.(13.Vcan,)(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+2.))(11.$12.(13.(8.&40.+97120.))(11.$12.(13.(8.&40.(;.(16.&40.Vsp0,)+20.)))(11.$12.(13.R1;.)(11.$12.(13.R1:.)(11.$12.(13.R19.)(11.$12.(13.R18.)(11.$12.(13.R17.)(14.$12.)))))))))))))P,(26.$7.R>.Vmsp,A1.VFRAMEA,R<.)P,(10.$7.R?.+65<:=0.(11.$12.(13.Vcan,)(14.$12.)))P,(>.$7.R10.(16.&40.Vpathp,)(49.(0.&8.)Vpath,(11.(0.&8.)(8.&8.=)(14.(0.&8.)))))(52.$7.(53.(5<.$5=.(15.(8.&40.+>149<.)(8.&40.(;.Vmsp,-60.))(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,R21.R20.(8.&40.=)(8.&40.+65<:=0.)(8.&40.-64.)Vpathp,(8.&40.+8000.)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.+38.)Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)R1:.R19.R18.R17.)(8.&40.+>;5:8.)R11.(1>.$7.))R>.)R13.)(52.$7.(53.(1;.(2;.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R6.(1>.$7.))R5.)R3.)")
(* [comment removed for export] *).
  Proof.
    intros * ME HC. pose proof ME as ME'. destruct ME' as [HH HKmo HT HS VOL VFR FRESH TM FI SSH SIm ST AV PATH PNZ POK PLO PHI FDS FS].
    pose proof (u64_range sp0) as SPR. pose proof (u64_range pathp) as PPR.
    pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK.
    assert (SCS : crange (hcs asegs R HIA h) (arl_stklo R) (esp - arl_stklo R)).
    { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [esp]; lia]. }
    assert (ACS : crange (hcs asegs R HIA h) (bv_unsigned sp0 + 16) 8).
    { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; lia | rewrite HS; lia]. }
    assert (CCS : crange (hcs asegs R HIA h) 0x65cad0 8).
    { intros x Hx. apply (hcs_static _ _ HIA h). apply DRVS. unfold drv_static. lia. }
    pose proof (ro_cell8_of_rdn m 0x65cad0 can (tm_can _ _ _ _ _ _ _ _ TM) ltac:(lia) ltac:(lia)) as CAN.
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HKmo | eapply (O1_steps (hcs asegs R HIA h)); [exact ST | exact (tm_mi _ _ _ _ _ _ _ _ TM) | exact SCS | exact AV | exact ACS] |].
    cbn beta. intros ms1 mo1 P1 HK1 MM1. destruct P1 as (pad & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HH1 : HM asegs R HIA h [] [] m1).
    { eapply (hm_munch _ _ HIA); [exact HH | exact MU1 | exact WM1 |].
      constructor; [| constructor]. cbn [fst snd]; intros a Ha. left. left. rewrite HT. cbv delta [esp] in Ha. lia. }
    assert (TM1 : tail_memA (Z_to_bv 64 msp) m1 can tid wp0 rp0 wp1 rp1).
    { eapply (tail_rebuild R HIA HRTC HM_LOWSH HM_ZIMG); [exact TM | | | | exact HH1 | exact MI1 |]; rewrite ?unsigned_lit by (cbv delta [msp]; lia).
      - intros a [Ha _]. apply MU1. rewrite wa_unsigned by (unfold drv_static in Ha; lia). cbn. unfold drv_static in Ha. cbv delta [esp]. lia.
      - intros a Ha W0. apply WM1. exact W0.
      - intros a Ha. unfold SSH_LO, SSH_HI in Ha. rewrite unsigned_lit in Ha by (cbv delta [msp]; lia). change (Z_to_bv 64 a) with (wa a). apply MU1. rewrite wa_unsigned by lia. cbn. cbv delta [esp msp] in *. rewrite STKLO. lia.
      - eapply (proj2 (stk_split asegs m1 (arl_stklo R) (msp - 4096) msp ST1 ltac:(rewrite STKLO; cbv delta [msp]; lia))). }
    assert (CAN1 : ro_cells asegs m1 0x65cad0 [C8 can]).
    { eapply ro_cells_transport; [exact CAN | exact MU1 | cbn [disjoint_from fst snd cells_size csize]; rewrite STKLO; lia]. }
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HK1 | eapply (O2_steps (hcs asegs R HIA h)); [exact ST1 | exact MI1 | eapply crange_sub; [exact SCS | lia | cbv delta [msp esp]; lia]
                                                       | apply HRTC; eapply (hm_rtc _ _ HIA); exact HH1 | exact CAN1 | exact CCS] |].
    cbn beta. intros ms2 mo2 P2 HK2 MM2. destruct P2 as (j16 & j48 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FR2).
    change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
    assert (HH2 : HM asegs R HIA h [] [] m2).
    { eapply (hm_munch _ _ HIA); [exact HH1 | exact MU2 | exact WM2 |].
      constructor; [| constructor]. cbn [fst snd]; intros a Ha. left. left. rewrite HT. cbv delta [msp] in Ha. lia. }
    pose proof (stk_release asegs m2 (arl_stklo R) (msp + -96) _ ST2 FR2 ltac:(rewrite STKLO; cbv delta [msp]; lia)) as ST2'.
    cbn [cells_size csize Nat.add] in ST2'. replace (msp + -96 + Z.of_nat 96) with msp in ST2' by lia.
    apply (HC m2 j16 pad mo2); try assumption.
    - eapply mo_mat_trans; [exact MM1 | exact MM2].
    - eapply (tail_munch R HIA HRTC HM_LOWSH HM_ZIMG can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m1 m2 h [] [] 0x65f000 0x65f000);
        rewrite ?unsigned_lit by (cbv delta [msp]; lia);
        [exact TM1 | eapply munch_weaken; [| exact MU2]; solve_sub_fp | exact WM2 | lia | lia | rewrite STKLO; lia | cbv delta [msp]; lia | exact HH2 | exact MI2
        | eapply (proj2 (stk_split asegs m2 (arl_stklo R) (msp - 4096) msp ST2' ltac:(rewrite STKLO; cbv delta [msp]; lia)))].
    - eapply files_munch; [| exact MU2 | cbn [disjoint_from fst snd]; rewrite STKLO; cbv delta [msp]; lia].
      eapply files_munch; [exact FI | exact MU1 | cbn [disjoint_from fst snd]; rewrite STKLO; cbv delta [esp]; lia].
    - eapply (sshad_munch asegs AL (hcs asegs R HIA h)); [exact CSOK | | | exact MU2 | exact WM2 |].
      + unfold w_client. constructor; [cbn [fst snd] | constructor]. eapply crange_sub; [exact SCS | lia | cbv delta [msp esp]; lia].
      + rewrite <- HS. apply (hcs_stack _ _ HIA h).
      + eapply (sshad_munch asegs AL (hcs asegs R HIA h)); [exact CSOK | | | exact MU1 | exact WM1 | exact SSH].
        * unfold w_client. constructor; [cbn [fst snd]; exact SCS | constructor].
        * rewrite <- HS. apply (hcs_stack _ _ HIA h).
    - eapply (si_munch (arl_L R) SI); [| exact MU2 | intros a NO; pose proof (SIFP a NO); cbn; rewrite STKLO; cbv delta [msp]; lia].
      eapply (si_munch (arl_L R) SI); [exact SIm | exact MU1 | intros a NO; pose proof (SIFP a NO); cbn; rewrite STKLO; cbv delta [esp]; lia].
    - eapply rw_cells_transport; [exact FR1 | exact MU2 | exact WM2 | cbv delta [FRAMEA]; cbn [cells_size csize A_main_loop.FRAMEA Nat.add disjoint_from fst snd]; rewrite STKLO; cbv delta [msp]; lia].
    - eapply ro_cells_transport; [exact CAN1 | exact MU2 | cbn [disjoint_from fst snd cells_size csize]; rewrite STKLO; cbv delta [msp]; lia].
    - eapply bytes_at_transport; [| exact MU2 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; rewrite STKLO; cbv delta [msp]; lia].
      eapply bytes_at_transport; [exact PATH | exact MU1 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; rewrite STKLO; cbv delta [esp]; lia].
  Qed.

  Lemma fds2_lookup2 : fd_lookup FDS2 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  Lemma alloc_fd_FDS2 : alloc_fd FDS2 = Z_to_bv 64 3.
  Proof. vm_compute. reflexivity. Qed.
  Lemma cap_ok_65536 : cap_ok 65536.
  Proof. exists 16. split; [lia | reflexivity]. Qed.

  (* [comment removed for export] *)
  Record ATOPEN (a3 a4 a5 a6 a7 : word) (j16 pad : list byte) (m2 : mem) (mo2 : Model) (h : HST asegs R HIA) : Prop := MKAO {
    ao_hm : HM asegs R HIA h [] [] m2;
    ao_hk : HK asegs R HIA h mo2;
    ao_mi : mem_inv asegs m2;
    ao_tail : tail_memA (Z_to_bv 64 msp) m2 can tid wp0 rp0 wp1 rp1;
    ao_files : files_pristine m2;
    ao_sshad : sshad asegs AL m2 (arl_stklo R) STKHI;
    ao_si : si_P SI m2;
    ao_stk : stk asegs m2 (arl_stklo R) (msp + -96);
    ao_frame96 : rw_cells asegs m2 (msp + -96) [CB 16 j16; C8 can; C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 0x097120);
                                             C8 (Z_to_bv 64 (bv_unsigned sp0 + 32)); C8 a3; C8 a4; C8 a5; C8 a6; C8 a7];
    ao_frameA : rw_cells asegs m2 msp (FRAMEA pad);
    ao_can : ro_cells asegs m2 0x65cad0 [C8 can];
    ao_path : bytes_at asegs m2 (bv_unsigned pathp) (path ++ [Z_to_bv 8 0]);
    ao_pathnz : ~ In (Z_to_bv 8 0) path;
    ao_pathok : path_has_slash path = false /\ path_eqb path dotdot_path = false;
    ao_pathlo : bv_unsigned sp0 + 40 <= bv_unsigned pathp;
    ao_pathhi : bv_unsigned pathp + Z.of_nat (length path) + 16 <= STKHI;
    ao_htop : htop asegs R HIA h = TOP;
    ao_hstkhi : hstkhi asegs R HIA h = STKHI;
    ao_fds : m_fds mo2 = FDS2;
    ao_fs : m_fs mo2 = fs0;
    ao_pathlen : Z.of_nat (length path) <= 131071
  }.

  Definition EREGS (t1 t2 a0 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "(15.(8.&40.+>149<.)(8.&40.(;.Vmsp,-60.))(8.&40.+10800.)(8.&40.+63<:90.)Vpathp,O7.O6.(8.&40.=)(8.&40.+65<:=0.)O5.Vpathp,(8.&40.+8000.)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.+38.)Vpathp,(8.&40.(;.(16.&40.Vsp0,)+20.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)O4.O3.O2.O1.)")
(* [comment removed for export] *).

  Lemma to_openat' : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)PT,$56.P,(57.R4.R3.R2.)P,Pm2,P,(0.&40.)(1.(0.&8.))Pj16,(4.(0.&8.))Ppad,(4.(0.&8.))Pmo2,$43.P,(5>.R12.R11.R10.R?.R>.R3.R2.R4.R1.R7.)(52.$7.(53.(5<.$5=.(5?.R15.R14.(8.&40.-64.)R>.R=.R<.R;.)(8.&40.+>;5:8.)R5.(1>.$7.))R2.)R7.)(52.$7.(53.(1;.(2;.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R6.(1>.$7.))R5.)R3.)")
(* [comment removed for export] *).
  Proof.
    intros * ME HC. pose proof ME as ME'. destruct ME' as [HH HKmo HT HS VOL VFR FRESH TM FI SSH SIm ST AV PATH PNZ POK PLO PHI FDS FS].
    eapply to_openat; [exact ME|]. intros m2 j16 pad mo2. intros. apply (HC m2 j16 pad mo2). split; try assumption.
    - rewrite (A_main_fin.mo_mat_fds _ _ ltac:(eassumption)). exact FDS.
    - rewrite (mo_mat_fs _ _ ltac:(eassumption)). exact FS.
  Qed.

  (* [comment removed for export] *)
  Lemma openfail_branch : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pj16,(4.(0.&8.))Ppad,(4.(0.&8.))Pe,$2.Pm2,P,(0.&40.)(1.(0.&8.))Pmo2,$43.Pmo3,$43.Ph,(44.$7.VR,VHIA,)P,(5>.R10.R?.R>.R=.R<.R7.R6.R4.R3.R1.)P,(1:.(:.+1.R6.)(:.R6.+???.))P,(46.$7.VR,VHIA,R3.R4.)P,(58.R6.R5.)(52.$7.(53.(5<.$5=.(60.(5?.R16.R15.(8.&40.-64.)R?.R>.R=.R<.)(61.&5.+:.$62.)(63.R9.))(64.(8.&40.+>;5:8.)+4.)R8.(1>.$7.))R6.)(54.(55.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * AO He' HK3 MM3. destruct AO as [HH HKh MI TM FI SSH SIm ST FR96 FRA CAN PATH PNZ POK PLO PHI HT HS FDS FS].
    pose proof (u64_range sp0) as SPR. pose proof (u64_range pathp) as PPR. pose proof (hcs_ok _ _ HIA h) as CSOK.
    change (regupd (EREGS t1 t2 (Z_to_bv 64 (-100)) t3 t4 t5 t6) 10 (errno_ret e)) with (EREGS t1 t2 (errno_ret e) t3 t4 t5 t6).
    unfold EREGS. unfold errno_ret. rewrite zbv_neg_errno.
    replace (v_addi (Z_to_bv 64 0x0eb5a8) 4) with (Z_to_bv 64 0x0eb5ac : word) by (apply bv_eq; reflexivity).
    change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
    destruct (errno_cell m2) as [je ERR].
    assert (CCS : crange (hcs asegs R HIA h) 0x65cad0 8).
    { intros x Hx. apply (hcs_static _ _ HIA h). apply DRVS. unfold drv_static. lia. }
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h)); [exact HK3 | |].
    { eapply (O3n_steps (hcs asegs R HIA h)); [exact He' | exact FR96 | | exact CAN | exact CCS | exact ST | | exact MI].
      - eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS; cbv delta [msp]; lia].
      - exact ERR. }
    cbn beta. intros ms4 mo4 P4 HK4 MM4. destruct P4 as (a1' & a2' & j8 & m4 & -> & MU4 & WM4 & MI4 & ST4).
    rewrite ?unsigned_lit in MU4, ST4 by (cbv delta [msp]; lia).
    apply (OPENFAIL _ _ _ _ _ _ _ _ _ _ _ _ _ m4 mo4 h).
    - exists m2. split; [exact HH|]. split; [exact MU4 | exact WM4].
    - exact HK4.
    - exact HT.
    - exact HS.
    - exact MI4.
    - eapply tail_errno; [exact TM | exact MU4 | exact WM4 | exact MI4 | exact ST4].
    - exact ST4.
    - eapply sshad_munch_far; [exact SSH | exact MU4 | exact WM4 |].
      intros g G1 G2. unfold shadow_of. change (al_sb AL) with (al_sb (arl_AL R)). fold AL. rewrite ASB.
      cbn [disjoint_from fst snd]. rewrite STKLO in *. cbv delta [msp]. Z.div_mod_to_equations. lia.
    - eapply bytes_at_transport; [exact PATH | exact MU4 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; rewrite STKLO; cbv delta [msp]; lia].
    - exact PNZ.
    - exact PLO.
    - exact PHI.
    - rewrite (A_main_fin.mo_mat_fds _ _ MM4), (A_main_fin.mo_mat_fds _ _ MM3), FDS. reflexivity.
    - rewrite (mo_mat_fs _ _ MM4), (mo_mat_fs _ _ MM3). exact FS.
    - assumption.
  Qed.

  Hypothesis AFTER : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pfdata,(4.(0.&8.))Ppad,(4.(0.&8.))P,(5.(1.(4.(0.&8.)))(65.Vfs0,Vpath,)(9.(4.(0.&8.))R2.))(66.VR,VHIA,VHID,Vsp0,Vpath,Vpathp,Vfs0,R3.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,VTOP,VSTKHI,VV0,VFR0,R2.VSI,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma file_branch : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pj16,(4.(0.&8.))Ppad,(4.(0.&8.))Pfdata,(4.(0.&8.))Pm2,P,(0.&40.)(1.(0.&8.))Pmo2,$43.Pmo3,$43.Ph,(44.$7.VR,VHIA,)P,(5>.R10.R?.R>.R=.R<.R7.R6.R4.R3.R1.)P,(5.(1.(4.(0.&8.)))(65.Vfs0,Vpath,)(9.(4.(0.&8.))R6.))P,(:.(;.(67.$7.VR,VHIA,R3.)+17?<0400.)VV0,)P,(:.(;.(68.$7.VR,VHIA,R4.)+3?.)VFR0,)P,Pc,$2.(69.$7.VR,VHIA,VHID,R6.R1.)P,(46.$7.VR,VHIA,R6.R7.)P,(58.(6:.(6;.$6<.(6=.$6<.)(6>.Vpath,(8.&40.=)))R9.)R8.)(52.$7.(53.(5<.$5=.(60.(5?.R19.R18.(8.&40.-64.)R12.R11.R10.R?.)(61.&5.+:.$62.)(6=.$6<.))(64.(8.&40.+>;5:8.)+4.)R;.(1>.$7.))R9.)(6?.R<.Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * AO Hfd VOL VFR FRESH HK3 MM3. destruct AO as [HH HKh MI TM FI SSH SIm ST FR96 FRA CAN PATH PNZ POK PLO PHI HT HS FDS FS].
    pose proof (u64_range sp0) as SPR. pose proof (u64_range pathp) as PPR. pose proof (hcs_ok _ _ HIA h) as CSOK. pose proof (art_alwf _ _ HIA) as ALWF.
    pose proof (hd_needs _ _ _ HID) as (NM & NF & NA). pose proof (hd_ceil _ _ _ HID) as HCEIL.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. destruct IMG' as (HGOT & HILO & HIHI & HGSB2).
    rewrite alloc_fd_FDS2 in *.
    change (regupd (EREGS t1 t2 (Z_to_bv 64 (-100)) t3 t4 t5 t6) 10 (Z_to_bv 64 3)) with (EREGS t1 t2 (Z_to_bv 64 3) t3 t4 t5 t6). unfold EREGS.
    replace (v_addi (Z_to_bv 64 0x0eb5a8) 4) with (Z_to_bv 64 0x0eb5ac : word) by (apply bv_eq; reflexivity).
    change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
    assert (CCS : crange (hcs asegs R HIA h) 0x65cad0 8).
    { intros x Hx. apply (hcs_static _ _ HIA h). apply DRVS. unfold drv_static. lia. }
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h)); [exact HK3 | |].
    { eapply (O3_steps (hcs asegs R HIA h)); [exact FR96 | | exact CAN | exact CCS].
      eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS; cbv delta [msp]; lia]. }
    cbn beta. intros ms4 mo4 (a1' & a2' & ->) HK4 MM4. rewrite <- HMALLOC.
    pose proof (stk_release asegs m2 (arl_stklo R) (msp + -96) _ ST FR96 ltac:(rewrite STKLO; cbv delta [msp]; lia)) as ST'.
    cbn [cells_size csize Nat.add] in ST'. replace (msp + -96 + Z.of_nat 96) with msp in ST' by lia.
    assert (FD2 : fd_lookup (m_fds mo4) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { rewrite (A_main_fin.mo_mat_fds _ _ MM4), (A_main_fin.mo_mat_fds _ _ MM3). reflexivity. }
    assert (FS4 : m_fs mo4 = fs0).
    { rewrite (mo_mat_fs _ _ MM4), (mo_mat_fs _ _ MM3). exact FS. }
    assert (FDS4 : m_fds mo4 = P_main_file.FDS path (Z_to_bv 64 0)).
    { rewrite (A_main_fin.mo_mat_fds _ _ MM4), (A_main_fin.mo_mat_fds _ _ MM3). reflexivity. }
    (* [comment removed for export] *)
    unfold t_opened. eapply srzJ_conseq; [| apply (LSHAPE_absorb fs0 fdata 65536)].
    eapply (heapA_malloc_split _ _ _ HID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              bvmap_empty (Z_to_bv 32 0) m2 mo4 h [] [] 65536 (arl_stklo R) 0);
      rewrite ?unsigned_lit by (cbv delta [msp]; lia);
      [ exact HH | exact HK4 | exact ST' | lia | cbv delta [msp]; lia | rewrite HT; cbv delta [msp]; lia | cbv delta [msp]; lia
      | exact MI | rewrite HTP; reflexivity | reflexivity | unfold AMAX; lia
      | left; unfold AMAX_SEC; lia
      | unfold AVOL_CALL in *; lia
      | unfold AVOL_CALL in *; lia   (* [comment removed for export] *)
      | apply uwc_data; [lia | rewrite STKLO; lia]   (* [comment removed for export] *)
      | unfold fr_charge; lia
      | intros _; eapply Z.le_lt_trans; [apply cnt24_le_length| cbn [length]; unfold C24MAX; lia]   (* [comment removed for export] *)
      | apply OOM_nil | apply LSHAPE_nil | | ].
    - (* [comment removed for export] *)
      intros t0' t1' t2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' m4 mo5 h4 MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK5 HCS4 HV4 HFR4 HFRESH4 HH4.
      reg_lit 0x097134.
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
        [exact HK5 | apply (O4n_steps (hcs asegs R HIA h4)) |].
      cbn beta. intros ms6 mo6 -> HK6 MM6. unfold OOM.
      replace fs0 with (m_fs mo6) by (rewrite (mo_mat_fs _ _ MM6), (A_main_fin.mo_frame_fs _ _ MF4); exact FS4).
      eapply (oom_glueA AL (hcs asegs R HIA h4) (HK asegs R HIA h4) IMG ALWF (hcs_ok _ _ HIA h4) ASB (HIMGCS h4)
                (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4) (hk_vmonly _ _ HIA h4) (Z_to_bv 64 msp));
        rewrite ?unsigned_lit by (cbv delta [msp]; lia);
        [ cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia
        | eapply crange_sub; [apply (hcs_stack _ _ HIA h4) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS4, HS; cbv delta [msp]; lia]
        | intros a n Ha Hn; apply (hcs_img _ _ HIA h4); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia
        | left; reflexivity
        | eapply (tail_presA R HIA ASB HRTC HM_LOWSH HM_ZIMG DRVS can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m2 m4 h4); rewrite ?unsigned_lit by (cbv delta [msp]; lia);
          [exact TM | rewrite <- HS; exact HP4 | exact HH4 | exact MI4 | exact ST4 | rewrite STKLO; cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia]
        | exact HK6
        | rewrite (A_main_fin.mo_mat_fds _ _ MM6), (A_main_fin.mo_frame_fds _ _ MF4); exact FD2 ].
    - (* [comment removed for export] *)
      intros t0' t1' t2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' m4 mo5 h4 buf jb MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK5 HCS4 HV4 HFR4 HFRESH4 AL16 FRSH4 BLK HH4 RW4.
      reg_lit 0x097134.
      destruct (hm_apart _ _ HIA h4 _ _ m4 HH4) as [HBLKS _]. pose proof (Forall_inv HBLKS) as AB. cbn [fst snd app] in AB. destruct AB as (AB1 & AB2 & AB3 & AB4).
      pose proof (hd_blk_band _ _ _ HID h4 _ _ m4 buf 65536 HH4 ltac:(left; reflexivity)) as (BLO & BCE & BHI).
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
        [exact HK5 | apply (O4_steps (hcs asegs R HIA h4)); lia |].
      cbn beta. intros ms6 mo6 -> HK6 MM6.
      eapply (read_loopA R HIA IMG ASB HMALLOC HFREE HMEMCPY HTP HID sp0 SPlo SPhi SPal STKLO path pathp fs0 fdata Hfd can tid wp0 rp0 wp1 rp1 TOP STKHI V0 FR0 HTOPlo HSTKHI HV0 HFR0 pad HIMGCS
                SI SIFP (AFTER fdata pad Hfd) (S (length fdata)) buf 0 65536 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 mo6 h4); [lia | lia |].
      split.
      + exact HH4.
      + exact HK6.
      + rewrite HT4. exact HT.
      + rewrite HS4. exact HS.
      + unfold AVOL_CALL in *. lia.
      + cbn [ndbl]. unfold fr_charge in *. lia.
      + eapply (tail_presA R HIA ASB HRTC HM_LOWSH HM_ZIMG DRVS can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m2 m4 h4); rewrite ?unsigned_lit by (cbv delta [msp]; lia);
          [exact TM | rewrite <- HS; exact HP4 | exact HH4 | exact MI4 | exact ST4 | rewrite STKLO; cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia].
      + eapply (files_presA R DRVS); [exact FI | exact HP4].
      + eapply (presA_sshad asegs R); [exact HP4 | | lia | rewrite HS; cbv delta [msp]; lia].
        eapply (proj1 (sshad_split asegs AL m2 (arl_stklo R) msp STKHI SSH ltac:(rewrite STKLO; cbv delta [msp]; lia) ltac:(cbv delta [msp]; lia))).
      + eapply si_heap_presx; [exact SIm | eapply presA_presx; exact HP4 | intros; exact I].
      + exact ST4.
      + eapply (presA_rw_cells asegs R); [exact HP4 | exact FRA | apply client_range_stack; lia | exact I].
      + apply rs_wr_at.
      + rewrite (mo_mat_fs _ _ MM6), (A_main_fin.mo_frame_fs _ _ MF4). exact FS4.
      + rewrite (A_main_fin.mo_mat_fds _ _ MM6), (A_main_fin.mo_frame_fds _ _ MF4). exact FDS4.
      + cbn [Z.to_nat firstn]. apply bytes_at_nil. lia.
      + exists jb. rewrite Z.add_0_r. split; [exact (proj1 (u8arr_of_rw_cells asegs m4 buf _ jb RW4)) |].
        pose proof RW4 as RW4'. destruct RW4' as [[WF4 _] _]. cbn in WF4. destruct WF4 as [LJ _]. lia.
      + pose proof (proj2 RW4) as W4. cbn [cells_size csize] in W4. rewrite Nat.add_0_r, Z2Nat.id in W4 by lia. exact W4.
      + lia.
      + apply cap_ok_65536.
      + rewrite HS in BLK. repeat split; [lia | exact BLK | lia].
      + intros c Hc. apply (HFRESH4 c ltac:(left; unfold AMAX_SEC; lia)). apply FRESH.
      + right. intros c. apply (HFRESH4 c ltac:(left; unfold AMAX_SEC; lia)). apply FRESH.
  Qed.

  (* [comment removed for export] *)
  Lemma path_atA_of : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pregs,(70.&5.(0.&40.))Pm,P,(0.&40.)(1.(0.&8.))P,(5.(0.&40.)(71.R2.(61.&5.+;.$62.))Vpathp,)P,(>.$7.R2.(16.&40.Vpathp,)(49.(0.&8.)Vpath,(11.(0.&8.)(8.&8.=)(14.(0.&8.)))))P,(32.(4:.(0.&8.)(8.&8.=)Vpath,))P,(72.(4;.(0.&8.)Vpath,)#???.)(73.$7.R6.R5.Vpath,)")
(* [comment removed for export] *).
  Proof.
    intros regs m G BY NZ LEN. unfold path_atA. rewrite G. split; [exact LEN|]. split; [exact NZ|].
    pose proof (bytes_at_rdn asegs m (bv_unsigned pathp) _ 0 (length path + 1) BY ltac:(rewrite length_app; cbn; lia)) as RD.
    rewrite Z.add_0_r in RD. unfold wa in RD. rewrite Z_to_bv_bv_unsigned in RD. rewrite RD. f_equal.
    rewrite <- (length_app path [Z_to_bv 8 0]) at 1 by reflexivity. cbn [skipn]. replace (length path + 1)%nat with (length (path ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia). apply firstn_all.
  Qed.

  (* [comment removed for export] *)
  Theorem main_fileA : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)Pfdata,(4.(0.&8.))P,(57.R4.R3.R2.)P,(5.(1.(4.(0.&8.)))(65.Vfs0,Vpath,)(9.(4.(0.&8.))R2.))P,(32.(5.(4.(0.&8.))Vpath,(14.(0.&8.))))P,(32.(5.(4.(0.&8.))Vpath,$74.))P,(72.(4;.(0.&8.)Vpath,)#???.)(52.$7.(53.(1;.(2;.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R9.(1>.$7.))R8.)(75.(54.(55.Vpath,)Vfs0,)(6?.R6.Vfs0,)))")
(* [comment removed for export] *).
  Proof.
    intros * ME Hfd Hne Hnd Hlen. pose proof ME as ME'. destruct ME' as [HH HKmo HT HS VOL VFR FRESH TM FI SSH SIm ST AV PATH PNZ POK PLO PHI FDS FS].
    pose proof (u64_range sp0) as SPR. pose proof (u64_range pathp) as PPR.
    eapply (to_openat' t0); [exact ME|]. intros m2 j16 pad mo2 AO.
    pose proof AO as AO'. destruct AO' as [HH2 HK2 MI2 TM2 FI2 SSH2 SI2 ST2 FR96 FRA CAN PATH2 _ POK2 _ _ HT2 HS2 FDS2' FS2].
    eapply (rz_openat_fileA asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
              _ (Z_to_bv 64 0x0eb5a8) m2 mo2 W_e81f8 F_e81f8 E_e81f8 HK2).
    - reflexivity.
    - reflexivity.
    - vm_compute. reflexivity.
    - rewrite FDS2'. reflexivity.
    - apply path_atA_of; [reflexivity | exact PATH2 | exact PNZ | exact Hlen].
    - exact Hne.
    - exact Hnd.
    - exact (proj1 POK2).
    - exact (proj2 POK2).
    - rewrite FS2. exact Hfd.
    - (* [comment removed for export] *)
      intros z Hz. unfold EREGS, mkR in Hz. norm_getr_in Hz. left.
      apply (hcs_stack _ _ HIA h). rewrite STKLO, HS. lia.
    - (* [comment removed for export] *)
      intros e He mo3 HK3 MM3. eapply openfail_branch; [exact AO | | exact HK3 | exact MM3].
      unfold openat_errnos in He. cbn [In] in He. unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
    - (* [comment removed for export] *)
      intros mo3 HK3 MM3. rewrite FDS2' in MM3 |- *. eapply file_branch; [exact AO | exact Hfd | exact VOL | exact VFR | exact FRESH | exact HK3 | exact MM3].
  Qed.

  (* [comment removed for export] *)
  Theorem main_absentA : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(57.R3.R2.R1.)P,(5.(1.(4.(0.&8.)))(65.Vfs0,Vpath,)(1=.(4.(0.&8.))))P,(32.(5.(4.(0.&8.))Vpath,(14.(0.&8.))))P,(32.(5.(4.(0.&8.))Vpath,$74.))P,(72.(4;.(0.&8.)Vpath,)#???.)(52.$7.(53.(1;.(2;.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R8.(1>.$7.))R7.)(54.(55.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * ME Hfd Hne Hnd Hlen.
    eapply (to_openat' t0); [exact ME|]. intros m2 j16 pad mo2 AO.
    pose proof AO as AO'. destruct AO' as [HH2 HK2 MI2 TM2 FI2 SSH2 SI2 ST2 FR96 FRA CAN PATH2 PNZ POK2 PLO PHI HT2 HS2 FDS2' FS2].
    eapply (rz_openat_absentA asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
              _ (Z_to_bv 64 0x0eb5a8) m2 mo2 W_e81f8 F_e81f8 E_e81f8 HK2).
    - reflexivity.
    - reflexivity.
    - vm_compute. reflexivity.
    - apply path_atA_of; [reflexivity | exact PATH2 | exact PNZ | exact Hlen].
    - exact Hne.
    - exact Hnd.
    - exact (proj1 POK2).
    - exact (proj2 POK2).
    - rewrite FS2. exact Hfd.
    - intros z Hz. unfold EREGS, mkR in Hz. norm_getr_in Hz. left. apply (hcs_stack _ _ HIA h). rewrite STKLO, HS2. lia.
    - intros mo3 HK3 MM3. eapply openfail_branch; [exact AO | unfold ENOENT; lia | exact HK3 | exact MM3].
  Qed.

  (* [comment removed for export] *)
  Theorem main_emptyA : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(57.R3.R2.R1.)P,(5.(4.(0.&8.))Vpath,(14.(0.&8.)))(52.$7.(53.(1;.(2;.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R5.(1>.$7.))R4.)(54.(55.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * ME Hp.
    eapply (to_openat' t0); [exact ME|]. intros m2 j16 pad mo2 AO.
    pose proof AO as AO'. destruct AO' as [HH2 HK2 MI2 TM2 FI2 SSH2 SI2 ST2 FR96 FRA CAN PATH2 PNZ POK2 PLO PHI HT2 HS2 FDS2' FS2].
    eapply (rz_openat_emptyA asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
              _ (Z_to_bv 64 0x0eb5a8) m2 mo2 W_e81f8 F_e81f8 E_e81f8 HK2).
    - reflexivity.
    - reflexivity.
    - vm_compute. reflexivity.
    - rewrite <- Hp. apply path_atA_of; [reflexivity | exact PATH2 | exact PNZ | rewrite Hp; cbn; lia].
    - unfold EREGS, mkR. norm_getr. left. apply (hcs_stack _ _ HIA h). rewrite STKLO, HS2. lia.
    - intros mo3 HK3 MM3. eapply openfail_branch; [exact AO | unfold ENOENT; lia | exact HK3 | exact MM3].
  Qed.

  (* [comment removed for export] *)
  Theorem main_toolongA : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(57.R3.R2.R1.)P,(72.#1000.(4;.(0.&8.)Vpath,))(52.$7.(53.(1;.(2;.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R5.(1>.$7.))R4.)(54.(55.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * ME Hlen.
    eapply (to_openat' t0); [exact ME|]. intros m2 j16 pad mo2 AO.
    pose proof AO as AO'. destruct AO' as [HH2 HK2 MI2 TM2 FI2 SSH2 SI2 ST2 FR96 FRA CAN PATH2 PNZ POK2 PLO PHI HT2 HS2 FDS2' FS2].
    pose proof (u64_range pathp) as PPR.
    eapply (rz_openat_toolongA asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
              _ (Z_to_bv 64 0x0eb5a8) m2 mo2 W_e81f8 F_e81f8 E_e81f8 HK2) with (bs := firstn 4096 path).
    - reflexivity.
    - reflexivity.
    - vm_compute. reflexivity.
    - unfold EREGS, mkR. norm_getr.
      pose proof (bytes_at_rdn asegs m2 (bv_unsigned pathp) _ 0 4096 PATH2 ltac:(rewrite length_app; cbn; lia)) as RD.
      rewrite Z.add_0_r in RD. unfold wa in RD. rewrite Z_to_bv_bv_unsigned in RD. rewrite RD. rewrite ?skipn_O. cbn [skipn]. rewrite firstn_app.
      replace (4096 - length path)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
    - intros Hin. apply PNZ. rewrite <- (firstn_skipn 4096 path). apply in_app_iff. left. exact Hin.
    - unfold EREGS, mkR. norm_getr. intros z Hz. left. apply (hcs_stack _ _ HIA h). rewrite STKLO, HS2. lia.
    - intros mo3 HK3 MM3. eapply openfail_branch; [exact AO | unfold ENAMETOOLONG; lia | exact HK3 | exact MM3].
  Qed.

  (* [comment removed for export] *)
  Lemma D1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pbuf,$2.Pm,P,(0.&40.)(1.(0.&8.))(29.$7.VAL,R12.Lms',$18.(5.$18.R1.(1;.(31.Vsp0,Vpathp,(8.&40.+971<8.)R12.R11.R10.(8.&40.-1.)R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.=+10000.)(1<.&5.(0.&40.))(8.&40.+9730<.)(8.&20.=)(1=.(0.&40.))R2.(1>.$7.)))(1;.(31.Vsp0,Vpathp,(8.&40.+971<8.)R11.R10.R?.(8.&40.-1.)R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.=+10000.)(1<.&5.(0.&40.))(8.&40.+971<8.)(8.&20.=)(1=.(0.&40.))R1.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros *. unfold LREGSA. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Definition readerr_stmtA : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pbuf,$2.Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(45.R1.(11.(20.$2.$2.)(21.$2.$2.R4.+10000.)(14.(20.$2.$2.)))R3.)P,(46.$7.VR,VHIA,R2.R3.)P,(5.$2.(47.$7.VR,VHIA,R3.)VTOP,)P,(5.$2.(48.$7.VR,VHIA,R4.)VSTKHI,)P,(24.$7.R7.)P,(35.(8.&40.Vmsp,)R8.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(25.$7.R9.(22.VR,)Vmsp,)P,(3>.$7.VAL,R:.(22.VR,)VSTKHI,)P,(>.$7.R;.(16.&40.Vpathp,)(49.(0.&8.)Vpath,(11.(0.&8.)(8.&8.=)(14.(0.&8.)))))P,(32.(4:.(0.&8.)(8.&8.=)Vpath,))P,(:.(;.(16.&40.Vsp0,)+28.)(16.&40.Vpathp,))P,(:.(;.(;.(16.&40.Vpathp,)(<.(4;.(0.&8.)Vpath,)))+10.)VSTKHI,)P,(5.(1.$4<.)(4=.(4>.R>.)(8.&40.+2.))(9.$4<.(4?.(8.&40.+2.))))P,(5.$50.(51.R?.)Vfs0,)(52.$7.(53.(1;.(31.Vsp0,Vpathp,(8.&40.+971<8.)R21.R20.R1?.(8.&40.-1.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.=+10000.)(1<.&5.(0.&40.))(8.&40.+9730<.)(8.&20.=)(1=.(0.&40.))R11.(1>.$7.))R10.)(54.(76.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Hypothesis READERR : readerr_stmtA.

  (* [comment removed for export] *)
  Lemma dir_branch : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pj16,(4.(0.&8.))Ppad,(4.(0.&8.))Pm2,P,(0.&40.)(1.(0.&8.))Pmo2,$43.Pmo3,$43.Ph,(44.$7.VR,VHIA,)P,(5>.R?.R>.R=.R<.R;.R6.R5.R4.R3.R1.)P,(:.(;.(67.$7.VR,VHIA,R2.)+17?<0400.)VV0,)P,(:.(;.(68.$7.VR,VHIA,R3.)+3?.)VFR0,)P,(46.$7.VR,VHIA,R4.R5.)P,(58.(6:.(6;.$6<.(6=.$6<.)$77.)R7.)R6.)(52.$7.(53.(5<.$5=.(60.(5?.R16.R15.(8.&40.-64.)R?.R>.R=.R<.)(61.&5.+:.$62.)(6=.$6<.))(64.(8.&40.+>;5:8.)+4.)R9.(1>.$7.))R7.)(78.Vpath,Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * AO VOL VFR HK3 MM3. destruct AO as [HH HKh MI TM FI SSH SIm ST FR96 FRA CAN PATH PNZ POK PLO PHI HT HS FDS FS].
    pose proof (u64_range sp0) as SPR. pose proof (u64_range pathp) as PPR. pose proof (hcs_ok _ _ HIA h) as CSOK. pose proof (art_alwf _ _ HIA) as ALWF.
    pose proof (hd_needs _ _ _ HID) as (NM & NF & NA). pose proof (hd_ceil _ _ _ HID) as HCEIL.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. destruct IMG' as (HGOT & HILO & HIHI & HGSB2).
    rewrite alloc_fd_FDS2 in *.
    change (regupd (EREGS t1 t2 (Z_to_bv 64 (-100)) t3 t4 t5 t6) 10 (Z_to_bv 64 3)) with (EREGS t1 t2 (Z_to_bv 64 3) t3 t4 t5 t6). unfold EREGS.
    replace (v_addi (Z_to_bv 64 0x0eb5a8) 4) with (Z_to_bv 64 0x0eb5ac : word) by (apply bv_eq; reflexivity).
    change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
    assert (CCS : crange (hcs asegs R HIA h) 0x65cad0 8).
    { intros x Hx. apply (hcs_static _ _ HIA h). apply DRVS. unfold drv_static. lia. }
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h)); [exact HK3 | |].
    { eapply (O3_steps (hcs asegs R HIA h)); [exact FR96 | | exact CAN | exact CCS].
      eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS; cbv delta [msp]; lia]. }
    cbn beta. intros ms4 mo4 (a1' & a2' & ->) HK4 MM4. rewrite <- HMALLOC.
    pose proof (stk_release asegs m2 (arl_stklo R) (msp + -96) _ ST FR96 ltac:(rewrite STKLO; cbv delta [msp]; lia)) as ST'.
    cbn [cells_size csize Nat.add] in ST'. replace (msp + -96 + Z.of_nat 96) with msp in ST' by lia.
    assert (FD2 : fd_lookup (m_fds mo4) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { rewrite (A_main_fin.mo_mat_fds _ _ MM4), (A_main_fin.mo_mat_fds _ _ MM3). reflexivity. }
    assert (FD3 : fd_lookup (m_fds mo4) (Z_to_bv 64 3) = Some FdDir).
    { rewrite (A_main_fin.mo_mat_fds _ _ MM4), (A_main_fin.mo_mat_fds _ _ MM3). reflexivity. }
    assert (FS4 : m_fs mo4 = fs0).
    { rewrite (mo_mat_fs _ _ MM4), (mo_mat_fs _ _ MM3). exact FS. }
    (* [comment removed for export] *)
    unfold t_opened_dir.
    eapply (heapA_malloc_split _ _ _ HID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              bvmap_empty (Z_to_bv 32 0) m2 mo4 h [] [] 65536 (arl_stklo R) 0);
      rewrite ?unsigned_lit by (cbv delta [msp]; lia);
      [ exact HH | exact HK4 | exact ST' | lia | cbv delta [msp]; lia | rewrite HT; cbv delta [msp]; lia | cbv delta [msp]; lia
      | exact MI | rewrite HTP; reflexivity | reflexivity | unfold AMAX; lia
      | left; unfold AMAX_SEC; lia
      | unfold AVOL_CALL in *; lia
      | unfold AVOL_CALL in *; lia   (* [comment removed for export] *)
      | apply uwc_data; [lia | rewrite STKLO; lia]   (* [comment removed for export] *)
      | unfold fr_charge; lia
      | intros _; eapply Z.le_lt_trans; [apply cnt24_le_length| cbn [length]; unfold C24MAX; lia]   (* [comment removed for export] *)
      | unfold t_die; apply t_emit_has_nil | unfold t_die; apply t_emit_has_nil | | ].
    - (* [comment removed for export] *)
      intros t0' t1' t2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' m4 mo5 h4 MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK5 HCS4 HV4 HFR4 HFRESH4 HH4.
      reg_lit 0x097134.
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
        [exact HK5 | apply (O4n_steps (hcs asegs R HIA h4)) |].
      cbn beta. intros ms6 mo6 -> HK6 MM6.
      replace fs0 with (m_fs mo6) by (rewrite (mo_mat_fs _ _ MM6), (A_main_fin.mo_frame_fs _ _ MF4); exact FS4).
      eapply (oom_glueA AL (hcs asegs R HIA h4) (HK asegs R HIA h4) IMG ALWF (hcs_ok _ _ HIA h4) ASB (HIMGCS h4)
                (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4) (hk_vmonly _ _ HIA h4) (Z_to_bv 64 msp));
        rewrite ?unsigned_lit by (cbv delta [msp]; lia);
        [ cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia
        | eapply crange_sub; [apply (hcs_stack _ _ HIA h4) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS4, HS; cbv delta [msp]; lia]
        | intros a n Ha Hn; apply (hcs_img _ _ HIA h4); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia
        | left; reflexivity
        | eapply (tail_presA R HIA ASB HRTC HM_LOWSH HM_ZIMG DRVS can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m2 m4 h4); rewrite ?unsigned_lit by (cbv delta [msp]; lia);
          [exact TM | rewrite <- HS; exact HP4 | exact HH4 | exact MI4 | exact ST4 | rewrite STKLO; cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia]
        | exact HK6
        | rewrite (A_main_fin.mo_mat_fds _ _ MM6), (A_main_fin.mo_frame_fds _ _ MF4); exact FD2 ].
    - (* [comment removed for export] *)
      intros t0' t1' t2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' m4 mo5 h4 buf jb MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK5 HCS4 HV4 HFR4 HFRESH4 AL16 FRSH4 BLK HH4 RW4.
      reg_lit 0x097134.
      destruct (hm_apart _ _ HIA h4 _ _ m4 HH4) as [HBLKS _]. pose proof (Forall_inv HBLKS) as AB. cbn [fst snd app] in AB. destruct AB as (AB1 & AB2 & AB3 & AB4).
      pose proof (hd_blk_band _ _ _ HID h4 _ _ m4 buf 65536 HH4 ltac:(left; reflexivity)) as (BLO & BCE & BHI).
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
        [exact HK5 | apply (O4_steps (hcs asegs R HIA h4)); lia |].
      cbn beta. intros ms6 mo6 -> HK6 MM6.
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
        [exact HK6 | apply (E1_steps R IMG sp0 SPlo pathp (hcs asegs R HIA h4)); lia |].
      cbn beta. intros ms7 mo7 -> HK7 MM7. unfold LREGSA. cbv zeta.
      replace (Z.min (65536 - 0) 65536) with 65536 by lia.
      assert (TM4 : tail_memA (Z_to_bv 64 msp) m4 can tid wp0 rp0 wp1 rp1).
      { eapply (tail_presA R HIA ASB HRTC HM_LOWSH HM_ZIMG DRVS can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m2 m4 h4); rewrite ?unsigned_lit by (cbv delta [msp]; lia);
          [exact TM | rewrite <- HS; exact HP4 | exact HH4 | exact MI4 | exact ST4 | rewrite STKLO; cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia]. }
      destruct (errno_cell m4) as [je ERR4].
      eapply (read_icpt_dirA AL IMG ALWF (hcs asegs R HIA h4) (hcs_ok _ _ HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                m4 mo7 3 RS 65536 0x63ca90 (arl_stklo R) je);
        rewrite ?unsigned_lit by (cbv delta [msp]; lia);
        [ exact HK7
        | rewrite (A_main_fin.mo_mat_fds _ _ MM7), (A_main_fin.mo_mat_fds _ _ MM6), (A_main_fin.mo_frame_fds _ _ MF4); exact FD3
        | apply rtc_rd_consts; apply HRTC; eapply (hm_rtc _ _ HIA); exact HH4
        | apply rs_wr_at
        | lia | unfold RS; lia | unfold RS; lia
        | reflexivity | lia
        | apply (hcs_img _ _ HIA h4); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia
        | exact ERR4
        | exact ST4 | rewrite STKLO; lia | cbv delta [msp]; lia
        | eapply crange_sub; [apply (hcs_stack _ _ HIA h4) | lia | rewrite HS4, HS; cbv delta [msp]; lia]
        | exact MI4 | lia
        | reflexivity | f_equal; lia | reflexivity | ].
      intros a1x a2x a3x a4x a5x a6x a7x m8 mo8 MU8 WM8 MI8 ST8 ERR8 HK8 MM8.
      reg_lit 0x0971c8. rewrite ?unsigned_lit in MU8, ST8 by (cbv delta [msp]; lia).
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
        [exact HK8 | apply (D1_steps (hcs asegs R HIA h4)) |].
      cbn beta. intros ms9 mo9 -> HK9 MM9.
      apply (READERR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ buf m8 mo9 h4).
      + exists m4. split; [exact HH4|]. split; [| exact WM8]. eapply munch_weaken; [| exact MU8]. unfold sub_fp; cbn [outside]; intros x Hx; lia.
      + exact HK9.
      + rewrite HT4. exact HT.
      + rewrite HS4. exact HS.
      + exact MI8.
      + eapply tail_errno; [exact TM4 | | exact WM8 | exact MI8 | exact ST8]. eapply munch_weaken; [| exact MU8]. unfold sub_fp; cbn [outside]; intros x Hx; lia.
      + exact ST8.
      + eapply sshad_munch_far; [| exact MU8 | exact WM8 |].
        * eapply (presA_sshad asegs R); [exact HP4 | exact SSH | lia | rewrite HS; lia].
        * intros g G1 G2. unfold shadow_of. change (al_sb AL) with (al_sb (arl_AL R)). fold AL. rewrite ASB.
          cbn [disjoint_from fst snd]. rewrite STKLO in *. cbv delta [msp]. Z.div_mod_to_equations. lia.
      + assert (PATH4 : bytes_at asegs m4 (bv_unsigned pathp) (path ++ [Z_to_bv 8 0])).
        { eapply (presA_bytes_at asegs R); [exact HP4 | exact PATH | apply client_range_stack; cbv delta [msp]; lia | exact I]. }
        eapply bytes_at_transport; [exact PATH4 | exact MU8 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; rewrite STKLO; cbv delta [msp]; lia].
      + exact PNZ.
      + exact PLO.
      + exact PHI.
      + rewrite (A_main_fin.mo_mat_fds _ _ MM9), (A_main_fin.mo_mat_fds _ _ MM8), (A_main_fin.mo_mat_fds _ _ MM7), (A_main_fin.mo_mat_fds _ _ MM6), (A_main_fin.mo_frame_fds _ _ MF4). exact FD2.
      + rewrite (mo_mat_fs _ _ MM9), (mo_mat_fs _ _ MM8), (mo_mat_fs _ _ MM7), (mo_mat_fs _ _ MM6), (A_main_fin.mo_frame_fs _ _ MF4). exact FS4.
  Qed.

  (* [comment removed for export] *)
  Theorem main_dirA : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(57.R3.R2.R1.)P,(5.(4.(0.&8.))Vpath,$74.)(52.$7.(53.(1;.(2;.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.+2.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R5.(1>.$7.))R4.)(75.(54.(55.Vpath,)Vfs0,)(78.Vpath,Vfs0,)))")
(* [comment removed for export] *).
  Proof.
    intros * ME Hp. pose proof ME as ME'. destruct ME' as [HH HKmo HT HS VOL VFR FRESH TM FI SSH SIm ST AV PATH PNZ POK PLO PHI FDS FS].
    eapply (to_openat' t0); [exact ME|]. intros m2 j16 pad mo2 AO.
    pose proof AO as AO'. destruct AO' as [HH2 HK2 MI2 TM2 FI2 SSH2 SI2 ST2 FR96 FRA CAN PATH2 _ POK2 _ _ HT2 HS2 FDS2' FS2].
    eapply (rz_openat_dotA asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
              _ (Z_to_bv 64 0x0eb5a8) m2 mo2 W_e81f8 F_e81f8 E_e81f8 HK2).
    - reflexivity.
    - reflexivity.
    - vm_compute. reflexivity.
    - rewrite FDS2'. reflexivity.
    - lazymatch goal with |- path_atA _ _ _ ?d => replace d with path by (rewrite Hp; reflexivity) end.
      apply path_atA_of; [reflexivity | exact PATH2 | exact PNZ | rewrite Hp; unfold dot_path; cbn; lia].
    - intros z Hz. unfold EREGS, mkR in Hz. norm_getr_in Hz. left. apply (hcs_stack _ _ HIA h). rewrite Hp in PHI. unfold dot_path in PHI. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in PHI. rewrite STKLO, HS2. lia.
    - intros e He mo3 HK3 MM3. eapply openfail_branch; [exact AO | | exact HK3 | exact MM3].
      unfold openat_errnos in He. cbn [In] in He. unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
    - intros mo3 HK3 MM3. rewrite FDS2' in MM3 |- *. eapply dir_branch; [exact AO | exact VOL | exact VFR | exact HK3 | exact MM3].
  Qed.

  (* [comment removed for export] *)
  Definition UFRAME (pad : list byte) (argc : Z) : list cell := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "(11.$12.(2<.#8.O2.)(11.$12.(13.(8.&40.=))(11.$12.(13.(8.&40.=))(11.$12.(13.(8.&40.=))(11.$12.(13.(8.&40.=))(11.$12.(13.(8.&40.(;.(;.(16.&40.Vsp0,)(17.+8.O1.))+10.)))(11.$12.(13.(8.&40.+970>0.))(11.$12.(13.(8.&40.O1.))(11.$12.(13.(8.&40.(;.(16.&40.Vsp0,)+8.)))(11.$12.(13.(8.&40.+>0::8.))(14.$12.)))))))))))")
(* [comment removed for export] *).
  Definition UREGS (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (argc : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "(15.(8.&40.+>0::8.)(8.&40.Vmsp,)(8.&40.+10800.)(8.&40.+63<:90.)O=.O<.O;.(8.&40.+2.)(8.&40.O1.)(8.&40.O1.)(8.&40.(;.(16.&40.Vsp0,)+8.))(8.&40.(;.(;.(16.&40.Vsp0,)(17.+8.O1.))+10.))O:.O9.O8.O7.O6.(8.&40.+970>0.)(8.&40.(;.(;.(16.&40.Vsp0,)(17.+8.O1.))+10.))(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)(8.&40.=)O5.O4.O3.O2.)")
(* [comment removed for export] *).

  Lemma U1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "PCS,P,$2.SpPt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pargc,$2.Pm,P,(0.&40.)(1.(0.&8.))P,(1:.(:.=R2.)(30.R2.(=.+2.+1?.)))P,(32.(5.$2.R3.+2.))P,(25.$7.R3.(22.VR,)Vesp,)P,(24.$7.R4.)P,(27.R13.(22.VR,)(28.Vesp,(22.VR,)))(29.$7.VAL,R14.Lms',$18.(19.(4.(0.&8.))Lpad,(4.(0.&8.))(19.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(1:.(5.$18.R3.(1;.(79.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)(1<.&5.(0.&40.))(8.&40.+97278.)(8.&20.=)(1=.(0.&40.))R1.(1>.$7.)))(1:.(1?.(11.(20.$2.$2.)(21.$2.$2.(22.VR,)Vesp,)(14.(20.$2.$2.)))R9.R1.)(1:.(23.$7.R9.R1.)(1:.(24.$7.R1.)(1:.(25.$7.R1.(22.VR,)Vmsp,)(26.$7.R1.Vmsp,(7:.R2.R:.)))))))))(1;.(2;.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R6.(1>.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros * Ha Hne ST MI SCS. unfold MREGS, UREGS, UFRAME. cbv delta [msp esp] in ST, SCS |- *.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(arl_stklo R, bv_unsigned sp0 - 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.                                          (* [comment removed for export] *)
    carve_frame 80%nat ST. try replace (bv_unsigned sp0 - 48 + -80) with (bv_unsigned sp0 + -128) in * by lia.
    try replace (bv_unsigned sp0 + -48 + -80) with (bv_unsigned sp0 + -128) in * by lia.
    replace (bv_unsigned sp0 - 48) with (bv_unsigned sp0 + -48) in MU by lia.
    do 9 zstep.                                     (* [comment removed for export] *)
    zstep. zstep. ifc true.                         (* [comment removed for export] *)
    replace (bv_unsigned sp0 - 128) with (bv_unsigned sp0 + -128) by lia.
    finish. all: try eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition usage_stmtA (argc : Z) (a0p : word) (a0s : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ppad,(4.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(41.$7.VR,VHIA,R1.(14.$42.)(14.$42.)R3.)P,(46.$7.VR,VHIA,R2.R3.)P,(5.$2.(47.$7.VR,VHIA,R3.)VTOP,)P,(5.$2.(48.$7.VR,VHIA,R4.)VSTKHI,)P,(24.$7.R7.)P,(35.(8.&40.Vmsp,)R8.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(25.$7.R9.(22.VR,)Vmsp,)P,(3>.$7.VAL,R:.(22.VR,)VSTKHI,)P,(26.$7.R;.Vmsp,(7:.R<.O3.))P,(26.$7.R<.(;.(16.&40.Vsp0,)+8.)(11.$12.(13.O2.)(14.$12.)))P,(>.$7.R=.(16.&40.O2.)(49.(0.&8.)O1.(11.(0.&8.)(8.&8.=)(14.(0.&8.)))))P,(32.(4:.(0.&8.)(8.&8.=)O1.))P,(:.(;.(;.(16.&40.Vsp0,)(17.+8.O3.))+18.)(16.&40.O2.))P,(:.(;.(;.(16.&40.O2.)(<.(4;.(0.&8.)O1.)))+10.)VSTKHI,)P,(5.(1.$4<.)(4=.(4>.R10.)(8.&40.+2.))(9.$4<.(4?.(8.&40.+2.))))P,(5.$50.(51.R11.)Vfs0,)P,(:.(<.(4;.(0.&8.)O1.))+1????.)P,(1:.(:.=O3.)(30.O3.(=.+2.+1?.)))(52.$7.(53.(1;.(79.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.O3.)(1<.&5.(0.&40.))(8.&40.+97278.)(8.&20.=)(1=.(0.&40.))R15.(1>.$7.))R14.)(54.(7;.O1.)Vfs0,))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Record MENTRYU (argc : Z) (a0p : word) (a0s : list byte) (m : mem) (mo : Model) (h : HST asegs R HIA) : Prop := MKMEU {
    mu_hm : HM asegs R HIA h [] [] m;
    mu_hk : HK asegs R HIA h mo;
    mu_htop : htop asegs R HIA h = TOP;
    mu_hstkhi : hstkhi asegs R HIA h = STKHI;
    mu_tail : tail_memA (Z_to_bv 64 msp) m can tid wp0 rp0 wp1 rp1;
    mu_sshad : sshad asegs AL m (arl_stklo R) STKHI;
    mu_stk : stk asegs m (arl_stklo R) esp;
    mu_argv0 : rw_cells asegs m (bv_unsigned sp0 + 8) [C8 a0p];
    mu_a0s : bytes_at asegs m (bv_unsigned a0p) (a0s ++ [Z_to_bv 8 0]);
    mu_a0snz : ~ In (Z_to_bv 8 0) a0s;
    mu_a0lo : bv_unsigned sp0 + 8 * argc + 24 <= bv_unsigned a0p;
    mu_a0hi : bv_unsigned a0p + Z.of_nat (length a0s) + 16 <= STKHI;
    mu_argc : 0 <= argc < 2^31;
    mu_fds : m_fds mo = FDS2;
    mu_fs : m_fs mo = fs0;
    mu_a0slen : Z.of_nat (length a0s) <= 131071                              (* [comment removed for export] *)
  }.

  Theorem main_usageA : ltac2:(CDefT.buildp (gd_tbl_A_main_open ()) "Pargc,$2.Pa0p,(0.&40.)Pa0s,(4.(0.&8.))Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$43.Ph,(44.$7.VR,VHIA,)P,(7<.R12.R11.R10.)P,(7=.R13.R12.R11.R4.R3.R2.)P,(32.(5.$2.R14.+2.))(52.$7.(53.(1;.(2;.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R15.)(1<.&5.(0.&40.))(8.&40.+970>0.)(8.&20.=)(1=.(0.&40.))R6.(1>.$7.))R5.)(54.(7;.R13.)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * USAGE ME Hne. destruct ME as [HH HKmo HT HS TM SSH ST AV A0S NZ LO HI ARGC FDS FS].
    pose proof (u64_range sp0) as SPR. pose proof (u64_range a0p) as A0R. pose proof (hcs_ok _ _ HIA h) as CSOK.
    assert (SCS : crange (hcs asegs R HIA h) (arl_stklo R) (esp - arl_stklo R)).
    { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [esp]; lia]. }
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HKmo | eapply (U1_steps (hcs asegs R HIA h)); [exact ARGC | exact Hne | exact ST | exact (tm_mi _ _ _ _ _ _ _ _ TM) | exact SCS] |].
    cbn beta. intros ms1 mo1 P1 HK1 MM1. destruct P1 as (pad & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HH1 : HM asegs R HIA h [] [] m1).
    { eapply (hm_munch _ _ HIA); [exact HH | exact MU1 | exact WM1 |].
      constructor; [| constructor]. cbn [fst snd]; intros a Ha. left. left. rewrite HT. cbv delta [esp] in Ha. lia. }
    apply (USAGE t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pad m1 mo1 h).
    - exact HH1.
    - exact HK1.
    - exact HT.
    - exact HS.
    - exact MI1.
    - eapply (tail_rebuild R HIA HRTC HM_LOWSH HM_ZIMG); [exact TM | | | | exact HH1 | exact MI1 |]; rewrite ?unsigned_lit by (cbv delta [msp]; lia).
      + intros a [Ha _]. apply MU1. rewrite wa_unsigned by (unfold drv_static in Ha; lia). cbn. unfold drv_static in Ha. cbv delta [esp]. lia.
      + intros a Ha W0. apply WM1. exact W0.
      + intros a Ha. unfold SSH_LO, SSH_HI in Ha. rewrite unsigned_lit in Ha by (cbv delta [msp]; lia). change (Z_to_bv 64 a) with (wa a). apply MU1. rewrite wa_unsigned by lia. cbn. cbv delta [esp msp] in *. rewrite STKLO. lia.
      + eapply (proj2 (stk_split asegs m1 (arl_stklo R) (msp - 4096) msp ST1 ltac:(rewrite STKLO; cbv delta [msp]; lia))).
    - exact ST1.
    - eapply (sshad_munch asegs AL (hcs asegs R HIA h)); [exact CSOK | | | exact MU1 | exact WM1 | exact SSH].
      + unfold w_client. constructor; [cbn [fst snd]; exact SCS | constructor].
      + rewrite <- HS. apply (hcs_stack _ _ HIA h).
    - exact FR1.
    - eapply rw_cells_transport; [exact AV | exact MU1 | exact WM1 | cbn [cells_size csize disjoint_from fst snd]; cbv delta [esp]; lia].
    - eapply bytes_at_transport; [exact A0S | exact MU1 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; rewrite STKLO; cbv delta [esp]; lia].
    - exact NZ.
    - exact LO.
    - exact HI.
    - rewrite (A_main_fin.mo_mat_fds _ _ MM1), FDS. reflexivity.
    - rewrite (mo_mat_fs _ _ MM1). exact FS.
    - assumption.
    - exact ARGC.
  Qed.
End Open.
