(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip A_amem_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA NodesA SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_code_58000_59000 A_code_59000_5a000 A_code_5a000_5b000 A_code_e8000_e9000 A_code_ec000_ecd48           .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02455682256ae42d 0 2 0 1 37 1P026eb2784de760b9 0 2 0 1 31 1P02a3bd40a3471674 0 2 0 1 31 1P03be159b732e024b 0 3 1 1 38 1 39 1P03d37ec139c7924e 0 2 0 1 48 1P046852b241985cf9 0 2 0 1 48 1P047252131abbe170 0 2 0 1 45 1P04f72a1753e387cb 0 2 0 1 45 1P05373611093b07c9 0 2 0 1 48 1P05c858f903a21af5 0 2 0 1 31 1P06c14580ce0fb11e 0 2 0 1 37 1P0720d8f2e64b2973 0 3 1 1 38 1 39 1P07de0d34ff33349e 0 3 0 1 34 1 52 1P07eca168459968ac 0 2 0 1 45 1P081238833c0549ff 0 2 0 1 45 1P086ffd8ee28bfe80 0 2 0 1 37 1P0882299e810ce478 0 2 0 1 46 1P0ae8dad86dcd7f09 0 4 1 1 21 1 32 1 33 1P0b4ee222a40ef2da 0 3 0 1 34 1 52 1P0b7f8a18e35654fb 0 2 0 1 45 1P0bb77d1ba583f122 0 2 0 1 37 1P0ea83a6155e13cc6 0 2 0 1 45 1P0f261959e6fcc514 0 3 1 1 38 1 39 1P0fa16df82f9f9e51 0 2 0 1 37 1P102cd32a3c5d78b6 0 3 1 1 38 1 39 1P10401ff6713e7a4b 0 4 1 1 21 1 32 1 33 1P111f9a5c6dea5a75 0 2 0 1 37 1P118c25be639da68c 0 2 0 1 31 1P119be5438daf8ed6 0 3 1 1 38 1 39 1P1237bb912a4aef5c 0 2 0 1 31 1P12c05015db4a1866 0 2 0 1 45 1P138f62ac773fe129 0 2 0 1 45 1P14241016c05a3980 0 2 0 1 48 1P16d371c7010905cb 0 3 1 1 38 1 39 1P16e858c70dec48df 0 3 1 1 38 1 39 1P16f0e38e868b22fa 0 4 0 1 20 1 31 1 32 1P198613da4598b62e 0 2 0 1 37 1P1c303f04210d2dc1 0 3 1 1 38 1 39 1P1c6f046bbf9295db 0 3 1 1 38 1 39 1P1c8416aaf158e31c 0 3 1 1 38 1 39 1P1d0233c559d3c1e7 0 2 0 1 31 1P1d2a4ead077279a1 0 2 0 1 48 1P1eedfb53254236b9 0 2 0 1 31 1P21e98ddd9f3fa699 0 2 0 1 37 1P229e10d8195bb118 0 2 0 1 50 1P23f3d0cae12e4e29 0 2 0 1 48 1P2479f113a2f987a1 0 2 0 1 31 1P2526210fd8bda207 0 2 0 1 46 1P25c62b0e4d94783d 0 2 0 1 37 1P26ffc92289017b5c 0 3 1 1 38 1 39 1P27088a7570da2fac 0 2 0 1 46 1P271606a1252ec8fb 0 2 0 1 45 1P2987e02f1d5d641d 0 3 1 1 38 1 39 1P29f4df460817a676 0 3 1 1 38 1 39 1P2ad067c310cb8734 0 4 0 1 21 1 32 1 33 1P2af4725054e947f2 0 4 0 1 20 1 31 1 32 1P2b7ce7d726eb2b25 0 3 1 1 38 1 39 1P2c1916f7d16b8f39 0 2 0 1 37 1P2cd751fbd1c3851b 0 2 0 1 37 1P2eccf70d5eae7645 0 2 0 1 37 1P2f760c784b90482c 0 3 0 1 34 1 52 1P3013b47a98d1c3b4 0 3 1 1 38 1 39 1P31a1ef44232f7d75 0 2 0 1 31 1P331b69506a069c4b 0 2 0 1 48 1P33db9f113bd2ae14 0 2 0 1 37 1P33fd53a9fb452588 0 2 0 1 48 1P37235b19d49c745e 0 2 0 1 31 1P38ec60065d5fa70a 0 2 0 1 31 1P3b6b828fc1553c31 0 2 0 1 45 1P3c94e7d5007cc17d 0 2 0 1 37 1P3dfc549d9b1696f4 0 2 0 1 37 1P3e24a0b0f1c241b6 0 3 1 1 38 1 39 1P3fcc8cd50e3deb75 0 2 0 1 37 1N00cabe9b67735a38N05d5a6c5820b61bdN082f9b28185828ccN0a38b628ff4eeb6dN0ef4ec7eb2ecd284N0f5a3a7ff6bf0703N12350b01feba5959N1993d78544f46accN1a17fd488480606cN1b2bdd13205e73b9N1f1421a7312664bfN1f5c019809fcc103N21c449654afdccdbN25d17ec8570b6a9eN29b8eb600af73774N2dc9127b7e26efbdN2f80d1b6d113c322N30200ee5abe6b6bcN30f6ee2016b3593eN34b4bfa49bc3c5aaN34c076d4eb9d9917N391b4c9cac54f12bN3b19ce9d5a4564b7"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_icpt_read () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.B.A_rip.rip_consts"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Walk.rdchk_post"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Walk.rd_consts"; "Walk.rd_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Walk.rd_post_post"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Walk.rd_post_dir_post"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.Fs.path"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFile"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "LinuxProcessSemantics.LinuxProcessSem.Fs.file_read"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_insert"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "LinuxProcessSemantics.LinuxProcessSem.State.FdDir"].


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L13098224072.3L16501782611.3L18930760090.4L18932449448.3L56106241848.5L59873604755.5L6389619373.3 L64656765696.3L65871719702.3L66711149640.600000500=00@00A00D00L00R00W00]00dS1n1lS1n2Hn1lS1nSS1nS1n2Hn1lS1n2HnS1n1lS1n2HnS1n1D1H". (* [comment removed for export] *)
Lemma ltu_m64 : forall n, 1 <= n < 2^40 ->
  bv_ltu (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (-64)) = (65 <=? n).
Proof.
  intros n Hn. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace ((-64) mod 18446744073709551616) with 18446744073709551552 by reflexivity.
  destruct (Z_lt_le_dec n 65).
  - replace ((n + -65) mod 18446744073709551616) with (18446744073709551616 + (n - 65)).
    2:{ pose proof (Z.div_mod (n + -65) 18446744073709551616 ltac:(lia)) as D.
        pose proof (Z.mod_pos_bound (n + -65) 18446744073709551616 ltac:(lia)) as B.
        assert ((n + -65) / 18446744073709551616 = -1) by (symmetry; apply Z.div_unique with (r := 18446744073709551616 + (n - 65)); lia). lia. }
    replace (65 <=? n) with false by (symmetry; apply Z.leb_gt; lia). apply Z.ltb_ge. lia.
  - replace ((n + -65) mod 18446744073709551616) with (n - 65) by (symmetry; apply Z.mod_small; lia).
    replace (65 <=? n) with true by (symmetry; apply Z.leb_le; lia). apply Z.ltb_lt. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac norm_getr :=
  repeat match goal with
  | |- context [getr (TNode ?a ?b ?c) ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let v := eval cbn [tget] in (match tget p (TNode a b c) with Some v => v | None => w0 end) in
      change (getr (TNode a b c) r) with v
  end.

Ltac solve_sub_fp :=
  unfold sub_fp; cbn [outside]; let Hx := fresh "Hx" in intros ? Hx; decompose [and] Hx;
  repeat split; first [assumption | exact I | lia].

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Record rd_consts (m : mem) : Prop := {
    rc_inited : ro_cells asegs m 0x10a6d8 [C1 (Z_to_bv 8 1)];          (* [comment removed for export] *)
    rc_rread : ro_cells asegs m 0x0f7ba0 [C8 (Z_to_bv 64 0x0f00c4)];   (* [comment removed for export] *)
    rc_rip : rip_consts m
  }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L13949620599.16L26640887415.1600000:00DS2lo2hi2LOS2lo2hi2LO". (* [comment removed for export] *)
  Lemma rd_consts_munch : forall lo hi m m',
    munch [(lo, hi)] m m' -> HSE < lo -> rd_consts m -> rd_consts m'.
  Proof.
    intros lo hi m m' MU LO [R1 R2 RC].
    split; [ .. | eapply rip_consts_munch; eauto];
      (eapply ro_cells_transport; [eassumption | exact MU | cbn; split; [lia | exact I]]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11492616138.24L13278662602.24L15094864961.24L21008732362.24L23091693514.24L30549922881.24L33189653569.24L34609988673.24L36239340609.24L41545865281.24L46418475210.24L50311015114.24L52767765569.24L5488702154.24 L57371509706.24L6202003521.24 00000:00D00L00V00`00h01001801@01H01R01\01d01n02802@S2lo2hi2LOS2lo2hi2LOS1b1e2APS2lo2hi2LOS2lo2hi2LOS1b1e2APS1b1e2APS1b1e2APS1b1e2APS1b1e2APS2lo2hi2LOS2lo2hi2LOS1b1e2APS2lo2hi2LOS2lo2hi2LOS1b1e2AP". (* [comment removed for export] *)
  Lemma rip_consts_munch2 : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pb,$0.Pe,$0.Plo,$0.Phi,$0.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))P,(3.(4.(5.$0.$0.)(6.$0.$0.R6.R5.)(4.(5.$0.$0.)(6.$0.$0.R4.R3.)(7.(5.$0.$0.))))R2.R1.)P,(8.(9.R6.+?5>50.)(9.+1;6?00.R7.))P,(:.+10007???7???.R6.)P,(;.R5.)(;.R5.)")
(* [comment removed for export] *).
  Proof.
    intros b e lo hi m m' MU AP LO [R1 R2 R3 R4 R5 R6 R7 R8].
    split; (eapply ro_cells_transport; [eassumption | exact MU | cbn; split; [lia | split; [lia | exact I]]]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L16405147374.59L29644601389.59L30095897756.55L35469551417.59L40708893148.50L48379326627.59L53520163529.59L53520247005.59L56775215785.59L56775393469.59Q17581378383.58Q35222541774.58Q39502766003.58Q4111067988.58 Q52324771135.5800000C00P00f01902m03703U04604T05505K05L05\06006JS1k1p1q2lo2Hk2Hp2NES1k1p1q2Hk2NES1k1p1q2lo2hi2Hk2Hp2HqS1k1p1q2lo2Hk2Hp2EQS2AL2CS1p1q2ra2sp2gp2tp2t02t12t22s02s12a02a32a42a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo2Hk2HpS1k1p1q2HkS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi3Hlo2EQS1k1p1q2lo2hi2Hk2Hp2HqFS1k1p1q2lo2Hk2HpS1k1p1q2lo2Hk2Hp3HloS1k1p1q2lo2hi2Hk2Hp2Hq3Hhi". (* [comment removed for export] *)
  Lemma rd_orloop : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pk,$<.Pp,$0.Pq,$0.Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(=.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Plo,$0.Phi,$0.P,(9.(>.R23.R24.)(?.R25.))P,(10.(9.R3.R25.)(:.R25.R24.))P,(9.R25.R3.)P,(:.R4.(11.+2.+3?.))P,(9.=R6.)P,Px,$0.P,(10.(9.R8.R1.)(:.R1.R7.))(12.(1.&8.)Lb,(1.&8.)(13.$14.R;.R3.(4.(1.&8.)R1.(7.(1.&8.)))))P,Px,$0.P,(10.(9.R9.R1.)(:.R1.R8.))(15.VAL,VCS,R2.)(16.$14.VAL,VCS,Lms',$17.(12.(1.&40.)La3',(1.&40.)(12.(1.&40.)La4',(1.&40.)(18.$17.R3.(19.(1:.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.(1;.&40.R2=.)(1;.&40.R2=.)R2.R1.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(1;.&40.+5:638.)R>.(1<.(1.&40.))R=.(1=.$14.)))))(19.(1:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(1;.&40.R2;.)(1;.&40.R2:.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(1;.&40.+5:628.)R;.(1<.(1.&40.))R:.(1=.$14.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until hi; intros Hk Hp Hq Hhi Hlo RD AOK; [lia|]. al_facts.
    flat constr:((RD p ltac:(lia))) 2%nat. intros b B. pose proof (bytes_at_read1 _ _ _ _ B) as RDB.
    zstep. zstep. zstep. zstep.
    destruct (Z.eq_dec (p + 1) q) as [EQ|NE].
    - if_falseU. rewrite EQ. finish.
    - if_trueU. eapply IH; try eassumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac qc_block11 X n E0 E1 :=
    do 11 zstep;
    rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
    replace (X + n + -1) with (X + n - 1) by lia;
    rewrite !Z.mod_small by lia;
    rewrite !land_m8 by lia; rewrite !hull_sh by lia;
    rewrite E0, E1.

  Definition rdchk_post (sp gp tp s0 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (res lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Lms',$17.(12.(1.&40.)Lra,(1.&40.)(12.(1.&40.)Lt0,(1.&40.)(12.(1.&40.)Lt1,(1.&40.)(12.(1.&40.)Lt2,(1.&40.)(12.(1.&40.)Ls1,(1.&40.)(12.(1.&40.)La1,(1.&40.)(12.(1.&40.)La2,(1.&40.)(12.(1.&40.)La3,(1.&40.)(12.(1.&40.)La4,(1.&40.)(12.(1.&40.)La5,(1.&40.)(12.(1.&40.)La6,(1.&40.)(12.(1.&40.)La7,(1.&40.)(12.(1.&40.)Ls2,(1.&40.)(12.(1.&40.)Ls4,(1.&40.)(12.(1.&40.)Lt3,(1.&40.)(12.(1.&40.)Lt4,(1.&40.)(12.(1.&40.)Lt5,(1.&40.)(12.(1.&40.)Lt6,(1.&40.)(12.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(10.(18.$17.R14.(19.(1:.R13.O11.O10.O?.R12.R11.R10.O>.R?.(1;.&40.O3.)R>.R=.R<.R;.R:.R9.R8.R7.O=.R6.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(1;.&40.+5:4<4.)O4.(1<.(1.&40.))R1.(1=.$14.)))(10.(3.(4.(5.$0.$0.)(6.$0.$0.O2.(1>.&40.O11.))(7.(5.$0.$0.)))O1.R1.)(10.(1?.$14.O1.R1.)(10.(20.$14.R1.)(21.$14.R1.O2.(1>.&40.O11.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0250@C17025492443.111C17025492443.89 L11447729190.142L11475462041.70 L11944109973.86 L19628431903.88 L20966712717.90 L22018156435.90 L22183557714.70 L24122754266.90 L24122936649.90 L24124928684.84 L24124928684.85 L24982526223.88 L25039430029.69 L25696419826.85 L28083348026.86 L29784464483.89 L29786564236.85 L31686803170.90 L3248729870.2   L3421674955.90  L34922678286.2  L35144635169.0  L361130047.70   L363083587.92   L36325757693.85 L36929494798.2  L37128840075.57 L38150352304.90 L39594679749.85 L4113407135.69  L43068582970.85 L43080782292.70 L45368951967.69 L45607281678.2  L46392774347.68 L46392774347.69 L46393143296.84 L47543971773.90 L49899794702.2  L51172192526.2  L52065394884.84 L52514161039.88 L53519158063.88 L54369930157.70 L59632798299.69 L61097676998.2  L63649963320.90 L63931368594.90 L66311185895.70 L66488557582.2  L7106453518.2   O14206727921.111O14206727921.89 O15547502833.111O15547502833.89 O17025492443.111O17025492443.89 O23485702385.111O23485702385.89 O32131581681.111O32131581681.89 O38504098033.111O38504098033.89 O4492316913.111 O4492316913.89  O48978854641.111O48978854641.89 O65485481713.111O65485481713.89 P3245129067.111 P3245129067.89  P34917767787.111P34917767787.89 P36941614443.111P36941614443.89 P45611546219.111P45611546219.89 P49904706411.111P49904706411.89 P51184575339.111P51184575339.89 P66501341803.111P66501341803.89 P7102853739.111 P7102853739.89  Q19275945964.85 Q19423716882.86 Q20567854270.85 Q21797814763.85 Q23650890746.89 Q24745328269.89 Q2497790322.85  Q26322276993.89 Q28218390483.89 Q29427030349.85 Q31394395900.85 Q31429356051.85 Q34268098539.85 Q34947676851.85 Q36722057835.85 Q36942329756.85 Q3742509637.85  Q38148316102.85 Q38578926834.85 Q39388716773.89 Q39425452606.85 Q39778974580.85 Q39942779359.85 Q41324687698.89 Q43608312681.86 Q43855177782.85 Q44556843737.89 Q45748806138.89 Q46309744770.89 Q46311840365.85 Q49087365069.86 Q49545476915.85 Q51241282684.85 Q52818999351.85 Q52821082840.89 Q53519998161.85 Q56964988266.85 Q59322611797.85 Q59365683033.85 Q62824840384.85 Q63037122486.85 Q6460837458.85  Q65033170488.85 Q66715486460.85 Q67805910652.85 Q840527223.85   00000100200300>00?00M00]00i01201C01T01U01f01o02;02D02E02N02W02i02j03?03@03A03H03S03a03b03n04G04X04_04k05705E05F05T05b06006B06C06D06R06[06d07007707807M07Y07f07g07h07i07j07k07l08708B08C08D08E08F08G08H08I08J08K08L08M08N08a08l09?09J09]09h0:;0:F0:Y0:d0;70;B0;U0;`0<30<>0<N0<Y0<Z0<[0<\0=30=40=50=B0=C0=L0=M0=h0=i0=j0=k0=l0>E0>F0>G0>H0>T0?40?50?>0?O0?g0@40@F0@a0@j0@k0A40A50A60AH0AI0Ab0B:0B[0Bl0Bm0Bn0CB0CV0CWFFFS3res5SMALLFS3BUF3res1N2B0S3BUF3res2q13Q45S3BUF3res2GES3res3BIGS3BUF3res3H8a3H8bS3BUF3res3H8a3H8bFS3BUF3res3H8b3H8aS3BUF3resS3BUF3res2B0S3BUF3resFS3BUF3resS3BUF3resS3BUF3res2q02q12DBFS3BUF3res2q02q12DB2LTFSS3res1NS3BUF3res1NS3BUF3res1N2B0FS3BUF3res2ARS3BUF3res2B02q02q12E03Q01S3BUF3res3H8b3H8aS3res1NS3BUF3res2B0S3BUF3res2B0S3BUF3res1N2B0FS3BUF3res1N2B0S3BUF3res1N2B0S3BUF3res1N2B0S3BUF3res2B05SMALLFFS3BUF3res1N2B0S3BUF3resS3BUF3resS3BUF3res2B0S3res1NFS3BUF3res2q02q12DB2GES3BUF3res2LTS3res1N5SMALLFFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp3BUF3res2lo3LO0S2sp2lo3LO0S2sp3BUF3res2lo3LO0S2sp2lo3LO0S2sp3BUF3res2lo3LO0S2sp2lo3LO0S2sp3BUF3res2lo3LO0S2sp2lo3LO0S2sp3BUF3res2lo3LO0S2sp2lo3LO0S2sp3BUF3res2lo3LO0S2sp2lo3LO0S2sp3BUF3res2lo3LO0S2sp2lo3LO0S2sp3BUF3res2lo3LO0S2sp2lo3LO0S3BUF3res2q13Q45S3BUF3res1NFFFS3BUF3res1N2B02q02q12DBFFS3BUF3res3H8bFS3BUF3resFS3BUF3res1N2B02q02q13Q012DBFFFFS3BUF3res2B02q02q12E03Q01FFFS3BUF3res2q0S2AL3BUF3res4IMG'2B02q02q12E12DBFS3BUF3resS2AL3BUF3res4IMG'S2AL3BUF3res4IMG'2B03H8bS3BUF3res3H8bS3BUF3res2q02q12DBS3BUF3res1N2B02q02q13Q012DBS3BUF3resFS3BUF3resFFS2AL3BUF3res5ALWF'FS3BUF3res2B02q02q13Q452DBS3BUF3res2B02q02q12E12DBS2AL3BUF3res4IMG'2B02q02q12E03Q01S2AL3BUF3res4IMG'FFS2AL3BUF3res4IMG'2B0S2AL3BUF3res4IMG'2B0F". (* [comment removed for export] *)
  Lemma rd_chk : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(=.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))PBUF,$0.Pres,$0.Plo,$0.P,(22.$14.VAL,VCS,R4.R3.R2.)P,(10.(9.+1.R3.)(:.R3.(11.+2.+28.)))P,(23.R5.(24.(24.R5.R4.)+7.))P,(25.VCS,(>.R6.(26.R6.+40.))+40.)P,(25.VCS,(>.(>.(24.R7.R6.)+1.)(26.(>.(24.R7.R6.)+1.)+40.))+40.)P,Pc,$0.P,A1.VCS,R1.(12.(1.&8.)Lb,(1.&8.)(13.$14.R<.(27.VAL,R3.)(4.(1.&8.)R1.(7.(1.&8.)))))P,(;.R:.)P,(21.$14.R;.R8.(1>.&40.R2;.))P,(:.+10007???7???.R9.)P,(9.R:.(>.(1>.&40.R2=.)+50.))P,(25.VCS,R;.(>.(1>.&40.R2>.)R;.))P,(20.$14.R?.)P,(18.(1.&40.)R29.(1;.&40.R?.))P,(18.(1.&40.)R29.(1;.&40.R?.))(16.$14.VAL,VCS,(28.R32.R31.R30.R2<.R21.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.R10.R?.R12.)(19.(1:.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(1;.&40.+5:46<.)R13.(1<.(1.&40.))R12.(1=.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros OBJ N AR HULL0 HULL1 SHRD RC ST LO0 SPL SCS MI -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < BUF /\ BUF + res + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    (* [comment removed for export] *)
    Ltac ripR BUF res lo :=
      (* [comment removed for export] *)
      zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx BUF res |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := BUF) (n := res) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      (* [comment removed for export] *)
      zstep; zstep; zstep;
      unfold rdchk_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite zb_lxor_ones by lia. if_falseU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite ltu_m64 by lia.
    destruct (Z_lt_le_dec res 65) as [SMALL | BIG].
    2:{ replace (65 <=? res) with true by (symmetry; apply Z.leb_le; lia). cbv iota. ripR BUF res lo. }
    replace (65 <=? res) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
    destruct (qc_facts AL IMG ALWF CS CSOK ASB m BUF res OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    (* [comment removed for export] *)
    qc_block11 BUF res E0 E1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold rdchk_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (BUF + res - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((BUF + res - 1) / 8) 2147450880) in RDk.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (BUF / 8) ((BUF + res - 1) / 8)) as [LT|GE].
      - if_falseU. eapply rd_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (BUF / 8) with ((BUF + res - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. intros ms' (a3' & a4' & ->).
    (* [comment removed for export] *)
    zstep. zstep.
    if_cases Ks.
    2:{ zstep. ripR BUF res lo. }
    unfold rdchk_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rd_pre_post (sp gp tp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (ra s0 s1 s2 s3 s4 : word) (fd BUF n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Lms',$17.(12.(1.&40.)Lx0,(1.&40.)(12.(29.(1.&8.))Lj8,(29.(1.&8.))(12.(29.(1.&8.))Lj2080,(29.(1.&8.))(12.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(10.(18.$17.R5.(19.(1:.(1;.&40.+?00><.)(1;.&40.(24.(1>.&40.O1>.)-860.))O1=.O1<.O1;.O1:.O19.R4.(1;.&40.O4.)(1;.&40.O5.)(1;.&40.O4.)(1;.&40.O3.)(1;.&40.=)(1;.&40.=)(1;.&40.=)(1;.&40.=)(1;.&40.+3?.)(1;.&40.O3.)(1;.&40.O5.)(1;.&40.+1.)O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.)O=.(1;.&40.+>;5:8.)O<.(1<.(1.&40.))R1.(1=.$14.)))(10.(3.(4.(5.$0.$0.)(6.$0.$0.O2.(1>.&40.O1>.))(7.(5.$0.$0.)))O1.R1.)(10.(1?.$14.O1.R1.)(10.(20.$14.R1.)(10.(21.$14.R1.O2.(24.(1>.&40.O1>.)-860.))(10.(2:.$14.R1.(24.(1>.&40.O1>.)-30.)(4.$2;.(2<.O6.)(4.$2;.(2<.O7.)(4.$2;.(2<.O8.)(4.$2;.(2<.O9.)(4.$2;.(2<.O:.)(4.$2;.(2<.O;.)(7.$2;.))))))))(10.(2:.$14.R1.(24.(1>.&40.O1>.)-850.)(4.$2;.(2=.#820.R2.)(7.$2;.)))(2:.$14.R1.(24.(1>.&40.O1>.)-860.)(4.$2;.(2=.#8.R3.)(4.$2;.(2<.(1;.&40.+5:464.))(7.$2;.)))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L15555153991.63L16008486173.1 L31378308326.61L37827660420.61L42978102852.65L43055334409.59L4583770596.74 L51837457415.1 L60616668326.63L64834299037.1 00000400800<00G00K00V00Z00^00i00mS2spS2spS2spS2sp2lo3SPLS2spS2sp2lo3SPLS2spS2spS2sp2lo3SPLS2sp". (* [comment removed for export] *)
  Lemma rd_pre : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(=.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Pfd,$0.PBUF,$0.Pn,$0.Plo,$0.P,(2>.R5.)P,(21.$14.R6.R2.(1>.&40.R26.))P,(:.+10007???7???.R3.)P,(9.R4.(>.(1>.&40.R28.)+860.))P,(25.VCS,R5.(>.(1>.&40.R29.)R5.))P,(20.$14.R:.)P,(10.(9.=R:.)(:.R:.(11.+2.+1?.)))P,(10.(9.=R:.)(:.R:.(11.+2.+40.)))P,(10.(9.=R:.)(:.R:.(11.+2.+40.)))P,(18.(1.&40.)R26.(1;.&40.R=.))P,(18.(1.&40.)R26.(1;.&40.R=.))P,(18.(1.&40.)R26.(1;.&40.R=.))(16.$14.VAL,VCS,(2?.R31.R30.R2?.R2>.R2=.R2<.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R32.R2;.R2:.R21.R20.R1?.R10.R?.R>.R=.R11.)(19.(1:.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(1;.&40.+5:414.)R12.(1<.(1.&40.))R11.(1=.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros until lo. intros RC ST LO0 SPL SCS MI FD B0 N0 -> -> ->. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    destruct RC as [RC1 RC2 RC].
    assert (GSB0 : al_gsb AL = 0x1099f8) by ((flat constr:(IMG') 4%nat; flclear IMG'; intros _ _ _ G); exact G). clear GSB.   (* [comment removed for export] *)
    change (lx_hidden (al_sb AL = SB)) in ASB.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. carve_frame 2080%nat ST. carve_frame 16%nat ST.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x0eb5a8] [] 120%N). lx_tree.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ ?mx (bv_unsigned sp + -2144) (C8 ?w :: _) |- _ =>
      chunk_split H 1%nat FRw Hr1; chunk_split Hr1 1%nat FRq Hr2; chunk_split Hr2 1%nat FRM FRS;
      lazymatch type of FRq with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2136) in FRq by (clear; lia) end;
      lazymatch type of FRM with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2128) in FRM by (clear; lia) end;
      lazymatch type of FRS with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -48) in FRS by (clear; lia) end;
      apply (fun X => CellsX.rw_cells_reshape asegs mx (bv_unsigned sp + -2144) [C8 w] [CB 8 (cbytes (C8 w))] X
               (conj (Cells.cbytes_length (C8 w) I) I) eq_refl) in FRw;
      chunk_join FRw FRq FRR
    end.
    unfold rd_pre_post; finish; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rd_post_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (res lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Lms',$17.(12.(1.&40.)Lt0',(1.&40.)(12.(1.&40.)Lt1',(1.&40.)(12.(1.&40.)Lt2',(1.&40.)(12.(1.&40.)La1,(1.&40.)(12.(1.&40.)La2,(1.&40.)(12.(1.&40.)La3,(1.&40.)(12.(1.&40.)La4,(1.&40.)(12.(1.&40.)La5,(1.&40.)(12.(1.&40.)La6,(1.&40.)(12.(1.&40.)La7,(1.&40.)(12.(1.&40.)Lt3',(1.&40.)(12.(1.&40.)Lt4',(1.&40.)(12.(1.&40.)Lt5',(1.&40.)(12.(1.&40.)Lt6',(1.&40.)(12.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(10.(18.$17.R10.(19.(1:.O1<.O1;.O1:.O19.R?.R>.R=.O15.O14.(1;.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R5.R4.R3.R2.)O5.(30.O1<.)O4.(1<.(1.&40.))R1.(1=.$14.)))(10.(3.(4.(5.$0.$0.)(6.$0.$0.O2.(1>.&40.O1;.))(7.(5.$0.$0.)))O1.R1.)(10.(1?.$14.O1.R1.)(10.(20.$14.R1.)(21.$14.R1.O2.(1>.&40.O1;.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@C17025492443.126L11461159062.2  L12210755389.2  L16643574376.81 L16643587019.4  L16848505495.102L20114510486.2  L20534550589.2  L21714201917.2  L25139758844.103L28555812619.87 L30835578941.2  L31587298130.87 L35497563788.82 L35499695790.83 L35675001669.2  L37963462512.86 L38237936380.103L42810671421.2  L43492454205.2  L43882031648.103L46748130687.103L48323028949.103L49923921406.103L57610234043.86 L58880020570.101L59632798218.103L59638011965.2  L61753448509.2  N22854454483.127N53015413047.127O14206727921.126O15547502833.126O17025492443.126O23485702385.126O32131581681.126O38504098033.126O4492316913.126 O48978854641.126O65485481713.126P12199019864.126P20522431064.126P21718859608.126P30823844440.126P42806547288.126P43496324440.126P59634403928.126P61740534360.126Q38248387216.126Q43879899724.126Q49923921406.10300000100800900A00O00b00i00j00k00l01>01?01M01N01S01T01b01n01o02002?02T02g03B03T03`04404504604K04`04a04b04m04n04o05005105205305F05Y05l06?06R06e07807K07W07f08AFS2sp2loFS3res2R1S1n3res3RES2RPS2sp3BUF3res2lo3SPLS2sp2loFFFS3BUF1n3res3RES2R1FS3BUF3res1y2HySS3BUFFS3BUF3res1y2HyS3BUF3res2loFFS2sp3BUF3res2loS3BUF1n3res3RES2AR2RPS2sp3BUF3res2lo3SPLS2sp3BUF3res2lo3LO03SPL3SPHS3BUF1n3res3RES2R1S2sp3BUF3resS3BUF1n3res3RES1N2R1FFS2sp3BUF3res2lo3x191CS2sp3BUF3res2lo3x191CFFS2sp2lo3SPLFFFFFFS2sp3BUF3res2lo3LO0S2sp3BUF3res2lo3LO0S2sp3BUF3res2lo3LO0S2sp3BUF3res2lo3LO0S2sp3BUF3res2lo3LO0S2sp3BUF3res2lo3LO0S2sp3BUF3res2lo3LO0S2sp3BUF3res2lo3LO0S3BUF3res2loS2sp3BUF3res2loS2sp3BUF3res2lo3LO03SPL3SPH". (* [comment removed for export] *)
  Lemma rd_post : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Px0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pxs2,(1.&40.)Pxs3,(1.&40.)PF,(=.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))PBUF,$0.Pn,$0.Pres,$0.Plo,$0.Pj8,(29.(1.&8.))Pj2080,(29.(1.&8.))P,P,(9.+1.R4.)(22.$14.VAL,VCS,R8.R7.R5.)P,(10.(9.=R5.)(9.R5.R6.))P,(:.R7.(11.+2.+28.))P,(23.R9.(24.(24.R9.R8.)+7.))P,Px,$0.Py,$0.P,(10.(9.R<.R2.)(:.R2.(24.R<.R;.)))P,(10.(9.(>.R3.(26.R3.+40.))R2.)(:.R2.(24.(>.R3.(26.R3.+40.))+40.)))A1.VCS,R3.P,Pc,$0.P,A1.VCS,R1.(12.(1.&8.)Lb,(1.&8.)(13.$14.R?.(27.VAL,R3.)(4.(1.&8.)R1.(7.(1.&8.)))))P,(;.R=.)P,(21.$14.R>.R:.(24.(1>.&40.R30.)-860.))P,(:.+10007???7???.R;.)P,(9.R<.(>.(1>.&40.R32.)+8:0.))P,(:.(1>.&40.R33.)(11.+2.+40.))P,(25.VCS,R>.(>.(1>.&40.R34.)R>.))P,(20.$14.R13.)P,(2:.$14.R14.(24.(1>.&40.R36.)-30.)(4.$2;.(2<.R2<.)(4.$2;.(2<.R2=.)(4.$2;.(2<.R2>.)(4.$2;.(2<.R2?.)(4.$2;.(2<.R30.)(4.$2;.(2<.R37.)(7.$2;.))))))))P,(2:.$14.R15.(24.(1>.&40.R37.)-850.)(4.$2;.(2=.#820.R?.)(7.$2;.)))P,(2:.$14.R16.(24.(1>.&40.R38.)-860.)(4.$2;.(2=.#8.R11.)(4.$2;.(2<.(1;.&40.+5:464.))(7.$2;.))))(16.$14.VAL,VCS,(31.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R19.R18.R14.R13.R17.)(19.(1:.(1;.&40.+?00><.)(1;.&40.(24.(1>.&40.R39.)-860.))R38.R37.R36.R35.R34.R23.(1;.&40.R16.)(1;.&40.R14.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(1;.&40.+1.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R19.(1;.&40.+>;5:<.)R18.(1<.(1.&40.))R17.(1=.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros until j2080. intros OBJ RES N AR HULL SHRD RC ST LO0 SPL SPH SCS MI FRS FRM FRR. al_facts. unfold app_range in AR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    assert (GSB0 : al_gsb AL = 0x1099f8) by ((flat constr:(IMG') 4%nat; flclear IMG'; intros _ _ _ G); exact G). clear GSB.   (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    destruct (Z.eq_dec res 0) as [R0 | RP].
    { (* [comment removed for export] *)
      subst res. lx_run_tac (PLAN ([] : list Z) [] 60%N). lx_tree.
      unfold rd_post_post; finish. }
    (* [comment removed for export] *)
    assert (R1 : 1 <= res) by (clear - RES RP; lia).
    specialize (OBJ ltac:(lia)).
    pose proof (aobj_crange _ _ _ _ _ _ OBJ) as CR.
    pose proof (Z.mod_pos_bound BUF 64 ltac:(lia)) as MB0. pose proof (Z.mod_pos_bound (BUF + res - 1) 64 ltac:(lia)) as MB1.
    assert (HULL0 : crange CS (BUF - BUF mod 64) 64) by (intros y Hy; apply (HULL BUF); lia).
    assert (HULL1 : crange CS (BUF + res - 1 - (BUF + res - 1) mod 64) 64) by (intros y Hy; apply (HULL (BUF + res - 1)); lia).
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x5a46c] [] 60%N). lx_tree.
    lazymatch goal with H1 : rw_cells _ ?mx (bv_unsigned sp + -2144) _, H : stk _ ?mx lo _ |- _ (MS _ _ _ _ _ ?mx _) => release_frame H1 H (bv_unsigned sp + -2128)%Z end.
    lazymatch goal with OBJx : aobj _ _ _ ?mx BUF _, MUx : munch _ m ?mx |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (shrd_munch AL CS CSOK [(lo, bv_unsigned sp)] m mx ltac:(unfold w_client; apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil]) MUx SHRD) as SH;
      pose proof (rip_consts_munch _ _ m mx MUx LO0 RC') as RCx;
      callxA_sp (bv_unsigned sp + -2128)
        (eapply rd_chk with (BUF := BUF) (res := res) (lo := lo);
         rewrite ?(unsigned_lit (bv_unsigned sp + -2128)) by lia;
         first [ exact OBJx | exact HULL0 | exact HULL1 | exact SH | exact RCx | split; assumption | eassumption
               | reflexivity | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
    end.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "RDCHK-LEFT:" g end.
    (* [comment removed for export] *)
    lx_run_tac (PLAN ([] : list Z) [] 40%N). lx_tree.
    unfold rd_post_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rd_post_dir_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (ERR lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Lms',$17.(12.(1.&40.)La1,(1.&40.)(12.(1.&40.)La2,(1.&40.)(12.(1.&40.)La3,(1.&40.)(12.(1.&40.)La4,(1.&40.)(12.(1.&40.)La5,(1.&40.)(12.(1.&40.)La6,(1.&40.)(12.(1.&40.)La7,(1.&40.)(12.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(10.(18.$17.R9.(19.(1:.O1<.O1;.O1:.O19.O18.O17.O16.O15.O14.(1;.&40.-1.)R8.R7.R6.R5.R4.R3.R2.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)O5.(30.O1<.)O4.(1<.(1.&40.))R1.(1=.$14.)))(10.(3.(4.(5.$0.$0.)(6.$0.$0.O3.(24.O3.+4.))(4.(5.$0.$0.)(6.$0.$0.O2.(1>.&40.O1;.))(7.(5.$0.$0.))))O1.R1.)(10.(1?.$14.O1.R1.)(10.(20.$14.R1.)(10.(21.$14.R1.O2.(1>.&40.O1;.))(2:.$14.R1.O3.(4.$2;.(32.(1;.&40.+15.))(7.$2;.))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L35865851541.1000004S2TP". (* [comment removed for export] *)
  Lemma rd_post_dir : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Px0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pxs2,(1.&40.)Pxs3,(1.&40.)PF,(=.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))PBUF,$0.PTP,$0.Plo,$0.Pj8,(29.(1.&8.))Pj2080,(29.(1.&8.))Pje,(29.(1.&8.))P,(18.(1.&40.)R27.(1;.&40.R5.))P,(10.(9.(24.+10000.+:4.)R6.)(:.R6.+65?000.))P,(25.VCS,(24.R7.-:4.)+4.)P,(2:.$14.R:.(24.R8.-:4.)(4.$2;.(2=.#4.R4.)(7.$2;.)))P,(21.$14.R;.R8.(24.(1>.&40.R2=.)-860.))P,(:.+10007???7???.R9.)P,(9.R:.(>.(1>.&40.R2?.)+870.))P,(:.(1>.&40.R30.)(11.+2.+40.))P,(25.VCS,R<.(>.(1>.&40.R31.)R<.))P,(20.$14.R10.)P,(2:.$14.R11.(24.(1>.&40.R33.)-30.)(4.$2;.(2<.R29.)(4.$2;.(2<.R2:.)(4.$2;.(2<.R2;.)(4.$2;.(2<.R2<.)(4.$2;.(2<.R2=.)(4.$2;.(2<.R34.)(7.$2;.))))))))P,(2:.$14.R12.(24.(1>.&40.R34.)-850.)(4.$2;.(2=.#820.R=.)(7.$2;.)))P,(2:.$14.R13.(24.(1>.&40.R35.)-860.)(4.$2;.(2=.#8.R?.)(4.$2;.(2<.(1;.&40.+5:464.))(7.$2;.))))(16.$14.VAL,VCS,(33.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R16.R15.(24.R12.-:4.)R11.R14.)(19.(1:.(1;.&40.+?00><.)(1;.&40.(24.(1>.&40.R36.)-860.))R35.R34.R33.R32.R31.R20.(1;.&40.R13.)(1;.&40.(>.(11.+2.+40.)+15.))R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(1;.&40.+1.)R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R16.(1;.&40.+>;5:<.)R15.(1<.(1.&40.))R14.(1=.$14.)))")
(* [comment removed for export] *).
  Proof.
    intros until je. intros -> TPB ECS ERR ST LO0 SPL SPH SCS MI FRS FRM FRR. al_facts.
    pose proof (munch_refl [(TP + -164, TP + -164 + 4); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (GSB0 : al_gsb AL = 0x1099f8) by ((flat constr:(IMG') 4%nat; flclear IMG'; intros _ _ _ G); exact G). clear GSB.   (* [comment removed for export] *)
    change (lx_hidden (al_sb AL = SB)) in ASB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    (* [comment removed for export] *)
    lx_run_tac (PLAN ([] : list Z) [] 60%N). lx_tree.
    unfold rd_post_dir_post; finish.
    all: try (replace (TP + -164 + 4) with (TP + -160) by (clear; lia); assumption).   (* [comment removed for export] *)
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Glue.
    Variable K : Model -> Prop.
    Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
    Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pmo,$34.Pacc,(29.(5.(1.&40.)$<.))P,A1.VK,R2.P,(35.VAL,VCS,R2.)(12.$34.Lmo',$34.(10.(18.(2.$34.)(36.R5.R4.)(37.$34.R1.))(10.A1.VK,R1.(38.R5.R1.))))")
(* [comment removed for export] *).
    Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pmo,$34.Pmo',$34.P,A1.VK,R2.P,(18.$39.(3:.R2.)(3:.R3.))P,(18.(29.(5.(1.&40.)(1.&40.)))(3;.R3.)(3;.R4.))P,(18.(29.(1.&40.))(3<.R4.)(3<.R5.))P,(18.(2.(1.&40.))(3=.R5.)(3=.R6.))A1.VK,R6.")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@L12656318656.108L15032542337.89 L15047440768.98 L18473459024.73 L19736505596.96 L20741164017.108L26277551253.110L26277566005.73 L29734350002.131L29975776223.89 L30679028321.110L32920543317.110L32920562421.73 L36166444316.101L38162903322.91 L38237936310.110L38813752902.105L39045802992.110L40157607889.89 L40205141472.89 L40644575510.132L43068201578.101L43068480234.100L43068626410.99 L43070741697.96 L43083225066.103L43083225834.102L43782018652.110L43882031722.110L44802311068.102L46392788080.73 L46403622609.89 L46510101851.98 L46520076378.89 L48358701980.103L492208538.103  L492211354.102  L496241329.96   L498322458.101  L498353050.99   L498568346.100  L5007911407.110 L50535246048.89 L50545915361.98 L54441148554.89 L61929918126.94 L61931765936.73 L62192421824.73 L67098856960.89 L6716358663.89  L942286889.73   00000A00B00O00Z00m01@01T01\02:02?02N02O02P03603B03R03c04:04A04F04U04j05?05T05i06>06S06g07:07`08108B08S08X09>09U09l0:C0:Z0;10;H0;W0;\0;k0<20<C0<H0<O0<Z0<_0<`S3BUF1n2bs2BL3resSS1n2bs2BL3resS2sp2lo3SPLS3BUF1n1N2bs2BL3resS3BUF1n1N2bs2BL3resS1n2lo3LO02bs2BL3resS2lo3LO0S2sp3BUF1n2lo1N3LO04DISJ2bs2BLS1n1NS1n1N2bs2BL3resFFS2sp3BUF1n2lo1N3LO03SPL4DISJ2bs2BL3resS3BUF1n1z2HzS1n2lo2bs2BL3resS3BUF1n2bs2BL3resS2sp1n2lo3SPL2bs2BL3resS2fd2FDS1n1NS1n1N2bs2BL3resS3BUF1n2bs3AR'2BL3resS3BUF1n2bs3AR'2BL3resS3BUF1n2bs3AR'2BL3resS3BUF1n2bs3AR'2BL3resS3BUF1n2bs3AR'2BL3resS3BUF1n2bs3AR'2BL3resS2sp1n2bs3SPR2BL3resS2sp1n2lo2bs2BL3resS2sp3BUF1n2lo1N3LO03SPL4DISJ2bs2BL3resS3BUF1n1N3RTA3AR'S3BUF1n1N3RTA3AR'S3BUF1n2bs2BL3resS3BUFS2sp3BUF1n2lo1N3LO03SPL4DISJ2bs2BL3resS3BUF1n1N2bs3AR'2BL3resS3BUF1n1N2bs3AR'2BL3resS3BUF1n1N2bs3AR'2BL3resS3BUF1n1N2bs3AR'2BL3resS3BUF1n1N2bs3AR'2BL3resS3BUF1n1N2bs3AR'2BL3resS1n1N2bs2BL3resS1n1NS1n1N2bs2BL3resS2fd2FDS1n3off4data1N2BLS1n1NS2fd2FDS3BUF1n3AR'S1n1NF". (* [comment removed for export] *)
    Theorem read_icpt_fileA : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pm,P,(1.&40.)(2.(1.&8.))Pmo,$34.Pfd,$0.PBUF,$0.Pn,$0.Plo,$0.Pp,$3>.Poff,(1.&40.)Pdata,(29.(1.&8.))PT,$3?.P,A1.VK,R9.P,(18.(2.$40.)(41.(42.R:.)(1;.&40.R9.))(37.$40.(43.R5.R4.)))P,(18.(2.(29.(1.&8.)))(44.(45.R;.)R6.)(37.(29.(1.&8.))R4.))P,(2>.R=.)P,(46.$14.R>.R;.R:.)P,(22.$14.VAL,VCS,R?.R<.R;.)P,(10.(9.+1.R<.)(:.R<.(11.+2.+18.)))P,(23.R>.(24.(24.R>.R=.)+7.))P,Px,$0.Py,$0.P,(10.(9.R11.R2.)(:.R2.(24.R11.R10.)))P,(10.(9.(>.R3.(26.R3.+40.))R2.)(:.R2.(24.(>.R3.(26.R3.+40.))+40.)))A1.VCS,R3.P,Pc,$0.P,A1.VCS,R1.(12.(1.&8.)Lb,(1.&8.)(13.$14.R16.(27.VAL,R3.)(4.(1.&8.)R1.(7.(1.&8.)))))P,(21.$14.R14.R?.(1>.&40.R32.))P,(:.+10007???7???.R10.)P,(9.R11.(>.(1>.&40.R34.)+8:0.))P,(25.VCS,R12.(>.(1>.&40.R35.)R12.))P,(8.(9.(24.R15.R14.)R13.)(9.(1>.&40.R36.)R15.))P,(20.$14.R19.)P,(10.(9.=R18.)(:.R18.(11.+2.+1?.)))P,(8.(9.(24.R18.R17.)+?5>50.)(9.+1;6?00.R18.))P,(18.(1.&40.)R32.(1;.&40.R1:.))P,(18.(1.&40.)R32.(1;.&40.R1:.))P,(18.(1.&40.)R32.(1;.&40.R1:.))Zbs,(29.(1.&8.))(47.R17.R18.(1;.&40.R1;.))P,Pt0',(1.&40.)Pt1',(1.&40.)Pt2',(1.&40.)Pa1',(1.&40.)Pa2',(1.&40.)Pa3',(1.&40.)Pa4',(1.&40.)Pa5',(1.&40.)Pa6',(1.&40.)Pa7',(1.&40.)Pt3',(1.&40.)Pt4',(1.&40.)Pt5',(1.&40.)Pt6',(1.&40.)Pm',P,(1.&40.)(2.(1.&8.))Pmo',$34.P,(3.(4.(5.$0.$0.)(6.$0.$0.R2=.(24.R2=.R2<.))(4.(5.$0.$0.)(6.$0.$0.R2;.(1>.&40.R4>.))(7.(5.$0.$0.))))R30.R2.)P,(1?.$14.R31.R3.)P,(20.$14.R4.)P,(21.$14.R5.R2>.(1>.&40.R51.))P,(13.$14.R6.R31.R15.)P,(9.(?.(48.(1.&8.)R16.))R31.)P,A1.VK,R7.P,(18.(29.(5.(1.&40.)$40.))(42.R8.)(49.(42.R36.)(1;.&40.R35.)(43.R31.(4:.&40.R30.(4;.(1.&8.)R18.)))))P,(18.$4<.(45.R9.)(45.R37.))(4=.$14.(4>.(19.(1:.R58.R57.R56.R55.R19.R18.R17.R51.R50.(4;.(1.&8.)R1:.)R16.R15.R14.R13.R12.R11.R10.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R?.R>.R=.R<.)(4?.&5.(1.&40.))(30.R58.)(1;.&20.=)(1<.(1.&40.))R;.(1=.$14.))R:.)R30.)(4=.$14.(4>.(19.(1:.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)(4?.&5.(1.&40.))(1;.&40.+5:414.)(1;.&20.=)(1<.(1.&40.))R21.(1=.$14.))R20.)R18.)")
(* [comment removed for export] *).
    Proof.
      intros until T. intros HK Hfd Hfs RC WR OBJ N AR HULL SHRD ST LO0 SPL SCS DISJ MI FD RTA -> -> ->. cbv zeta. intros HC.
      al_facts. pose proof AR as AR'. unfold app_range in AR'.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HK | | ].
      { eapply rd_pre with (fd := fd) (BUF := BUF) (n := n) (lo := lo); first [exact RC | exact ST | reflexivity | lia | exact SCS | exact MI]. }
      cbn beta. intros ms1 mo1 POST HK1 MM1. unfold rd_pre_post in POST.
      flat constr:(POST) 12%nat. flclear POST. intros x0 j8 j2080 m1 -> MU1 WM1 MI1 ST1 FRS FRM FRR.
      (* [comment removed for export] *)
      change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pc Mx rom).
      assert (Hfd1 : fd_lookup (m_fds mo1) (Z_to_bv 64 fd) = Some (FdFile p off)).
      { unfold m_fds in *. flat constr:(MM1) 2%nat. flclear MM1. intros E _. rewrite E. exact Hfd. }
      assert (Hfs1 : fs_lookup (m_fs mo1) p = Some data) by (rewrite (mo_mat_fs _ _ MM1); exact Hfs).
      eapply (rz_read_fileA asegs AL CS K K_halted K_mat K_vmonly _ (Z_to_bv 64 0x0eb5a8) m1 mo1 W_e81f8 (Z_to_bv 64 fd) p off data n);
        [ exact F_e81f8 | exact E_e81f8 | exact HK1
        | reflexivity | reflexivity | rewrite unsigned_lit by lia; lia | exact Hfd1 | exact Hfs1 | reflexivity
        | lia | unfold MAX_RW_COUNT; lia | lia
        | unfold mkR; norm_getr; rewrite unsigned_lit by lia; unfold TASK_SIZE; lia
        | unfold mkR; norm_getr; replace (Z_to_bv 64 BUF) with (wa (BUF + 0)) by (unfold wa; f_equal; lia);
          eapply wr_at_store_ok; [eapply wr_at_transport; [exact WR | exact WM1] | lia | lia]
        | unfold mkR; norm_getr; rewrite unsigned_lit by lia; intros z Hz; left; apply (aobj_crange _ _ _ _ _ _ OBJ); lia
        | ].
      cbv zeta. intros mo2 HK2 MM2.
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst (regupd ?R 10 ?v) _ _ _) _) _ =>
        change (regupd R 10 v) with
          (mkR (Z_to_bv 64 0x0f00ec) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 x0 (Z_to_bv 64 BUF)
               v (Z_to_bv 64 BUF) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63)
               (Z_to_bv 64 n) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) end.
      unfold mkR. norm_getr.
      replace (v_addi (Z_to_bv 64 964008) 4) with (Z_to_bv 64 0x0eb5ac) by (apply bv_eq; reflexivity).
      set (bs := file_read data off (Z_to_bv 64 n)) in *.
      pose proof (proj1 (file_read_length_le data off (Z_to_bv 64 n))) as BL. unfold word_to_nat in BL. rewrite unsigned_lit in BL by lia.
      fold bs in BL.
      set (res := Z.of_nat (length bs)).
      assert (LW : len_word bs = Z_to_bv 64 res) by (subst res; rewrite len_word_nat; reflexivity).
      rewrite LW.
      (* [comment removed for export] *)
      change (CatExec.wbytes m1 (Z_to_bv 64 BUF) bs) with (write_to_mem m1 (wa BUF) bs).
      set (m2 := write_to_mem m1 (wa BUF) bs).
      assert (MU2 : munch [(BUF, BUF + n); (lo, bv_unsigned sp)] m1 m2).
      { subst m2. apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia]. }
      assert (WM2 : wmono asegs m1 m2) by (subst m2; apply wmono_write; apply wmono_refl).
      assert (MI2 : mem_inv asegs m2).
      { subst m2. apply mem_inv_store; [exact MI1|].
        replace (wa BUF) with (wa (BUF + 0)) by (f_equal; lia).
        eapply wr_at_store_ok; [eapply wr_at_transport; [exact WR | exact WM1] | lia | lia]. }
      assert (BS2 : bytes_at asegs m2 BUF bs) by (subst m2; apply bytes_at_write_same; lia).
      assert (ST2 : stk asegs m2 lo (bv_unsigned sp + -2144)) by (subst m2; apply stk_write; [exact ST1 | lia | lia]).
      assert (FRS2 : rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { subst m2. apply rw_cells_frame; [exact FRS | lia | lia | cbn; lia]. }
      assert (FRM2 : rw_cells asegs m2 (bv_unsigned sp + -2128) [CB 2080 j2080]).
      { subst m2. apply rw_cells_frame; [exact FRM | lia | lia | cbn; lia]. }
      assert (FRR2 : rw_cells asegs m2 (bv_unsigned sp + -2144) [CB 8 j8; C8 (Z_to_bv 64 0x5a464)]).
      { subst m2. apply rw_cells_frame; [exact FRR | lia | lia | cbn; lia]. }
      assert (W12 : w_client CS [(BUF, BUF + n); (lo, bv_unsigned sp)]).
      { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (BUF + n - BUF) with n by lia; apply (aobj_crange _ _ _ _ _ _ OBJ)|].
        apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil]. }
      pose proof (munch_trans _ _ _ _ (munch_weaken [(lo, bv_unsigned sp)] [(BUF, BUF + n); (lo, bv_unsigned sp)] m m1 ltac:(solve_sub_fp) MU1) MU2) as MU02.
      assert (OBJ2 : 1 <= res -> aobj asegs AL CS m2 BUF res).
      { intros Hr. eapply aobj_sub with (A := BUF) (n := n); [| lia | lia]. eapply (aobj_munch asegs AL CS CSOK); [exact W12 | exact MU02 | exact OBJ]. }
      assert (SHRD2 : forall c, CS c -> exists b, bytes_at asegs m2 (shadow_of AL c) [b]).
      { eapply (shrd_munch AL CS CSOK); [exact W12 | exact MU02 | exact SHRD]. }
      assert (RC2 : rip_consts m2).
      { destruct RC as [_ _ RC0]. eapply rip_consts_munch2; [exact MU02 | exact RTA | exact LO0 | exact RC0]. }
      (* [comment removed for export] *)
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HK2 | | ].
      { eapply rd_post with (BUF := BUF) (n := n) (res := res) (lo := lo);
          first [exact OBJ2 | exact HULL | exact SHRD2 | exact RC2 | exact ST2 | exact FRS2 | exact FRM2 | exact FRR2 | exact MI2 | exact AR
                | lia | eapply crange_sub; [exact SCS | lia | lia] ]. }
      cbn beta. intros ms3 mo3 POST HK3 MM3. unfold rd_post_post in POST.
      flat constr:(POST) 20%nat. flclear POST. intros t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m3 -> MU3 WM3 MI3 ST3.
      apply HC.
      - eapply munch_trans; [exact MU02 | eapply munch_weaken; [| exact MU3]]. solve_sub_fp.
      - eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]].
      - exact MI3.
      - exact ST3.
      - eapply bytes_at_transport; [exact BS2 | exact MU3 |]. cbn [disjoint_from]. subst res. split; [lia | exact I].
      - lia.
      - exact HK3.
      - flat constr:(MM3) 2%nat. flclear MM3. intros E3 _. flat constr:(MM2) 2%nat. flclear MM2. intros E2 _. flat constr:(MM1) 2%nat. flclear MM1. intros E1 _. unfold m_fds in *. rewrite E3, E2.
        cbn [m_fd with_fds fdst_table]. rewrite E1.
        match goal with |- context [getr ?R 12] => change (getr R 12) with (Z_to_bv 64 n) end. fold bs. rewrite LW. reflexivity.
      - rewrite (mo_mat_fs _ _ MM3). etransitivity; [| exact (mo_mat_fs _ _ MM1)].
        flat constr:(MM2) 6%nat. flclear MM2. intros _ _ _ _ E2 _. unfold m_fs. rewrite E2. reflexivity.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L15032544257.85L18473459024.70L26277566005.70L26284021524.86L29212181715.85L29975774047.85L32920562421.70L32930687956.86L38248730935.86L40157609809.85L43779710429.86L43880243691.86L46392788080.70L46403624529.85L46520074458.85L50535243872.85L54441150474.85L59448353649.86L61931765936.70L62192421824.70L6433076081.86 L66792010720.85L67098855040.85L942286889.70  00000100<00D00L00^00c00d00e00i01001801?01N01]01b01g01n02602;02B02M02R02\02]SS2sp2lo3SPLS2lo3LO0S2lo3LO0S2sp2TP2lo3TPB3LO0S1n1NFFS2loS2fd2FDS2sp3SPRS2sp2loS3BUF1n1N2B02B1S3BUF1n1N2B02B1S3BUFS1n1NS2fd2FDS2TP3TPBS1n1NS2fd2FDS2sp2lo3SPLS1n1NS3BUF1n2B1F". (* [comment removed for export] *)
    Theorem read_icpt_dirA : ltac2:(CDefT.buildp (gd_tbl_A_icpt_read ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pm,P,(1.&40.)(2.(1.&8.))Pmo,$34.Pfd,$0.PBUF,$0.Pn,$0.PTP,$0.Plo,$0.Pje,(29.(1.&8.))PT,$3?.P,A1.VK,R8.P,(18.(2.$40.)(41.(42.R9.)(1;.&40.R8.))(37.$40.$50.))P,(2>.R;.)P,(46.$14.R<.R9.R8.)P,(10.(9.+1.R9.)(:.R9.(11.+2.+18.)))P,(:.=R;.)P,(:.(24.R<.R;.)(11.+2.+2?.))P,(18.(1.&40.)R2<.(1;.&40.R;.))P,(10.(9.(24.+10000.+:4.)R<.)(:.R<.+65?000.))P,(25.VCS,(24.R=.-:4.)+4.)P,(2:.$14.R13.(24.R>.-:4.)(4.$2;.(2=.#4.R<.)(7.$2;.)))P,(21.$14.R14.R>.(1>.&40.R32.))P,(:.+10007???7???.R?.)P,(9.R10.(>.(1>.&40.R34.)+8:0.))P,(25.VCS,R11.(>.(1>.&40.R35.)R11.))P,(20.$14.R18.)P,(10.(9.=R17.)(:.R17.(11.+2.+1?.)))P,(18.(1.&40.)R30.(1;.&40.R18.))P,(18.(1.&40.)R30.(1;.&40.R18.))P,(18.(1.&40.)R30.(1;.&40.R18.))P,Pa1',(1.&40.)Pa2',(1.&40.)Pa3',(1.&40.)Pa4',(1.&40.)Pa5',(1.&40.)Pa6',(1.&40.)Pa7',(1.&40.)Pm',P,(1.&40.)(2.(1.&8.))Pmo',$34.P,(3.(4.(5.$0.$0.)(6.$0.$0.(24.R21.-:4.)(24.(24.R21.-:4.)+4.))(4.(5.$0.$0.)(6.$0.$0.R20.(1>.&40.R44.))(7.(5.$0.$0.))))R26.R2.)P,(1?.$14.R27.R3.)P,(20.$14.R4.)P,(21.$14.R5.R23.(1>.&40.R47.))P,(2:.$14.R6.(24.R25.-:4.)(4.$2;.(32.(1;.&40.+15.))(7.$2;.)))P,A1.VK,R6.P,(38.R2;.R7.)(4=.$14.(4>.(19.(1:.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.(1;.&40.-1.)R10.R?.R>.R=.R<.R;.R:.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)(4?.&5.(1.&40.))(30.R4<.)(1;.&20.=)(1<.(1.&40.))R9.(1=.$14.))R8.)R25.)(4=.$14.(4>.(19.(1:.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)(4?.&5.(1.&40.))(1;.&40.+5:414.)(1;.&20.=)(1<.(1.&40.))R1>.(1=.$14.))R1=.)R16.)")
(* [comment removed for export] *).
    Proof.
      intros until T. intros HK Hfd RC WR N B0 B1 TPE TPB ECS ERR ST LO0 SPL SCS MI FD -> -> -> HC.
      al_facts.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
      eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HK | | ].
      { eapply rd_pre with (fd := fd) (BUF := BUF) (n := n) (lo := lo); first [exact RC | exact ST | reflexivity | lia | exact SCS | exact MI]. }
      cbn beta. intros ms1 mo1 POST HK1 MM1. unfold rd_pre_post in POST.
      flat constr:(POST) 12%nat. flclear POST. intros x0 j8 j2080 m1 -> MU1 WM1 MI1 ST1 FRS FRM FRR.
      change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pc Mx rom).
      assert (Hfd1 : fd_lookup (m_fds mo1) (Z_to_bv 64 fd) = Some FdDir).
      { unfold m_fds in *. flat constr:(MM1) 2%nat. flclear MM1. intros E _. rewrite E. exact Hfd. }
      eapply (rz_read_dir_mappedA asegs K K_halted _ (Z_to_bv 64 0x0eb5a8) m1 mo1 W_e81f8 (Z_to_bv 64 fd) n);
        [ exact F_e81f8 | exact E_e81f8 | exact HK1
        | reflexivity | reflexivity | rewrite unsigned_lit by lia; lia | exact Hfd1 | reflexivity
        | lia | lia
        | unfold mkR; norm_getr; rewrite unsigned_lit by lia; unfold TASK_SIZE; lia
        | unfold mkR; norm_getr; replace (Z_to_bv 64 BUF) with (wa (BUF + 0)) by (unfold wa; f_equal; lia);
          eapply wr_at_store_ok; [eapply wr_at_transport; [exact WR | exact WM1] | lia | lia]
        | ].
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst (regupd ?R 10 ?v) _ _ _) _) _ =>
        change (regupd R 10 v) with
          (mkR (Z_to_bv 64 0x0f00ec) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 x0 (Z_to_bv 64 BUF)
               v (Z_to_bv 64 BUF) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63)
               (Z_to_bv 64 n) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) end.
      change (errno_ret EISDIR) with (Z_to_bv 64 (- (21))).
      replace (Z_to_bv 64 (- (21))) with (Z_to_bv 64 (2^64 - 21)) by (apply bv_eq; reflexivity).
      replace (v_addi (Z_to_bv 64 964008) 4) with (Z_to_bv 64 0x0eb5ac) by (apply bv_eq; reflexivity).
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      assert (ERR1 : rw_cells asegs m1 (TP + -164) [CB 4 je]).
      { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; split; [lia | exact I]]. }
      eapply (rz_evtA_K asegs AL CS K K_halted K_mat); [exact HK1 | | ].
      { eapply rd_post_dir with (TP := TP) (lo := lo);
          first [exact TPE | exact ECS | exact ERR1 | exact ST1 | exact FRS | exact FRM | exact FRR | exact MI1 | lia
                | eapply crange_sub; [exact SCS | lia | lia] ]. }
      cbn beta. intros ms3 mo3 POST HK3 MM3. unfold rd_post_dir_post in POST.
      flat constr:(POST) 14%nat. flclear POST. intros b1 b2 b3 b4 b5 b6 b7 m3 -> MU3 WM3 MI3 ST3 ERR3.
      apply HC.
      - eapply munch_trans; [| exact MU3]. eapply munch_weaken; [| exact MU1]. solve_sub_fp.
      - eapply wmono_trans; [exact WM1 | exact WM3].
      - exact MI3.
      - exact ST3.
      - exact ERR3.
      - exact HK3.
      - eapply mo_mat_trans; [exact MM1 | exact MM3].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Glue.
End Walk.
