(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_lset P_mpi_copy P_mpi_divmod_stmt P_mpi_core_exp_mod_working_limbs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_frame_lib A_frame_kit A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_copy
     A_mpi_core_bitlen A_mpi_core_exp_mod_working_limbs A_mpi_lset A_mpi_get_mont_r2 A_mpi_zeroize_and_free A_mpi_client2 A_mpi_cmp_mpi A_mpi_grow A_mpi_core_montmul A_mpi_core_montmul_init A_mpi_core_to_mont_rep A_mpi_core_exp_mod_stmtA A_mpi_core_from_mont_rep A_mpi_core_check_zero_ct A_mpi_add_sub A_mpi_add_sub_stmtSZ A_mpi_stmtA_sz A_mpi_exp_mod_P A_mpi_exp_mod_C
     A_mpi_stmtA_c24 A_mpi_copy_c24 A_mpi_grow_c24 A_mpi_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_exp_mod_lib.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
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
Ltac2 gd_tbl_A_mpi_exp_mod_S_c24 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Lists.ListDef.map"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_exp_mod_lib.snapA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "WES.EMBg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_exp_mod_C.EMB"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "WES.EMBc"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_exp_mod_working_limbs.exp_mod_working_limbs"; "WES.HREL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.vchg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "WES.chunk_in"; "WES.EMBs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.pow"; "WES.EM_POISON_RR"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Stdlib.Lists.List.NoDup"; "WES.XST"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.binop_keep"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "WES.EMJ"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "Stdlib.Lists.List.incl"; "WES.em_GP"; "WES.em_GF"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_exp_mod_C.VIEWg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "WES.JSLOTS"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.copy_sep"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_FR"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_COPY"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "WES.set_sg"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mod_mpi_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mod_mpi_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow.grow_FR"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "WES.HARR"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "WES.set_limbs"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub.add_sub_FR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"; "WES.em_V1"; "WES.em_F1"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"].

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([658888]).
Local Ltac zchk_new ::= constr:([657484; 657488; 657512; 657516; 657520; 657608; 657612; 657616; 657844; 657848; 658272; 658276; 658280; 658676; 658680; 658684; 658740; 658744; 658748]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Local Ltac zstep_to L :=
  repeat (lazymatch goal with
          | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => zstep end
          end).
Section WES.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dX : mpd) (lo slo : Z).
  Local Notation X := (md_addr dX).
  Local Notation KEEP := (mpd_keep LB dX).
  Local Notation WX := [(X, X + 16)].
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 1248 - arl_need_ecp R.
  Hypothesis NEEDE : 0 <= arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis HH0 : HM asegs R HIA h LB LF m.
  Hypothesis SSL : arl_stklo R <= slo.
  Hypothesis SLL : slo <= lo.
  Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation EMB0 := (EMB R HIA h LB LF m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 dX lo slo).

  (* [comment removed for export] *)
  Definition HREL (hc : HST asegs R HIA) (v f : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(0.(1.$2.(3.$4.VR,VHIA,O3.)(3.$4.VR,VHIA,Vh,))(0.(1.$2.(5.$4.VR,VHIA,O3.)(5.$4.VR,VHIA,Vh,))(0.(1.$2.(6.$4.VR,VHIA,O3.)(6.$4.VR,VHIA,Vh,))(0.Px,$2.P,(7.$4.VR,VHIA,Vh,R1.)(7.$4.VR,VHIA,O3.R2.)(0.(8.(9.$4.VR,VHIA,O3.)(:.(9.$4.VR,VHIA,Vh,)O2.))(8.(;.$4.VR,VHIA,O3.)(:.(;.$4.VR,VHIA,Vh,)O1.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition EMBg (PC : list cell) (sp1 : Z) (hc : HST asegs R HIA) (LBc : list blk) (mq : mem) (sl : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(0.(0.(8.(<.(=.&40.Vsp,)+150.)O5.)(8.O5.(<.(=.&40.Vsp,)+140.)))(0.(1.$2.(>.O5.+20.)=)(0.(?.$4.VR,VHIA,O4.O3.VLF,O2.)(0.(10.$4.O2.(:.(=.&40.Vsp,)-68.)(11.$12.(13.Vs11,)(11.$12.(13.Vs10,)(11.$12.(13.Vs9,)(11.$12.(13.Vs8,)(11.$12.(13.Vs7,)(11.$12.(13.Vs6,)(11.$12.(13.Vs5,)(11.$12.(13.Vs4,)(11.$12.(13.Vs3,)(11.$12.(13.Vs2,)(11.$12.(13.Vs1,)(11.$12.(13.Vs0,)(11.$12.(13.Vra,)(14.$12.)))))))))))))))(0.(10.$4.O2.O5.(15.(16.&40.)$12.$13.O1.))(0.(1.$17.(18.(16.&40.)O1.)#1;.)(0.(19.$4.O2.(:.O5.+=8.)(:.(=.&40.Vsp,)-68.))(0.(19.$4.O2.Vlo,O5.)(0.(1:.$4.O2.)(0.(10.$4.O2.(:.(1;.(:.O5.+60.)+3.)(1<.(1=.VR,)))O6.)(0.(1>.$4.(1=.VR,)O2.Vslo,(:.O5.+60.))(0.(1>.$4.(1=.VR,)O2.(:.O5.+<0.)(=.&40.Vsp,))(0.(1?.$4.(1=.VR,)Vm,O2.(20.VR,)(:.O5.+60.))(0.(1?.$4.(1=.VR,)Vm,O2.(:.O5.+<0.)(=.&40.Vsp,))(21.$4.VR,VHIA,Vh,(22.VLB,VdX,)VLF,(=.&40.Vsp,)(=.&40.Vsp,)(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))Vm,O2.)))))))))))))))")
(* [comment removed for export] *).
  Definition EMBc := EMBg EM_POISON.
  Definition EM_POISON_RR : list cell := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(11.$12.(26.(27.&8.+?1.))(11.$12.(26.(27.&8.+?1.))(11.$12.(26.(27.&8.+?1.))(11.$12.(26.(27.&8.+?1.))(11.$12.(26.(27.&8.+?8.))(11.$12.(26.(27.&8.+?2.))(11.$12.(26.(27.&8.+?8.))(11.$12.(26.(27.&8.+?2.))(11.$12.(26.(27.&8.=))(11.$12.(26.(27.&8.=))(11.$12.(26.(27.&8.+?3.))(11.$12.(26.(27.&8.+?3.))(14.$12.)))))))))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma embc_of_emb : forall sp1 mq sl, EMB0 sp1 mq sl -> EMBc sp1 h LB mq sl.
  Proof.
    intros sp1 mq sl EB. unfold EMB in EB.
    ddestruct EB as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES & _ & _).
    unfold EMBc, EMBg. repeat (split; [assumption|]). assumption.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24243817879.39000006S1l2IH". (* [comment removed for export] *)
  #[using="Type"] Lemma cells_size_map_C8 : forall (l : list word), cells_size (map C8 l) = (8 * length l)%nat.
  Proof. induction l as [|w l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10376588162.10L1540877545.3  L18546069956.14L20870518615.6 L29098720600.3 L29919900381.13L31021792691.6 L40281191306.3 L50530042726.3 L50790584144.8 L519294241.8   L52045659405.3 L55896549980.8 L5956688929.3  L62018535662.1 L6203415987.3  L6203936179.1  L63205382458.8 L66151427842.16L7538573601.8  L8931088584.3  L8931608776.1  00000W00c01V01g01o02[03003903E03\04;04G04d04h04k05005505R05n06M06R06WS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACPS2sp3sp13SP1S1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp13SP14HTOP1c2HcS3sp11a1n2Ha1x2HxS2sp3sp1S1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP11a1n2H12H2S1R3HIA1h2sp3TOP4HTOPS1R3HIA1hS2sp3sp13SP1S1R2sp2lo3LOS3SLO5NEEDES1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S2sp3sp13SP1S1R3HIA1h2sp3TOP3sp13SP14HTOPS2spS1RS3sp1S3sp1S1R3HIA1h2sp3TOP3sp13SP14HTOPS3sp12r04SP1M1q1r1H2H02q02H4S1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S3sp1S3sp1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL DSX"] Lemma embg_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PPC,(28.$12.)Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmq,P,(16.&40.)(2;.(16.&8.))Psl,(28.(16.&40.))Ph',(29.$4.VR,VHIA,)PLB',(28.$2:.)Pm',P,(16.&40.)(2;.(16.&8.))PLBp,(28.$2:.)PW',(28.$2<.)P,(1.$17.(2=.R;.)#<.)P,(2>.R<.R;.R:.R9.R8.R7.)P,(1:.$4.R5.)P,(19.$4.R6.Vlo,R=.)P,(2?.$4.VR,R6.VLF,R>.(20.VR,)(5.$4.VR,VHIA,Vh,)R5.R;.R7.)P,Pb,$2:.P,(30.$2:.R1.(22.VLB,VdX,))(30.$2:.R2.R9.)P,Px,$2.P,(31.(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))R1.)(31.R9.R2.)P,Pa,$2.Pn,$2.P,(32.(8.(:.R2.R1.)(25.VdX,))(8.(:.(25.VdX,)+10.)R2.))(33.R;.R3.R2.)P,(?.$4.VR,VHIA,R=.R<.VLF,R;.)(2>.R14.R13.R>.R=.R<.R?.)")
(* [comment removed for export] *).
  Proof.
    intros PC sp1 hc LBc mq sl h' LB' m' LBp W' HPC EB MI' ST' HP KS WS DJW HH'.
    ddestruct EB as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    assert (CRS : forall a n, sp1 <= a -> client_range L (LBp ++ fdata LF) sp1 a n) by (intros a n Ha x Hx; left; clear - Ha Hx; lia).
    assert (DXS : forall a n, sp1 <= a -> a + n <= bv_unsigned sp -> a + n <= X \/ X + 16 <= a) by (intros a n H1 H2; clear - H1 H2 DSX SP1 SLO NEEDE; lia).
    unfold EMBg. split; [exact SP1|]. split; [exact SP1M|]. split; [exact HH'|].
    split; [eapply (presA_rw_cells asegs R); [exact HP| exact SAVE| apply CRS; clear - SP1; lia| apply DJW; apply DXS; simpl_sizes; clear - SP1; lia]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP| exact SPILL| apply CRS; clear; lia| apply DJW; apply DXS; rewrite ?cells_size_map_C8, ?LSL; clear - SP1; lia]|].
    split; [exact LSL|].
    split; [eapply (presA_stk asegs R); [exact HP| exact SThi| clear; lia| apply DJW; apply DXS; clear - SP1; lia]|].
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply (presA_shadow_cells_sh asegs R CS); [exact CSOK| | clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1 SLO NEEDE LOS ALO ACP; lia| exact HP| exact SHC|].
             - rewrite HPC. eapply crange_sub; [exact SCS0| clear - SP1 SLO NEEDE LOS; lia| clear - SP1 TOP HTOP; lia].
             - intros c Hc. left. rewrite HPC in Hc. clear - Hc SP1 SLO NEEDE LOS TOP HTOP. lia. }
    split; [eapply (presA_sshad asegs R); [exact HP| exact SSlo| exact SSL| clear - SP1 TOP HTOP; lia]|].
    split; [eapply (presA_sshad asegs R); [exact HP| exact SShi| clear - SP1 SLO NEEDE LOS; lia| clear - TOP HTOP; lia]|].
    split; [eapply (snapA_presA asegs R); [exact SNlo| exact HP| clear; lia| clear - SP1 TOP HTOP; lia]|].
    split; [eapply (snapA_presA asegs R); [exact SNhi| exact HP| clear - SP1 SLO NEEDE LOS; lia| clear - TOP HTOP; lia]|].
    eapply (presW_call asegs R HIA h); [exact PRES| exact HP| exact KS| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1 SLO NEEDE LOS; lia| clear; lia| exact WS].
    all: match goal with |- ?g => idtac "EMBC-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition embc_call := embg_call EM_POISON.
  (* [comment removed for export] *)
  Variable mo : Model.
  Variables (Rr : Z -> mpd -> Prop) (PHI FR d : Z).
  Hypothesis SSMAP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Ph,(29.$4.VR,VHIA,)PLB,(28.$2:.)PLF,(28.$2:.)Pm,P,(16.&40.)(2;.(16.&8.))Pg,$2.P,(?.$4.VR,VHIA,R5.R4.R3.R2.)P,(0.(8.(20.VR,)R2.)(34.R2.(5.$4.VR,VHIA,R6.)))(35.(1.(2;.(16.&8.))A1.R4.(36.(37.(1=.VR,)R3.))(38.(16.&8.))))")
(* [comment removed for export] *).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SS0 : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis MX0 : mpd_at asegs m LB dX.
  Hypothesis NSX : md_own dX <> LStatic.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis XL0 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "P,(35.(1.$39.(3:.VdX,)$3;.))(0.(3<.(7.$4.VR,VHIA,Vh,)(3=.VdX,)(3>.+4.(3?.VdX,)))(0.(34.=(3?.VdX,))(32.(8.(:.(3=.VdX,)(3>.+4.(3?.VdX,)))Vlo,)(8.(=.&40.Vsp,)(3=.VdX,)))))")
(* [comment removed for export] *).
  Hypothesis OX0 : mpd_aobjA asegs AL CS m dX.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis UW0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis LSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis BUDL : havol asegs R HIA h + grow_PHI 1 <= AVOL_MAX /\ grow_PHI 1 <= PHI.
  Hypothesis BUDFL : hfr asegs R HIA h + lset_FR (d + 1) <= FR_MAX /\ lset_FR (d + 1) <= FR.
  Hypothesis RRL : forall r dX', lset_R 1 dX LB r dX' -> -2^31 < r <= 0 -> Rr r dX'.
  Local Notation POSTA := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX Rr PHI FR lo m mo).
  Local Notation SH a := (Z_to_bv 64 (Z.shiftr a 3 + al_sb AL)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0?L12197920272.7 L13738244421.4 L1540877545.3  L18457785511.0 L19979671403.10L19980016842.7 L19980537034.4 L21750098805.10L21752195445.11L22946302800.4 L23928828085.3 L23929269012.8 L2397676628.0  L26892418956.1 L28816784755.3 L28857505470.11L28872300092.12L29917858283.4 L29956516996.0 L3482346814.8  L3482791583.7  L3483319967.1  L35653428328.13L35653441506.7 L35655440110.8 L35655621967.11L35659386041.4 L36633707715.6 L37116416843.9 L37122707787.8 L39188636933.0 L40305513247.8 L40307609887.8 L47760128357.7 L49799904432.3 L5042118001.3  L5045881991.10 L5046093606.9  L5048087968.12 L52101802030.14L52616371395.6 L56658999053.1 L60098763854.3 L60657453715.2 L62639005208.12L62641071935.10L62641253534.7 L62645825733.3 L6546795745.6  L65506830933.2 L65682842671.2 L66151427842.16L696052593.2   L8190532385.0  L9356559676.11 00000I00U00a00b00c01;01<01=01>01I01J01c01d01h02102W03E03O03P03Q03R03S03T03l03m03n03o04C04D04E04F04G04c05705C05D05E05F05G06406D06H06R06X06Y06Z06[06\07107807@07c07k07l08WS1R3HIA1h3PHI4BUDL2h23HV2S1R2dX1d3UWXS2sp3sp13SP1SFS1R3HIA1h2sp3TOP3sp13SP1FFFS1R3HIA1h1QFS1R2sp2lo3SLO3sp13SP13NERSS2spS1R3HIA1hS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP4HTOPS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp13SP14HTOPS2dX1a1n1DSFFFFS1R3HIA1h2sp2lo3TOP4HTOPFFFS2sp2dX2lo3sp13SP11QFFSFS1R3HIA1h2FR1d5BUDFL2h24HFR2S1R3HIA1h2sp2lo1a2HaS2sp3sp13SP1FFFFS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3sp13ALO1a2Ha2B1S1R3HIA1h2sp1a1SS2spS1R2lo3LOSS2s01QFFFFS1R2lo3LOS3ALO3dX22BLS1R3sp1S3dX22N1S2sp2r03SPA1q1r1H2H02q02H43sp14SP1MS2sp3SPRSS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SSMAP SPA SS0 MX0 NSX XW XL0 OX0 TPV UW0 UWX LSET BUDL BUDFL RRL"] Lemma em_lset : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Pmq,P,(16.&40.)(2;.(16.&8.))Psl,(28.(16.&40.))Pxra,(16.&40.)Pxt0,(16.&40.)Pxt1,(16.&40.)Pxt2,(16.&40.)Pxs1,(16.&40.)Pxa0,(16.&40.)Pxa1,(16.&40.)Pxa2,(16.&40.)Pxa3,(16.&40.)Pxa4,(16.&40.)Pxa5,(16.&40.)Pxa6,(16.&40.)Pxa7,(16.&40.)Pxs2,(16.&40.)Pxs4,(16.&40.)Pxs5,(16.&40.)Pxs6,(16.&40.)Pxs7,(16.&40.)Pxs9,(16.&40.)Pxs10,(16.&40.)Pxs11,(16.&40.)Pxt3,(16.&40.)Pxt4,(16.&40.)Pxt5,(16.&40.)Pxt6,(16.&40.)P,(40.VR,VHIA,Vh,VLB,VLF,Vm,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VdX,Vlo,Vslo,R1<.R1;.R1:.)(41.$4.(42.$4.VR,VHIA,Vh,Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R1:.(27.&40.R1=.)Vgp,Vtp,R19.R18.R17.Vsp,R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.(27.&40.(25.VdX,))R<.R;.R:.R9.(27.&40.(:.(1;.(:.R1=.+60.)+3.)(1<.(1=.VR,))))R8.R7.R6.R5.R4.R3.R2.)VF,(27.&40.+:0:00.)Vfc,(38.(16.&40.))R1<.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros EB. assert (SLO8 : lo <= bv_unsigned sp - 1088 - arl_need_ecp R) by (clear - SLO; lia).
    pose proof (emb_X R HIA h LB LF m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 dX lo slo LOS SLO8 NEEDE TOP HH0 MX0 (aobj_crange _ _ _ _ _ _ (proj1 OX0)) DSX XL0 _ _ _ EB) as MXq.
    pose proof (embc_of_emb _ _ _ EB) as EBc.
    unfold EMB in EB. ddestruct EB as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES & MU & WM).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    (* [comment removed for export] *)
    zstep_to [657920]. zstep_to [657928]. zstep_to [639492].
    (* [comment removed for export] *)
    assert (UWq : uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { pose proof (hcs_shadow_band asegs R HIA h) as BAND.
      assert (UWm : uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      assert (T64 : hstkhi asegs R HIA h <= 2^64).
      { destruct CSOK as (C1 & _). assert (CSt : CS (hstkhi asegs R HIA h - 1)).
        { replace (hstkhi asegs R HIA h - 1) with (arl_stklo R + (hstkhi asegs R HIA h - 1 - arl_stklo R)) by (clear; lia). apply SCS0. clear - HTOP TOP SLO NEEDE LOS SPR. lia. }
        pose proof (proj1 (C1 _ CSt)) as Q. clear - Q. lia. }
      { eapply uwc_munch; [exact UW0| exact MU| clear - SPR; lia| exact T64|].
        intros a Ha. cbn [outside]. split; [clear - Ha; lia|]. split; [| exact I].
        assert (CSq : CS (sp1 + 96)) by (replace (sp1 + 96) with (arl_stklo R + (sp1 + 96 - arl_stklo R)) by (clear; lia); apply SCS0; clear - SP1 SLO NEEDE LOS TOP HTOP; lia).
        pose proof (BAND _ CSq) as B1. unfold shadow_of in B1. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
        clear - B1 Ha ALO LOS SLO NEEDE SP1. lia. }
      chunk_split SAVE 11%nat SVa SVb. chunk_split SVb 1%nat SVs SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SVs by (clear; lia).
      eapply (uwc_frame asegs mq _ _ (bv_unsigned sp) sp1 (bv_unsigned s0) d); [clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| pose proof (bv_unsigned_in_range 64 s0) as Q; unfold bv_modulus in Q; cbn [Z.pow Z.of_N Pos.pow] in Q; clear - Q; lia| eapply uwc_nonneg; exact UW0| | exact UWm].
      rewrite Z_to_bv_bv_unsigned. exact (proj1 SVs). }
    assert (OXq : mpd_aobjA asegs AL CS mq dX).
    { destruct XW as [CW DXP]. split.
      - eapply (presA_aobj asegs R CS); [exact CSOK| exact (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES)| exact (proj1 OX0)| | clear; lia| intros x Hx; eapply hcs_below_top; exact Hx].
        pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
        intros a Ha. destruct (CWk a Ha) as [S|[D|B]]; [left; clear - S; lia| right; left; exact D| right; right; exact B].
      - intros ES. exfalso. exact (NSX ES). }
    pose proof LSET as LS'. unfold mpi_lset_stmtA, mpi_xop_stmtA in LS'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply LS' with (h := h) (LB := LB) (LF := LF) (dX := dX) (v := 1) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHq | exact HK1 | exact MXq | exact NSX | exact STlo | exact LOS | exact TPV | exact MIq | exact OXq | exact UWq | reflexivity
              | eapply mpd_writableA_sp_mono; [exact XW| clear - SP1; lia]
              | intros NN; ddestruct (XL0 NN) as (_ & _ & Q); clear - Q SP1; lia
              | clear; lia
              | clear - SP1 SLO NEEDE NER; lia | clear - SP1 TOP; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | exact (proj1 BUDL) | exact (proj1 BUDFL)
              | unfold uw_obj in *; clear - UWX; lia
              | match goal with |- ?g => idtac "LSET-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E' & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 657932)) with (Z_to_bv 64 657932 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (embc_call sp1 h LB mq sl h2 LB2 m2 KEEP WX eq_refl EBc MI2 ST2 HP2 ltac:(intros b Hb; exact Hb) ltac:(intros x Hx; exact Hx)
                  ltac:(intros a n D; cbn [disjoint_from]; split; [clear - D; lia| exact I]) HH2) as EB2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
    ddestruct EB2 as (_ & _ & _ & SAVE2 & SPILL2 & LSL2 & SThi2 & STlo2 & _ & SHC2 & SSlo2 & SShi2 & SNlo2 & SNhi2 & PRES2).
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    zstep_to [658144].
    assert (RNG : -2^31 < r <= 0 /\ lset_R 1 dX LB r dX2).
    { split; [| exact CR]. ddestruct CR as ([(-> & _)|(-> & _)] & _); [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]. }
    eapply (em_epi R HIA IMG h LB LF m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dX lo slo) with (hc := h2) (LBc := LB2) (dXc := dX2) (sl := sl);
      first [ eassumption | exact (RRL _ _ (proj2 RNG) (proj1 RNG))
            | clear - HV2 BUDL; lia | clear - HFR2 BUDFL; lia
            | match goal with |- ?g => idtac "LSET-EPI-LEFT:" g end ].
    - eapply crange_mono; [exact HCS2| exact (aobj_crange _ _ _ _ _ _ (proj1 OX0))].
    - intros NN. pose proof MX2 as [(_ & _ & _ & _ & _ & OW) _]. ddestruct OUT2 as (_ & ONS & _).
      destruct (md_own dX2) eqn:EO; [exfalso; exact (NN eq_refl)| | exfalso; exact (ONS eq_refl)].
      ddestruct OW as (N1 & HIN & _).
      pose proof (hm_blocks_low asegs R HIA h2 LB2 LF m2 HH2 (md_p dX2) (4 * md_n dX2) ltac:(apply in_or_app; left; exact HIN)) as BL.
      split; [exact (aobj_crange _ _ _ _ _ _ (hm_aobj_block asegs R HIA h2 LB2 LF m2 _ _ HH2 HIN))|]. split; [clear - N1; lia|].
      left. clear - BL ALO LOS. lia.
    all: match goal with |- ?g => idtac "LSET-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L22946302800.4 L28816784755.3 L28857505470.11L28872300092.12L39188636933.0 L47760128357.7 L49799904432.3 L52101802030.14L56658999053.1 L60657453715.2 L65506830933.2 L66151427842.16L696052593.2   00000;00D00j01X01Y01m02902f02j03003703Q03YS1R3HIA1h1QS1R3HIA1hS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP4HTOPS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp13SP14HTOPSS1R3HIA1h2sp2lo1a2HaS2sp3sp13SP1S1R3HIA1h2sp2lo3LOS3SLO5NEEDE3sp13ALO1a2Ha2B1S2spS2s01QS1R3sp1S2sp2r03SPA1q1r1H2H02q02H4S2sp3SPR". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SPA UW0"] Lemma emb_uwc : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Pmq,P,(16.&40.)(2;.(16.&8.))Psl,(28.(16.&40.))P,(40.VR,VHIA,Vh,VLB,VLF,Vm,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VdX,Vlo,Vslo,R3.R2.R1.)(47.$4.R3.(20.VR,)(5.$4.VR,VHIA,Vh,)(=.&40.Vsp,)R4.(:.Vd,+1.))")
(* [comment removed for export] *).
  Proof.
    intros sp1 mq sl EB. unfold EMB in EB.
    ddestruct EB as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES & MU & WM).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hcs_shadow_band asegs R HIA h) as BAND.
    assert (T64 : hstkhi asegs R HIA h <= 2^64).
    { destruct CSOK as (C1 & _). assert (CSt : CS (hstkhi asegs R HIA h - 1)).
      { replace (hstkhi asegs R HIA h - 1) with (arl_stklo R + (hstkhi asegs R HIA h - 1 - arl_stklo R)) by (clear; lia). apply SCS0. clear - HTOP TOP SLO NEEDE LOS SPR. lia. }
      pose proof (proj1 (C1 _ CSt)) as Q. clear - Q. lia. }
    assert (UWm : uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply uwc_munch; [exact UW0| exact MU| clear - SPR; lia| exact T64|].
      intros a Ha. cbn [outside]. split; [clear - Ha; lia|]. split; [| exact I].
      assert (CSq : CS (sp1 + 96)) by (replace (sp1 + 96) with (arl_stklo R + (sp1 + 96 - arl_stklo R)) by (clear; lia); apply SCS0; clear - SP1 SLO NEEDE LOS TOP HTOP; lia).
      pose proof (BAND _ CSq) as B1. unfold shadow_of in B1. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
      clear - B1 Ha ALO LOS SLO NEEDE SP1. lia. }
    chunk_split SAVE 11%nat SVa SVb. chunk_split SVb 1%nat SVs SVr.
    replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SVs by (clear; lia).
    eapply (uwc_frame asegs mq _ _ (bv_unsigned sp) sp1 (bv_unsigned s0) d); [clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia
      | pose proof (bv_unsigned_in_range 64 s0) as Q; unfold bv_modulus in Q; cbn [Z.pow Z.of_N Pos.pow] in Q; clear - Q; lia| eapply uwc_nonneg; exact UW0| | exact UWm].
    rewrite Z_to_bv_bv_unsigned. exact (proj1 SVs).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (dE dN : mpd).
  Local Notation E := (md_addr dE).
  Local Notation N := (md_addr dN).
  Hypothesis MN0 : mpd_at asegs m LB dN.
  Hypothesis SXN : X + 16 <= N \/ N + 16 <= X.
  Hypothesis OSN : opnd_sep dX dN lo (bv_unsigned sp).
  Hypothesis CRN : client_range L (LB ++ fdata LF) lo N 16.
  Hypothesis CRNL : md_own dN = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dN) (4 * md_n dN).
  Hypothesis ODN : mpd_aobjA asegs AL CS m dN.
  Hypothesis IMN : mpd_imgA dN.
  Hypothesis NN4 : md_n dN <= 4999.
  Hypothesis CALLOC : arl_calloc R = 0x69484.
  Local Notation WL := (exp_mod_working_limbs (md_n dN) (md_n dE)).
  Hypothesis RR16 : Rr (-16) dX.
  Hypothesis BUDA : havol asegs R HIA h + vchg (WL * 4) <= AVOL_MAX.
  Hypothesis BUDFA : hfr asegs R HIA h + fr_charge (d + 1) <= FR_MAX.
  Hypothesis C24A : cnt24 LB < C24MAX.
  Local Notation SBw := (Z_to_bv 64 (al_sb AL)).
  Local Notation RF sp1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (mkR (Z_to_bv 64 0xa0944) (Z_to_bv 64 sp1) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 (N + 10)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         (SH N) (Z_to_bv 64 N) (Z_to_bv 64 X) SBw (SH (N + 10)) (Z_to_bv 64 (E + 10)) (SH E) (SH (E + 10)) (Z_to_bv 64 (sp1 + 128)) (SH (sp1 + 96)) xt3 xt4 xt5 xt6).
  Hypothesis BUDA2 : vchg (WL * 4) <= PHI.
  Hypothesis BUDFA2 : fr_charge (d + 1) <= FR.
  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@D21667997106.176D60189065437.176L10685100449.0  L15516709496.3  L1685717371.0   L19979673078.11 L19980016842.7  L21750098802.12 L21752195442.11 L22594986486.2  L24166965860.1  L26371003663.11 L26372958089.9  L26373007029.11 L29000744808.9  L2953146085.8   L3482349475.9   L3482791583.7   L35653441506.7  L37593896758.1  L40823280849.9  L45137363843.9  L45139460483.10 L47278198764.2  L4854876195.11  L4856509588.3   L4856576677.9   L4856888217.11  L49932578389.3  L57698627611.2  L58641002120.158L58790367512.9  L59308632823.3  L60098763854.3  L62228589345.0  L66151427842.16 L68207037895.10 L68209135559.8  L8171746705.16  L9356559676.11  P47293664555.177P57713046236.176Q10149575540.176Q10149575540.177Q11801279589.176Q16285785003.160Q17968854497.159Q17969015064.160Q17971522816.157Q20414272036.176Q23927705296.177Q27882953602.176Q28465177121.174Q31814056690.157Q3421936230.176 Q37991114286.173Q39180574961.176Q39212284437.160Q42439443119.176Q51087705995.176Q5129158642.176 Q5129158642.177 Q51752217908.159Q5265442331.175 Q55415036769.176Q57037327601.176Q57037327601.177Q57228775306.176Q58125335435.176Q58125335435.177Q59865321072.176Q60305443321.160Q60511567613.160Q6186103236.176 Q62011970312.177Q64041402609.176Q64683667846.176Q66562203059.173Q9540948703.157 00000i01i01j02502602702O02P02Q02Y02]02^02_02`03@03X03Y03Z04204604704804904:04;04F04G04H04S04T04b05?05H05R05S05o06006M06f07Q07R08308S09309409;09?09C09G0:70:i0:j0;70;;0;_0;n0<f0<j0=N0=h0=i0=j0=n0><0>]0?M0@=0@m0AG0Aa0Ab0Af0Ag0BK0Bg0CW0DM0Dh0DiS1R3HIA1h2sp3TOP2dE2dN3sp13SP12NB3SPR4SP1R2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE2dE2dN3sp13SP12NB3SPR4SP1R2HB5Ha_st5Hl_stSS2dN3NN42N1SFS1R3HIA1h2sp3TOP3sp13SP1FFS2dN3NRNS2dXFFFS1R3HIA1h3PHI2dE2dN5BUDA22h33HV3S1R3HIA1h2sp3sp13SP11a1SFFS1R3HIA1h2sp2lo3TOP4HTOPS2dXSFFFFS2dE2dN3WLBFFS2dE2dN3WLBFS2sp2dN3sp12NBS1R2sp2lo3SLO3sp13SP13NER3NRMS1T2T02KTS1R2lo3LOSSS3sp12r04SP1M1q1r1H2H02q02H4FS1R3HIA1h2FR1d6BUDFA22h34HFR3S1R2dE2dN3ACV3WLB1T2F02F1S1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRFS2sp2dE2dN3sp13SP12HB5Ha_st5Hl_stS2sp2lo2dE2dN3sp12HB5Ha_st5Hl_stS2sp2lo2dE2dN3sp12HB5Ha_st5Hl_stFS2dN2NBS2dNS2dNS2dNS1R2sp2lo3SLO5NEEDE2dE2dN3sp13SP12HB5Ha_st5Hl_stS1R3HIA1h2sp3TOP2dE2dN3sp13SP14HTOP2HB5Ha_st5Hl_stFS3sp14SP1R2HBS2dNS2sp2lo2dE2dN3sp13SP12HB5Ha_st5Hl_stS2sp2lo3sp13SP1S1R2sp2lo3LOS3SLO5NEEDE2dE2dN3sp13SP13ALO2HB5Ha_st5Hl_stS2dNS1R3slo3SSL2dE2dN3sp12HB5Ha_st5Hl_stS2dE2dN3sp12HB5Ha_st5Hl_stFFS2dNS3sp12HB5Ha_stS2sp2dE2dN3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dE2dN3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dE2dN3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dE2dN3sp13SP12HB5Ha_st5Hl_stS2dE2dN3sp12HB5Ha_st5Hl_stS2dE2dN3sp12HB5Ha_st5Hl_stFS2dNSS2sp2lo2dE2dN3sp13SP12HB5Ha_st5Hl_stS1R2dE2dN3sp12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE2dE2dN3sp13SP12HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP2dE2dN3sp13SP14HTOP2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP1S". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 MX0 NSX XW XL0 OX0 TPV UW0 MN0 SXN OSN CRN CRNL ODN IMN NN4 CALLOC RR16 BUDA BUDFA C24A BUDA2 BUDFA2"] Lemma em_alloc : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Pmq,P,(16.&40.)(2;.(16.&8.))Psl,(28.(16.&40.))Pxt0,(16.&40.)Pxt1,(16.&40.)Pxt2,(16.&40.)Pxa3,(16.&40.)Pxa4,(16.&40.)Pxa5,(16.&40.)Pxa6,(16.&40.)Pxa7,(16.&40.)Pxs5,(16.&40.)Pxt3,(16.&40.)Pxt4,(16.&40.)Pxt5,(16.&40.)Pxt6,(16.&40.)P,(40.VR,VHIA,Vh,VLB,VLF,Vm,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VdX,Vlo,Vslo,R10.R?.R>.)P,(8.+1.(3?.VdN,))P,(0.(8.=(3?.VdE,))(8.(3?.VdE,)+2710.))P,Ph1,(29.$4.VR,VHIA,)Pm1,P,(16.&40.)(2;.(16.&8.))Psl1,(28.(16.&40.))PT,$2.Pyra,(16.&40.)Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(48.R26.R13.(11.(23.$2.$2.)(24.$2.$2.R10.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))VLB,)R12.R11.)P,(4:.R14.(4;.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(4<.(:.Vd,+1.)))P,(4=.$4.R14.VLB,VdX,)P,(10.$4.R15.R13.(11.$12.(4>.(4?.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(50.(16.&8.)(27.&8.=)(4?.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))))(14.$12.)))P,(1.$2.(>.R14.+10.)=)P,(51.VR,VLB,VLF,R15.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))P,(1.(2;.(16.&40.))(52.(16.&40.)R17.#6.)(53.(16.&40.)(27.&40.(49.(3?.VdN,)(3?.VdE,)))))P,(1.(2;.(16.&40.))(52.(16.&40.)R18.#7.)(53.(16.&40.)(27.&40.R17.)))P,Pk,$17.P,(35.(1.$17.R1.#6.))P,(35.(1.$17.R2.#7.))(1.(2;.(16.&40.))(52.(16.&40.)R1<.R3.)(52.(16.&40.)R2?.R3.))(41.$4.(42.$4.VR,VHIA,R1<.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R18.(27.&40.R2?.)Vgp,Vtp,R17.R16.R15.Vsp,(27.&40.=)(27.&40.R19.)R14.R13.R12.R11.R10.R?.R>.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))R24.(27.&40.(49.(3?.VdN,)(3?.VdE,)))(27.&40.=)(27.&40.(:.(1;.(:.R2?.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R=.R<.R;.R:.)VF,(27.&40.+:0990.)Vfc,(38.(16.&40.))R1;.(46.$4.)))(41.$4.(42.$4.VR,VHIA,Vh,Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.+:0944.)(27.&40.R14.)Vgp,Vtp,R11.R10.R?.Vsp,(27.&40.=)(27.&40.(:.(25.VdN,)+:.))(27.&40.(3?.VdE,))(27.&40.(:.(1;.(:.(25.VdN,)+:.)+3.)(1<.(1=.VR,))))R>.R=.R<.R;.R:.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))R9.(27.&40.-4.)(27.&40.=)(27.&40.(:.(1;.(:.R14.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R8.R7.R6.R5.)VF,(27.&40.+:0968.)Vfc,(38.(16.&40.))R13.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros EB N1 NE K. assert (SLO8 : lo <= bv_unsigned sp - 1088 - arl_need_ecp R) by (clear - SLO; lia).
    pose proof (emb_X R HIA h LB LF m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 dX lo slo LOS SLO8 NEEDE TOP HH0 MX0 (aobj_crange _ _ _ _ _ _ (proj1 OX0)) DSX XL0 _ _ _ EB) as MXq.
    pose proof (emb_uwc _ _ _ EB) as UWq. pose proof (embc_of_emb _ _ _ EB) as EBc.
    pose proof EB as EB'. unfold EMB in EB'. ddestruct EB' as (SP1 & SP1M & HHq & SAVE & SPILL & LSL & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES & MU & WM).
    assert (VN : rw_cells asegs mq N [C8 (Z_to_bv 64 (md_p dN)); C2 (Z_to_bv 64 (md_sg dN)); C2 (Z_to_bv 64 (md_n dN)); C4 (md_pad dN)]
                 /\ 0 <= md_n dN <= 10000 /\ (0 < N /\ N + 16 <= 2^64) /\ N mod 8 = 0 /\ aobj asegs AL CS mq N 16).
    { edestruct (em_view R HIA IMG h LB LF m) with (d := dN) (mq := mq) (dX := dX) (lo := lo) (sp := sp) as (C1 & _ & _ & C4 & _ & C6 & _ & C8' & C9 & _); try eassumption.
      repeat (split; [assumption|]). assumption. }
    ddestruct VN as (CN & NRN & NB & NAL & ON).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER. pose proof (arl_need_rt_malloc R) as NRM.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    repeat (destruct sl as [|? sl]; [discriminate LSL|]). destruct sl; [| discriminate LSL]. clear LSL. cbn [map] in SPILL.
    unfold EM_POISON in SHC.
    (* [comment removed for export] *)
    shadow_chk ON (N + 10) 2.
    zstep_to [657780]. rewrite zx16_small by (clear - NRN; lia). zstep_to [679432].
    pose proof (A_mpi_core_exp_mod_working_limbs_spec AL IMG) as SPW. unfold mpi_core_exp_mod_working_limbs_stmtA, A_MPI_CORE_EXP_MOD_WORKING_LIMBS in SPW.
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply SPW with (CS := CS) (an := md_n dN) (en := md_n dE); first [exact MIq| exact CSOK| exact (art_alwf asegs R HIA)| reflexivity| exact NRN| exact NE]. }
    clear SPW. intros ms' PO. unfold mpi_core_exp_mod_working_limbs_post in PO.
    ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & -> & _ & _ & _ & ->).
    replace (ret_pc (Z_to_bv 64 657784)) with (Z_to_bv 64 657784 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    (* [comment removed for export] *)
    zstep. zstep_to [657792]. zstep_to [431236].
    lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo sp1, H3 : HM _ _ _ h LB LF ?m2, H4 : stk asegs ?m2 (sp1 + 216) _ |- _ =>
      lazymatch type of SPILL with rw_cells _ _ _ ?cs =>
        let ws := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) cs) in
        assert (EB2 : EMB0 sp1 m2 ws) by (unfold EMB; refine (conj SP1 (conj SP1M (conj H3 (conj SAVE (conj SPILL (conj eq_refl (conj H4 (conj H2 (conj H1 (conj SHC (conj SSlo (conj SShi (conj SNlo (conj SNhi (conj PRES (conj MU WM)))))))))))))))));
        rename H1 into MI2; rename H2 into ST2; rename H3 into HH2; rename m2 into m2'
      end end.
    pose proof (emb_X R HIA h LB LF m ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 dX lo slo LOS SLO8 NEEDE TOP HH0 MX0 (aobj_crange _ _ _ _ _ _ (proj1 OX0)) DSX XL0 _ _ _ EB2) as MX2.
    pose proof (emb_uwc _ _ _ EB2) as UW2. pose proof (embc_of_emb _ _ _ EB2) as EBc2.
    assert (WLB : 0 <= WL <= 60000) by (unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); clear - NN4 N1; lia).
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc_t asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := WL) (sz := 4) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HH2 | exact HK1 | exact ST2 | exact LOS | exact MI2 | exact TPV | exact UW2 | exact BUDA | exact BUDFA | reflexivity
              | intros _; exact C24A
              | clear - SP1 SLO NEEDE NER NRM; lia | clear - SP1 TOP; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | unfold AMAX; clear - WLB; lia
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E' & PO). injection E' as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E' PO]. subst ms'.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (MI3 & ST3 & MF3 & WM3 & HP3 & h3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m3 end.
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo) _ _ mo' (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo) as KINV.
    (* [comment removed for export] *)
    assert (MX3 : mpd_at asegs m3 LB dX).
    { destruct XW as [CW DXP].
      eapply (mpd_at_heap_presx asegs L m2' m3 LB (LB ++ fdata LF) LB sp1 [] dX); [exact MX2| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP3)| exact MI2| exact MI3| | | exact I| intros _; exact I| intros bq Hbq; pose proof MX0 as [(_ & _ & _ & _ & _ & OW) _]; unfold mpd_blk in Hbq; destruct (md_own dX); try (destruct Hbq; fail); destruct Hbq as [<-|[]]; exact (proj1 (proj2 OW))].
      - intros a Ha. destruct (CW a Ha) as [S|[D|B]]; [left; clear - S SP1; lia| right; left; exact D| right; right; exact B].
      - intros EH. pose proof MX0 as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
        eapply client_range_block; [apply in_or_app; left; exact HIN| clear; lia| clear; lia]. }
    assert (HP3' : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) [] m2' m3) by exact HP3.
    destruct CASES as [(Er & HH3)|(T & Er & T16 & FRT & TLOC & HH3 & TCELLS)]; (lazymatch type of Er with ?v = _ => subst v end).
    - (* [comment removed for export] *)
      pose proof (embc_call sp1 h LB m2' _ h3 LB m3 LB [] eq_refl EBc2 MI3 ST3 HP3' ltac:(intros bq Hbq; eapply In_mpd_keep; exact Hbq) ltac:(intros xq _; exact I)
                    ltac:(intros aq nq _; exact I) HH3) as EB3.
      ddestruct EB3 as (_ & _ & _ & SAVE3 & SPILL3 & LSL3 & SThi3 & STlo3 & _ & SHC3 & SSlo3 & SShi3 & SNlo3 & SNhi3 & PRES3).
      pose proof (munch_refl ([] : list ivl) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3'.
      zstep_to [657940]. zstep. zstep_to [658144].
      eapply (em_epi R HIA IMG h LB LF m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dX lo slo) with (hc := h3) (LBc := LB) (dXc := dX);
        first [ eassumption | exact RR16 | apply mpd_out_refl; exact NSX | intros bq Hbq; left; exact Hbq
              | clear - HV3 BUDA2; lia | clear - HFR3 BUDFA2; lia
              | eapply crange_mono; [exact HCS3| exact (aobj_crange _ _ _ _ _ _ (proj1 OX0))]
              | intros NN; ddestruct (XL0 NN) as (Q1 & Q2 & Q3); split; [eapply crange_mono; [exact HCS3| exact Q1]| split; [exact Q2| exact Q3]]
              | match goal with |- ?g => idtac "ALLOC-EPI-LEFT:" g end ].
    - (* [comment removed for export] *)
      pose proof (embc_call sp1 h LB m2' _ h3 ((T, WL * 4) :: LB) m3 LB [] eq_refl EBc2 MI3 ST3 HP3' ltac:(intros bq Hbq; eapply In_mpd_keep; exact Hbq) ltac:(intros xq _; exact I)
                    ltac:(intros aq nq _; exact I) HH3) as EB3.
      assert (T0 : 0 < T) by (destruct FRT as (F0 & _); exact F0).
      assert (TR : 0 <= T < 2^64) by (ddestruct FRT as (F0 & F1 & _); cbn [fst snd] in *; clear - F0 F1 ACV ACP WLB ALO SPR LOS SLO NEEDE; lia).
      (zstep_to [657796]; zstep). if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by exact TR; [exfalso; clear - KT T0; lia|].
      assert (TLO : T + WL * 4 <= lo) by (ddestruct FRT as (F0 & F1 & _); cbn [fst snd] in *; clear - F0 F1 ACV ACP WLB ALO SPR LOS SLO NEEDE; lia).
      pose proof (conj MI3 I) as MI3c. pose proof (conj TCELLS I) as TC3.
      ddestruct EB3 as (_ & _ & HH4 & SAVE4 & SPILL4 & _ & SThi4 & STlo4 & MI4 & SHC4 & SSlo4 & SShi4 & SNlo4 & SNhi4 & PRES4).
      cbn [map] in SPILL4. try unfold EM_POISON in SHC4.
      pose proof (munch_refl [(sp1, sp1 + 216)] m3) as MU4. pose proof (wmono_refl asegs m3) as WM4.
      pose proof (hcs_stack asegs R HIA h3) as SCS03. first [rewrite HS3 in SCS03| rewrite <- HS3 in SCS03].
      assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS03| clear - LOS; lia| clear - TOP HTOP; lia]).
      zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?m4 _) =>
        assert (MX4 : mpd_at asegs m4 LB dX);
        [ eapply (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.MpiClient.mpd_at_munch_pw asegs m3 m4 LB dX [(sp1, sp1 + 216)]); [exact MX3| exact MU4| exact WM4| exact (proj1 MI3c)| assumption
          | intros xq Hxq; cbn [outside]; split; [clear - Hxq DSX SP1 SLO NEEDE; lia| exact I]
          | intros EH xq Hxq; cbn [outside]; split; [| exact I]; assert (NN : md_own dX <> LNull) by (rewrite EH; discriminate);
            ddestruct (XL0 NN) as (_ & _ & Q); clear - Q Hxq SP1 SLO NEEDE; lia]
        | lazymatch goal with H1 : mem_inv asegs m4, H2 : stk asegs m4 lo sp1, H3 : HM _ _ _ h3 _ LF m4, H4 : stk asegs m4 (sp1 + 216) _ |- _ =>
            lazymatch type of SPILL4 with rw_cells _ _ _ ?cs =>
              let ws := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) cs) in
              eapply (K h3 m4 ws T);
                [ unfold EMBc, EMBg; refine (conj SP1 (conj SP1M (conj H3 (conj SAVE4 (conj SPILL4 (conj eq_refl (conj H4 (conj H2 (conj H1 (conj SHC4 (conj SSlo4 (conj SShi4 (conj SNlo4 (conj SNhi4 PRES4))))))))))))))
                | unfold HREL; repeat (split; [assumption|]); assumption
                | exact MX4
                | first [ exact TCELLS
                        | eapply rw_cells_transport; [exact (proj1 TC3)| exact MU4| exact WM4|];
                          cbn [disjoint_from cells_size csize]; rewrite ?Nat.add_0_r, ?repeat_length, ?Z2Nat.id by (clear - WLB; lia);
                          split; [left; clear - TLO SP1 SLO NEEDE; lia| exact I] ]
                | exact T16 | exact FRT | reflexivity | reflexivity | ]
            end
          end ]
      end.
      intros k K6 K7. do 27 (destruct k as [|k]; [first [reflexivity| exfalso; first [apply K6; reflexivity| apply K7; reflexivity]]|]). reflexivity.
    all: match goal with |- ?g => idtac "ALLOC-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition chunk_in (sp1 : Z) (ac : Z * list cell) : Prop := sp1 <= fst ac /\ fst ac + Z.of_nat (cells_size (snd ac)) <= sp1 + 216.
  Definition EMBs (PC : list cell) (sp1 : Z) (hc : HST asegs R HIA) (LBc : list blk) (mq : mem) (CH : list (Z * list cell)) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(0.(0.(8.(<.(=.&40.Vsp,)+150.)O5.)(8.O5.(<.(=.&40.Vsp,)+140.)))(0.(1.$2.(>.O5.+20.)=)(0.(?.$4.VR,VHIA,O4.O3.VLF,O2.)(0.(10.$4.O2.(:.(=.&40.Vsp,)-68.)(11.$12.(13.Vs11,)(11.$12.(13.Vs10,)(11.$12.(13.Vs9,)(11.$12.(13.Vs8,)(11.$12.(13.Vs7,)(11.$12.(13.Vs6,)(11.$12.(13.Vs5,)(11.$12.(13.Vs4,)(11.$12.(13.Vs3,)(11.$12.(13.Vs2,)(11.$12.(13.Vs1,)(11.$12.(13.Vs0,)(11.$12.(13.Vra,)(14.$12.)))))))))))))))(0.(54.(23.$2.(28.$12.))Lac,(23.$2.(28.$12.))(10.$4.O2.(55.$2.(28.$12.)R1.)(56.$2.(28.$12.)R1.))O1.)(0.(54.(23.$2.(28.$12.))(57.O5.)O1.)(0.(19.$4.O2.(:.O5.+=8.)(:.(=.&40.Vsp,)-68.))(0.(19.$4.O2.Vlo,O5.)(0.(1:.$4.O2.)(0.(10.$4.O2.(:.(1;.(:.O5.+60.)+3.)(1<.(1=.VR,)))O6.)(0.(1>.$4.(1=.VR,)O2.Vslo,(:.O5.+60.))(0.(1>.$4.(1=.VR,)O2.(:.O5.+<0.)(=.&40.Vsp,))(0.(1?.$4.(1=.VR,)Vm,O2.(20.VR,)(:.O5.+60.))(0.(1?.$4.(1=.VR,)Vm,O2.(:.O5.+<0.)(=.&40.Vsp,))(21.$4.VR,VHIA,Vh,(22.VLB,VdX,)VLF,(=.&40.Vsp,)(=.&40.Vsp,)(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))Vm,O2.)))))))))))))))")
(* [comment removed for export] *).

  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L10376588162.10L15017612426.3 L18546069956.14L20870518615.6 L26892418956.1 L29098720600.3 L31021792691.6 L40281191306.3 L46434938305.3 L50790584144.8 L519294241.8   L52045659405.3 L55896549980.8 L5956688929.3  L62018535662.1 L63205382458.8 L66151427842.16L7538573601.8  L8931608776.1  00000W00c01V01g01k02302H02Q02V02m03L03X04504904<04Y05505T05YS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACPS2sp3sp13SP1S1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp13SP14HTOP1c2HcS3sp11a1n2Ha1x2HxS2spS2sp3sp1S1R3HIA1h2sp3TOP4HTOPS1R3HIA1hS3sp1S1R2sp2lo3LOS3SLO5NEEDES1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S2sp3sp13SP1S1R3HIA1h2sp3TOP3sp13SP14HTOPS2spS1RS1R3HIA1h2sp3TOP3sp13SP14HTOPS3sp12r04SP1M1q1r1H2H02q02H4S1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S3sp1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL"] Lemma embs_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PPC,(28.$12.)Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmq,P,(16.&40.)(2;.(16.&8.))PCH,(28.(23.$2.(28.$12.)))Ph',(29.$4.VR,VHIA,)PLB',(28.$2:.)Pm',P,(16.&40.)(2;.(16.&8.))PLBp,(28.$2:.)PW',(28.$2<.)P,(1.$17.(2=.R;.)#<.)P,(58.R<.R;.R:.R9.R8.R7.)P,(1:.$4.R5.)P,(19.$4.R6.Vlo,R=.)P,(2?.$4.VR,R6.VLF,R>.(20.VR,)(5.$4.VR,VHIA,Vh,)R5.R;.R7.)P,Pb,$2:.P,(30.$2:.R1.(22.VLB,VdX,))(30.$2:.R2.R9.)P,Pa,$2.Pn,$2.P,(8.(:.R12.+=8.)R2.)P,(8.(:.R3.R2.)(=.&40.Vsp,))(33.R;.R4.R3.)P,(54.(23.$2.(28.$12.))Lac,(23.$2.(28.$12.))(33.R9.(55.$2.(28.$12.)R1.)(59.(2=.(56.$2.(28.$12.)R1.))))R=.)PWE,(28.$2<.)PLBe,(28.$2:.)P,(2?.$4.VR,R1.VLF,(=.&40.Vsp,)(20.VR,)(5.$4.VR,VHIA,Vh,)R2.R11.R=.)P,Pb,$2:.P,(30.$2:.R1.(22.VLB,VdX,))(30.$2:.R2.R4.)P,Px,$2.P,(31.(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))R1.)(31.R6.R2.)P,(?.$4.VR,VHIA,R12.R11.VLF,R10.)(58.R19.R18.R13.R12.R11.R14.)")
(* [comment removed for export] *).
  Proof.
    intros PC sp1 hc LBc mq CH h' LB' m' LBp W' HPC EB MI' ST' HP KS DJH DJC WE LBe HPE KSe WS HH'.
    ddestruct EB as (SP1 & SP1M & HHq & SAVE & CHS & CHI & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    assert (CRS : forall a n, sp1 <= a -> client_range L (LBp ++ fdata LF) sp1 a n) by (intros a n Ha x Hx; left; clear - Ha Hx; lia).
    unfold EMBs. split; [exact SP1|]. split; [exact SP1M|]. split; [exact HH'|].
    split; [eapply (presA_rw_cells asegs R); [exact HP| exact SAVE| apply CRS; clear - SP1; lia| apply DJH; simpl_sizes; clear - SP1; lia]|].
    split. { rewrite Forall_forall in *. intros ac Hac. eapply (presA_rw_cells asegs R); [exact HP| exact (CHS ac Hac)| apply CRS; exact (proj1 (CHI ac Hac))| exact (DJC ac Hac)]. }
    split; [exact CHI|].
    split; [eapply (presA_stk asegs R); [exact HP| exact SThi| clear; lia| apply DJH; clear - SP1; lia]|].
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply (presA_shadow_cells_sh asegs R CS); [exact CSOK| | clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1 SLO NEEDE LOS ALO ACP; lia| exact HP| exact SHC|].
             - rewrite HPC. eapply crange_sub; [exact SCS0| clear - SP1 SLO NEEDE LOS; lia| clear - SP1 TOP HTOP; lia].
             - intros c Hc. left. rewrite HPC in Hc. clear - Hc SP1 SLO NEEDE LOS TOP HTOP. lia. }
    split; [eapply (presA_sshad asegs R); [exact HP| exact SSlo| exact SSL| clear - SP1 TOP HTOP; lia]|].
    split; [eapply (presA_sshad asegs R); [exact HP| exact SShi| clear - SP1 SLO NEEDE LOS; lia| clear - TOP HTOP; lia]|].
    split; [eapply (snapA_presA asegs R); [exact SNlo| exact HP| clear; lia| clear - SP1 TOP HTOP; lia]|].
    split; [eapply (snapA_presA asegs R); [exact SNhi| exact HP| clear - SP1 SLO NEEDE LOS; lia| clear - TOP HTOP; lia]|].
    eapply (presW_call asegs R HIA h); [exact PRES| exact HPE| exact KSe| intros b Hb; exact Hb| clear; lia| clear - SP1 SLO NEEDE LOS; lia| clear; lia| exact WS].
    all: match goal with |- ?g => idtac "EMBS-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02P0@D29720839482.169D39565106411.169D60189065437.169D66773894610.169D67132161033.169L11001591018.168L11001591018.169L14447004729.1  L1685717371.0   L24023900370.0  L26786418512.1  L29217191679.1  L29467392662.1  L35394346383.164L35653441506.7  L39021173840.1  L39953770108.164L41392044326.1  L42411609006.0  L50297546224.164L55145925024.1  L57698627611.2  L59310725461.2  L59778510703.164L60098763854.3  L63124129830.1  L7735748552.2   L881835912.0    L9356559676.11  P37490721692.169P37492742106.168P43689334159.168P43691311561.169P57713046236.169P7750690063.169 Q10147393908.169Q10149569842.168Q10149575540.169Q10795743881.166Q11745175873.168Q11747458311.169Q11757758971.161Q11801279589.169Q11984464272.165Q12386485516.165Q12855921464.166Q13757566536.168Q13847363207.165Q14344642822.169Q14346824454.169Q14346827072.168Q14360074768.168Q15502880852.168Q15504892946.169Q19266142736.165Q19684542039.168Q19686527505.169Q19688736493.161Q19902651425.169Q19904628839.168Q19904632353.169Q19958542126.166Q22567378950.169Q22569298438.169Q22569301056.168Q22712450012.169Q23927705296.169Q25511591557.169Q27396422419.165Q27882953602.169Q27998746771.169Q28000660693.168Q28465177121.166Q28543176864.168Q28545156326.169Q28972344821.169Q29744571393.165Q30450372056.165Q30892206990.169Q31080693520.165Q337601009.164  Q33901187717.168Q34111792263.165Q3419689062.169 Q34357517863.167Q34964695582.166Q34977521200.169Q35446334555.164Q35513210238.165Q35630459446.169Q3635788169.166 Q36478638430.169Q36480552216.168Q36480553822.169Q37763447218.168Q38023289336.165Q38431974391.165Q38947563736.166Q38948581247.165Q39180574961.169Q41293137210.160Q41310749089.169Q41313029025.169Q41313031655.168Q41524280297.165Q42439443119.169Q42439449833.168Q42441394351.169Q43149532678.169Q43433810408.165Q43502280779.166Q43523501813.166Q44032118377.165Q44457726048.165Q44899125339.166Q46069942980.166Q46466075430.165Q46541935337.165Q46598154214.168Q46652616699.165Q48117819565.168Q48119774443.169Q49698585326.167Q51087705995.169Q51182740981.169Q5129158642.169 Q51318020329.168Q52573706639.169Q5265442331.167 Q53115289716.160Q54481541667.167Q55415036769.169Q57035343601.169Q57037327601.169Q57037329079.168Q57230951818.169Q58125335435.169Q59564297645.168Q59566316011.169Q59582104521.168Q59582111119.169Q59584026511.169Q59865321072.169Q59865321526.168Q59867563120.169Q60755250510.168Q60757203208.169Q6186103236.169 Q62011970312.169Q64041402609.169Q64681458566.169Q64683667392.168Q64683667846.169Q67152440095.168Q67172579234.165Q7340652294.169 Q7843680142.169 Q7845954958.169 Q7845960648.168 Q930551778.168  00000g01`02Y03P04G05T06a06f06g06h06m07207707?07W07\07d07i07j08208708808?08G08Q08V08W08X09C09]0:70:P0:i0;F0;a0<=0<Y0=50=60=V0>60>J0>K0>P0?:0?D0?Z0?[0@10@G0@]0A30AZ0BA0BB0Bl0CV0D40D50D60D70DD0DZ0E00EF0Ea0F[0G90G>0G?0GX0H10H>0H[0I80Ij0Io0J40J50J:0Jd0Je0Jf0KF0Kb0LL0M60MV0M[0NM0NN0NO0NP0NQ0Ne0Nj0No0OO0OT0PH0PW0PX0PY0PZ0P_0Q?0Q]0R;0R<0RA0RB0RO0RT0RY0Rc0Rm0SM0SR0Sf0Sg0TU0UC0UQ0Ug0VQ0VR0Vf0W<0WJ0We0XK0Xh0YR0Z>0Zh0[T0[j0\@0\V0\l0]B0]X0]Y0]Z0][0^M0_?0__0`70`c0a_0b[0cY0cm0d20d30dI0da0e70eKS1R3HIA1h2sp3TOP3sp12h13SP13HT13SPR4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2sp3TOP3sp12h11T3SP13HT13SPR4SP1R2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp11T3SP13SPR4SP1R2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13SPR4SP1R2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13SPR4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp12h13SP13HT13SPR4SP1R2HB5Ha_st5Hl_st1x2HxS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp12h13SP13HT13SPR4SP1R2HB5Ha_st5Hl_st1x2HxS3sp1SSS3sp1S3sp1S3sp1S2sp3sp1S1R3HIA1h2sp2lo3TOP4HTOPS3sp1S2sp3sp1S3sp1SS2sp3sp1S3sp1FS1k3K16S2sp3sp1S1R2lo3LOSS3sp1FSS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS1R3slo3sp12HB5Ha_st5Hl_stS1R3slo3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS2sp3sp11T3SP12HB5Ha_st5Hl_stS2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS2sp2lo3sp12HB5Ha_st5Hl_st1TFS1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp13SP12HBFS3sp1S1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R3sp12HBS3sp11T2HB5Ha_st5Hl_stFS1R3sp12HB5Ha_st5Hl_stS3sp12HB5Ha_st5Hl_st1TS1R3sp12HB5Ha_st5Hl_stS3sp11T2HB5Ha_st5Hl_stS1R2sp3sp14SP1M3SPR4SP1R2HB5Ha_st5Hl_stS1R2sp3sp14SP1M3SPR4SP1R2HB5Ha_st5Hl_stFS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HBFFFS3sp14SP1R2HBS1R3sp12HB5Ha_st5Hl_stS3sp12HB5Ha_st5Hl_st1TS1R3sp12HB5Ha_st5Hl_stS2sp3sp13SP12HB5Ha_st5Hl_stS1R3HIA1h2sp3TOP3sp12h13SP13HT13HS15HTOP12HB5Ha_st5Hl_st1TS2sp2lo3sp13SP12HB5Ha_st5Hl_stS3sp1FS1R2sp3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS3sp14SP1R2HBS1R2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO2HB5Ha_st5Hl_stS3sp1S3sp1FS3sp1S1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stFFS2sp2lo3sp11T3SP12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS3sp1S1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO2HB5Ha_st5Hl_stFFFFS3sp12HB5Ha_st5Hl_stS3sp1S3sp1S1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS3sp1S1R2sp2lo3LOS3SLO5NEEDE3sp11T3SP13ALO2HB5Ha_st5Hl_stS2sp2lo3sp13SP1FFFS3sp1S1R3slo3SSL3sp12HB5Ha_st5Hl_st1TS1R3slo3SSL3sp12HB5Ha_st5Hl_stS1R3slo3SSL3sp12HB5Ha_st5Hl_stFS3sp1FS3sp14SP1R2HBS3sp1S3sp1S1R3sp12HBS1R3sp12HBS1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS3sp1S3sp12HB5Ha_st5Hl_stFS1R2sp2lo3LOS3SLO5NEEDE3sp13ALO2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13ALO2HB5Ha_st5Hl_stS3sp12HB5Ha_stS3sp11T2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stFS3sp12HB5Ha_st5Hl_stS3sp12HB5Ha_st5Hl_st1TS3sp12HB5Ha_stS1R2sp2lo3SLO5NEEDE3sp13SP1S1R2sp2lo3SLO5NEEDE3sp12HB5Ha_st5Hl_stS2sp3sp11T3SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_st1TS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp11T3SP12HB5Ha_st5Hl_stS3sp11T2HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS3sp12HB5Ha_st5Hl_st1TS1R3sp12HB5Ha_st5Hl_stFFFS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO2HB5Ha_st5Hl_stS2sp2lo3sp13SP12HB5Ha_st5Hl_st1TS1R3sp12HB5Ha_st5Hl_st1TS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_st1TS1R3HIA1h2sp3slo3TOP3sp12h13SP13HT13HS15HTOP12HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP3sp12h13SP13HT13HS15HTOP12HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP3sp12h13SP13HT13HS15HTOP12HB5Ha_st5Hl_st1TS3sp12HB5Ha_st5Hl_stS3sp1FS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_st1TS1R3sp12HB5Ha_st5Hl_stS3sp12HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL"] Lemma em_rr1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Ph1,(29.$4.VR,VHIA,)PLB1,(28.$2:.)Pm1,P,(16.&40.)(2;.(16.&8.))Psl1,(28.(16.&40.))PT,$2.Pyra,(16.&40.)Pyt0,(16.&40.)Pyt1,(16.&40.)Pyt2,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Pxs5,(16.&40.)Pyt3,(16.&40.)Pyt4,(16.&40.)Pyt5,(16.&40.)Pyt6,(16.&40.)P,(48.R16.R15.R14.R13.R12.)P,(5:.$2.Lv,$2.(5:.$2.Lf,$2.(4:.R18.R2.R1.)))P,(1.(2;.(16.&40.))(52.(16.&40.)R14.#6.)(53.(16.&40.)(27.&40.(49.(3?.VdN,)(3?.VdE,)))))P,(1.(2;.(16.&40.))(52.(16.&40.)R15.#7.)(53.(16.&40.)(27.&40.R14.)))P,(0.(8.=R15.)(34.R15.(5;.+2.+40.)))P,Pm2,P,(16.&40.)(2;.(16.&8.))PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pj4,(28.(16.&8.))Pzt0,(16.&40.)Pzt1,(16.&40.)Pzt2,(16.&40.)Pza1,(16.&40.)Pza2,(16.&40.)Pza3,(16.&40.)Pza4,(16.&40.)Pza5,(16.&40.)Pza6,(16.&40.)Pza7,(16.&40.)Pzt3,(16.&40.)Pzt4,(16.&40.)Pzt5,(16.&40.)Pzt6,(16.&40.)P,(58.$5<.R2=.R2<.R2;.R12.(11.(23.$2.(28.$12.))(24.$2.(28.$12.)R2=.(15.(16.&40.)$12.$13.R11.))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.R2=.+:0.)(11.$12.(13.(27.&40.=))(11.$12.(5=.(27.&40.+1.))(11.$12.(4>.#4.R?.)(14.$12.)))))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.R2=.+;0.)(15.(16.&40.)$12.$13.R10.))(14.(23.$2.(28.$12.)))))))P,(1.$17.(18.(16.&40.)R12.)#14.)P,(1.$17.(18.(16.&40.)R12.)#5.)P,(1.$17.(18.(16.&8.)R12.)#4.)P,(1.(2;.(16.&40.))(52.(16.&40.)R15.#5.)(53.(16.&40.)(27.&40.=)))P,(1.(2;.(16.&40.))(52.(16.&40.)R16.#6.)(53.(16.&40.)(27.&40.(49.(3?.VdN,)(3?.VdE,)))))P,(1.(2;.(16.&40.))(52.(16.&40.)R17.#7.)(53.(16.&40.)(27.&40.R2>.)))P,Pk,$17.P,(35.(1.$17.R1.#5.))P,(35.(1.$17.R2.#6.))P,(5>.R3.#14.)(1.(2;.(16.&40.))(52.(16.&40.)R1<.R4.)(52.(16.&40.)R34.R4.))P,(5?.(11.(23.$2.$2.)(24.$2.$2.R35.(:.R35.+=8.))(11.(23.$2.$2.)(24.$2.$2.(:.(1;.(:.R35.+60.)+3.)(1<.(1=.VR,)))(:.(:.(1;.(:.R35.+60.)+3.)(1<.(1=.VR,)))+<.))(14.(23.$2.$2.))))R32.R1:.)P,(60.$4.R33.R1;.)(41.$4.(42.$4.VR,VHIA,R36.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R31.(27.&40.R37.)Vgp,Vtp,R18.R17.R16.Vsp,(27.&40.=)(27.&40.(:.R37.+:0.))R15.R14.R13.R12.R11.R10.R?.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))R26.(27.&40.(49.(3?.VdN,)(3?.VdE,)))(27.&40.=)(27.&40.(:.(1;.(:.R37.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R>.R=.R<.R;.)VF,(27.&40.+:0:1<.)Vfc,(38.(16.&40.))R1<.(46.$4.)))(41.$4.(42.$4.VR,VHIA,R1;.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R16.(27.&40.R1<.)Vgp,Vtp,R15.R14.R13.Vsp,(27.&40.=)(27.&40.R17.)R12.R11.R10.R?.R>.R=.R<.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))R;.(27.&40.(49.(3?.VdN,)(3?.VdE,)))(27.&40.=)(27.&40.(:.(1;.(:.R1<.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R:.R9.R8.R7.)VF,(27.&40.+:0990.)Vfc,(38.(16.&40.))R19.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until yt6. (intros EB dd_H; ddestruct dd_H as (v1 & f1 & HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1); intros S6 S7 TR K).
    ddestruct EB as (SP1 & SP1M & HH1 & SAVE & SPILL & LSL & SThi & STlo & MI1 & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_ok asegs R HIA h1) as CSOK1.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA h1) as SCS01. pose proof (hm_top asegs R HIA h1 LB1 LF _ HH1) as HTOP1.
    rewrite HS1 in SCS01.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SCSc : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS01| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo) as KINV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    repeat (destruct sl1 as [|? sl1]; [discriminate LSL|]). destruct sl1; [| discriminate LSL]. clear LSL. cbn [map] in SPILL.
    cbn [nth_error] in S6, S7. injection S6 as ->. injection S7 as ->.
    chunk_split SPILL 20%nat CHA CHr. chunk_split CHr 2%nat CHR CHB.
    replace (sp1 + 160 + 16) with (sp1 + 176) in CHB by (clear; lia).
    apply rw_cells_CB_of in CHR; [| cbn; clear; lia]. cbn [cells_size csize Nat.add] in CHR.
    unfold EM_POISON in SHC.
    pose proof (munch_refl [(sp1, sp1 + 216); (Z.shiftr (sp1 + 96) 3 + al_sb AL, Z.shiftr (sp1 + 96) 3 + al_sb AL + 12)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep_to [657812]. zstep_to [657816]. zstep_to [657820]. zstep_to [657824]. zstep_to [657828]. zstep.
    (* [comment removed for export] *)
    zstep_to [657832]. zstep_to [657836]. zstep. zstep_to [657840]. zstep_to [657948].
    norm_b8 SHC.
    lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo sp1, H3 : HM _ _ _ h1 LB1 LF ?m2, H4 : stk asegs ?m2 (sp1 + 216) _ |- _ =>
      lazymatch type of CHA with rw_cells _ _ _ ?csA => lazymatch type of CHB with rw_cells _ _ _ ?csB =>
        let wsA := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) csA) in
        let wsB := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) csB) in
        eapply (K m2 wsA wsB);
          [ unfold EMBs; refine (conj SP1 (conj SP1M (conj H3 (conj SAVE (conj _ (conj _ (conj H4 (conj H2 (conj H1 (conj SHC (conj SSlo (conj SShi (conj SNlo (conj SNhi PRES))))))))))))));
            [ repeat (apply Forall_cons; [cbn [fst snd]; first [exact CHA| exact CHR| exact CHB]|]); apply Forall_nil
            | repeat (apply Forall_cons; [unfold chunk_in; cbn [fst snd cells_size csize map Nat.add]; clear; lia|]); apply Forall_nil ]
          | reflexivity | reflexivity | rewrite !length_skipn; cbn; reflexivity | reflexivity | reflexivity | reflexivity
          | intros k K5 K6 K16; do 20 (destruct k as [|k]; [first [reflexivity| exfalso; first [apply K5; reflexivity| apply K6; reflexivity]]|]); exfalso; clear - K16; lia
          | exact MU | exact WM ]
      end end end.
    all: match goal with |- ?g => idtac "RR1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30741553502.0 L66151427842.1600000100MSS3sp12r04SP1M1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="Type"] Lemma rr_null_at : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Pmq,P,(16.&40.)(2;.(16.&8.))PLBq,(28.$2:.)Psp1,$2.Pj4,(28.(16.&8.))P,(10.$4.R4.(:.R2.+:0.)(11.$12.(13.(27.&40.=))(11.$12.(5=.(27.&40.+1.))(11.$12.(4>.#4.R1.)(14.$12.)))))P,(1.$17.(18.(16.&8.)R2.)#4.)P,(1.$2.(>.R4.+20.)=)P,(34.=(:.R5.+:0.))(5:.(16.&40.)Lpad,(16.&40.)(4=.$4.R9.R8.(61.(:.R7.+:0.)+1.==(14.(16.&40.))R1.$3;.)))")
(* [comment removed for export] *).
  Proof.
    intros mq LBq sp1 j4 CHR LJ SP1M P0.
    ddestruct (bytes_as_u32s 1 j4 ltac:(rewrite LJ; reflexivity)) as (ws & EJ & LW).
    destruct ws as [|pad [|? ?]]; try discriminate LW.
    exists pad. eapply mpd_at_rebuild; [discriminate| | clear - SP1M; Z.div_mod_to_equations; lia| exact P0| reflexivity| unfold MPI_MAX_LIMBS; clear; lia| left; reflexivity| intros _; split; reflexivity| intros EH; discriminate EH].
    unfold mpi_cells. eapply rw_cells_reshape; [exact CHR| cbn; repeat split; try apply length_le2; try apply length_le4; try apply length_le8; exact I|].
    subst j4. cbn [cells_bytes cbytes app u32s flat_map]. rewrite ?app_nil_r.
    reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2414656577.1  L59308586248.2 L66151427842.1600000500;00WS3sp1S1i2HiS3sp12r04SP1M1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="Type"] Lemma rr_aobj : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Phq,(29.$4.VR,VHIA,)Pmq,P,(16.&40.)(2;.(16.&8.))Psp1,$2.P,(10.$4.R2.(:.(1;.(:.R1.+60.)+3.)(1<.(1=.VR,)))$5<.)P,(3<.(7.$4.VR,VHIA,R4.)(:.R2.+:0.)+10.)P,(1.$2.(>.R3.+20.)=)P,(8.=(:.R4.+60.))(62.$4.(1=.VR,)(7.$4.VR,VHIA,R7.)R6.(:.R5.+:0.)+10.)")
(* [comment removed for export] *).
  Proof.
    intros hq mq sp1 SHC CR SP1M P0.
    eapply (aobj_of_zero_shadow_sh asegs AL (hcs asegs R HIA hq) mq (sp1 + 96) EM_POISON_RR (sp1 + 160) 8 2);
      [exact (hcs_ok asegs R HIA hq)| exact SHC| exact CR| clear - SP1M; Z.div_mod_to_equations; lia| exact P0| clear; lia|].
    intros i Hi. destruct i as [|[|i]]; [reflexivity| reflexivity| exfalso; clear - Hi; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition XST (EX : list blk) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(0.(4=.$4.O2.O3.O1.)(0.(1.$2.(25.O1.)(25.VdX,))(0.(1.(16.&40.)(63.O1.)(63.VdX,))(0.(35.(1.$39.(3:.O1.)$64.))(0.(8.(3?.VdX,)(3?.O1.))(0.Pb,$2:.P,(30.$2:.R1.(65.O1.))(32.(30.$2:.R2.(65.VdX,))(51.VR,(22.VLB,VdX,)VLF,(55.$2.$2.R2.)(56.$2.$2.R2.)))(0.Pb,$2:.P,(30.$2:.R1.(65.O1.))(32.(30.$2:.R2.(65.VdX,))(35.(30.$2:.R2.VLB,)))(0.(62.$4.(1=.VR,)(7.$4.VR,VHIA,O4.)O2.(25.VdX,)+10.)(0.Pb,$2:.P,(30.$2:.R1.O3.)(32.(30.$2:.R2.VLB,)(32.(30.$2:.R2.(65.O1.))(30.$2:.R2.O5.)))(0.Pb,$2:.P,(30.$2:.R1.VLB,)P,(35.(30.$2:.R2.(65.VdX,)))(30.$2:.R3.O3.)(0.Pb,$2:.P,(30.$2:.R1.(65.VdX,))P,(30.$2:.R2.O3.)(1.(28.$2:.)(65.O1.)(65.VdX,))(0.Pb,$2:.P,(30.$2:.R1.O5.)(0.(30.$2:.R2.O3.)(0.(51.VR,VLB,VLF,(55.$2.$2.R2.)(56.$2.$2.R2.))(0.(35.(30.$2:.R2.(65.O1.)))(34.=(56.$2.$2.R2.)))))(66.$2:.O5.)))))))))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma keep_not_blk : forall LBq dq b, In b (mpd_keep LBq dq) -> ~ In b (mpd_blk dq).
  Proof.
    intros LBq dq b Hb. unfold mpd_keep in Hb. unfold mpd_blk. destruct (md_own dq); [intros []| | intros []].
    apply filter_In in Hb. destruct Hb as [_ Hne]. intros [E|[]]. rewrite <- E in Hne.
    unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
  Qed.

  #[using="Type"] Lemma blk_in_dec : forall (b : blk) (l : list blk), {In b l} + {~ In b l}.
  Proof. intros b l. apply in_dec. intros [a1 a2] [b1 b2]. destruct (Z.eq_dec a1 b1) as [->|N1]; [destruct (Z.eq_dec a2 b2) as [->|N2]; [left; reflexivity| right; intros E; injection E as E; exact (N2 E)]| right; intros E; injection E as E _; exact (N1 E)]. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59315284336.400000:S1B1j2Hj1Q". (* [comment removed for export] *)
  #[using="Type"] Lemma fresh_not_in : forall LBq (b : blk), fresh_apart R LBq LF (fst b) (snd b) -> 0 < snd b -> ~ In b LBq.
  Proof. (intros LBq [B j] dd_H; ddestruct dd_H as (_ & _ & _ & F3); intros Hj Hb). cbn [fst snd] in *. pose proof (F3 B j ltac:(apply in_app_iff; left; exact Hb)) as Q. clear - Q Hj. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma xst_keep : forall EX hc LBc mc dXc b, XST EX hc LBc mc dXc -> In b KEEP -> In b (mpd_keep LBc dXc).
  Proof.
    (intros EX hc LBc mc dXc b dd_H; ddestruct dd_H as (_ & _ & _ & _ & _ & _ & FRS & _ & _ & O4 & _); intros Hb).
    pose proof (In_mpd_keep _ _ _ Hb) as HbL. pose proof (keep_not_blk _ _ _ Hb) as HbN.
    apply In_mpd_keep_intro; [exact (O4 b HbL HbN)|]. intros Hc. destruct (FRS b Hc) as [Q|Q]; [exact (HbN Q)| exact (Q HbL)].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L24166965860.1000004S2dX". (* [comment removed for export] *)
  #[using="h m sp lo MX0 NSX XL0"] Lemma xst_start : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PEX,(28.$2:.)P,(4=.$4.R2.R3.VdX,)P,(62.$4.(1=.VR,)(7.$4.VR,VHIA,R5.)R3.(25.VdX,)+10.)P,Pb,$2:.P,(30.$2:.R1.R6.)(32.(30.$2:.R2.VLB,)(30.$2:.R2.R5.))P,Pb,$2:.P,(30.$2:.R1.VLB,)(30.$2:.R2.R8.)P,Pb,$2:.P,(30.$2:.R1.R6.)(0.(30.$2:.R2.R9.)(0.(51.VR,VLB,VLF,(55.$2.$2.R2.)(56.$2.$2.R2.))(34.=(56.$2.$2.R2.))))P,(66.$2:.R6.)(67.R7.R:.R9.R8.VdX,)")
(* [comment removed for export] *).
  Proof.
    intros hc LBc mc EX MXc OXc I1 I2 I3 NDE. unfold XST.
    split; [exact MXc|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact NSX|]. split; [clear; lia|].
    split; [intros b Hb; left; exact Hb|]. split; [intros b Hb; left; exact Hb|]. split; [exact OXc|].
    split; [intros b Hb; destruct (I1 b Hb) as [Q|Q]; [left; exact Q| right; right; exact Q]|].
    split; [intros b Hb _; exact (I2 b Hb)|]. split; [intros b _ _; reflexivity|]. split; [| exact NDE].
    intros b Hb. ddestruct (I3 b Hb) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|]. split; [| exact Q3].
    intros Hc. apply (fresh_not_in _ _ Q2 Q3). pose proof MX0 as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hc. destruct (md_own dX); try (destruct Hc; fail).
    destruct Hc as [<-|[]]. exact (proj1 (proj2 OW)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L32376998569.5L59315284336.4L6034577831.8 00000B00L00dS2dX3dXc3dX'2NM2BNS1B1j2Q41QS1R3HIA1h2sp3SPc3HSP1a1S". (* [comment removed for export] *)
  #[using="h lo NSX XW XL0"] Lemma xst_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PEX,(28.$2:.)Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.Ph',(29.$4.VR,VHIA,)PLB',(28.$2:.)Pm',P,(16.&40.)(2;.(16.&8.))PdX',$68.PSPc,$2.P,(67.R:.R9.R8.R7.R6.)P,(8.R2.(=.&40.Vsp,))P,(8.(20.VR,)R3.)P,(2?.$4.VR,(22.R;.R9.)VLF,R4.(20.VR,)(5.$4.VR,VHIA,R<.)(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))R:.R6.)P,Px,$2.P,(7.$4.VR,VHIA,R>.R1.)(7.$4.VR,VHIA,R;.R2.)P,(4=.$4.R8.R9.R7.)P,(69.R>.R<.R:.R8.)P,(6:.R?.R=.R9.)P,Pb,$2:.P,(30.$2:.R1.(65.R;.))(32.(30.$2:.R2.(65.R10.))(51.VR,(22.R12.R10.)VLF,(55.$2.$2.R2.)(56.$2.$2.R2.)))(67.R13.R>.R=.R<.R;.)")
(* [comment removed for export] *).
  Proof.
    intros EX hc LBc mc dXc h' LB' m' dX' SPc J HSP HSL HP HCS' MX' OUT' BK FRA'.
    pose proof (fun b => xst_keep EX hc LBc mc dXc b J) as KK.
    ddestruct J as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE).
    ddestruct OUT' as (OA & ONS & P3 & P4 & P5). ddestruct BK as (BA & BP & BF & BN).
    destruct XW as [CW DXP]. pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
    unfold XST. split; [exact MX'|]. split; [rewrite OA; exact AD|]. split; [rewrite BP; exact PD|]. split; [exact ONS|]. split; [clear - NM BN; lia|].
    split. { intros b Hb. destruct (FRA' b Hb) as [Q|Q]; [exact (FRA b Q)| right; eapply fresh_apart_blocks_mono; [exact Q| exact KK]]. }
    split. { intros b Hb. destruct (BF b Hb) as [Q|Q]; [exact (FRS b Q)|]. destruct (blk_in_dec b (mpd_blk dX)) as [I|NI]; [left; exact I| right; intros HL; exact (Q (O4 b HL NI))]. }
    split. { eapply aobj_cs_mono; [exact HCS'|]. eapply (presA_aobj asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP| exact OXc| | exact HSL| intros x Hx; eapply hcs_below_top; exact Hx].
             intros a Ha. destruct (CWk a Ha) as [S|[D|([q k] & Hq & Rq)]]; [left; clear - S HSP; lia| right; left; exact D| right; right].
             exists (q, k). split; [| exact Rq]. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left; exact (KK _ Hq)| right; exact Hq]. }
    split. { intros b Hb. destruct (P3 b Hb) as [Q|Q]; [| right; left; exact Q]. destruct (O3 b Q) as [Q1|[Q1|Q1]]; [left; exact Q1| | right; right; exact Q1].
             right; left. rewrite (P5 b Q1 Hb). exact Q1. }
    split. { intros b Hb NI. apply P4; [exact (O4 b Hb NI)|]. intros Hc. destruct (FRS b Hc) as [Q|Q]; [exact (NI Q)| exact (Q Hb)]. }
    split. { intros b Hb Hb'. destruct (P3 b Hb') as [Q|Q].
             - pose proof (O5 b Hb Q) as E5. rewrite <- E5. apply (P5 b); [rewrite E5; exact Hb| exact Hb'].
             - unfold mpd_blk in *. destruct (md_own dX'), (md_own dX); try (destruct Q; fail); try (destruct Hb; fail). destruct Q as [<-|[]]. destruct Hb as [<-|[]]. reflexivity. }
    split; [| exact NDE].
    intros b Hb. ddestruct (OEX b Hb) as (Q1 & Q2 & Q3 & Q4). split; [exact (P4 b Q1 Q3)|]. split; [exact Q2|]. split; [| exact Q4].
    intros Hc. destruct (FRA' b Hc) as [Q|(_ & _ & _ & F3)]; [exact (Q3 Q)|].
    destruct b as [B j]. cbn [fst snd] in *. pose proof (F3 B j ltac:(apply in_app_iff; left; apply In_mpd_keep_intro; [exact Q1| exact Q3])) as Q. clear - Q Q4. lia.
    all: match goal with |- ?g => idtac "XSTCALL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EMJ (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc dRc : mpd) (slA slB ts : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(0.(58.$5<.O:.O8.O7.O6.(11.(23.$2.(28.$12.))(24.$2.(28.$12.)O:.(15.(16.&40.)$12.$13.O3.))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.O:.+;0.)(15.(16.&40.)$12.$13.O2.))(14.(23.$2.(28.$12.))))))(0.(1.$17.(18.(16.&40.)O3.)#14.)(0.(1.$17.(18.(16.&40.)O2.)#5.)(0.(67.(11.(23.$2.$2.)(24.$2.$2.O9.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(65.O4.))O8.O7.O6.O5.)(0.(4=.$4.O6.O7.O4.)(0.(1.$2.(25.O4.)(:.O:.+:0.))(0.(35.(1.$39.(3:.O4.)$64.))(0.(6;.$4.O6.O9.O1.)(0.(1.$2.(59.(18.(16.&40.)O1.))(49.(3?.VdN,)(3?.VdE,)))(0.(8.(49.(3?.VdN,)(3?.VdE,))+>:60.)(1.$2.(>.O9.+10.)=)))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L24166965860.1L38948636245.0L48132467214.7L9144082496.1 00000400500P00TS2dXSS1R2sp2lo3LOS3SLO5NEEDE3ALOS2dX". (* [comment removed for export] *)
  #[using="HIA h sp lo LOS SLO NEEDE XW"] Lemma x_vs_fresh : forall N k, fresh_apart R KEEP LF N k -> 0 < k -> N + k <= X \/ X + 16 <= N.
  Proof.
    intros N k HF Hk. destruct XW as [CW DXP]. pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
    pose proof (art_lo asegs R HIA) as ALO.
    destruct (fresh_apart_client R KEEP LF (bv_unsigned sp) X 16 N k HF) as [Q|Q]; [| clear; lia| exact Hk| clear - ALO LOS SLO NEEDE; lia| left; exact Q| right; exact Q].
    eapply client_range_inside; [exact CWk| intros b Hb; exact Hb| clear; lia| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L21220692068.9L860202308.9  00000L00jS1R3HIA1h2hc1v2h'2dv3HV13HV'S1R3HIA1h2hc1f2h'2df4HFR14HFR'". (* [comment removed for export] *)
  #[using="Type"] Lemma hrel_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Phc,(29.$4.VR,VHIA,)Pv,$2.Pf,$2.Ph',(29.$4.VR,VHIA,)Pdv,$2.Pdf,$2.P,(4:.R6.R5.R4.)P,(1.$2.(3.$4.VR,VHIA,R4.)(3.$4.VR,VHIA,R7.))P,(1.$2.(5.$4.VR,VHIA,R5.)(5.$4.VR,VHIA,R8.))P,(1.$2.(6.$4.VR,VHIA,R6.)(6.$4.VR,VHIA,R9.))P,Px,$2.P,(7.$4.VR,VHIA,R;.R1.)(7.$4.VR,VHIA,R9.R2.)P,(8.(9.$4.VR,VHIA,R8.)(:.(9.$4.VR,VHIA,R;.)R7.))P,(8.(;.$4.VR,VHIA,R9.)(:.(;.$4.VR,VHIA,R<.)R7.))(4:.R:.(:.R<.R9.)(:.R;.R8.))")
(* [comment removed for export] *).
  Proof.
    (intros hc v f h' dv df dd_H; ddestruct dd_H as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1); intros HT' HS' HF' HCS' HV' HFR'). unfold HREL.
    split; [rewrite HT'; exact HT1|]. split; [rewrite HS'; exact HS1|]. split; [rewrite HF'; exact HF1|].
    split; [intros x Hx; exact (HCS' x (HCS1 x Hx))|]. split; [clear - HV1 HV'; lia| clear - HFR1 HFR'; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L1540877545.3  L16468080934.9 L21474879437.1 L21602859321.3 L23615739305.3 L23898603878.1 L24459976397.1 L29919900381.13L31466573843.5 L33571791132.7 L35513731400.1 L46518800544.9 L61887524866.9 L62018535662.1 L67028235242.8 00000<00^00c00m01701:01?01k02:02N02S03503W03Z049S2sp3sp13SP1S1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1S3dRcS2dX3dRc1QS1R3HIA2hcS1TS3dRcS1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP11a1n2H12H2S2dE2dN1T2ts2TLS2dX2dE2dN1T2ts2TL1QS3sp1S1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1S1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1S1RS1R2sp2lo3LOS3SLO5NEEDE3sp13SP1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL DSX NSX XW XL0"] Lemma emj_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Ph',(29.$4.VR,VHIA,)PLB',(28.$2:.)Pm',P,(16.&40.)(2;.(16.&8.))PdX',$68.Pdv,$2.Pdf,$2.P,(6<.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)P,(4:.R11.R9.R8.)P,(1:.$4.R6.)P,(19.$4.R7.Vlo,R15.)P,(2?.$4.VR,(22.R13.R11.)VLF,R16.(20.VR,)(5.$4.VR,VHIA,R14.)(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))R12.R8.)P,(1.$2.(3.$4.VR,VHIA,R;.)(3.$4.VR,VHIA,R15.))P,(1.$2.(5.$4.VR,VHIA,R<.)(5.$4.VR,VHIA,R16.))P,(1.$2.(6.$4.VR,VHIA,R=.)(6.$4.VR,VHIA,R17.))P,Px,$2.P,(7.$4.VR,VHIA,R19.R1.)(7.$4.VR,VHIA,R10.R2.)P,(8.(9.$4.VR,VHIA,R?.)(:.(9.$4.VR,VHIA,R19.)R;.))P,(8.(;.$4.VR,VHIA,R10.)(:.(;.$4.VR,VHIA,R1:.)R;.))P,(?.$4.VR,VHIA,R11.R10.VLF,R?.)P,(4=.$4.R10.R11.R?.)P,(69.R1<.R1:.R12.R10.)P,(6:.R1=.R1;.R11.)P,Pb,$2:.P,(30.$2:.R1.(65.R13.))(32.(30.$2:.R2.(65.R1>.))(51.VR,(22.R20.R1>.)VLF,(55.$2.$2.R2.)(56.$2.$2.R2.)))(0.(6<.R22.R21.R16.R15.R14.R13.R1<.R1;.R1:.R19.)(4:.R16.(:.R18.R12.)(:.R17.R11.)))")
(* [comment removed for export] *).
  Proof.
    (intros sp1 T hc LBc mc dXc dRc slA slB ts v f h' LB' m' dX' dv df dd_H; ddestruct dd_H as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB); intros HR MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' MX' OUT' BK FRA').
    split; [| eapply hrel_step; eassumption].
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (fun b => xst_keep _ hc LBc mc dXc b J) as KK.
    dpose J as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE).
    dpose EB as (SP1 & SP1M & HHc & _ & _ & _ & _ & _ & MIc & _).
    pose proof (art_lo asegs R HIA) as ALO.
    assert (EXK : forall b, In b ((T, WL * 4) :: mpd_blk dRc) -> In b (mpd_keep LBc dXc)).
    { intros b Hb. ddestruct (OEX b Hb) as (Q1 & _ & Q3 & _). apply In_mpd_keep_intro; assumption. }
    assert (EXX : forall b, In b ((T, WL * 4) :: mpd_blk dRc) -> fst b + snd b <= X \/ X + 16 <= fst b).
    { intros b Hb. ddestruct (OEX b Hb) as (_ & Q2 & _ & Q4). apply x_vs_fresh; [apply fresh_apart_keep; exact Q2| exact Q4]. }
    unfold EMJ.
    split. { eapply embs_call with (LBp := mpd_keep LBc dXc) (W' := [(X, X + 16)]) (WE := [(X, X + 16)]) (LBe := mpd_keep LBc dXc);
               [reflexivity| exact EB| exact MI'| exact ST'| rewrite <- HS1; exact HP| exact KK| | | | exact KK| intros x Hx; exact Hx| exact HH'].
             - intros a n H1 H2. cbn [disjoint_from]. split; [clear - H1 H2 DSX SP1 SLO NEEDE; lia| exact I].
             - apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd disjoint_from]; rewrite cells_size_map_C8, ?LA, ?LBl; (split; [clear - DSX SP1 SLO NEEDE; lia| exact I]).
             - rewrite <- HS1. eapply presA_weaken; [exact HP| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    split; [exact LA|]. split; [exact LBl|].
    split. { eapply (xst_call _ hc LBc mc dXc h' LB' m' dX' sp1); [exact J| clear - SP1; lia| clear - SP1 SLO NEEDE LOS; lia| exact HP| exact HCS'| exact MX'| exact OUT'| exact BK| exact FRA']. }
    ddestruct OUT' as (_ & _ & _ & P4 & _).
    split. { eapply (mpd_at_heap_presx asegs L mc m' LBc (mpd_keep LBc dXc ++ fdata LF) LB' sp1 [(X, X + 16)] dRc);
               [exact MR| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP)| exact MIc| exact MI'| rewrite AR; apply client_range_stack; clear; lia| | | |].
             - intros EH. eapply client_range_block; [apply in_or_app; left; apply EXK; right; unfold mpd_blk; rewrite EH; left; reflexivity| clear; lia| clear; lia].
             - rewrite AR. cbn [disjoint_from]. split; [clear - DSX SP1 SLO NEEDE; lia| exact I].
             - intros EH. pose proof (EXX (md_p dRc, 4 * md_n dRc) ltac:(right; unfold mpd_blk; rewrite EH; left; reflexivity)) as Q. cbn [fst snd] in Q.
               cbn [disjoint_from]. split; [clear - Q; lia| exact I].
             - intros b Hb. ddestruct (OEX b (or_intror Hb)) as (Q1 & _ & Q3 & _). exact (P4 b Q1 Q3). }
    split; [exact AR|]. split; [exact NSR|]. split; [| split; [exact TL| exact WLB]].
    eapply u32arr_of_cells; [| reflexivity].
    eapply (presA_rw_cells asegs R); [exact HP| apply u32arr_cells; exact TA| |].
    - cbn [cells_size csize]. rewrite Nat.add_0_r. eapply client_range_block; [apply in_or_app; left; apply EXK; left; reflexivity| clear; lia| clear - TL; lia].
    - cbn [cells_size csize]. rewrite Nat.add_0_r. pose proof (EXX (T, WL * 4) (or_introl eq_refl)) as Q. cbn [fst snd] in Q.
      cbn [disjoint_from]. split; [clear - Q TL; lia| exact I].
    all: match goal with |- ?g => idtac "EMJCALL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  #[using="Type"] Lemma nodup_fst : forall (l : list blk) a x y, List.NoDup (map fst l) -> In (a, x) l -> In (a, y) l -> x = y.
  Proof.
    induction l as [|[c j] r IH]; cbn; intros a x y ND Hx Hy; [destruct Hx|]. inversion ND as [|? ? NI ND']; subst.
    destruct Hx as [Ex|Hx]; destruct Hy as [Ey|Hy].
    - congruence.
    - injection Ex as -> ->. exfalso. apply NI. apply (in_map fst) in Hy. exact Hy.
    - injection Ey as -> ->. exfalso. apply NI. apply (in_map fst) in Hx. exact Hx.
    - exact (IH a x y ND' Hx Hy).
  Qed.
  #[using="Type"] Lemma lb_remove_not : forall A (l : list blk) b, List.NoDup (map fst l) -> In b (lb_remove A l) -> fst b <> A.
  Proof.
    induction l as [|c r IH]; cbn; intros b ND Hb; [destruct Hb|]. inversion ND as [|? ? NI ND']; subst.
    destruct (Z.eqb_spec (fst c) A) as [E|NE].
    - intros Eb. apply NI. rewrite E, <- Eb. apply in_map. exact Hb.
    - destruct Hb as [<-|Hb]; [exact NE| exact (IH b ND' Hb)].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L38569812941.1L41886271693.1L44753866840.4L53639754160.4L6034577831.8 00000500:00E00P00hS3dXcS3dXcS2dX1B1k2BXS1B1k3dXc1QS1R3HIA1h2sp3SPc3HSP1a1S". (* [comment removed for export] *)
  #[using="h lo LOS SLO NEEDE XW HND"] Lemma xst_free : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PEX1,(28.(23.$2.$2.))PB,$2.Pk,$2.PEX2,(28.(23.$2.$2.))Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.Ph',(29.$4.VR,VHIA,)Pm',P,(16.&40.)(2;.(16.&8.))PSPc,$2.P,(67.(6=.(23.$2.$2.)R;.(11.(23.$2.$2.)(24.$2.$2.R:.R9.)R8.))R7.R6.R5.R4.)P,(?.$4.VR,VHIA,R8.R7.VLF,R6.)P,(1:.$4.R7.)P,(1:.$4.R5.)P,(8.R5.(=.&40.Vsp,))P,(8.(20.VR,)R6.)P,(2?.$4.VR,(6>.R10.R<.)VLF,R7.(20.VR,)(5.$4.VR,VHIA,R=.)(11.(23.$2.$2.)(24.$2.$2.R10.(:.R10.R?.))(14.(23.$2.$2.)))R;.R8.)P,Px,$2.P,(7.$4.VR,VHIA,R?.R1.)(7.$4.VR,VHIA,R<.R2.)(67.(6=.(23.$2.$2.)R13.R10.)R;.(6>.R12.R>.)R:.R<.)")
(* [comment removed for export] *).
  Proof.
    intros EX1 B k EX2 hc LBc mc dXc h' m' SPc J HHc MIc MI' HSP HSL HP HCS'.
    pose proof (fun b => xst_keep _ hc LBc mc dXc b J) as KK.
    ddestruct J as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE).
    pose proof (HND _ _ _ _ HHc) as ND. destruct (hm_apart asegs R HIA hc LBc LF mc HHc) as [_ BA0]. pose proof (blocks_apart_app_l _ _ BA0) as BA.
    ddestruct (OEX (B, k) ltac:(apply in_or_app; right; left; reflexivity)) as (BIN & BFR & BNX & BK0). cbn [fst snd] in BFR, BK0.
    assert (KEEPR : forall b, In b LBc -> b <> (B, k) -> In b (lb_remove B LBc)).
    { intros [c j] Hb NEb. apply In_lb_remove_keep; [exact Hb|]. intros ->. apply NEb. f_equal. exact (nodup_fst LBc B j k ND Hb BIN). }
    assert (KR : forall b, In b KEEP -> In b (lb_remove B LBc)).
    { intros b Hb. pose proof (In_mpd_keep _ _ _ Hb) as HbL. apply KEEPR; [exact (In_mpd_keep _ _ _ (KK b Hb))|]. intros ->. exact (fresh_not_in LB (B, k) BFR BK0 HbL). }
    destruct XW as [CW DXP]. pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
    assert (CRX : client_range L (lb_remove B LBc ++ fdata LF) SPc X 16).
    { intros a Ha. destruct (CWk a Ha) as [S|[D|([q j] & Hq & Rq)]]; [left; clear - S HSP; lia| right; left; exact D| right; right].
      exists (q, j). split; [| exact Rq]. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left; exact (KR _ Hq)| right; exact Hq]. }
    pose proof (x_vs_fresh B k (fresh_apart_keep R LB LF dX B k BFR) BK0) as BX.
    unfold XST.
    split. { eapply (mpd_at_heap_presx asegs L mc m' LBc (lb_remove B LBc ++ fdata LF) (lb_remove B LBc) SPc [(B, B + k)] dXc);
               [exact MXc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP)| exact MIc| exact MI'| rewrite AD; exact CRX| | | |].
             - intros EH. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & XIN & _).
               eapply client_range_block; [apply in_or_app; left; apply KEEPR; [exact XIN| intros E; apply BNX; rewrite <- E; unfold mpd_blk; rewrite EH; left; reflexivity]| clear; lia| clear; lia].
             - rewrite AD. cbn [disjoint_from]. split; [clear - BX; lia| exact I].
             - intros EH. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (N1 & XIN & _).
               assert (NEB : md_p dXc <> B).
               { intros E. apply BNX. unfold mpd_blk. rewrite EH. left. rewrite E. f_equal. rewrite E in XIN. exact (nodup_fst LBc B _ _ ND XIN BIN). }
               pose proof (blocks_apart_in2 LBc _ _ _ _ BA XIN BIN NEB) as Q. cbn [disjoint_from]. split; [clear - Q; lia| exact I].
             - intros b Hb. apply KEEPR; [| intros ->; exact (BNX Hb)]. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hb. destruct (md_own dXc); try (destruct Hb; fail).
               destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)). }
    split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|]. split; [exact FRA|]. split; [exact FRS|].
    split. { eapply aobj_cs_mono; [exact HCS'|]. eapply (presA_aobj asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP| exact OXc| exact CRX| exact HSL| intros x Hx; eapply hcs_below_top; exact Hx]. }
    split. { intros b Hb. pose proof (lb_remove_not B LBc b ND Hb) as NEb. destruct (O3 b (In_lb_remove _ _ _ Hb)) as [Q|[Q|Q]]; [left; exact Q| right; left; exact Q| right; right].
             apply in_app_iff in Q. apply in_app_iff. destruct Q as [Q|[Q|Q]]; [left; exact Q| exfalso; apply NEb; rewrite <- Q; reflexivity| right; exact Q]. }
    split. { intros b Hb NI. apply KEEPR; [exact (O4 b Hb NI)|]. intros ->. exact (fresh_not_in LB (B, k) BFR BK0 Hb). }
    split. { intros b Hb Hb'. exact (O5 b Hb (In_lb_remove _ _ _ Hb')). }
    split; [| eapply List.NoDup_remove_1; exact NDE].
    intros b Hb. assert (Hb' : In b (EX1 ++ (B, k) :: EX2)) by (apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]).
    ddestruct (OEX b Hb') as (Q1 & Q2 & Q3 & Q4). split; [| split; [exact Q2| split; [exact Q3| exact Q4]]].
    apply KEEPR; [exact Q1|]. intros ->. exact (List.NoDup_remove_2 _ _ _ NDE Hb).
    all: match goal with |- ?g => idtac "XSTFREE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L22946302800.4 L25498419105.2 L26892418956.1 L28816784755.3 L28857505470.11L49799904432.3 L52101693566.12L56658999053.1 L60657453715.2 L66151427842.16L696052593.2   00000;00B00F00O01501A01j01n02402N02VS1R3HIA1h1QS1d3CAPS2spS1R3HIA1hS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP4HTOPS2sp3sp13SP1S1R3HIA1h2sp2dX2lo3LOS3SLO5NEEDE3XLO1a2HaS2spS2s01QS2sp2r03SPA1q1r1H2H02q02H4S2sp3SPR". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SPA UW0 UWX"] Lemma embs_uwc : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PPC,(28.$12.)Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmq,P,(16.&40.)(2;.(16.&8.))PCH,(28.(23.$2.(28.$12.)))P,(58.R6.R5.R4.R3.R2.R1.)(47.$4.R3.(20.VR,)(5.$4.VR,VHIA,Vh,)(=.&40.Vsp,)R6.(:.Vd,+1.))")
(* [comment removed for export] *).
  Proof.
    (intros PC sp1 hc LBc mq CH dd_H; ddestruct dd_H as (SP1 & SP1M & HHq & SAVE & CHS & CHI & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES)).
    destruct UWX as [[XLO D0]|CAP]; [| apply uwc_cap; clear - CAP; lia].
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (T64 : hstkhi asegs R HIA h <= 2^64).
    { destruct CSOK as (C1 & _). assert (CSt : CS (hstkhi asegs R HIA h - 1)).
      { replace (hstkhi asegs R HIA h - 1) with (arl_stklo R + (hstkhi asegs R HIA h - 1 - arl_stklo R)) by (clear; lia). apply SCS0. clear - HTOP TOP SLO NEEDE LOS SPR. lia. }
      pose proof (proj1 (C1 _ CSt)) as Q. clear - Q. lia. }
    assert (UWm : uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES)| exact UW0| clear; lia| | clear - SPR; lia| exact T64].
      intros a Ha. cbn [outside]. split; [clear - Ha XLO LOS SLO NEEDE; lia| exact I]. }
    chunk_split SAVE 11%nat SVa SVb. chunk_split SVb 1%nat SVs SVr.
    replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SVs by (clear; lia).
    eapply (uwc_frame asegs mq _ _ (bv_unsigned sp) sp1 (bv_unsigned s0) d); [clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia
      | pose proof (bv_unsigned_in_range 64 s0) as Q; unfold bv_modulus in Q; cbn [Z.pow Z.of_N Pos.pow] in Q; clear - Q; lia| exact D0| | exact UWm].
    rewrite Z_to_bv_bv_unsigned. exact (proj1 SVs).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis MPIFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Variable SZB : Z.
  Hypothesis RRX : forall r dX', -2^31 < r <= 0 -> binop_keep LB dX dX' -> md_n dX' <= SZB -> Rr r dX'.
  Hypothesis BUDT : havol asegs R HIA h + PHI <= AVOL_MAX.
  Hypothesis BUDFT : hfr asegs R HIA h + FR <= FR_MAX.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L12528839134.2L41943888700.600000800MS3dXc2N1S1R2lo3LOS3dXc3ALO2BL". (* [comment removed for export] *)
  #[using="LOS"] Lemma xst_final : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.P,(67.(14.$2:.)R4.R3.R2.R1.)P,(?.$4.VR,VHIA,R5.R4.VLF,R3.)(0.(69.VLB,VdX,R5.R3.)(0.(6:.VLB,VdX,R3.)(0.(3<.(7.$4.VR,VHIA,R6.)(25.VdX,)+10.)P,(35.(1.$39.(3:.R3.)$3;.))(0.(3<.(7.$4.VR,VHIA,R7.)(3=.R4.)(3>.+4.(3?.R4.)))(0.(34.=(3?.R4.))(32.(8.(:.(3=.R4.)(3>.+4.(3?.R4.)))Vlo,)(8.(=.&40.Vsp,)(3=.R4.))))))))")
(* [comment removed for export] *).
  Proof.
    (intros hc LBc mc dXc dd_H; ddestruct dd_H as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE); intros HHc).
    pose proof (art_lo asegs R HIA) as ALO.
    split. { unfold mpd_out. split; [exact AD|]. split; [exact NS|]. split; [| split; [exact O4| exact O5]].
             intros b Hb. destruct (O3 b Hb) as [Q|[Q|[]]]; [left; exact Q| right; exact Q]. }
    split; [unfold binop_keep; split; [exact AD|]; split; [exact PD|]; split; [exact FRS| exact NM]|].
    split; [exact (aobj_crange _ _ _ _ _ _ OXc)|].
    intros NN. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _].
    destruct (md_own dXc) eqn:EO; [exfalso; exact (NN eq_refl)| | exfalso; exact (NS eq_refl)].
    ddestruct OW as (N1 & HIN & _).
    pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc (md_p dXc) (4 * md_n dXc) ltac:(apply in_or_app; left; exact HIN)) as BL.
    split; [exact (aobj_crange _ _ _ _ _ _ (hm_aobj_block asegs R HIA hc LBc LF mc _ _ HHc HIN))|]. split; [clear - N1; lia|].
    left. clear - BL ALO LOS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01M0@L1685717371.0   L19774174584.1  L24023900370.0  L29038974481.4  L29533097009.9  L29539388977.8  L29916034296.2  L35653441506.7  L38948636245.0  L39188636933.0  L39332637397.0  L40622469209.2  L41931188542.8  L42411609006.0  L42565789183.1  L5832837669.4   L60098763854.3  L64052154934.7  L7142300770.4   L8171953640.209 L9356559676.11  P37490721692.209P37492742106.208P43689334159.208P43691311561.209P55506762762.209Q10147393908.209Q10149569842.208Q10795743881.207Q11745175873.209Q11747458311.209Q11757758971.202Q11799361125.209Q11801272867.208Q12390505713.205Q12855921464.206Q14344642822.209Q14346827072.208Q15502880852.208Q15502880852.209Q15504892946.209Q19684542039.209Q19686527505.209Q19688736493.202Q19735397569.206Q19902651425.209Q19904628839.208Q20354162744.206Q22567378950.209Q22569301056.208Q27396422419.205Q27998746771.209Q28000660693.209Q28543176864.209Q28545156326.209Q30450372056.205Q34111792263.205Q34357517863.208Q34964695582.207Q350074892.206  Q35433938342.206Q3635788169.207 Q36478638430.209Q36480552216.208Q38947563736.207Q41293137210.201Q41310749089.209Q41313031655.208Q42439449833.208Q42441394351.209Q43502280779.206Q44899125339.206Q46069942980.206Q46462063323.205Q48117819565.209Q48119774443.209Q50468654075.206Q53115289716.201Q54481541667.208Q57035343601.209Q57037329079.208Q59564297645.209Q59566316011.209Q59582104521.208Q59584026511.209Q59865321526.208Q59867563120.209Q60755250510.209Q60757203208.209Q64681458566.209Q64683667392.208Q67172579234.205Q67655581346.20500000100600700C00D00]00e01=01>01?01@01G01`01a01f02502?02Z02g04C04n05W06@06h07P07Q08<08g08h09W0:F0:i0;N0<30<l0=E0=j0>O0?E0@;0A10Aj0Bc0CP0CQ0CR0CS0CT0D90D^0E20EZ0FB0Fn0GZ0Gn0Go0HZ0IS0JL0K;0K<0K=0K>0Km0LK0LL0LM0M:0Mg0Mh0NA0NZ0OI0PF0QC0Qh0RR0SG0T@0U90U^0VC0Vh0WM0WN0WO0XP0YQ0ZP0[O0[c0[dSS3sp1SS1R2dX3sp11QFS1R3HIA1h2FR2hc1f2HF4HFR1S3dXc2NPS1R3HIA1h2sp2lo3TOP4HTOPSSSS1R3sp1S1R3HIA1h3PHI2hc1v2HV3HV1SS3sp1S2sp2lo3sp13SP1S1R2lo3LOSS1R2sp2lo3SLO5NEEDE3sp13SP1S1R3sp13dXc1QS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp12hc3rrc3SP13RRS3HT13SPR4SP1R2bs3RBL2HB5Ha_st5Hl_st1x2HxS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS1R3slo3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3slo3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stFS1R2sp2lo3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stFS1R2sp2lo3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3sp13rrc3SP13RRS2bs3RBL2HBS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HBS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc4SP1M3RRS3SPR4SP1R2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc4SP1M3RRS3SPR4SP1R2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc4SP1M3RRS3SPR4SP1R2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HBFFFFS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS3sp13rrc3RRS2bs3RBLS1R2sp3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS3sp13rrc3RRS2bs3RBLFS1R2sp2lo3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stFFFS1R2sp2lo3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS2sp2lo3sp13rrc3SP13RRS2bs3RBLFFS1R3slo3SSL3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3slo3SSL3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stFS1R3sp13rrc3RRS2bs3RBL2HBS1R3sp13rrc3RRS2bs3RBL2HBS1R2sp2lo3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13rrc3RRS3ALO2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13rrc3RRS3ALO2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBLS1R2sp2lo3SLO5NEEDE3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13rrc3SP13RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stS1R3sp13rrc3RRS2bs3RBL2HB5Ha_st5Hl_stFFS1R2sp2lo3LOS3SLO5NEEDE3sp13rrc3SP13RRS3ALO2bs3RBL2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13rrc3SP13RRS3ALO2bs3RBL2HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP3sp13rrc3SP13RRS4HTOP2bs3RBL2HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP3sp13rrc3SP13RRS4HTOP2bs3RBL2HB5Ha_st5Hl_stS3sp13rrc3RRS2bs3RBLF". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SS0 RRX"] Lemma em_tail : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Prrc,(28.$12.)Pv,$2.Pf,$2.Pr,$2.Pxra,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pxs1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs2,(16.&40.)Pxs3,(16.&40.)Pxs4,(16.&40.)Pxs5,(16.&40.)Pxs7,(16.&40.)Pxs9,(16.&40.)Pxs10,(16.&40.)Pxs11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(58.$5<.R24.R23.R22.R21.(11.(23.$2.(28.$12.))(24.$2.(28.$12.)R24.(15.(16.&40.)$12.$13.R1?.))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.R24.+;0.)(15.(16.&40.)$12.$13.R1>.))(14.(23.$2.(28.$12.))))))P,(1.$17.(18.(16.&40.)R20.)#14.)P,(1.$17.(18.(16.&40.)R20.)#5.)P,(10.$4.R24.(:.R27.+:0.)R20.)P,(1.$17.(2=.R21.)#10.)P,(67.(14.$2:.)R28.R27.R26.R25.)P,(4:.R29.R22.R21.)P,(8.R23.VPHI,)P,(8.R23.VFR,)P,(0.(34.(6?.(5;.+2.+1?.))R23.)(8.R23.=))P,(8.(3?.R2:.)VSZB,)(41.$4.(42.$4.VR,VHIA,R2>.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R24.(27.&40.R2?.)Vgp,Vtp,R23.R22.R21.Vsp,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.(27.&40.R25.)R13.(27.&40.(:.(1;.(:.R2?.+60.)+3.)(1<.(1=.VR,))))R12.R11.R10.R?.R>.R=.R<.)VF,(27.&40.+:0:=4.)Vfc,(38.(16.&40.))R2<.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EB LA LBl RRC RRS J HR HV HF RNG HSZ.
    ddestruct (xst_final hc LBc mc dXc J ltac:(exact (proj1 (proj2 (proj2 EB))))) as (OUTc & BKc & CRX & XLc).
    ddestruct J as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    ddestruct EB as (SP1 & SP1M & HHc & SAVE & CHS & CHI & SThi & STlo & MIc & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. pose proof (Forall_inv (Forall_inv_tail CHS)) as CHB. cbn [fst snd] in CHA, CHB.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    (* [comment removed for export] *)
    pose proof RRC as [[RWF _] _]. pose proof (cells_bytes_length rrc RWF) as RBL. rewrite RRS in RBL.
    set (bs := cells_bytes rrc) in *.
    assert (RR2 : rw_cells asegs mc (sp1 + 160) [C8 (le_bytes_to_word (firstn 8 bs)); C8 (le_bytes_to_word (skipn 8 bs))]).
    { eapply rw_cells_reshape; [exact RRC| cbn; repeat split| ].
      cbn [cells_bytes cbytes]. rewrite !le8_le_bytes_to_word by (rewrite ?length_firstn, ?length_skipn, RBL; reflexivity). rewrite app_nil_r. apply firstn_skipn. }
    clear RRC RWF. generalize dependent (le_bytes_to_word (firstn 8 bs)). intros w1 RR2. generalize dependent (le_bytes_to_word (skipn 8 bs)). intros w2 RR2.
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA]. clear LA.
    repeat (destruct slB as [|? slB]; [discriminate LBl|]). destruct slB; [| discriminate LBl]. clear LBl.
    cbn [map] in CHA, CHB. clear CHS CHI.
    pose proof (munch_refl [(Z.shiftr (sp1 + 96) 3 + al_sb AL, Z.shiftr (sp1 + 96) 3 + al_sb AL + 12)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    unfold EM_POISON_RR in SHC.
    (* [comment removed for export] *)
    zstep_to [658136]. zstep_to [658140]. zstep_to [658144].
    norm_b8 SHC.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mq _) => rename mq into mf end.
    assert (MXf : mpd_at asegs mf LBc dXc).
    { eapply mpd_at_munch_any; [exact MXc| exact MU| exact WM| |].
      - cbn [disjoint_from]. rewrite AD.
        destruct (apart_shadow_client AL (hcs asegs R HIA hc) X 16 (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOKc CRX
                    ltac:(eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]) ltac:(unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [Q|Q];
          (split; [clear - Q; lia| exact I]).
      - intros NN. ddestruct (XLc NN) as (CRP & NP & DSP). cbn [disjoint_from].
        destruct (apart_shadow_client AL (hcs asegs R HIA hc) (md_p dXc) (4 * md_n dXc) (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOKc CRP
                    ltac:(eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]) ltac:(unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia) ltac:(clear - NP; lia) ltac:(clear; lia)) as [Q|Q];
          (split; [clear - Q; lia| exact I]). }
    lazymatch type of CHA with rw_cells _ _ _ (map C8 ?la) => idtac | rw_cells _ _ _ ?ca => lazymatch type of CHB with rw_cells _ _ _ ?cb =>
      assert (SPILL : rw_cells asegs mf sp1 (ca ++ [C8 w1; C8 w2] ++ cb));
        [ apply rw_cells_app; split; [exact CHA|]; cbn [cells_size csize Nat.add]; replace (sp1 + Z.of_nat 160) with (sp1 + 160) by (clear; lia);
          apply rw_cells_app; split; [exact RR2|]; cbn [cells_size csize Nat.add]; replace (sp1 + 160 + Z.of_nat 16) with (sp1 + 176) by (clear; lia); exact CHB |] end end.
    cbn [app] in SPILL.
    lazymatch type of SPILL with rw_cells _ _ _ ?cs =>
      let ws := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) cs) in
      change (rw_cells asegs mf sp1 (map C8 ws)) in SPILL end.
    lazymatch type of SPILL with rw_cells _ _ _ (map C8 ?slw) =>
    eapply (em_epi R HIA IMG h LB LF m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dX lo slo) with (hc := hc) (LBc := LBc) (dXc := dXc) (sl := slw) end;
      first [ eassumption | exact (RRX _ _ RNG BKc HSZ) | reflexivity
            | clear - HV1 HV; lia | clear - HFR1 HF; lia | clear - SLO; lia
            | match goal with |- ?g => idtac "TAIL-EPI-LEFT:" g end ].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="HND"] Lemma xst_keep_free : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PEX1,(28.(23.$2.$2.))PB,$2.Pk,$2.PEX2,(28.(23.$2.$2.))Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.Pb,$2:.P,(67.(6=.(23.$2.$2.)R9.(11.(23.$2.$2.)(24.$2.$2.R8.R7.)R6.))R5.R4.R3.R2.)P,(?.$4.VR,VHIA,R6.R5.VLF,R4.)P,(30.$2:.R3.(22.VLB,VdX,))(30.$2:.R4.(6>.R;.R7.))")
(* [comment removed for export] *).
  Proof.
    intros EX1 B k EX2 hc LBc mc dXc b J HHc Hb.
    pose proof (xst_keep _ hc LBc mc dXc b J Hb) as KK.
    ddestruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OEX & _).
    pose proof (HND _ _ _ _ HHc) as ND.
    ddestruct (OEX (B, k) ltac:(apply in_or_app; right; left; reflexivity)) as (BIN & BFR & _ & BK0). cbn [fst snd] in BFR, BK0.
    pose proof (In_mpd_keep _ _ _ Hb) as HbL. pose proof (In_mpd_keep _ _ _ KK) as HbC. destruct b as [c j].
    apply In_lb_remove_keep; [exact HbC|]. intros ->. rewrite (nodup_fst LBc B j k ND HbC BIN) in HbL. exact (fresh_not_in LB (B, k) BFR BK0 HbL).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L1540877545.3  L23615739305.3 L50794956004.6 L62018535662.1 L63312079411.15L67028235242.8 L7515719069.14 00000<00F00]00`01Q02002`S2sp3sp13SP1S1R3HIA2hcS1R2sp2lo3LOS3SLO5NEEDES1RS1R2sp2lo3LOS3SLO5NEEDE3sp11B1k3SP12BL3ALO1a1n2H1S1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S1R2sp2lo3LOS3SLO5NEEDE3sp11B1k3SP12BL3ALO2ac2C1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL XW HND"] Lemma embs_free : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PPC,(28.$12.)Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PCH,(28.(23.$2.(28.$12.)))PEX1,(28.(23.$2.$2.))PB,$2.Pk,$2.PEX2,(28.(23.$2.$2.))PdXc,$68.Pv,$2.Pf,$2.Ph',(29.$4.VR,VHIA,)Pm',P,(16.&40.)(2;.(16.&8.))P,(1.$17.(2=.R?.)#<.)P,(58.R10.R?.R>.R=.R<.R;.)P,(67.(6=.(23.$2.$2.)R;.(11.(23.$2.$2.)(24.$2.$2.R:.R9.)R8.))R?.R>.R=.R7.)P,(4:.R10.R7.R6.)P,(1:.$4.R5.)P,(19.$4.R6.Vlo,R13.)P,(2?.$4.VR,(6>.R>.R12.)VLF,R14.(20.VR,)(5.$4.VR,VHIA,R13.)(11.(23.$2.$2.)(24.$2.$2.R>.(:.R>.R=.))(14.(23.$2.$2.)))R11.R7.)P,(1.$2.(3.$4.VR,VHIA,R9.)(3.$4.VR,VHIA,R14.))P,(1.$2.(5.$4.VR,VHIA,R:.)(5.$4.VR,VHIA,R15.))P,(1.$2.(6.$4.VR,VHIA,R;.)(6.$4.VR,VHIA,R16.))P,Px,$2.P,(7.$4.VR,VHIA,R18.R1.)(7.$4.VR,VHIA,R>.R2.)P,(8.(9.$4.VR,VHIA,R=.)(:.(9.$4.VR,VHIA,R18.)$70.))P,(8.(;.$4.VR,VHIA,R>.)(:.(;.$4.VR,VHIA,R19.)(4<.(:.Vd,+1.))))P,(?.$4.VR,VHIA,R?.(6>.R15.R19.)VLF,R>.)(0.(58.R1=.R1<.R10.(6>.R16.R1:.)R?.R18.)(0.(67.(6=.(23.$2.$2.)R17.R14.)R10.(6>.R16.R1:.)R?.R13.)(4:.R10.(:.R12.$70.)(:.R11.(4<.(:.Vd,+1.))))))")
(* [comment removed for export] *).
  Proof.
    intros PC sp1 hc LBc mc CH EX1 B k EX2 dXc v f h' m' HPC EB J HR MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH'.
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (fun b => xst_keep_free EX1 B k EX2 hc LBc mc dXc b J (proj1 (proj2 (proj2 EB)))) as KR.
    dpose EB as (SP1 & SP1M & HHc & _ & _ & CHI & _ & _ & MIc & _).
    dpose J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OEX & _).
    ddestruct (OEX (B, k) ltac:(apply in_or_app; right; left; reflexivity)) as (BIN & BFR & _ & BK0). cbn [fst snd] in BFR, BK0.
    pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc B k ltac:(apply in_or_app; left; exact BIN)) as BL.
    pose proof (art_lo asegs R HIA) as ALO.
    split; [| split; [| eapply hrel_step; eassumption]].
    - eapply embs_call with (LBp := lb_remove B LBc) (W' := [(B, B + k)]) (WE := ([] : list ivl)) (LBe := KEEP);
        [exact HPC| exact EB| exact MI'| exact ST'| rewrite <- HS1; exact HP| exact KR| | | | intros b Hb; exact Hb| intros x _; exact I| exact HH'].
      + intros a n H1 H2. cbn [disjoint_from]. split; [clear - H1 BL ALO LOS SLO NEEDE SP1; lia| exact I].
      + rewrite Forall_forall in *. intros ac Hac. destruct (CHI ac Hac) as [C1 C2]. cbn [disjoint_from]. split; [clear - C1 BL ALO LOS SLO NEEDE SP1; lia| exact I].
      + eapply (presA_drop_fresh asegs R HIA h KEEP LF [] B k); [| apply fresh_apart_keep; exact BFR| clear - LOS SLO NEEDE; lia].
        rewrite <- HS1. eapply presA_weaken; [exact HP| exact KR| intros b Hb; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx].
    - eapply (xst_free EX1 B k EX2 hc LBc mc dXc h' m' sp1); [exact J| exact HHc| exact MIc| exact MI'| clear - SP1; lia| clear - SP1 SLO NEEDE LOS; lia| exact HP| exact HCS'].
    all: match goal with |- ?g => idtac "EMBSFREE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L13103334224.10L19980016842.7 L2406440468.8  L33560573857.12L33562562182.10L33562658343.9 L3482346814.8  L66151427842.16L7371209359.10 L7375390985.13 L7377399854.11 L7377500303.10 L9356559676.11 00000100I00b00c00d01B01C01_02@02A02B02C02nFS1R3HIA1h2sp3TOP3sp13SP1S1R2sp2lo3SLO3sp13SP13NERFFS1R3HIA1h3PHI4BUDT2hc1v2HV3HV1FS3sp12r04SP1M1q1r1H2H02q02H4S1R3HIA1h2FR1d5BUDFT2hc1f2HF4HFR1FFFS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL SPA XW TPV UW0 UWX HND ZF BUDT BUDFT"] Lemma em_zf : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Pretpc,$2.PPC,(28.$12.)Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PCH,(28.(23.$2.(28.$12.)))PEX1,(28.(23.$2.$2.))PB,$2.Pk,$2.PEX2,(28.(23.$2.$2.))PdXc,$68.Pv,$2.Pf,$2.Pjunk,(28.(16.&8.))Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pxs1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs2,(16.&40.)Pxs3,(16.&40.)Pxs4,(16.&40.)Pxs5,(16.&40.)Pxs6,(16.&40.)Pxs7,(16.&40.)Pxs8,(16.&40.)Pxs9,(16.&40.)Pxs10,(16.&40.)Pxs11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(1.$17.(2=.R26.)#<.)P,(58.R27.R26.R25.R24.R23.R22.)P,(67.(6=.(23.$2.$2.)R22.(11.(23.$2.$2.)(24.$2.$2.R21.R20.)R1?.))R26.R25.R24.R1>.)P,(4:.R27.R1>.R1=.)P,(10.$4.R26.R23.(11.$12.(4>.(4?.R22.)R1=.)(14.$12.)))P,(0.(8.=R23.)(34.R23.(5;.+2.+28.)))P,(8.(:.R21.$70.)VPHI,)P,(8.(:.R21.(4<.(:.Vd,+1.)))VFR,)P,(0.(8.=R2?.)(34.R2?.(5;.+2.+40.)))P,(1.$2.(>.R30.+2.)=)P,Ph',(29.$4.VR,VHIA,)Pm',P,(16.&40.)(2;.(16.&8.))Py0,(16.&40.)Py1,(16.&40.)Py2,(16.&40.)Pya0,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Py3,(16.&40.)Py4,(16.&40.)Py5,(16.&40.)Py6,(16.&40.)P,(58.R41.R40.R11.(6>.R3:.R3>.)R10.R3<.)P,(67.(6=.(23.$2.$2.)R3<.R39.)R12.(6>.R3;.R3?.)R11.R38.)P,(4:.R13.(:.R38.$70.)(:.R37.(4<.(:.Vd,+1.))))P,(2?.$4.VR,(6>.R3=.R41.)VLF,R43.(20.VR,)(5.$4.VR,VHIA,R42.)(11.(23.$2.$2.)(24.$2.$2.R3=.(:.R3=.R3<.))(14.(23.$2.$2.)))R40.R13.)P,(1:.$4.R14.)(41.$4.(42.$4.VR,VHIA,R16.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.R47.)(27.&40.R45.)Vgp,Vtp,R14.R13.R12.Vsp,R35.R11.R10.R?.R>.R=.R<.R;.R:.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R9.R8.R7.R6.)VF,(27.&40.R47.)Vfc,(38.(16.&40.))R15.(46.$4.)))(41.$4.(42.$4.VR,VHIA,R2?.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.R32.)(27.&40.R30.)Vgp,Vtp,R23.R22.R21.Vsp,R20.(27.&40.R2:.)(27.&40.R29.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)VF,(27.&40.$71.)Vfc,(38.(16.&40.))R2=.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HPC EB J HR BC Hk HV HF RPC RPE K.
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (embs_uwc _ _ _ _ _ _ EB) as UWc. rewrite <- HS1 in UWc.
    dpose EB as (SP1 & SP1M & HHc & _ & _ & _ & _ & STlo & MIc & _).
    dpose J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OEX & _).
    ddestruct (OEX (B, k) ltac:(apply in_or_app; right; left; reflexivity)) as (BIN & _ & _ & BK0). cbn [fst snd] in BK0.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    pose proof ZF as ZF'. unfold zeroize_and_free_stmtA in ZF'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply ZF' with (h := hc) (LB := LBc) (LF := LF) (buf := B) (len := k) (lo := lo) (d := d + 1) (junk := junk);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact STlo | exact LOS | exact TPV | exact MIc | exact UWc | exact Hk | reflexivity
              | right; split; [exact BIN| exact BC]
              | clear - SP1 SLO NEEDE NER; lia | rewrite HT1; clear - SP1 TOP; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | clear - HV1 HV BUDT; lia | clear - HFR1 HF BUDFT; lia
              | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold zeroize_and_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & E' & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    ddestruct (embs_free PC sp1 hc LBc mc CH EX1 B k EX2 dXc v f h2 m2 HPC EB J HR MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as (EB2 & J2 & HR2).
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact EB2| exact J2| exact HR2| exact HP2| exact MI2].
    all: match goal with |- ?g => idtac "ZF-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="h XW"] Lemma xst_pres : forall EX hc LBc mc dXc (h' : HST asegs R HIA) m' SPc,
    XST EX hc LBc mc dXc -> HM asegs R HIA hc LBc LF mc -> mem_inv asegs mc -> mem_inv asegs m' ->
    SPc <= bv_unsigned sp -> arl_stklo R <= SPc ->
    presA asegs R LBc LF SPc (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m' ->
    (forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h' x) ->
    XST EX h' LBc m' dXc.
  Proof.
    intros EX hc LBc mc dXc h' m' SPc J HHc MIc MI' HSP HSL HP HCS'.
    pose proof (fun b => xst_keep _ hc LBc mc dXc b J) as KK.
    ddestruct J as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE).
    destruct XW as [CW DXP]. pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
    assert (CRX : client_range L (LBc ++ fdata LF) SPc X 16).
    { intros a Ha. destruct (CWk a Ha) as [S|[D|([q j] & Hq & Rq)]]; [left; clear - S HSP; lia| right; left; exact D| right; right].
      exists (q, j). split; [| exact Rq]. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left; exact (In_mpd_keep _ _ _ (KK _ Hq))| right; exact Hq]. }
    unfold XST.
    split. { eapply (mpd_at_heap_presx asegs L mc m' LBc (LBc ++ fdata LF) LBc SPc [] dXc);
               [exact MXc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP)| exact MIc| exact MI'| rewrite AD; exact CRX| | exact I| intros _; exact I|].
             - intros EH. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & XIN & _).
               eapply client_range_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia].
             - intros b Hb. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hb. destruct (md_own dXc); try (destruct Hb; fail).
               destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)). }
    split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|]. split; [exact FRA|]. split; [exact FRS|].
    split. { eapply aobj_cs_mono; [exact HCS'|]. eapply (presA_aobj asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP| exact OXc| exact CRX| exact HSL| intros x Hx; eapply hcs_below_top; exact Hx]. }
    split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. split; [exact OEX| exact NDE].
  Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@L1028513246.5   L143464676.2    L1442591806.1   L14583489263.0  L15151186337.0  L18445603269.11 L35394345996.171L35394345996.177L35513731400.1  L35653441506.7  L36667852792.0  L37233812813.3  L39172636981.0  L46495920348.2  L488109778.2    L59308632823.3  L60098763854.3  L65321081951.7  L65321506788.2  L66615591583.178L9356559676.11  Q10299702385.180Q12388795671.179Q12388912010.173Q20537601674.179Q20537614359.173Q27428150429.173Q27428229632.179Q37481766779.179Q37481845222.173Q4467029164.180 Q62698698278.180Q7087230429.180 00000>00G00L00M00N01901T01o02402L02M02W02X02a02k03603@03V03_04:04e05S06A06o07Q08308P08m09P0:30:U0;20;US2FR1d1f2HF2D0S3dRc3NRRS3dRcSSS1R2sp2lo3LOS3SLO5NEEDE3sp13dRc3SP13ALO3PC'S2sp3sp13dRc3slA3slB2LA3LBlS2sp3sp13dRc3slA3slB2LA3LBlS3sp1S1R3HIA1h2sp2lo3TOP4HTOPSS3PHI1v2HVSS3dRc3NRRS3dRc4LENRS3dRc2P02KTS1R2lo3LOSS1R3dRc3ACV3NRR2P03PC'S3dRc3NRRS2sp3sp13dRc3slA3slB2LA3LBlS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS1R2sp2lo3SLO5NEEDE3sp13dRc3slA3slB2LA3LBl3SP1S1R2sp2lo3SLO5NEEDE3sp13dRc3slA3slB2LA3LBl3SP1S1R2sp2lo3SLO5NEEDE3sp13dRc3slA3slB2LA3LBl3SP1S2sp2lo3sp13dRc3slA3slB2LA3LBl3SP1S2sp2lo3sp13dRc3slA3slB2LA3LBl3SP1S3sp13dRc3slA3slB2LA3LBl4SP1RS3sp13dRc3slA3slB2LA3LBl4SP1RS2sp3sp13dRc3slA3slB2LA3LBl3SP13SPRS2sp3sp13dRc3slA3slB2LA3LBl3SP13SPRS2sp2lo3sp13dRc3slA3slB2LA3LBl3SP1S3sp13dRc3slA3slB2LA3LBl4SP1RS2sp3sp13dRc3slA3slB2LA3LBl3SP13SPR". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 XW TPV UW0 UWX HND ZF MPIFREE RRX BUDT BUDFT"] Lemma em_clean2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pv,$2.Pf,$2.Pr,$2.Pxra,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pxs1,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs2,(16.&40.)Pxs3,(16.&40.)Pxs4,(16.&40.)Pxs5,(16.&40.)Pxs7,(16.&40.)Pxs9,(16.&40.)Pxs10,(16.&40.)Pxs11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(58.$5<.R23.R22.R21.R20.(11.(23.$2.(28.$12.))(24.$2.(28.$12.)R23.(15.(16.&40.)$12.$13.R1=.))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.R23.+;0.)(15.(16.&40.)$12.$13.R1<.))(14.(23.$2.(28.$12.))))))P,(1.$17.(18.(16.&40.)R1>.)#14.)P,(1.$17.(18.(16.&40.)R1>.)#5.)P,(67.(65.R21.)R25.R24.R23.R22.)P,(4=.$4.R24.R25.R22.)P,(1.$2.(25.R23.)(:.R28.+:0.))P,(35.(1.$39.(3:.R24.)$64.))P,(4:.R29.R22.R21.)P,(8.(:.R23.$70.)VPHI,)P,(8.(:.R23.(4<.(87.(:.Vd,+1.)+1<.)))VFR,)P,(0.(34.(6?.(5;.+2.+1?.))R23.)(8.R23.=))P,(8.(3?.R2:.)VSZB,)(41.$4.(42.$4.VR,VHIA,R2>.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R24.(27.&40.R2?.)Vgp,Vtp,R23.R22.R21.Vsp,R20.(27.&40.(:.R2?.+:0.))R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(27.&40.R25.)R14.(27.&40.(:.(1;.(:.R2?.+60.)+3.)(1<.(1=.VR,))))R13.R12.R11.R10.R?.R>.R=.)VF,(27.&40.+:0:=0.)Vfc,(38.(16.&40.))R2<.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EB LA LBl J MR AR NSR HR HV HF RNG HSZ.
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (fun b => xst_keep _ hc LBc mc dXc b J) as KK.
    dpose EB as (SP1 & SP1M & HHc & SAVE & CHS & CHI & SThi & STlo & MIc & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    pose proof MR as [MAT SGR].
    assert (ZA : Z.of_nat (cells_size (map C8 slA)) = 160) by (rewrite cells_size_map_C8, LA; reflexivity).
    assert (ZB : Z.of_nat (cells_size (map C8 slB)) = 40) by (rewrite cells_size_map_C8, LBl; reflexivity).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep.
    pose proof MPIFREE as MF'. unfold mpi_free_stmtA in MF'.
    eapply aevtA_call.
    { intros mo1 [HK1 MFm1].
      eapply MF' with (h := hc) (LB := LBc) (LF := LF) (X := md_addr dRc) (sw := Z_to_bv 64 (md_sg dRc)) (n := md_n dRc) (P := md_p dRc)
                      (limbs := md_limbs dRc) (pad := md_pad dRc) (own := md_own dRc) (lo := lo) (d := Z.max (d + 1) 28);
        rewrite ?(unsigned_lit sp1) by exact SP1R.
      all: first
        [ exact HHc | exact HK1 | exact MAT | exact NSR | exact STlo | exact LOS | exact TPV | exact MIc
        | (unfold client_wrange, client_waddr; intros a Ha; left; rewrite HT1; rewrite AR in Ha; clear - Ha SP1 TOP; lia)
        | (intros EH; pose proof MAT as (_ & _ & _ & _ & _ & OW); rewrite EH in OW; destruct OW as (_ & PIN & _);
           pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc _ _ ltac:(apply in_or_app; left; exact PIN)) as BL;
           right; rewrite AR; clear - BL ALO LOS SLO NEEDE SP1; lia)
        | (rewrite AR; eapply rr_aobj; [exact SHC| eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1 SLO NEEDE; lia]| exact SP1M| clear - SP1R; lia])
        | (unfold uw_obj; right; clear; lia)
        | (rewrite AR; reflexivity)
        | (clear - SP1 SLO NEEDE NER; lia)
        | (rewrite HT1; clear - SP1 TOP; lia)
        | (clear - SP1M; Z.div_mod_to_equations; lia)
        | (clear - HV1 HV BUDT; unfold AVOL_CALL in *; lia)
        | (clear - HFR1 HF BUDFT; lia)
        | match goal with |- ?g => idtac "MFREE-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MFm1] & PO)). unfold mpi_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & E' & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HFL2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & CX2).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite AR in HP2, CX2.
    match goal with |- context [ret_pc (Z_to_bv 64 ?q)] => rewrite (ret_pc_even q) by (clear; lia) end.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MFm1 MF2))).
    pose proof (hrel_step hc v f h2 AVOL_CALL (fr_charge (Z.max (d + 1) 28)) HR HT2 HS2 HFL2 HCS2 HV2 HFR2) as HR2.
    assert (HPs : presA asegs R (P_mpi_free.mpi_free_LB (md_own dRc) (md_p dRc) (md_n dRc) LBc) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA hc) (P_mpi_free.mpi_free_X (md_own dRc) (md_p dRc) (md_n dRc)) mc m2).
    { rewrite <- HS2. eapply (presA_drop_below asegs R HIA h2 _ LF _ (sp1 + 160) (sp1 + 160 + 16) m2 mc m2 (bv_unsigned sp)); [exact HH2| | clear - SP1; lia| clear - SP1 SLO NEEDE LOS; lia].
      rewrite HS2. eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    destruct (md_own dRc) eqn:EOR; [| | exfalso; exact (NSR eq_refl)]; cbn [P_mpi_free.mpi_free_LB P_mpi_free.mpi_free_X] in HPs, HP2, HH2.
    - (* [comment removed for export] *)
      unfold mpd_blk in J. rewrite EOR in J. change (XST [] hc LBc mc dXc) in J.
      assert (KR2 : forall b, In b KEEP -> In b LBc) by (intros b Hb; exact (In_mpd_keep _ _ _ (KK b Hb))).
      assert (HPK : presA asegs R KEEP LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [] mc m2).
      { rewrite <- HS1. eapply presA_weaken; [exact HPs| exact KR2| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
      (* [comment removed for export] *)
      assert (XS2 : XST [] h2 LBc m2 dXc).
      { eapply (xst_pres [] hc LBc mc dXc h2 m2 (bv_unsigned sp)); [exact J| exact HHc| exact MIc| exact MI2| clear; lia| clear - LOS SLO NEEDE; lia| exact HPs| exact HCS2]. }
      assert (EB2 : EMBs EM_POISON_RR sp1 h2 LBc m2 [(sp1, map C8 slA); (sp1 + 176, map C8 slB)]).
      { eapply embs_call with (LBp := LBc) (W' := [(sp1 + 160, sp1 + 160 + 16)]) (WE := ([] : list ivl)) (LBe := KEEP);
          [reflexivity| exact EB| exact MI2| exact ST2| rewrite <- HS1; exact HP2| exact KR2| | | exact HPK| intros b Hb; exact Hb| intros x _; exact I| exact HH2].
        + intros a n H1 H2. cbn [disjoint_from]. split; [clear - H1 SP1; lia| exact I].
        + constructor; [| constructor; [| constructor]]; cbn [fst snd]; rewrite ?ZA, ?ZB; cbn [disjoint_from]; (split; [clear; lia| exact I]). }
      eapply (em_tail sp1 h2 _ m2 dXc slA slB _ _ _ r); [exact EB2| exact LA| exact LBl| exact CX2| reflexivity| exact XS2| exact HR2| clear - HV; unfold AVOL_CALL in *; lia| clear - HF; lia| exact RNG| exact HSZ].
    - pose proof MAT as (_ & _ & _ & _ & _ & OWh). destruct OWh as (N1 & PIN & P16 & PARR).
      pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc _ _ ltac:(apply in_or_app; left; exact PIN)) as BL.
      unfold mpd_blk in J. rewrite EOR in J. change (XST [(md_p dRc, 4 * md_n dRc)] hc LBc mc dXc) in J.
      dpose J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OEX & _).
      ddestruct (OEX (md_p dRc, 4 * md_n dRc) ltac:(left; reflexivity)) as (BIN & BFR & BNX & BK0). cbn [fst snd] in BFR, BK0.
      (* [comment removed for export] *)
      pose proof (fun b => xst_keep_free [] (md_p dRc) (4 * md_n dRc) [] hc LBc mc dXc b J HHc) as KR2.
      assert (HPK : presA asegs R KEEP LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [] mc m2).
      { eapply (presA_drop_fresh asegs R HIA h KEEP LF [] (md_p dRc) (4 * md_n dRc)); [| apply fresh_apart_keep; exact BFR| clear - LOS SLO NEEDE; lia].
        rewrite <- HS1. eapply presA_weaken; [exact HPs| exact KR2| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
      assert (XS2 : XST [] h2 (lb_remove (md_p dRc) LBc) m2 dXc).
      { exact (xst_free [] (md_p dRc) (4 * md_n dRc) [] hc LBc mc dXc h2 m2 (bv_unsigned sp) J HHc MIc MI2 ltac:(clear; lia) ltac:(clear - LOS SLO NEEDE; lia) HPs HCS2). }
      assert (EB2 : EMBs EM_POISON_RR sp1 h2 (lb_remove (md_p dRc) LBc) m2 [(sp1, map C8 slA); (sp1 + 176, map C8 slB)]).
      { eapply embs_call with (LBp := lb_remove (md_p dRc) LBc) (W' := [(sp1 + 160, sp1 + 160 + 16); (md_p dRc, md_p dRc + 4 * md_n dRc)]) (WE := ([] : list ivl)) (LBe := KEEP);
          [reflexivity| exact EB| exact MI2| exact ST2| rewrite <- HS1; exact HP2| exact KR2| | | exact HPK| intros b Hb; exact Hb| intros x _; exact I| exact HH2].
        + intros a n H1 H2. cbn [disjoint_from]. split; [clear - H1 SP1; lia| split; [clear - H1 BL ALO LOS SLO NEEDE SP1; lia| exact I]].
        + constructor; [| constructor; [| constructor]]; cbn [fst snd]; rewrite ?ZA, ?ZB; cbn [disjoint_from];
            (split; [clear; lia| split; [clear - BL ALO LOS SLO NEEDE SP1; lia| exact I]]). }
      (* [comment removed for export] *)
      eapply (em_tail sp1 h2 _ m2 dXc slA slB _ _ _ r); [exact EB2| exact LA| exact LBl| exact CX2| reflexivity| exact XS2| exact HR2| clear - HV; unfold AVOL_CALL in *; lia| clear - HF; lia| exact RNG| exact HSZ].
    all: match goal with |- ?g => idtac "CLEAN2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L20351311254.6 L21474879437.1 L24459976397.1 L25672850873.13L35513731400.1 L62077484021.5 00000?00D00I01801=01LS2dE2dN1T1c1j1QS3dRcS3dRcS1R2sp2lo3LOS3SLO5NEEDE2dE2dN3sp11T3SP13ALO3TBLS3sp1S2dE2dN1T3dRc1Q". (* [comment removed for export] *)
  #[using="lo LOS SLO NEEDE HND"] Lemma rr_across_freeT : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.Pm2,P,(16.&40.)(2;.(16.&8.))P,(67.(11.(23.$2.$2.)(24.$2.$2.R7.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(65.R2.))R6.R5.R4.R3.)P,(?.$4.VR,VHIA,R7.R6.VLF,R5.)P,(1:.$4.R6.)P,(1:.$4.R4.)P,(0.(8.(<.(=.&40.Vsp,)+150.)R<.)(8.R<.(<.(=.&40.Vsp,)+140.)))P,(4=.$4.R9.R:.R7.)P,(1.$2.(25.R8.)(:.R>.+:0.))P,(2?.$4.VR,(6>.R>.R<.)VLF,R?.(20.VR,)(5.$4.VR,VHIA,R=.)(11.(23.$2.$2.)(24.$2.$2.R>.(:.R>.(3>.(49.(3?.VdN,)(3?.VdE,))+4.)))(14.(23.$2.$2.)))R;.R8.)(4=.$4.R9.(6>.R?.R=.)R:.)")
(* [comment removed for export] *).
  Proof.
    intros sp1 T hc LBc mc dXc dRc m2 J HHc MIc MI2 SP1 MR AR HP2.
    pose proof (art_lo asegs R HIA) as ALO.
    dpose J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OEX & NDE).
    ddestruct (OEX (T, WL * 4) (or_introl eq_refl)) as (TIN & TFR & _ & TK0). cbn [fst snd] in TFR, TK0.
    pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc T (WL * 4) ltac:(apply in_or_app; left; exact TIN)) as TBL.
    pose proof (HND _ _ _ _ HHc) as ND. destruct (hm_apart asegs R HIA hc LBc LF mc HHc) as [_ BA0]. pose proof (blocks_apart_app_l _ _ BA0) as BA.
    assert (RK : forall bq, In bq (mpd_blk dRc) -> In bq (lb_remove T LBc) /\ (fst bq + snd bq <= T \/ T + WL * 4 <= fst bq)).
    { intros [c j] Hb. ddestruct (OEX (c, j) (or_intror Hb)) as (Q1 & _ & _ & Q4). cbn [snd] in Q4.
      assert (NE : c <> T). { intros ->. pose proof (nodup_fst LBc T j (WL * 4) ND Q1 TIN) as E. subst j. inversion NDE as [|? ? NI _]. exact (NI Hb). }
      split; [apply In_lb_remove_keep; [exact Q1| exact NE]|]. cbn [fst snd]. pose proof (blocks_apart_in2 LBc _ _ _ _ BA Q1 TIN NE) as Q. clear - Q. lia. }
    eapply (mpd_at_heap_presx asegs L mc m2 LBc (lb_remove T LBc ++ fdata LF) (lb_remove T LBc) sp1 [(T, T + WL * 4)] dRc);
      [exact MR| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| exact MIc| exact MI2| rewrite AR; apply client_range_stack; clear; lia| | | |].
    - intros EH. eapply client_range_block; [apply in_or_app; left; apply RK; unfold mpd_blk; rewrite EH; left; reflexivity| clear; lia| clear; lia].
    - rewrite AR. cbn [disjoint_from]. split; [clear - TBL ALO LOS SLO NEEDE SP1; lia| exact I].
    - intros EH. destruct (RK (md_p dRc, 4 * md_n dRc) ltac:(unfold mpd_blk; rewrite EH; left; reflexivity)) as [_ Q]. cbn [fst snd] in Q. cbn [disjoint_from]. split; [clear - Q; lia| exact I].
    - intros bq Hbq. exact (proj1 (RK bq Hbq)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L15368277804.3  L24908312083.2  L32159527170.5  L35653441506.7  L36667852792.0  L39172636981.0  L4854428826.4   L48560392403.5  L5188852329.3   L60098763854.3  L62204918573.4  L62374908996.5  L67446014369.0  L8929620893.182 L9356559676.11  Q1358053815.229 Q1433360151.184 Q36959464477.184Q37991553687.184Q3853489290.184 Q39031183914.229Q40460158112.229Q42969751453.184Q54622460379.229Q59128988006.184Q66561630474.184Q67149614822.18400000:00A00R00j00k00l01901D01N01X01e02302403D03o05J06Y07c0920:M0;\0<f0>00?@0@P0Ak0C;S3PHI1v2HVS2dE2dNS2dE2dN1T3WLB3WL0S1R3HIA1h2sp2lo3TOP4HTOPSSS2dE2dN2ts2TLS2FR1d1f2HFS3PHI1v2HVS1R2lo3LOSS2dE2dN2ts2TLS2FR1d1f2HF2D0SS2sp2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3WLB3WL0S1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS1R2sp2lo3SLO5NEEDE2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP1S2sp2lo2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP1S2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl4SP1RS2sp2lo2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP1S1R2sp2lo3SLO5NEEDE2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP1S2sp2lo2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP1S2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl4SP1RS2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl4SP1RS2sp2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP13SPRS2sp2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP13SPRS1R2sp2lo3SLO5NEEDE2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP1S2sp2dE2dN3sp11T1b2b02b12b22b32b42b72b82b93b113b123b133b143slB2ts2LA3LBl3SP13SPR". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 XW TPV UW0 UWX HND ZF MPIFREE RRX BUDT BUDFT"] Lemma em_clean1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Pr,$2.Pxra,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs2,(16.&40.)Pxs3,(16.&40.)Pxs4,(16.&40.)Pxs5,(16.&40.)Pxs7,(16.&40.)Pxs9,(16.&40.)Pxs10,(16.&40.)Pxs11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(6<.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(4:.R24.R1<.R1;.)P,(1.(2;.(16.&40.))(52.(16.&40.)R20.#7.)(53.(16.&40.)(27.&40.R26.)))P,(1.(2;.(16.&40.))(52.(16.&40.)R21.#6.)(53.(16.&40.)(27.&40.(49.(3?.VdN,)(3?.VdE,)))))P,(8.(:.R1?.(3>.+2.$70.))VPHI,)P,(8.(:.R1?.(:.(4<.(:.Vd,+1.))(4<.(87.(:.Vd,+1.)+1<.))))VFR,)P,(0.(34.(6?.(5;.+2.+1?.))R1?.)(8.R1?.=))P,(8.(3?.R27.)VSZB,)(41.$4.(42.$4.VR,VHIA,R2;.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R20.(27.&40.R2=.)Vgp,Vtp,R1?.R1>.R1=.Vsp,(27.&40.=)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.(27.&40.R21.)R10.(27.&40.(:.(1;.(:.R2=.+60.)+3.)(1<.(1=.VR,))))R?.R>.R=.R<.R;.R:.R9.)VF,(27.&40.+:0:8<.)Vfc,(38.(16.&40.))R29.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR ST SW HV HF RNG HSZ.
    ddestruct EJ as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0.
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    cbn [nth_error] in ST, SW. injection ST as ->. injection SW as ->.
    dpose EB as (SP1 & SP1M & HHc & SAVE & CHS & CHI & SThi & STlo & MIc & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. cbn [fst snd map] in CHA.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    assert (WL0 : 0 <= WL) by (clear - TL; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep_to [658064]. zstep_to [658068]. zstep_to [658072]. zstep_to [687892].
    rewrite ?(unsigned_lit WL) by (clear - WL0 WLB; lia).
    replace (Z.shiftl WL 2) with (WL * 4) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    eapply (em_zf 0xa0a9c EM_POISON_RR sp1 hc LBc mc _ [] T (WL * 4) (mpd_blk dRc) dXc v f (u32s ts));
      [reflexivity| exact EB| exact J| exact HR| | clear - WL0 WLB; lia| clear - HV; unfold AVOL_CALL in *; lia| clear - HF D0; unfold fr_charge in *; lia| clear; lia| reflexivity|].
    { pose proof (u32arr_cells _ _ _ _ TA) as Q. replace (Z.to_nat (WL * 4)) with (4 * length ts)%nat by (clear - TL; lia). exact Q. }
    intros h2 m2 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 EB2 J2 HR2 HP2 MI2. cbn [app] in J2.
    dpose EB2 as (_ & _ & HH2 & SAVE2 & CHS2 & _ & SThi2 & STlo2 & _ & SHC2 & SSlo2 & SShi2 & SNlo2 & SNhi2 & PRES2).
    pose proof (Forall_inv CHS2) as CHA2. cbn [fst snd map] in CHA2.
    dpose HR2 as (HT2 & HS2 & HF2 & HCS2 & HV2 & HFR2).
    pose proof (hcs_stack asegs R HIA h2) as SCS02. rewrite HS2 in SCS02.
    assert (SCS2 : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS02| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2. clear LAWS KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    pose proof (rr_across_freeT sp1 T hc LBc mc dXc dRc m2 J HHc MIc MI2 SP1 MR AR HP2) as MR2.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply (em_clean2 sp1 h2 _ m2 dXc dRc _ slB _ _ r); [exact EB2| reflexivity| exact LBl| exact J2| exact MR2| exact AR| exact NSR| exact HR2| clear - HV; unfold AVOL_CALL in *; lia| clear - HF D0; unfold fr_charge in *; lia| exact RNG| exact HSZ].
    all: match goal with |- ?g => idtac "CLEAN1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 XW TPV UW0 UWX HND ZF MPIFREE RRX BUDT BUDFT"] Lemma em_clean : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Pr,$2.Pxra,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs2,(16.&40.)Pxs3,(16.&40.)Pxs4,(16.&40.)Pxs5,(16.&40.)Pxs6,(16.&40.)Pxs7,(16.&40.)Pxs9,(16.&40.)Pxs10,(16.&40.)Pxs11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(6<.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(4:.R24.R1<.R1;.)P,(1.(2;.(16.&40.))(52.(16.&40.)R20.#7.)(53.(16.&40.)(27.&40.R26.)))P,(1.(2;.(16.&40.))(52.(16.&40.)R21.#6.)(53.(16.&40.)(27.&40.(49.(3?.VdN,)(3?.VdE,)))))P,(8.(:.R1?.(3>.+2.$70.))VPHI,)P,(8.(:.R1?.(:.(4<.(:.Vd,+1.))(4<.(87.(:.Vd,+1.)+1<.))))VFR,)P,(0.(34.(6?.(5;.+2.+1?.))R1?.)(8.R1?.=))P,(8.(3?.R27.)VSZB,)(41.$4.(42.$4.VR,VHIA,R2;.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R20.(27.&40.R2=.)Vgp,Vtp,R1?.R1>.R1=.Vsp,(27.&40.=)(27.&40.R21.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.(27.&40.(:.(1;.(:.R2=.+60.)+3.)(1<.(1=.VR,))))R?.R>.R=.R<.R;.R:.R9.)VF,(27.&40.+:0:88.)Vfc,(38.(16.&40.))R29.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR S6 S7 HV HF RNG HSZ.
    pose proof EJ as (EB & _). dpose EB as (_ & _ & HHc & _ & _ & _ & _ & _ & MIc & _).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep_to [658060].
    eapply (em_clean1 sp1 T hc LBc mc dXc dRc slA slB ts v f r); eassumption.
  Qed.
  (* [comment removed for export] *)
  Hypothesis GMR : mpi_get_mont_r2_stmtA asegs R HIA A_MPI_GET_MONT_R2.
  Hypothesis LFN : (length LF < 511)%nat.
  Hypothesis UWN : uw_obj R N 16 d.
  Hypothesis C24G : cnt24 LB + 1 + C24_GET_MONT_R2 <= C24MAX.
  Hypothesis SZ0 : md_n dX <= SZB.
  (* [comment removed for export] *)
  Definition em_GP : Z := get_mont_r2_PHI (mkMPD 0 1 0 0 [] (Z_to_bv 64 0) LNull) dN.
  Definition em_GF : Z := get_mont_r2_FR (mkMPD 0 1 0 0 [] (Z_to_bv 64 0) LNull) dN (Z.max (d + 1) 28).
  Hypothesis BUDGP : vchg (WL * 4) + em_GP + 2 * AVOL_CALL <= PHI.
  Hypothesis BUDGF : fr_charge (d + 1) + em_GF + (fr_charge (d + 1) + fr_charge (Z.max (d + 1) 28)) <= FR.
  #[using="Type d"] Lemma embs_chunks : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PPC,(28.$12.)Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmq,P,(16.&40.)(2;.(16.&8.))PCH,(28.(23.$2.(28.$12.)))PCH',(28.(23.$2.(28.$12.)))P,(58.R7.R6.R5.R4.R3.R2.)P,(72.(23.$2.(28.$12.))R2.R3.)(58.R9.R8.R7.R6.R5.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros PC sp1 hc LBc mq CH CH' dd_H; ddestruct dd_H as (SP1 & SP1M & HHq & SAVE & CHS & CHI & REST); intros INC). unfold EMBs.
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact HHq|]. split; [exact SAVE|].
    split; [rewrite Forall_forall in *; intros ac Hac; exact (CHS ac (INC ac Hac))|]. split; [rewrite Forall_forall in *; intros ac Hac; exact (CHI ac (INC ac Hac))| exact REST].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0220@L10376588162.10 L11270384162.6  L12386747446.7  L14059006689.11 L1529930734.9   L1540877545.3   L17017994445.13 L17179765636.9  L17321421241.10 L18215345933.15 L19980016842.7  L23176488136.10 L23178390479.6  L23178569935.11 L23178600553.10 L23178600558.10 L23180663113.12 L23180860364.11 L23898603878.1  L24166965860.1  L24908312083.2  L25535630363.12 L25535630364.12 L25535661242.13 L25537574841.13 L25537770812.15 L25550293181.13 L26892418956.1  L27430607234.10 L2876257148.12  L2878371802.12  L2878371805.12  L2878472059.12  L2878815355.7   L2880556797.13  L2880621688.14  L29010569222.240L29236034446.1  L2953146085.8   L31160029338.9  L31466573843.5  L31613515553.8  L32159527216.3  L3480232344.9   L3482346809.8   L3482346814.8   L34903427498.10 L34905541899.9  L34905541900.9  L34905638317.12 L34905982637.5  L34907747371.11 L34907813550.12 L35513211208.7  L35653441506.7  L35664581156.9  L36241416831.4  L36667852792.0  L37593896758.1  L37615286513.4  L38126335426.1  L38330469153.0  L38440593842.9  L38451064084.8  L39014995563.2  L39172636981.0  L39277668772.6  L40065630053.3  L40080765026.9  L40876251957.14 L42185655489.13 L42188001809.12 L42189977920.14 L4385609475.9   L44359808915.5  L44854341639.9  L46466337308.4  L46836419270.3  L46884469021.13 L47426545708.16 L49061843008.9  L49879678227.8  L49879678228.8  L49894341042.9  L50187340766.1  L51667246862.7  L52300511057.10 L52302696049.9  L52302696054.9  L52304775888.9  L52483474800.3  L52616371395.6  L58737438393.10 L58737438393.11 L58737534488.11 L58737534488.12 L58737534495.11 L58737534495.12 L58739465658.11 L58739531583.13 L58739531583.14 L58752230078.11 L58752230078.12 L60098763854.3  L60101736328.4  L6106346273.0   L62018535662.1  L62204918573.4  L63875740144.9  L66151426447.10 L66151427842.16 L66928097697.10 L66928097702.10 L66938600704.11 L67032116288.12 L67034196193.12 L67034196198.12 L67036320193.14 L7696713571.3   L8942141095.264 L9110247005.5   L9356559676.11  Q1437489709.270 Q36946944295.270Q37995681709.270Q3849230768.270 Q42982396583.270Q59133250652.270Q66565762096.270Q67153740764.27000000W00k01F01o02;02G02H02j02k03_04704804904:04;04<04=04>04A04E04L04M04N04O04P04Q04R04V05=05>05?05@05A05B05C05D05E05J05b06B06Q07007;07<07=07>07?07@07A07B07C07D07E07J07b07c08408508908J08O08P08Q08j09209309J09V09b09c09d09e09f0:I0:U0;50;D0;O0;P0;Q0<40<M0<N0<O0<R0<j0<k0<l0<m0<n0=90=I0=n0=o0>00>10>20>30>X0>Y0>Z0>[0>\0>f0?20?30?60?C0?T0?f0@B0@C0@D0@E0@F0@G0@H0@I0@S0An0B=0Bh0DF0E_0G=0Hg0J@0K_0MI0NhS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACPS2sp2lo2dN3sp13SP11HS1R2sp2lo3SLO5NEEDE3sp13SP1S1R2sp2dX2lo3LOS3SLO5NEEDE3sp13SP13ALO2BLS2sp3sp13SP1S2sp3sp13SP1FS1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1FS1R2sp2lo3LOS3SLO5NEEDE2dE2dN3sp11T2ts3SP12TL3ALO2BLS1R3HIA1h2sp3TOP3sp13SP1FFFFFFFS1TS2dXS2dE2dNFFFFFFS2spS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACPFFFFFFFFS3sp1S1R3HIA1h2sp3sp13SP11a1SS1R2sp2lo3SLO5NEEDE2dN3sp13SP11QS2dE2dN1T2ts2TLS1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S2dE2dN3WLBFFFFFFFFFFS3sp1S1R3HIA1h2sp2lo3TOP4HTOPFS3PHI2dE2dN5BUDGPSS2dXS3PHI2dE2dN5BUDGPS3sp1SFS1R2sp2lo3SLO3sp13SP13NERS3dR32N1SS2sp2lo2dN3sp13SP14OSN4S2sp3sp13SP1S2sp3sp13SP1FFFFS1R2sp2lo3slo3SLO5NEEDE3SLL3sp13SP1S2FR1d5BUDGFS1R2sp2lo3SLO5NEEDE2dN3sp13SP11HS2sp2lo3sp13SP1S2dE2dN3WLBFFS1R2sp2lo3SLO5NEEDE2dN3sp13SP14OSN4S1R2sp2lo3SLO3sp13SP13NESFFS1dS1R3HIA1h2sp3TOP3sp13SP1FFFFS2dE2dN3WLBS1R3HIA1h2sp1a1SS1R3HIA1h3PHI2dE2dN4BUDT5BUDGP2h13HV1FFFFFS1R3HIA1h2FR1d5BUDFT5BUDGF2h14HFR12D0FFFFS1R2lo3LOSS3sp11a1n2H1SS1RS2dE2dN2ts2TLS2sp2dN3sp13SP11QS1r4RNG32r02KT1q1HS3sp12r04SP1M1q1r1H2H02q02H4FFFFFFFS1R3HIA2h1S2LF2sp1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts2LJ2LA3LBl3WLBS2FR1d5BUDGF2D0S1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS2LF2sp2lo1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts3SP12LJ2LA3LBlS2LF1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts2LJ2LA3LBl4SP1RS2LF2sp2lo1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts3SP12LJ2LA3LBlS1R2LF2sp2lo3SLO5NEEDE1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts3SP12LJ2LA3LBlS2LF1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts2LJ2LA3LBl4SP1RS2LF2sp1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts3SP12LJ2LA3LBl3SPRS1R2LF2sp2lo3SLO5NEEDE1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts3SP12LJ2LA3LBlS2LF2sp1d2dE2dN3LFN3sp11b2b02b12b22b32b42b72b82b93b113b123b133b143slB2j41T2ts3SP12LJ2LA3LBl3SPR". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 MX0 NSX XW XL0 OX0 TPV UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN HND ZF MPIFREE SZB RRX BUDT BUDFT GMR LFN C24G SZ0 BUDGP BUDGF d"] Lemma em_rr2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Ph1,(29.$4.VR,VHIA,)Pm2,P,(16.&40.)(2;.(16.&8.))PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pj4,(28.(16.&8.))PT,$2.Pts,(28.(16.&40.))Pyra,(16.&40.)Pzt0,(16.&40.)Pzt1,(16.&40.)Pzt2,(16.&40.)Pza1,(16.&40.)Pza2,(16.&40.)Pza3,(16.&40.)Pza4,(16.&40.)Pza5,(16.&40.)Pza6,(16.&40.)Pza7,(16.&40.)Pxs5,(16.&40.)Pzt3,(16.&40.)Pzt4,(16.&40.)Pzt5,(16.&40.)Pzt6,(16.&40.)P,(58.$5<.R18.R17.(11.(23.$2.$2.)(24.$2.$2.R12.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))VLB,)R16.(11.(23.$2.(28.$12.))(24.$2.(28.$12.)R18.(15.(16.&40.)$12.$13.R15.))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.R18.+:0.)(11.$12.(13.(27.&40.=))(11.$12.(5=.(27.&40.+1.))(11.$12.(4>.#4.R13.)(14.$12.)))))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.R18.+;0.)(15.(16.&40.)$12.$13.R14.))(14.(23.$2.(28.$12.)))))))P,(4:.R18.(4;.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(4<.(:.Vd,+1.)))P,(1.$17.(18.(16.&8.)R15.)#4.)P,(1.$17.(18.(16.&40.)R18.)#14.)P,(1.$17.(18.(16.&40.)R18.)#5.)P,(1.(2;.(16.&40.))(52.(16.&40.)R1:.#6.)(53.(16.&40.)(27.&40.(49.(3?.VdN,)(3?.VdE,)))))P,(1.(2;.(16.&40.))(52.(16.&40.)R1;.#7.)(53.(16.&40.)(27.&40.R18.)))P,(4=.$4.R1=.VLB,VdX,)P,(6;.$4.R1>.R1:.R19.)P,(1.$2.(59.(18.(16.&40.)R1:.))(49.(3?.VdN,)(3?.VdE,)))P,(0.(34.=(49.(3?.VdN,)(3?.VdE,)))(8.(49.(3?.VdN,)(3?.VdE,))+>:60.))P,(51.VR,VLB,VLF,R1=.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))P,(1.$2.(>.R1>.+10.)=)P,Ph3,(29.$4.VR,VHIA,)PLB3,(28.$2:.)Pm3,P,(16.&40.)(2;.(16.&8.))PdR3,$68.Py0,(16.&40.)Py1,(16.&40.)Py2,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Py3,(16.&40.)Py4,(16.&40.)Py5,(16.&40.)Py6,(16.&40.)P,(6<.R37.R31.R12.R11.R10.VdX,R?.R34.R33.R30.)P,(4:.R13.(:.(4;.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))$73.)(:.(4<.(:.Vd,+1.))$74.))P,(8.(3?.VdN,)(3?.R11.))(41.$4.(42.$4.VR,VHIA,R15.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.+:0:24.)(27.&40.R3:.)Vgp,Vtp,R11.R10.R?.Vsp,(27.&40.=)(27.&40.=)R>.R=.R<.R;.R:.R9.R8.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))R27.(27.&40.(49.(3?.VdN,)(3?.VdE,)))(27.&40.=)(27.&40.(:.(1;.(:.R3:.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R7.R6.R5.R4.)VF,(27.&40.+:0:78.)Vfc,(38.(16.&40.))R13.(46.$4.)))(41.$4.(42.$4.VR,VHIA,R25.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R1>.(27.&40.R26.)Vgp,Vtp,R1=.R1<.R1;.Vsp,(27.&40.=)(27.&40.(:.R26.+:0.))R1:.R19.R18.R17.R16.R15.R14.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))R13.(27.&40.(49.(3?.VdN,)(3?.VdE,)))(27.&40.=)(27.&40.(:.(1;.(:.R26.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R12.R11.R10.R?.)VF,(27.&40.+:0:1<.)Vfc,(38.(16.&40.))R24.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until zt6. intros EB HR LJ LA LBl S6 S7 MX2 TA TL WLB FRT T16 K.
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof EB as EB0.
    ddestruct EB as (SP1 & SP1M & HH2 & SAVE & CHS & CHI & SThi & STlo & MI2 & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. pose proof (Forall_inv (Forall_inv_tail CHS)) as CHR. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CHS))) as CHB. cbn [fst snd] in CHA, CHR, CHB.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA h1) as SCS01. rewrite HS1 in SCS01.
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo) as KINV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER. pose proof (arl_need_ecp_smalloc R) as NES.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    assert (SCSc : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS01| clear - LOS; lia| clear - TOP HTOP; lia]).
    destruct (rr_null_at m2 ((T, WL * 4) :: LB) sp1 j4 CHR LJ SP1M ltac:(clear - SP1 SLO NEEDE LOS ALO ACP; lia)) as (pad & MRR).
    set (dRR := mkMPD (sp1 + 160) 1 0 0 [] pad LNull) in *.
    pose proof (rr_aobj h1 m2 sp1 SHC ltac:(eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]) SP1M ltac:(clear - SP1 SLO NEEDE LOS ALO ACP; lia)) as ORR.
    assert (EGP : get_mont_r2_PHI dRR dN = em_GP) by reflexivity.
    assert (EGF : get_mont_r2_FR dRR dN (Z.max (d + 1) 28) = em_GF) by reflexivity.
    assert (VN : VIEWg R HIA h1 ((T, WL * 4) :: LB) m2 dN).
    { eapply (em_view_g R HIA IMG h LB LF m) with (dX := dX) (lo := lo) (sp := sp); try eassumption.
      intros bq Hbq. right. pose proof MN0 as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hbq. destruct (md_own dN); try (destruct Hbq; fail). destruct Hbq as [<-|[]]. exact (proj1 (proj2 OW)). }
    (* [comment removed for export] *)
    zstep. zstep_to [657952]. zstep_to [678000].
    ddestruct VN as (CN & BYN & LENN & NRN & SGN & NB & PBN & NAL & ON & ONL & PB2 & MDN).
    dpose OSN as (OSN1 & OSN2 & OSN3 & OSN4 & OSN5).
    assert (SSq : sshad asegs AL m2 slo sp1).
    { destruct (sshad_split asegs AL m2 slo sp1 (sp1 + 96) SSlo ltac:(clear - SP1 SLO NEEDE SLL; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [Q _]. exact Q. }
    pose proof GMR as GM'. unfold mpi_get_mont_r2_stmtA in GM'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GM' with (h := h1) (LB := (T, WL * 4) :: LB) (LF := LF) (dX := dRR) (dN := dN) (lo := lo) (slo := slo) (d := Z.max (d + 1) 28) (F0 := bv_unsigned sp);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EGP, ?EGF; subst dRR; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        first [ exact HH2 | exact HK1 | exact LFN | exact MRR | exact MDN | exact STlo | exact LOS | exact TPV | exact MI2 | exact SSq | exact SSL | exact SLL | reflexivity
              | discriminate
              | unfold mpd_sep; cbn [md_addr]; destruct OSN4 as [Q|Q]; [right; right| right; left]; clear - Q SP1 SLO NEEDE; lia
              | clear - OSN4 SP1 SLO NEEDE; lia
              | unfold opnd_sep; cbn [md_addr md_own md_p md_n]; split; [intros NN; pose proof (OSN5 NN); clear - H SP1 SLO NEEDE; lia|]; split; [intros EH; discriminate EH|]; split; [right; left; discriminate|]; split; [clear - OSN4 SP1; lia| intros NN; pose proof (OSN5 NN); clear - H SP1; lia]
              | eapply client_range_incl; [exact CRN| intros bq Hbq; apply in_app_iff in Hbq; apply in_app_iff; destruct Hbq as [Hbq|Hbq]; [left; right; exact Hbq| right; exact Hbq]]
              | intros EH; eapply client_range_incl; [exact (CRNL EH)| intros bq Hbq; apply in_app_iff in Hbq; apply in_app_iff; destruct Hbq as [Hbq|Hbq]; [left; right; exact Hbq| right; exact Hbq]]
              | split; [apply client_wrange_stack; cbn [md_addr]; rewrite ?HT1; clear - SP1 TOP; lia| intros EH; discriminate EH]
              | intros NN; exfalso; apply NN; reflexivity
              | clear - SP1 SLO NEEDE NER; lia | clear - SP1 SLO NEEDE NES; lia | rewrite HT1; clear - SP1 TOP; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | split; [exact ORR| intros ES; discriminate ES]
              | split; [exact ON| intros ES; apply ONL; pose proof MDN as [(_ & _ & _ & _ & _ & OW) _]; rewrite ES in OW; exact (proj1 OW)]
              | intros ES _; exact (IMN ES)
              | clear - BUDGP BUDT HV1; unfold AVOL_CALL in *; lia
              | clear - BUDGF BUDFT HFR1 D0; unfold fr_charge in *; lia
              | apply uwc_cap; clear; lia
              | clear - SP1; lia
              | right; clear; lia
              | eapply Z.le_trans; [apply Z.add_le_mono_r; exact (proj2 (cnt24_cons_le (T, WL * 4) LB))| exact C24G]
              | match goal with |- ?g => idtac "GMR-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m3 & mo3 & h3 & LB3 & dR3 & r & E' & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MR3 & OUT3 & FRA3 & CR3).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST3, HP3 by exact SP1R. rewrite ?EGP, ?EGF in *.
    replace (ret_pc (Z_to_bv 64 657956)) with (Z_to_bv 64 657956 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold mpd_keep, mpd_blk in HP3, FRA3. subst dRR. cbn [md_addr md_own] in HP3, FRA3, OUT3, CR3.
    ddestruct OUT3 as (OA3 & ONS3 & P3 & P4 & P5). cbn [md_addr] in OA3. unfold mpd_blk in P4, P5. cbn [md_own] in P4, P5.
    ddestruct CR3 as ((CRN3 & RNG3) & _).
    assert (HBL : forall bk, In bk (((T, WL * 4) :: LB) ++ LF) -> fst bk + snd bk <= hl_ceil (arl_L R)).
    { intros [c j] Hbk. exact (hm_blocks_low asegs R HIA h1 _ LF m2 HH2 c j Hbk). }
    (* [comment removed for export] *)
    assert (EB3 : EMBs EM_POISON_RR sp1 h3 LB3 m3 [(sp1, map C8 slA); (sp1 + 176, map C8 slB)]).
    { eapply embs_call with (LBp := (T, WL * 4) :: LB) (W' := [(sp1 + 160, sp1 + 160 + 16)]) (WE := ([] : list ivl)) (LBe := (T, WL * 4) :: LB);
        [reflexivity| eapply embs_chunks; [exact EB0| intros ac [<-|[<-|[]]]; [left; reflexivity| right; right; left; reflexivity]]| exact MI3| exact ST3| rewrite <- HS1; exact HP3
        | intros bq Hbq; right; eapply In_mpd_keep; exact Hbq| | | | intros bq Hbq; right; eapply In_mpd_keep; exact Hbq| intros xq _; exact I| exact HH3].
      - intros a n H1 H2. cbn [disjoint_from]. split; [clear - H1; lia| exact I].
      - apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd disjoint_from]; rewrite cells_size_map_C8, ?LA, ?LBl; (split; [clear; lia| exact I]).
      - eapply (presA_drop_below_w asegs R HIA _ LF [] (sp1 + 160) (sp1 + 160 + 16)); [exact HBL| | clear - SP1; lia| clear - SP1 SLO NEEDE LOS; lia].
        rewrite <- HS1. eapply presA_weaken; [exact HP3| intros bq Hbq; exact Hbq| intros bq Hbq; exact Hbq| clear - SP1; lia| clear; lia| clear; lia| intros xq Hxq; exact Hxq]. }
    dpose EB3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PRES3).
    (* [comment removed for export] *)
    destruct XW as [CW DXP].
    assert (MX3 : mpd_at asegs m3 LB3 dX).
    { eapply (mpd_at_heap_presx asegs L m2 m3 LB (((T, WL * 4) :: LB) ++ fdata LF) LB3 sp1 [(sp1 + 160, sp1 + 160 + 16)] dX);
        [exact MX2| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP3)| exact MI2| exact MI3| | | | |].
      - intros a Ha. destruct (CW a Ha) as [S|[D|([q k] & Hq & Rq)]]; [left; clear - S SP1; lia| right; left; exact D| right; right].
        exists (q, k). split; [| exact Rq]. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left; right; exact Hq| right; exact Hq].
      - intros EH. pose proof MX0 as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
        eapply client_range_block; [apply in_or_app; left; right; exact HIN| clear; lia| clear; lia].
      - cbn [disjoint_from]. split; [clear - DSX SP1 SLO NEEDE; lia| exact I].
      - intros EH. pose proof MX0 as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
        pose proof (hm_blocks_low asegs R HIA h LB LF m HH0 _ _ ltac:(apply in_or_app; left; exact HIN)) as BL.
        cbn [disjoint_from]. split; [clear - BL ALO LOS SLO NEEDE SP1; lia| exact I].
      - intros bq Hbq. apply P4; [right| intros []]. pose proof MX0 as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hbq. destruct (md_own dX); try (destruct Hbq; fail).
        destruct Hbq as [<-|[]]. exact (proj1 (proj2 OW)). }
    assert (OX3 : aobj asegs AL (hcs asegs R HIA h3) m3 X 16).
    { eapply aobj_cs_mono; [intros xq Hxq; exact (HCS3 xq (HCS1 xq Hxq))|].
      eapply (presA_aobj asegs R CS); [exact CSOK| exact (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES3)| exact (proj1 OX0)| | clear; lia| intros xq Hxq; eapply hcs_below_top; exact Hxq].
      pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
      intros a Ha. destruct (CWk a Ha) as [S|[D|B]]; [left; clear - S; lia| right; left; exact D| right; right; exact B]. }
    assert (RFR : forall bq, In bq (mpd_blk dR3) -> In bq LB3 /\ fresh_apart R ((T, WL * 4) :: LB) LF (fst bq) (snd bq) /\ 0 < snd bq).
    { intros bq Hbq. destruct (FRA3 bq Hbq) as [[]|Q]. split; [| split; [exact Q|]];
        pose proof MR3 as [(_ & _ & _ & _ & _ & OW) _]; unfold mpd_blk in Hbq; destruct (md_own dR3); try (destruct Hbq; fail); destruct Hbq as [<-|[]]; ddestruct OW as (N1 & HIN & _); [exact HIN| cbn [snd]; clear - N1; lia]. }
    assert (J3 : XST ((T, WL * 4) :: mpd_blk dR3) h3 LB3 m3 dX).
    { apply xst_start; [exact MX3| exact OX3| | | |].
      - intros bq Hbq. destruct (P3 bq Hbq) as [[Q|Q]|Q]; [right; left; exact Q| left; exact Q| right; right; exact Q].
      - intros bq Hbq. apply P4; [right; exact Hbq| intros []].
      - intros bq [<-|Hbq]; [split; [apply P4; [left; reflexivity| intros []]| split; [exact FRT| cbn [snd]; clear - WLB; lia]]|].
        ddestruct (RFR bq Hbq) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3]. eapply fresh_apart_blocks_mono; [exact Q2| intros b' Hb'; right; exact Hb'].
      - apply List.NoDup_cons; [| unfold mpd_blk; destruct (md_own dR3); repeat constructor; intros []].
        intros Hbq. destruct (RFR _ Hbq) as (_ & Q2 & Q3). exact (fresh_not_in _ _ Q2 Q3 (or_introl eq_refl)). }
    assert (TA3 : u32arr asegs m3 T ts).
    { eapply u32arr_of_cells; [| reflexivity].
      eapply (presA_rw_cells asegs R); [exact HP3| apply u32arr_cells; exact TA| |]; cbn [cells_size csize]; rewrite Nat.add_0_r.
      - eapply client_range_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - TL; lia].
      - pose proof (hm_blocks_low asegs R HIA h1 _ LF m2 HH2 T (WL * 4) ltac:(left; reflexivity)) as BL.
        cbn [disjoint_from]. split; [clear - BL TL ALO LOS SLO NEEDE SP1; lia| exact I]. }
    assert (EJ3 : EMJ sp1 T h3 LB3 m3 dX dR3 slA slB ts).
    { unfold EMJ. split; [exact EB3|]. split; [exact LA|]. split; [exact LBl|]. split; [exact J3|]. split; [exact MR3|]. split; [exact OA3|]. split; [exact ONS3|].
      split; [exact TA3|]. split; [exact TL| split; [clear - WLB; lia| exact T16]]. }
    assert (HR3 : HREL h3 (vchg (WL * 4) + em_GP) (fr_charge (d + 1) + em_GF)) by (eapply hrel_step; eassumption).
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo) _ _ mo3 (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo) as KINV3. clear LAWS KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    (* [comment removed for export] *)
    (zstep_to [657956]; zstep). if_cases KT; zify_cond KT.
    - assert (R0 : r = 0) by (clear - KT RNG3; Z.div_mod_to_equations; lia). subst r.
      eapply (K h3 LB3 m3 dR3); [exact EJ3| exact HR3| exact (CRN3 eq_refl)].
    - (* [comment removed for export] *)
      dpose EJ3 as (_ & _ & _ & J3' & _ & _ & _ & _ & _ & _).
      repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
      cbn [nth_error] in S6, S7. injection S6 as ->. injection S7 as ->.
      dpose EB3 as (_ & _ & _ & SAVE3 & CHS3 & _ & SThi3 & STlo3 & _ & SHC3 & SSlo3 & SShi3 & SNlo3 & SNhi3 & _).
      pose proof (Forall_inv CHS3) as CHA3. cbn [fst snd map] in CHA3.
      dpose HR3 as (HT3' & HS3' & _).
      pose proof (hcs_stack asegs R HIA h3) as SCS03. rewrite HS3' in SCS03.
      assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS03| clear - LOS; lia| clear - TOP HTOP; lia]).
      (* [comment removed for export] *)
      zstep_to [657968]. zstep. zstep_to [657972]. zstep_to [657976]. zstep_to [687892].
      rewrite ?(unsigned_lit WL) by (clear - WLB; lia).
      replace (Z.shiftl WL 2) with (WL * 4) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
      eapply (em_zf 0xa0a3c EM_POISON_RR sp1 h3 LB3 m3 _ [] T (WL * 4) (mpd_blk dR3) dX _ _ (u32s ts));
        [reflexivity| exact EB3| exact J3'| exact HR3| | clear - WLB; lia| clear - BUDGP; unfold AVOL_CALL in *; lia| clear - BUDGF D0; unfold fr_charge in *; lia| clear; lia| reflexivity|].
      { pose proof (u32arr_cells _ _ _ _ TA3) as Q. replace (Z.to_nat (WL * 4)) with (4 * length ts)%nat by (clear - TL; lia). exact Q. }
      intros h4 m4 z0 z1 z2 za0' za1' za2' za3' za4' za5' za6' za7' z3 z4 z5 z6 EB4 J4 HR4 HP4 MI4. cbn [app] in J4.
      dpose EB3 as (_ & _ & HH3' & _ & _ & _ & _ & _ & MI3' & _).
      pose proof (rr_across_freeT sp1 T h3 LB3 m3 dX dR3 m4 J3' HH3' MI3' MI4 SP1 MR3 OA3 HP4) as MR4.
      pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo) as KINV4. clear LAWS3 KINV3.
      pose proof (munch_refl ([] : list ivl) m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
      (* [comment removed for export] *)
      zstep. zstep_to [658128].
      eapply (em_clean2 sp1 h4 _ m4 dX dR3 _ slB _ _ r); [exact EB4| reflexivity| exact LBl| exact J4| exact MR4| exact OA3| exact ONS3| exact HR4
        | clear - BUDGP; unfold AVOL_CALL in *; lia| clear - BUDGF D0; unfold fr_charge in *; lia| exact RNG3| exact SZ0].
    all: match goal with |- ?g => idtac "RR2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable dA : mpd.
  Local Notation A := (md_addr dA).
  Hypothesis MA0 : mpd_at asegs m LB dA.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis OSA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis CRA : client_range L (LB ++ fdata LF) lo A 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA).
  Hypothesis ODA : mpd_aobjA asegs AL CS m dA.
  Hypothesis IMA : mpd_imgA dA.
  Hypothesis NXA : md_n dX <= md_n dA.
  Hypothesis ME0 : mpd_at asegs m LB dE.
  Hypothesis SXE : X + 16 <= E \/ E + 16 <= X.
  Hypothesis OSE : opnd_sep dX dE lo (bv_unsigned sp).
  Hypothesis CRE : client_range L (LB ++ fdata LF) lo E 16.
  Hypothesis CREL : md_own dE = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dE) (4 * md_n dE).
  Hypothesis ODE : mpd_aobjA asegs AL CS m dE.
  Hypothesis IME : mpd_imgA dE.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L11478171044.5 L12341806169.8 L19980016842.7 L29916022107.2 L41717332665.5 L41943888700.6 L4385609475.9  L66151427842.16L9356559676.11 00000@00X01001801E01Z02=02Y03DS2dX3dXc2E12E21QS1R3HIA1h2sp3sp13SP11a1SS1R3HIA1h2sp3TOP3sp13SP1S3dXc2N1S2dX3dXc2E11QS1R2lo3LOS3dXc3ALO2BLS1R2sp2lo3slo3SLO5NEEDE3SLL3sp13SP1S3sp12r04SP1M1q1r1H2H02q02H4S1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SLL SPA NSX XW XL0 UW0 UWX d"] Lemma emj_xfacts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.P,(6<.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4:.R;.R3.R2.)(0.(0.(8.(<.(=.&40.Vsp,)+150.)R>.)(8.R>.(<.(=.&40.Vsp,)+140.)))(0.(1.$2.(>.R>.+20.)=)(0.(0.(8.=R>.)(34.R>.(5;.+2.+40.)))(0.(?.$4.VR,VHIA,R<.R;.VLF,R:.)(0.(4=.$4.R:.R;.R9.)(0.(35.(1.$39.(3:.R9.)$64.))(0.(75.VR,R;.VLF,R>.(3.$4.VR,VHIA,R<.)R9.)(0.P,(35.(1.$39.(3:.R9.)$3;.))(32.(8.(:.(3=.R:.)(3>.+4.(3?.R:.)))Vlo,)(8.R?.(3=.R:.)))(0.(19.$4.R:.Vlo,R>.)(0.(1:.$4.R:.)(0.(76.$4.(1=.VR,)(7.$4.VR,VHIA,R<.)R:.R9.)(0.(47.$4.R:.(20.VR,)(5.$4.VR,VHIA,R<.)(=.&40.Vsp,)R>.(:.Vd,+1.))(0.(1>.$4.(1=.VR,)R:.Vslo,R>.)(8.R>.(3.$4.VR,VHIA,R<.)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    (intros sp1 T hc LBc mc dXc dRc slA slB ts v f dd_H; ddestruct dd_H as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB); intros HR).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (embs_uwc _ _ _ _ _ _ EB) as UWc. rewrite <- HS1 in UWc.
    pose proof (fun b => xst_keep _ hc LBc mc dXc b J) as KK.
    ddestruct EB as (SP1 & SP1M & HHc & SAVE & CHS & CHI & SThi & STlo & MIc & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    ddestruct J as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE).
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    destruct XW as [CW DXP]. pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
    split; [exact SP1|]. split; [exact SP1M|]. split; [clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia|]. split; [exact HHc|]. split; [exact MXc|]. split; [exact NS|].
    split. { split.
             - rewrite AD, HT1. intros a Ha. destruct (CWk a Ha) as [S|[D|([q k] & Hq & Rq)]]; [left; clear - S SP1; lia| right; left; exact D| right; right].
               exists (q, k). split; [| exact Rq]. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left; exact (In_mpd_keep _ _ _ (KK _ Hq))| right; exact Hq].
             - intros EH. rewrite AD. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. destruct OW as (N1 & _).
               destruct (FRA (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EH; left; reflexivity)) as [Hb|HFRA].
               + unfold mpd_blk in Hb. destruct (md_own dX); try (destruct Hb; fail). destruct Hb as [Eb|[]]. injection Eb as E1 E2.
                 destruct (DXP eq_refl) as [Q|Q]; [left| right]; clear - Q E1 E2; lia.
               + cbn [fst snd] in HFRA. destruct (x_vs_fresh _ _ HFRA ltac:(clear - N1; lia)) as [Q|Q]; [right| left]; exact Q. }
    split. { intros NN. left. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _].
             destruct (md_own dXc) eqn:EO; [exfalso; exact (NN eq_refl)| | exfalso; exact (NS eq_refl)]. ddestruct OW as (_ & HIN & _).
             pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc _ _ ltac:(apply in_or_app; left; exact HIN)) as BL. clear - BL ALO LOS. lia. }
    split; [exact STlo|]. split; [exact MIc|].
    split; [split; [rewrite AD; exact OXc| intros ES; exfalso; exact (NS ES)]|].
    split; [exact UWc|].
    split. { destruct (sshad_split asegs AL mc slo sp1 (sp1 + 96) SSlo ltac:(clear - SP1 SLO NEEDE SLL; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [Q _]. exact Q. }
    rewrite HT1. clear - SP1 TOP. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type d"] Lemma own_dec : forall a b : limb_own, {a = b} + {a <> b}.
  Proof. decide equality. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0>L13470772036.6L15756354262.4L29916022107.2L30618255785.2L37153691545.2L37171002439.3L38948636245.0L45664208411.6L48734894514.4L51163457977.2L59051358004.3L59308661201.6L59311123687.2L59957207461.3L65525384585.6L8929594402.4 00000D00R00Z00b00j01501601I01U01]01h02:02B02K02a030S2sp2lo2dq3sp13SP11QS1R2lo3LOS3ALOS3dXc2N1S2dq3N1qS2dq3N1qS2dX3dXc2E2SS1R2dq3dXc2XI2R12R2S2dq3PBB3N1qS2dq3N1qS2dX2dq3SXDS2dX2dq1C2N12E12E2S2dX3SXDS2dX2dq1CS2sp2lo2dq3sp13SP13OS4S2dq3PBB3N1q2P0". (* [comment removed for export] *)
  #[using="IMG LOS HH0 MI0 NSX XL0 ROIMG d"] Lemma emj_opnd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Pdq,$68.Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.P,(6<.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4:.R;.R3.R2.)P,(4=.$4.Vm,VLB,R?.)P,(32.(8.(:.(25.VdX,)+10.)(25.R10.))(8.(:.(25.R10.)+10.)(25.VdX,)))P,(77.VdX,R11.Vlo,(=.&40.Vsp,))P,(78.(79.VR,)(6=.$2:.VLB,(7:.VLF,))Vlo,(25.R12.)+10.)P,P,(1.$39.(3:.R13.)$7;.)(78.(79.VR,)(6=.$2:.VLB,(7:.VLF,))Vlo,(3=.R14.)(3>.+4.(3?.R14.)))P,(76.$4.(1=.VR,)(7.$4.VR,VHIA,Vh,)Vm,R14.)P,(7<.R15.)(0.(7=.VR,VHIA,R13.R12.R11.R16.)(0.(7>.R10.R16.)(0.(77.R10.R16.Vlo,R15.)(0.(78.(79.VR,)(6=.$2:.R12.(7:.VLF,))Vlo,(25.R16.)+10.)(0.P,(1.$39.(3:.R16.)$7;.)(78.(79.VR,)(6=.$2:.R13.(7:.VLF,))Vlo,(3=.R17.)(3>.+4.(3?.R17.)))(76.$4.(1=.VR,)(7.$4.VR,VHIA,R13.)R11.R16.))))))")
(* [comment removed for export] *).
  Proof.
    (intros dq sp1 T hc LBc mc dXc dRc slA slB ts v f dd_H; ddestruct dd_H as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB); intros HR MD SXD OS CRD CRDL OD IMD).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    ddestruct EB as (SP1 & SP1M & HHc & SAVE & CHS & CHI & SThi & STlo & MIc & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    ddestruct J as (MXc & AD & PD & NS & NM & FRA & FRS & OXc & O3 & O4 & O5 & OEX & NDE).
    dpose OS as (OS1 & OS2 & OS3 & OS4 & OS5).
    pose proof (art_lo asegs R HIA) as ALO.
    (* [comment removed for export] *)
    assert (DK : forall bq, In bq (mpd_blk dq) -> In bq KEEP).
    { intros bq Hbq. pose proof MD as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hbq. destruct (md_own dq) eqn:EOD; try (destruct Hbq; fail). destruct Hbq as [<-|[]].
      ddestruct OW as (N1 & HIN & _). apply In_mpd_keep_intro; [exact HIN|]. intros Hx. unfold mpd_blk in Hx. destruct (md_own dX) eqn:EOX; try (destruct Hx; fail).
      destruct Hx as [Ex|[]]. injection Ex as E1 E2. destruct OS3 as [C|[C|[C|C]]]; [subst dq; clear - SXD; lia| exact (C eq_refl)| discriminate C| clear - C E1 E2 N1; lia]. }
    assert (DC : forall bq, In bq (mpd_blk dq) -> In bq LBc).
    { intros bq Hbq. pose proof (DK bq Hbq) as Hk. apply O4; [exact (In_mpd_keep _ _ _ Hk)| exact (keep_not_blk _ _ _ Hk)]. }
    assert (VW : VIEWg R HIA hc LBc mc dq).
    { eapply (em_view_g R HIA IMG h LB LF m) with (dX := dX) (lo := lo) (sp := sp); try eassumption. }
    (* [comment removed for export] *)
    assert (CRk : client_range L (KEEP ++ fdata LF) lo (md_addr dq) 16) by exact (client_range_keep L LB LF lo dX (md_addr dq) 16 CRD OS2).
    assert (CRLk : md_own dq = LHeap -> client_range L (KEEP ++ fdata LF) lo (md_p dq) (4 * md_n dq)).
    { intros EH. assert (NN : md_own dq <> LNull) by (rewrite EH; discriminate).
      apply (client_range_keep L LB LF lo dX (md_p dq) (4 * md_n dq) (CRDL EH)).
      intros EX. destruct OS3 as [C|[C|[C|C]]]; [exfalso; subst dq; clear - SXD; lia| exfalso; exact (C EX)| exfalso; exact (NN C)| clear - C; lia]. }
    assert (KSUB : forall bq, In bq (KEEP ++ fdata LF) -> In bq (LBc ++ fdata LF)).
    { intros bq Hbq. apply in_app_iff in Hbq. apply in_app_iff. destruct Hbq as [Hbq|Hbq]; [left| right; exact Hbq]. apply O4; [exact (In_mpd_keep _ _ _ Hbq)| exact (keep_not_blk _ _ _ Hbq)]. }
    split; [exact VW|].
    ddestruct VW as (CE & BY & LENq & NRq & SGq & BD & PBq & DAL & OSq & OLq & PBB & MDq).
    split; [right; rewrite AD; clear - SXD; lia|].
    split. { unfold opnd_sep. rewrite AD.
             split; [exact OS1|].
             assert (XB : md_own dXc = LHeap -> (md_own dX = LHeap /\ md_p dX = md_p dXc /\ md_n dX = md_n dXc) \/ (fresh_apart R KEEP LF (md_p dXc) (4 * md_n dXc) /\ 1 <= md_n dXc)).
             { intros EH. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. destruct OW as (N1 & _).
               destruct (FRA (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EH; left; reflexivity)) as [Hb|HFRA]; [left| right; split; [exact HFRA| exact N1]].
               unfold mpd_blk in Hb. destruct (md_own dX); try (destruct Hb; fail). destruct Hb as [Eb|[]]. injection Eb as E1 E2. split; [reflexivity| split; [exact E1| clear - E2; lia]]. }
             split. { intros EH. destruct (XB EH) as [(EOX & EP & EN)|[HFRA N1]]; [rewrite <- EP, <- EN; exact (OS2 EOX)|].
                      destruct (fresh_apart_client R KEEP LF lo (md_addr dq) 16 _ _ HFRA CRk ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [Q|Q]; [right| left]; exact Q. }
             split. { destruct (own_dec (md_own dXc) LHeap) as [EH|NEH]; [| right; left; exact NEH].
                      destruct (own_dec (md_own dq) LNull) as [EQN|NQN]; [right; right; left; exact EQN|]. right; right; right.
                      destruct (XB EH) as [(EOX & EP & EN)|[HFRA N1]].
                      - rewrite <- EP, <- EN. destruct OS3 as [C|[C|[C|C]]]; [exfalso; subst dq; clear - SXD; lia| exfalso; exact (C EOX)| exfalso; exact (NQN C)| exact C].
                      - pose proof MD as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dq) eqn:EOD; [exfalso; exact (NQN eq_refl)| |].
                        + destruct OW as (N1q & _). destruct (fresh_apart_client R KEEP LF lo (md_p dq) (4 * md_n dq) _ _ HFRA (CRLk eq_refl) ltac:(clear - N1q; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [Q|Q]; [left| right]; exact Q.
                        + (* [comment removed for export] *)
                          ddestruct OW as (N1q & _ & P0 & _ & RO).
                          pose proof MXc as [(_ & _ & _ & _ & _ & OWx) _]. rewrite EH in OWx. ddestruct OWx as (_ & XIN & _).
                          destruct (hm_apart asegs R HIA hc LBc LF mc HHc) as [HFA _]. rewrite Forall_forall in HFA.
                          destruct (HFA _ ltac:(apply in_or_app; left; exact XIN)) as (_ & _ & _ & XI). cbn [fst snd] in XI.
                          pose proof (ROIMG (md_p dq + 0) (RO 0 ltac:(clear - N1q; lia)) ltac:(clear - P0 PBB N1q; lia)) as R1.
                          pose proof (ROIMG (md_p dq + (4 * md_n dq - 1)) (RO (4 * md_n dq - 1) ltac:(clear - N1q; lia)) ltac:(clear - P0 PBB N1q; lia)) as R2.
                          clear - XI R1 R2. lia. }
             split; [clear - OS4 SP1; lia|]. intros NN. pose proof (OS5 NN) as Q. clear - Q SP1. lia. }
    split; [eapply client_range_incl; [exact CRk| exact KSUB]|].
    split; [intros EH; eapply client_range_incl; [exact (CRLk EH)| exact KSUB]|].
    split; [exact OSq|]. intros ES. apply OLq. pose proof MDq as [(_ & _ & _ & _ & _ & OW) _]. rewrite ES in OW. exact (proj1 OW).
    all: match goal with |- ?g => idtac "OPND-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis C24J : cnt24 LB + 3 + C24_MOD_MPI <= C24MAX.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39220637093.0L42645688555.0000001002SS". (* [comment removed for export] *)
  #[using="HND d"] Lemma emj_cnt24 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))P,(6<.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(8.(7?.R8.)(:.(7?.VLB,)+3.))")
(* [comment removed for export] *).
  Proof.
    (intros sp1 T hc LBc mc dXc dRc slA slB ts dd_H; ddestruct dd_H as (EB & _ & _ & J & _)). dpose EB as (_ & _ & HHc & _).
    ddestruct J as (_ & _ & _ & _ & _ & _ & _ & _ & O3 & _).
    pose proof (HND _ _ _ _ HHc) as ND. apply NoDup_map_inv in ND.
    assert (INC : incl LBc (LB ++ mpd_blk dXc ++ (T, WL * 4) :: mpd_blk dRc)).
    { intros bq Hbq. apply in_or_app. destruct (O3 bq Hbq) as [Q|[Q|Q]]; [left; exact Q| right; apply in_or_app; left; exact Q| right; apply in_or_app; right; exact Q]. }
    pose proof (cnt24_incl _ _ ND INC) as C. rewrite !cnt24_app in C.
    assert (C1 : forall dq, cnt24 (mpd_blk dq) <= 1).
    { intros dq. unfold mpd_blk. destruct (md_own dq); try (rewrite cnt24_nil; clear; lia).
      pose proof (cnt24_cons_le (md_p dq, 4 * md_n dq) []) as C2. rewrite cnt24_nil in C2. exact (proj2 C2). }
    pose proof (C1 dXc) as CX1. pose proof (C1 dRc) as CR1. pose proof (proj2 (cnt24_cons_le (T, WL * 4) (mpd_blk dRc))) as CT.
    eapply Z.le_trans; [exact C|]. apply Z.add_le_mono_l.
    eapply Z.le_trans; [apply Z.add_le_mono; [exact CX1| eapply Z.le_trans; [exact CT| apply Z.add_le_mono_r; exact CR1]]| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis COPY : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 :=
    (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 N) (Z_to_bv 64 X) (Z_to_bv 64 E) (Z_to_bv 64 A) xs6 (Z_to_bv 64 0) (SH (sp1 + 96)) SBw (SH N) (Z_to_bv 64 (E + 10)) t3 t4 t5 t6).
  Definition JSLOTS (T : Z) (slA : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(0.(1.(2;.(16.&40.))(52.(16.&40.)O1.#5.)(53.(16.&40.)(27.&40.=)))(0.(1.(2;.(16.&40.))(52.(16.&40.)O1.#6.)(53.(16.&40.)(27.&40.(49.(3?.VdN,)(3?.VdE,)))))(0.(1.(2;.(16.&40.))(52.(16.&40.)O1.#7.)(53.(16.&40.)(27.&40.O2.)))(0.(1.(2;.(16.&40.))(52.(16.&40.)O1.#8.)(53.(16.&40.)(27.&40.(:.(1;.(:.(25.VdN,)+:.)+3.)(1<.(1=.VR,))))))(0.(1.(2;.(16.&40.))(52.(16.&40.)O1.#9.)(53.(16.&40.)(27.&40.(:.(25.VdN,)+:.))))(0.(1.(2;.(16.&40.))(52.(16.&40.)O1.#:.)(53.(16.&40.)(27.&40.(:.(1;.(25.VdE,)+3.)(1<.(1=.VR,))))))(1.(2;.(16.&40.))(52.(16.&40.)O1.#;.)(53.(16.&40.)(27.&40.(:.(1;.(:.(25.VdE,)+:.)+3.)(1<.(1=.VR,))))))))))))")
(* [comment removed for export] *).
  Definition JSLOTSX (T : Z) (slA : list word) : Prop :=
    JSLOTS T slA /\ nth_error slA 3 = Some (Z_to_bv 64 (X + 8)) /\ nth_error slA 4 = Some (SH (X + 8)).
  Definition JSLOTSX2 (T : Z) (slA : list word) : Prop := JSLOTSX T slA /\ nth_error slA 2 = Some (SH X).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L24166965860.1 L29956516996.0 L31188595651.4 L32033311278.4 L3482346814.8  L40738020923.4 L49037419540.8 L54300097155.10L54300162054.12L54302081956.9 L54302182149.11L54980941250.13L54983042116.10L54983077093.11L55536219297.0 L66151427842.16L6970806972.4  L7702585352.11 L7702685865.11 L7704779055.13 L7704845226.11 00000400500@00N00O00a01:01;01<01=01>01?01`01a01b02>02K02L02M02N032S2dXSS2FR1d1f2HFS2dX2dY3dX22CNFS2LB4C24J3LBc4C24qS1R2sp2lo3SLO3sp13SP13NERFFFFFS1R3HIA1h3PHI4BUDT2dY2hc1v2HV3HV1FSS3sp12r04SP1M1q1r1H2H02q02H4S3PHI2dY1v2HVFFFS1R3HIA1h2FR1d5BUDFT2hc1f2HF4HFR12D0". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 NSX XW XL0 TPV UW0 UWX HND ZF MPIFREE SZB RRX BUDT BUDFT SZ0 C24J COPY d"] Lemma em_copy_gen : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PdY,$68.Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs6,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(6<.R19.R18.R17.R16.R15.VdX,R14.R13.R12.R11.)P,(4:.R18.R11.R10.)P,(80.R1:.R15.)P,(4=.$4.R18.R19.R1=.)P,(7>.VdX,R1>.)P,(81.VdX,R1?.Vlo,R1>.)P,(78.(79.VR,)(6=.$2:.R1<.(7:.VLF,))Vlo,(25.R20.)+10.)P,P,(1.$39.(3:.R21.)$7;.)(78.(79.VR,)(6=.$2:.R1>.(7:.VLF,))Vlo,(3=.R22.)(3>.+4.(3?.R22.)))P,(62.$4.(1=.VR,)(7.$4.VR,VHIA,R1?.)R1=.(25.R22.)+10.)P,P,(1.$39.(3:.R23.)$64.)(1.$82.(83.(3=.R24.)(3>.+4.(3?.R24.)))$84.)P,(8.(:.(:.R1:.(85.R24.))(3>.+2.$70.))VPHI,)P,(8.(:.(:.R1:.(86.Vd,))(:.(4<.(:.Vd,+1.))(4<.(87.(:.Vd,+1.)+1<.))))VFR,)P,Ph2,(29.$4.VR,VHIA,)PLB2,(28.$2:.)Pm2,P,(16.&40.)(2;.(16.&8.))PdX2,$68.Py0,(16.&40.)Py1,(16.&40.)Py2,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Py3,(16.&40.)Py4,(16.&40.)Py5,(16.&40.)Py6,(16.&40.)P,(6<.R37.R36.R12.R11.R10.R?.R32.R31.R30.R2?.)P,(4:.R13.(:.R2?.(85.R39.))(:.R2>.(86.Vd,)))P,(8.(3?.R11.)(87.(3?.VdX,)(3?.R3:.)))(41.$4.(42.$4.VR,VHIA,R15.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.+:0:84.)(27.&40.R3:.)Vgp,Vtp,R11.R10.R?.Vsp,(27.&40.=)(27.&40.=)R>.R=.R<.R;.R:.R9.R8.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))(27.&40.(25.VdA,))R26.(27.&40.=)(27.&40.(:.(1;.(:.R3:.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R7.R6.R5.R4.)VF,(27.&40.+:0;60.)Vfc,(38.(16.&40.))R13.(46.$4.)))(41.$4.(42.$4.VR,VHIA,R24.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.+:0:84.)(27.&40.R26.)Vgp,Vtp,R1;.R1:.R19.Vsp,(27.&40.=)(27.&40.(25.VdX,))(27.&40.(25.R27.))R18.R17.R16.R15.R14.R13.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))(27.&40.(25.VdA,))R12.(27.&40.=)(27.&40.(:.(1;.(:.R26.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R11.R10.R?.R>.)VF,(27.&40.$88.)Vfc,(38.(16.&40.))R22.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. (intros EJ HR dd_H; ddestruct dd_H as (S5 & S6 & S7 & S8 & S9 & S10 & S11); intros MY SXY CSY CRY CRYL OY IMY HV HF K).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0. pose proof (arl_need_ecp_rt R) as NER.
    pose proof COPY as CP'. unfold mpi_copy_stmtA_x_c, mpi_copy_stmtA_gen_c in CP'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply CP' with (h := hc) (LB := LBc) (LF := LF) (dX := dX) (dY := dY) (lo := lo) (d := d);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact MXc | exact NSX | exact MY | exact SXY | exact CSY | exact CRY | exact CRYL | exact XWc | exact STc | exact LOS | exact TPV | exact MIc
              | exact (proj1 OXc) | exact OY | exact IMY | exact UWX | exact TOPc | reflexivity
              | clear - SP1 SLO NEEDE NER; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | clear - HV1 HV BUDT; unfold AVOL_CALL in *; lia | clear - HFR1 HF BUDFT D0; unfold fr_charge in *; lia
              | (lazymatch goal with |- cnt24 _ + _ <= C24MAX => idtac end; pose proof (emj_cnt24 _ _ _ _ _ _ _ _ _ _ EJ) as C24q; unfold C24_COPY_c, C24_GROW_c, C24_MOD_MPI in *; clear - C24q C24J; lia)
              | match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E' & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 658052)) with (Z_to_bv 64 658052 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    destruct CR as [(CR1 & CAD & CPD & CFR) _].
    assert (BK : binop_keep LBc dX dX2).
    { unfold binop_keep. split; [exact CAD|]. split; [exact CPD|]. split; [exact CFR|]. destruct CR1 as [(_ & _ & Q & _)|(_ & Q & _)]; [exact Q| rewrite Q; clear; lia]. }
    destruct (emj_call sp1 T hc LBc mc dX dRc slA slB ts v f h2 LB2 m2 dX2 _ _ EJ HR MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as (EJ2 & HR2).
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    zstep.
    destruct CR1 as [(-> & _ & CN)|(-> & CN & _)].
    - eapply K; [exact EJ2| exact HR2| clear - CN; lia].
    - eapply (em_clean sp1 T h2 LB2 m2 dX2 dRc slA slB ts _ _ (-16)); [exact EJ2| exact HR2| exact S7| exact S6| clear - HV; lia| clear - HF; lia| clear; lia| rewrite CN; exact SZ0].
    all: match goal with |- ?g => idtac "COPY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L13732636588.3  L17863669337.9  L24166965860.1  L26983617546.4  L35653441506.7  L36667852792.0  L37593896758.1  L50171369813.5  L59657045483.11 L60098763854.3  Q35050355942.206Q41259381015.206Q46487649693.206Q7366406794.206 00000<00R00V00h01@01A01E01X02>02H03^05306C07dS2dX3dX23SZ2S2sp2dX2lo3DSX3sp13SP1S2dXS2dX2X01a2Ha2dA2A0S1R3HIA1h2sp2lo3TOP4HTOPSS2dXS2dX2dA3NXA3dX23SZ2S1R3HIA2sp2lo3SLO5NEEDE3sp12hc3SP11a1SS1R2lo3LOSS2LF2sp3LFN2dA3sp11b2b02b12b22b32b42b52b62b72b83b103b113b123b133b143slB3SP12LA3LBl3SPRS2LF2sp2lo3LFN2dA3sp11b2b02b12b22b32b42b52b62b72b83b103b113b123b133b143slB3SP12LA3LBlS2LF3LFN2dA3sp11b2b02b12b22b32b42b52b62b72b83b103b113b123b133b143slB4SP1R2LA3LBlS1R2LF2sp2lo3SLO5NEEDE3LFN2dA3sp11b2b02b12b22b32b42b52b62b72b83b103b113b123b133b143slB3SP12LA3LBl". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 NSX XW XL0 TPV UW0 UWX HND ZF MPIFREE SZB RRX BUDT BUDFT LFN SZ0 MA0 SXA OSA CRA CRAL ODA IMA NXA ROIMG C24J COPY d"] Lemma em_copy : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Pxra,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pxs6,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(6<.R1<.R1;.R1:.R19.R18.VdX,R17.R16.R15.R14.)P,(4:.R1;.R14.R13.)P,(80.R1=.R18.)P,(8.(:.(:.R16.(85.VdA,))(3>.+2.$70.))VPHI,)P,(8.(:.(:.R16.(86.Vd,))(:.(4<.(:.Vd,+1.))(4<.(87.(:.Vd,+1.)+1<.))))VFR,)P,Ph2,(29.$4.VR,VHIA,)PLB2,(28.$2:.)Pm2,P,(16.&40.)(2;.(16.&8.))PdX2,$68.Py0,(16.&40.)Py1,(16.&40.)Py2,(16.&40.)Pya1,(16.&40.)Pya2,(16.&40.)Pya3,(16.&40.)Pya4,(16.&40.)Pya5,(16.&40.)Pya6,(16.&40.)Pya7,(16.&40.)Py3,(16.&40.)Py4,(16.&40.)Py5,(16.&40.)Py6,(16.&40.)P,(6<.R33.R32.R12.R11.R10.R?.R2>.R2=.R2<.R2;.)P,(4:.R13.(:.R2;.(85.VdA,))(:.R2:.(86.Vd,)))P,(8.(3?.R11.)(3?.VdA,))(41.$4.(42.$4.VR,VHIA,R15.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.+:0:84.)(27.&40.R36.)Vgp,Vtp,R11.R10.R?.Vsp,(27.&40.=)(27.&40.=)R>.R=.R<.R;.R:.R9.R8.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))(27.&40.(25.VdA,))R1?.(27.&40.=)(27.&40.(:.(1;.(:.R36.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R7.R6.R5.R4.)VF,(27.&40.+:0;60.)Vfc,(38.(16.&40.))R13.(46.$4.)))(41.$4.(42.$4.VR,VHIA,R20.Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.R17.(27.&40.R22.)Vgp,Vtp,R16.R15.R14.Vsp,(27.&40.=)R13.R12.R11.R10.R?.R>.R=.R<.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))(27.&40.(25.VdA,))R;.(27.&40.=)(27.&40.(:.(1;.(:.R22.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))(27.&40.(:.(1;.(25.VdN,)+3.)(1<.(1=.VR,))))(27.&40.(:.(25.VdE,)+:.))R:.R9.R8.R7.)VF,(27.&40.+:0:78.)Vfc,(38.(16.&40.))R1>.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JS HV HF K.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep_to [638476].
    destruct SXA as [EQA|SXA'].
    - (* [comment removed for export] *)
      eapply (em_copy_gen dA sp1 T hc LBc mc dRc _ slB ts v f); [exact EJ| exact HR| exact JS| rewrite <- EQA; exact MXc| left; exact EQA| | | | rewrite <- EQA; exact (proj1 OXc)| rewrite <- EQA; intros ES; exfalso; exact (NSX ES)| exact HV| exact HF|].
      + rewrite <- EQA. destruct XWc as [CWc XPc]. pose proof MXc as [(_ & _ & X0 & _) _].
        assert (OH : md_own dX <> LNull -> md_own dX = LHeap) by (intros NN; destruct (md_own dX); [exfalso; exact (NN eq_refl)| reflexivity| exfalso; exact (NSX eq_refl)]).
        unfold copy_sep. split; [intros NN; exact (XPc (OH NN))|]. split; [exact XPc|]. split; [left; reflexivity|]. split; [clear - DSX SP1 SLO NEEDE; lia|]. split; [exact XLc|].
        intros a Ha. clear - Ha X0. lia.
      + rewrite <- EQA. destruct XWc as [CWc _]. intros a Ha. destruct (CWc a Ha) as [S|[D|B]]; [left; clear - S SP1 SLO NEEDE; lia| right; left; exact D| right; right; exact B].
      + rewrite <- EQA. intros EH. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
        eapply client_range_block; [apply in_or_app; left; exact HIN| clear; lia| clear; lia].
      + intros h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 EJ2 HR2 SZ2. eapply K; [exact EJ2| exact HR2| rewrite <- EQA in SZ2 |- *; clear - SZ2; lia].
    - (* [comment removed for export] *)
      destruct (emj_opnd dA _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MA0 SXA' OSA CRA CRAL ODA IMA) as (VA & SPA' & OSA' & CRA' & CRAL' & ODA').
      ddestruct VA as (_ & _ & _ & _ & _ & (A0 & _) & _ & _ & _ & _ & _ & MAc).
      eapply (em_copy_gen dA sp1 T hc LBc mc dRc _ slB ts v f); [exact EJ| exact HR| exact JS| exact MAc| exact SPA'| | exact CRA'| exact CRAL'| exact (proj1 ODA')| exact IMA| exact HV| exact HF|].
      + ddestruct OSA' as (Q1 & Q2 & Q3 & Q4 & Q5). unfold copy_sep. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
        intros a Ha. clear - Ha A0. lia.
      + intros h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 EJ2 HR2 SZ2. eapply K; [exact EJ2| exact HR2| clear - SZ2 NXA; lia].
    all: match goal with |- ?g => idtac "COPY2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition set_sg (dq : mpd) (sg : Z) : mpd := mkMPD (md_addr dq) sg (md_n dq) (md_p dq) (md_limbs dq) (md_pad dq) (md_own dq).
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L16468080934.9 L21602859321.3 L23055610086.1 L25161329209.3 L26892418956.1 L30843122543.13L33571791132.7 L52616371395.6 L61969314058.9 L64604774881.7 L65525689354.9 00000R00\00a00k00o01[01o02?02a03603XS1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1S2dX3dRc1QS3sp1S2dX3dXc1QS2spS1R2sp2lo3SLO5NEEDE2dE2dN3sp11T2ts2TL3SP12BLS2dX2dE2dN1T2ts2TL1QS1R3HIA1h2sp1a1SS1R2sp2lo3SLO5NEEDE3sp13dXc3SP12BLS1R2lo3LOS3ALO1B1k2BLS1R2sp2lo3SLO5NEEDE3sp13dRc3SP12BL". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SLL DSX d SPA NSX XW XL0 OX0 UW0 UWX"] Lemma emj_upd : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Pm',P,(16.&40.)(2;.(16.&8.))PslA',(28.(16.&40.))Psg',$2.P,(6<.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(4:.R>.R6.R5.)P,(58.$5<.R11.R?.R>.R5.(11.(23.$2.(28.$12.))(24.$2.(28.$12.)R11.(15.(16.&40.)$12.$13.R4.))(11.(23.$2.(28.$12.))(24.$2.(28.$12.)(:.R11.+;0.)(15.(16.&40.)$12.$13.R9.))(14.(23.$2.(28.$12.))))))P,(1.$17.(18.(16.&40.)R5.)#14.)P,(5?.(11.(23.$2.$2.)(24.$2.$2.R13.(:.R13.+28.))(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.))))R?.R7.)P,(60.$4.R10.R8.)P,(10.$4.R9.(25.VdX,)(89.(3=.R10.)(27.&40.R7.)(3?.R10.)(63.R10.)))P,(32.(1.$2.R8.+1.)(1.$2.R8.-1.))(6<.R17.R16.R15.R14.R;.(8:.R12.R9.)R11.R:.R?.R>.)")
(* [comment removed for export] *).
  Proof.
    intros sp1 T hc LBc mc dXc dRc slA slB ts v f m' slA' sg' EJ HR EB' LA' MU WM CX' SG'.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    ddestruct EJ as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose J as (_ & AD & PD & NS & NM & FRA & FRS & _ & O3 & O4 & O5 & OEX & NDE).
    dpose EB' as (_ & _ & HH' & _ & _ & _ & _ & _ & MI' & _ & _ & _ & _ & _ & PRES').
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hcs_ok asegs R HIA h) as CSOK.
    assert (BLOW : forall B k, In (B, k) LBc -> B + k <= lo).
    { intros B k Hb. pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc B k ltac:(apply in_or_app; left; exact Hb)) as BL. clear - BL ALO LOS. lia. }
    assert (EXX : forall bq, In bq ((T, WL * 4) :: mpd_blk dRc) -> In bq LBc /\ (fst bq + snd bq <= X \/ X + 16 <= fst bq)).
    { intros bq Hbq. ddestruct (OEX bq Hbq) as (Q1 & Q2 & _ & Q4). split; [exact Q1|]. apply x_vs_fresh; [apply fresh_apart_keep; exact Q2| exact Q4]. }
    unfold EMJ. split; [exact EB'|]. split; [exact LA'|]. split; [exact LBl|].
    split. { unfold XST, set_sg. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpd_blk. cbn [md_own md_p md_n].
             split. { pose proof MXc as [(_ & XAL & X0 & LEN & NR & OW) _].
                      apply mpd_at_rebuild; [exact NS| rewrite AD; exact CX'| exact XAL| exact X0| exact LEN| exact NR| exact SG'| intros EN; rewrite EN in OW; exact OW|].
                      intros EH. rewrite EH in OW. ddestruct OW as (N1 & XIN & XP16 & XARR). split; [exact N1|]. split; [exact XIN|]. split; [exact XP16|].
                      eapply (u32arr_transport asegs _ mc m'); [exact XARR| exact MU| exact WM|].
                      destruct XWc as [_ XPc]. pose proof (XPc EH) as Q. rewrite AD in Q. pose proof (BLOW _ _ XIN) as BL.
                      cbn [disjoint_from]. split; [rewrite LEN; clear - BL SP1 SLO NEEDE; lia|]. split; [rewrite LEN; clear - Q; lia| exact I]. }
             split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|]. split; [exact FRA|]. split; [exact FRS|].
             split. { eapply aobj_cs_mono; [exact HCS1|].
                      destruct XW as [CW DXP]. pose proof (client_wrange_keep L LB LF (bv_unsigned sp) (htop asegs R HIA h) dX X 16 CW DXP) as CWk.
                      eapply (presA_aobj asegs R CS); [exact CSOK| exact (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES')| exact (proj1 OX0)| | clear; lia| intros xq Hxq; eapply hcs_below_top; exact Hxq].
                      intros a Ha. destruct (CWk a Ha) as [S|[D|B]]; [left; clear - S; lia| right; left; exact D| right; right; exact B]. }
             split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. split; [exact OEX| exact NDE]. }
    split. { eapply mpd_at_munch_any; [exact MR| exact MU| exact WM| |].
             - rewrite AR. cbn [disjoint_from]. split; [clear; lia|]. split; [clear - DSX SP1 SLO NEEDE; lia| exact I].
             - intros NN. pose proof MR as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dRc) eqn:EOR; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSR eq_refl)].
               ddestruct OW as (N1 & RIN & _). destruct (EXX (md_p dRc, 4 * md_n dRc) ltac:(right; unfold mpd_blk; rewrite EOR; left; reflexivity)) as [_ Q]. cbn [fst snd] in Q.
               pose proof (BLOW _ _ RIN) as BL. cbn [disjoint_from]. split; [clear - BL SP1 SLO NEEDE; lia|]. split; [clear - Q; lia| exact I]. }
    split; [exact AR|]. split; [exact NSR|]. split; [| split; [exact TL| exact WLB]].
    eapply (u32arr_transport asegs _ mc m'); [exact TA| exact MU| exact WM|].
    destruct (EXX (T, WL * 4) (or_introl eq_refl)) as [TIN Q]. cbn [fst snd] in Q. pose proof (BLOW _ _ TIN) as BL.
    cbn [disjoint_from]. split; [clear - BL TL SP1 SLO NEEDE; lia|]. split; [clear - Q TL; lia| exact I].
    all: match goal with |- ?g => idtac "UPD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01<0@D26706871854.226D3953997537.224 D60189065437.224D61573083454.226D67038978349.226K14461423358.226K29219025976.226K66088614017.224K7750690063.226 L14447004729.2  L1685717371.0   L26786418512.1  L28401028998.9  L29217191679.2  L29467392662.1  L35653441506.7  L39188636933.0  L41392044326.1  L43938116273.217L57698627611.2  L60098763854.3  L66099886662.2  L7737701347.2   L80297513.25    P57713046236.224Q10149575540.224Q10149575540.226Q11801279589.224Q11801279589.226Q14211868145.223Q14308027860.222Q14308272604.223Q15515733206.223Q15901829514.220Q23927705296.224Q23927705296.226Q26706871854.226Q26708823086.225Q27882953602.224Q28465177121.221Q32982186054.222Q3419689062.224 Q3421936230.223 Q39180574961.224Q42418792113.222Q42439443119.224Q42439443119.226Q45416656394.222Q49698585326.224Q51087705995.224Q5129158642.224 Q5265442331.222 Q55415036769.224Q57037327601.224Q57037327601.226Q57228775306.223Q57230951818.224Q58125335435.224Q59865321072.224Q59865321072.226Q61573083454.226Q61575035710.225Q6186103236.224 Q6186103236.226 Q62011970312.224Q62011970312.226Q63774139624.223Q64041402609.224Q64041402609.226Q64683667846.224Q64683667846.226Q67147694615.220Q7845954958.224 Q7845954958.226 Q8699115497.224 Q8699115497.226 00001g04A06[08R0:l0<a0>V0@K0BM0BN0BO0BT0C60C70C<0CT0CU0CZ0EB0EC0EM0EN0EO0Ej0Ga0IW0KM0KN0M:0NW0P40QQ0SL0UC0WK0YS0[?0\k0\l0^U0`20al0cf0f40gQ0iK0kA0l^0nD10410511_13V15\17b19h1;n1=^1=_1=`1?L1A81C21Dl1F^1HL1Il1L21N81PD1RP1T;1Uk1W[1Yg1\3S2LF2sp2dX3LFN3sp13dXc1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3TOP3LFN3sp12hc3dXc1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP14SP1R3HT12LA3LBl2X03SPR2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3LOS3SLO5NEEDE3LFN3sp13dXc1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP14SP1R2LA3LBl2X03SPR2XB2HB5Ha_st5Hl_stS2LF2sp2dX3LFN3sp13dXc1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3LOS3SLO5NEEDE3LFN3sp13dXc1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP14SP1R2LA3LBl2X03SPR2XB2HB5Ha_st5Hl_stS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB4DSX12HB5Ha_st5Hl_stS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB4DSX12HB5Ha_st5Hl_stS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB4DSX12HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE3DSX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stFSS3sp1S1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1FS3sp1S1R3HIA1h2sp2lo3TOP4HTOPSS3sp1S2LF2sp2dX3LFN3sp13dXc1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBFS1R2lo3LOSFFS1R2dX1q1r1H2H02q02r02H42H5S2LF2sp2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stFS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2sp2dX3LFN3sp13dXc1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2LA3LBl2AD3XAL2X03SPR2XBS1R2LF2sp2dX2lo3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS1R3HIA1h2LF2sp2dX3TOP3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3TOP3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stFS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2LA3LBl2XB2HBS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2sp2dX2lo3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3LOS3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl3ALO2XB2HB5Ha_st5Hl_stS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX3slo3SSL3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX3slo3SSL3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_stS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stFS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_stS2LF2sp2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stFFS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX3LFN1b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HBS1R2LF2sp2dX2lo3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP3LFN3sp11b2b02b12b22b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA NSX XW XL0 OX0 UW0 UWX LFN"] Lemma em_sgn : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc dRc : mpd) (slA slB ts : list word) (v f : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    EMJ sp1 T hc LBc mc dXc dRc slA slB ts -> HREL hc v f -> JSLOTS T slA ->
    (forall (m' : mem) (slA' : list word),
       EMJ sp1 T hc LBc m' (set_sg dXc 1) dRc slA' slB ts -> JSLOTSX T slA' ->
       aevtA asegs (KF asegs R HIA hc mo) POSTA
         (MS (RJ xra sp1 t0 t1 t2 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658320) fc None m' (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo) POSTA
      (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658272) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JS K.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose EJ as (EB & LA & LBl & J & _). dpose J as (_ & AD & _).
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    repeat (destruct slB as [|? slB]; [discriminate LBl|]). destruct slB; [| discriminate LBl].
    dpose EB as (_ & _ & _ & SAVE & CHS & _ & SThi & STlo & _ & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. pose proof (Forall_inv (Forall_inv_tail CHS)) as CHB. cbn [fst snd map] in CHA, CHB.
    pose proof MXc as [(CX & XAL & X0 & _) _]. rewrite AD in CX. unfold mpi_cells in CX.
    destruct XWc as [CW _]. rewrite AD in CW. destruct OXc as [OXa _]. rewrite AD in OXa.
    pose proof (aobj_crange _ _ _ _ _ _ OXa) as CRXc. pose proof (aobj_crange _ _ _ _ _ _ (proj1 OX0)) as CRX0.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (rw_cells_bound _ _ _ _ CX) as XB. cbn [cells_size csize Nat.add] in XB.
    assert (DSX1 : X + 16 <= sp1 \/ sp1 + 288 <= X) by (clear - DSX SP1 SLO NEEDE; lia).
    unfold EM_POISON_RR in SHC.
    pose proof (munch_refl [(sp1, sp1 + 40); (X, X + 16)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep_to [658288]. zstep_to [658292]. zstep_to [658296]. zstep_to [658304].
    (* [comment removed for export] *)
    assert (E8 : Z.shiftr (X + 8) 3 + al_sb AL = Z.shiftr X 3 + al_sb AL + 1) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - XAL; Z.div_mod_to_equations; lia).
    rewrite E8. zstep_to [658308]. zstep_to [658312].
    zstep_to [658316]. zstep_to [658320].
    lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo sp1, H3 : HM _ _ _ hc LBc LF ?m2, H4 : stk asegs ?m2 (sp1 + 216) _ |- _ =>
      lazymatch type of CHA with rw_cells _ _ _ ?csA =>
        let wsA := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) csA) in
        eapply (K m2 wsA);
          [ eapply (emj_upd sp1 T hc LBc mc dXc dRc _ _ ts v f m2 wsA 1 EJ HR); [| reflexivity| exact MU| exact WM| exact CX| left; reflexivity];
            unfold EMBs; refine (conj SP1 (conj SP1M (conj H3 (conj SAVE (conj _ (conj _ (conj H4 (conj H2 (conj H1 (conj SHC (conj SSlo (conj SShi (conj SNlo (conj SNhi PRES))))))))))))));
            [ repeat (apply Forall_cons; [cbn [fst snd]; first [exact CHA| exact CHB]|]); apply Forall_nil
            | repeat (apply Forall_cons; [unfold chunk_in; cbn [fst snd cells_size csize map Nat.add]; clear; lia|]); apply Forall_nil ]
          | split; [exact JS| split; reflexivity] ]
      end end.
    all: match goal with |- ?g => idtac "SGN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L22368734472.131L4240556514.125 L56765669119.12600000F00X00hS2LF2sp3LFN1a2l12h12HrS1R2LF2sp3LFN1c2HrS2LF2sp3LFN1a2Ha". (* [comment removed for export] *)
  #[using="sp LFN d"] Lemma presW_munch_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Phc,(29.$4.VR,VHIA,)PSPq,$2.PSSPq,$2.PWq,(28.$2<.)Pmq,P,(16.&40.)(2;.(16.&8.))Pm',P,(16.&40.)(2;.(16.&8.))PW',(28.$2<.)P,(21.$4.VR,VHIA,Vh,(22.VLB,VdX,)VLF,R6.R5.R4.Vm,R3.)P,(5?.R2.R4.R3.)P,(60.$4.R5.R4.)P,Px,$2.P,(7.$4.VR,VHIA,Vh,R1.)(7.$4.VR,VHIA,R<.R2.)P,(8;.(7.$4.VR,VHIA,R;.)R5.)P,(54.(23.$2.$2.)Liv,(23.$2.$2.)(8<.VR,(22.VLB,VdX,)VLF,R<.R:.(55.$2.$2.R1.)(<.(56.$2.$2.R1.)(55.$2.$2.R1.)))R6.)(21.$4.VR,VHIA,Vh,(22.VLB,VdX,)VLF,R<.R;.R:.Vm,R8.)")
(* [comment removed for export] *).
  Proof.
    (intros hc SPq SSPq Wq mq m' W' dd_H; ddestruct dd_H as (P & C1 & C2 & C3); intros MU WM HCS HW HC).
    split; [| split; [exact C1| split; [exact C2| exact C3]]].
    eapply presA_trans; [exact P|]. split.
    - intros a Ha Hc Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
      destruct (outside_dec W' a) as [Y|NO]; [exact Y|]. exfalso.
      ddestruct (not_outside_in W' a NO) as (l1 & h1 & HIn & Hr).
      rewrite Forall_forall in HC. exact (HC (l1, h1) HIn a ltac:(cbn; lia) Hc Ho).
    - intros c Hc Hr. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
      pose proof (hcs_ok asegs R HIA hc) as OK. destruct OK as (K1 & _). apply (outside_of_not_cs (hcs asegs R HIA hc)); [exact HW|].
      exact (proj2 (proj2 (proj2 (K1 c (HCS c (C1 c Hc)))))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L46184773570.11500000HS2LF2sp3LFN2h11q1a2Ha2H1". (* [comment removed for export] *)
  #[using="LF sp LFN d"] Lemma dj_above : forall (W : list ivl) q a n, Forall (fun iv => snd iv <= q) W -> q <= a -> disjoint_from W a n.
  Proof. induction W as [|[l1 h1] W IH]; intros q a n HW Ha; cbn [disjoint_from]; [exact I|]. inversion HW; subst. cbn [snd] in *. split; [right; lia| eapply IH; eassumption]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L11118514343.120L15060807298.12100000D00[S2LF2sp3LFN2l12h12H3S1R2LF2sp3LFN2l12h11c1Q". (* [comment removed for export] *)
  #[using="LF sp LFN d"] Lemma dj_shadow : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PCSq,P,$2.SpPW,(28.$2<.)Pc,$2.Pk,$2.P,(8=.(1=.VR,)R4.)P,(8;.R5.R4.)P,(54.(23.$2.$2.)Liv,(23.$2.$2.)(34.(55.$2.$2.R1.)(56.$2.$2.R1.))R5.)P,(3<.R7.R5.(3>.+8.R4.))P,(34.=R5.)(33.R8.(37.(1=.VR,)R7.)R6.)")
(* [comment removed for export] *).
  Proof.
    intros CSq W c k OK. induction W as [|[l1 h1] W IH]; intros HW HP HC Hk; cbn [disjoint_from]; [exact I|].
    inversion HW; subst. inversion HP; subst. cbn [fst snd] in *. split; [| apply IH; assumption].
    destruct (apart_shadow_client AL CSq l1 (h1 - l1) c (shadow_of AL c) k OK ltac:(assumption) HC eq_refl ltac:(lia) Hk) as [Q|Q]; [left; exact Q| right; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L10134628787.4L1685717371.0 L23927528628.8L35653441506.7L39188636933.0L42437087959.3L52045659405.3L57031302710.7L60098763854.3L6180070147.4 L62018535662.1L64052154934.7L64683549666.9L8071854405.2 L8931608776.1 00000;00<00Y01101201=01I01d01n02=02@02[03<03C03HS2sp2lo3sp1SS1R3HIA1h2sp3TOP3sp13SP14HTOPS1R3HIA1h2sp2lo3TOP4HTOPSS1R3slo3SSLS2sp3sp13SP1S1R2sp2lo3SLO5NEEDE3sp13SP1S1R2lo3LOSS2sp2lo3sp13SP1S1RS1R2sp2lo3SLO5NEEDE3sp13SP1S1R3HIA1h2sp3slo3TOP3sp13SP14HTOPS1R3sp1S3sp1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL LFN d"] Lemma embs_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "PPC,(28.$12.)Psp1,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmq,P,(16.&40.)(2;.(16.&8.))PCH,(28.(23.$2.(28.$12.)))PW,(28.$2<.)Pm',P,(16.&40.)(2;.(16.&8.))P,(1.$17.(2=.R8.)#<.)P,(58.R9.R8.R7.R6.R5.R4.)P,Px,$2.P,(7.$4.VR,VHIA,Vh,R1.)(7.$4.VR,VHIA,R:.R2.)P,(1.$2.(5.$4.VR,VHIA,R9.)(5.$4.VR,VHIA,Vh,))P,(5?.R6.R8.R5.)P,(60.$4.R9.R6.)P,(1:.$4.R7.)P,(19.$4.R8.Vlo,R>.)P,(?.$4.VR,VHIA,R>.R=.VLF,R9.)P,(8;.(7.$4.VR,VHIA,R?.)R;.)P,(54.(23.$2.$2.)Liv,(23.$2.$2.)(34.(55.$2.$2.R1.)(56.$2.$2.R1.))R<.)P,(54.(23.$2.$2.)Liv,(23.$2.$2.)(8.(56.$2.$2.R1.)R13.)R=.)P,(54.(23.$2.$2.)Liv,(23.$2.$2.)(8<.VR,(22.VLB,VdX,)VLF,(=.&40.Vsp,)(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))(55.$2.$2.R1.)(<.(56.$2.$2.R1.)(55.$2.$2.R1.)))R>.)(58.R15.R14.R13.R12.R>.R10.)")
(* [comment removed for export] *).
  Proof.
    (intros PC sp1 hc LBc mq CH W m' HPC dd_H; ddestruct dd_H as (SP1 & SP1M & HHq & SAVE & CHS & CHI & SThi & STlo & MIq & SHC & SSlo & SShi & SNlo & SNhi & PRES); intros HCS HS1 MU WM MI' ST' HH' WC WP WB WCV).
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    unfold EMBs. split; [exact SP1|]. split; [exact SP1M|]. split; [exact HH'|].
    split; [eapply rw_cells_transport; [exact SAVE| exact MU| exact WM| eapply dj_above; [exact WB| clear - SP1; lia]]|].
    split. { rewrite Forall_forall in *. intros ac Hac. eapply rw_cells_transport; [exact (CHS ac Hac)| exact MU| exact WM| eapply dj_above; [rewrite Forall_forall; exact WB| exact (proj1 (CHI ac Hac))]]. }
    split; [exact CHI|].
    split; [eapply stk_transport_disjoint; [exact SThi| exact MU| exact WM| eapply dj_above; [exact WB| clear; lia]]|].
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite HPC.
             replace (Z.shiftr (sp1 + 96) 3 + al_sb AL) with (shadow_of AL (sp1 + 96)) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
             apply (dj_shadow (hcs asegs R HIA hc)); [exact CSOKc| exact WC| exact WP| | clear; lia].
             eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]. }
    split; [eapply (sshad_munch asegs AL (hcs asegs R HIA hc)); [exact CSOKc| exact WC| eapply crange_sub; [exact SCS0c| clear - SSL; lia| clear - SP1 TOP HTOP; lia]| exact MU| exact WM| exact SSlo]|].
    split; [eapply (sshad_munch asegs AL (hcs asegs R HIA hc)); [exact CSOKc| exact WC| eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MU| exact WM| exact SShi]|].
    split; [eapply (snapA_munch asegs AL (hcs asegs R HIA hc)); [exact CSOKc| exact WC| eapply crange_sub; [exact SCS0c| clear; lia| clear - SP1 TOP HTOP; lia]| exact MU| exact WM| exact SNlo]|].
    split; [eapply (snapA_munch asegs AL (hcs asegs R HIA hc)); [exact CSOKc| exact WC| eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MU| exact WM| exact SNhi]|].
    eapply (presW_munch_c hc); [exact PRES| exact MU| exact WM| exact HCS| exact WC| exact WCV].
    all: match goal with |- ?g => idtac "EMBSM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11558783777.4 L18078242826.6 L27739284940.7 L28375828416.10L30620693495.6 L35653441506.7 L4029010041.6  L456726504.6   L56307089111.11L56693472467.4 L59460993896.6 L59654577821.4 L60098763854.3 L6203936179.1  L64604774881.7 L7483610394.8  00000700J00a01?01S01k02902J02e03203E03R03\03a04604PS3sp11aS1R2lo3LOS3sp11a2HaS1R2lo3LOS3sp11a2Ha3ALOS2lo2dE2dN3sp11T2ts1a2TL2Ha2BLS2lo3sp13dRc1a2Ha2BLS1R3HIA1h2sp2lo3TOP4HTOPS2sp3sp11a3SP1S2sp2lo3sp11a3SP1S2sp2dX2lo3DSX3sp11a2Ha3SP1S2lo3sp11a2HaS2lo3sp13dXc1a2Ha1QS2lo3sp11a2HaS1R2lo3LOSS3sp1S1R2lo3LOS3ALO1B1k2BLS1R3HIA1h2sp3TOP3sp11a3SP1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA NSX XW XL0 UW0 UWX LFN"] Lemma emj_pure : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Pa,$2.Pm',P,(16.&40.)(2;.(16.&8.))P,(6<.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(4:.R=.R5.R4.)P,(0.(8.Vlo,R4.)(34.R4.R10.))P,(5?.(11.(23.$2.$2.)(24.$2.$2.R5.R11.)(14.(23.$2.$2.)))R=.R4.)P,(60.$4.R>.R5.)P,(1:.$4.R6.)P,(19.$4.R7.Vlo,R14.)(6<.R15.R14.R13.R12.R8.R10.R?.R>.R=.R<.)")
(* [comment removed for export] *).
  Proof.
    intros sp1 T hc LBc mc dXc dRc slA slB ts v f a m' EJ HR Ha MU WM MI' ST'.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    ddestruct EJ as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose J as (_ & AD & PD & NS & NM & FRA & FRS & OXa & O3 & O4 & O5 & OEX & NDE).
    dpose EB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PRES).
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hcs_ok asegs R HIA hc) as CSOKc.
    pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (WC : w_client (hcs asegs R HIA hc) [(a, sp1)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSc| clear - Ha; lia| clear - Ha SP1; lia]| apply Forall_nil]. }
    assert (HH' : HM asegs R HIA hc LBc LF m').
    { eapply (hm_munch asegs R HIA hc LBc LF _ mc m'); [exact HHc| exact MU| exact WM|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. apply w_writable_of_client_wrange. apply client_wrange_stack; [clear - Ha LOS; lia| rewrite HT1; clear - SP1 TOP; lia]. }
    assert (BLOW : forall B k, In (B, k) LBc -> B + k <= lo).
    { intros B k Hb. pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc B k ltac:(apply in_or_app; left; exact Hb)) as BL. clear - BL ALO LOS. lia. }
    unfold EMJ.
    split. { eapply (embs_munch EM_POISON_RR sp1 hc LBc mc _ [(a, sp1)] m'); [reflexivity| exact EB| exact HCS1| exact HS1| exact MU| exact WM| exact MI'| exact ST'| exact HH'| exact WC| | |].
             - apply Forall_cons; [cbn [fst snd]; clear - Ha; lia| apply Forall_nil].
             - apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil].
             - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. eapply (wcover_of_stack asegs R HIA h); [exact PRES| clear - Ha LOS ALO; lia| clear - Ha SP1; lia]. }
    split; [exact LA|]. split; [exact LBl|].
    split. { unfold XST. split.
             { eapply mpd_at_munch_any; [exact MXc| exact MU| exact WM| |].
               - rewrite AD. cbn [disjoint_from]. split; [clear - DSX Ha SP1 SLO NEEDE; lia| exact I].
               - intros NN. pose proof (XLc NN) as Q. cbn [disjoint_from]. split; [clear - Q Ha; lia| exact I]. }
             split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|]. split; [exact FRA|]. split; [exact FRS|].
             split; [eapply (aobj_munch asegs AL _ CSOKc _ mc m'); [exact WC| exact MU| exact OXa]|].
             split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. split; [exact OEX| exact NDE]. }
    split. { eapply mpd_at_munch_any; [exact MR| exact MU| exact WM| |].
             - rewrite AR. cbn [disjoint_from]. split; [clear - Ha; lia| exact I].
             - intros NN. pose proof MR as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dRc) eqn:EOR; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSR eq_refl)].
               ddestruct OW as (_ & RIN & _). pose proof (BLOW _ _ RIN) as BL. cbn [disjoint_from]. split; [clear - BL Ha; lia| exact I]. }
    split; [exact AR|]. split; [exact NSR|]. split; [| split; [exact TL| exact WLB]].
    eapply (u32arr_transport asegs _ mc m'); [exact TA| exact MU| exact WM|].
    destruct (OEX (T, WL * 4) (or_introl eq_refl)) as (TIN & _). pose proof (BLOW _ _ TIN) as BL.
    cbn [disjoint_from]. split; [clear - BL TL Ha; lia| exact I].
    all: match goal with |- ?g => idtac "PURE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L17863669337.8 L17863669337.9 L17863900410.7 L17866097887.11L27940405558.7 L27940637589.6 L29428324939.5 L3482559548.6  L3482791583.7  L35651271058.7 L35653441506.7 L37250098319.11L37251814921.10L37251814921.8 L37252045994.7 L38235734261.1 L39288187904.7 L39288481443.10L39288481443.8 L39290164261.11L48834180257.0 L59308567674.3 L59315284336.3 L59315284336.4 L59315284336.5 L60098763854.3 L66151427842.16L9080220944.4  00000100G00H00I00d00e01701801901T01l01m01n01o02002402502602702802902G02Q02R02S02]03903HFS2sp2dX2lo3DSX3sp13SP1FFS1R2sp2lo3SLO5NEEDE3sp13SP1FS1R2lo3LOS3ALO3ACPFFS1R2sp2lo3SLO5NEEDE3sp13SP1S1R3HIA1h2sp2lo3TOP4HTOPFFFFS2loFFFFSS3dXc2N12OW2dNS3dXc2N11QFFS1R2lo3LOSS3sp12r04SP1M1q1r1H2H02q02H4S2sp2lo3sp13SP1". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA MI0 NSX XW XL0 UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN LFN ROIMG"] Lemma em_cmp : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc dRc : mpd) (slA slB ts : list word) (v f : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    EMJ sp1 T hc LBc mc dXc dRc slA slB ts -> HREL hc v f ->
    (forall (m' : mem) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
       EMJ sp1 T hc LBc m' dXc dRc slA slB ts ->
       aevtA asegs (KF asegs R HIA hc mo) POSTA
         (MS (RJ (Z_to_bv 64 658332) sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658336) fc None m' (seg_rom asegs))) ->
    (forall (m' : mem) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
       EMJ sp1 T hc LBc m' dXc dRc slA slB ts ->
       aevtA asegs (KF asegs R HIA hc mo) POSTA
         (MS (RJ (Z_to_bv 64 658332) sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658356) fc None m' (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo) POSTA
      (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658320) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR KM KG.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & SPN & OSN' & CRN' & CRNL' & ODN').
    ddestruct VN as (_ & _ & _ & NRN & _ & _ & _ & _ & ONs & ONl & _ & MNc).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose EJ as (_ & _ & _ & J & _). dpose J as (_ & AD & _). destruct OXc as [OXa _]. rewrite AD in OXa.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    assert (HP0 : forall dq, mpd_at asegs mc LBc dq -> md_own dq = LHeap -> 0 < md_p dq).
    { intros dq MQ EH. destruct MQ as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
      destruct (hm_apart asegs R HIA hc LBc LF mc HHc) as [HFA _]. rewrite Forall_forall in HFA. destruct (HFA _ ltac:(apply in_or_app; left; exact HIN)) as (P0 & _). exact P0. }
    (* [comment removed for export] *)
    zstep_to [658328]. zstep.
    pose proof (A_mpi_cmp_mpi_spec AL IMG) as SPC. unfold mpi_cmp_mpi_stmtA, A_MPI_CMP_MPI_E in SPC.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { eapply SPC with (CS := hcs asegs R HIA hc) (LB := LBc) (dX := dXc) (dY := dN) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD;
        first [ exact MXc | exact MNc | exact (HP0 _ MXc) | exact (HP0 _ MNc) | exact MIc | exact CSOKc | exact (hm_abase asegs R HIA hc LBc LF mc HHc) | exact (art_alwf asegs R HIA)
              | exact OXa | exact ONs | exact ONl | exact STc | reflexivity
              | intros N1; pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]; destruct (md_own dXc) eqn:EO; [exfalso; destruct OW as (_ & Q); clear - Q N1; lia| | exfalso; exact (NSc eq_refl)];
                ddestruct OW as (_ & HIN & _); exact (hm_aobj_block asegs R HIA hc LBc LF mc _ _ HHc HIN)
              | eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
              | clear - ALO ACP LOS; lia | clear - SP1 SLO NEEDE; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | clear - DSX SP1 SLO NEEDE; lia
              | ddestruct OSN' as (_ & _ & _ & Q & _); exact Q
              | intros N1; apply XLc; intros EN; pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]; rewrite EN in OW; clear - OW N1; lia
              | intros N1; ddestruct OSN' as (_ & _ & _ & _ & Q); apply Q; intros EN; pose proof MNc as [(_ & _ & _ & _ & _ & OW) _]; rewrite EN in OW; clear - OW N1; lia
              | match goal with |- ?g => idtac "CMP-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_cmp_postA in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m' & -> & MUc & WMc & MI' & ST').
    replace (ret_pc (Z_to_bv 64 658332)) with (Z_to_bv 64 658332 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (emj_pure sp1 T hc LBc mc dXc dRc slA slB ts v f lo m' EJ HR ltac:(clear - SP1 SLO NEEDE; lia) MUc WMc MI' ST') as EJ'.
    pose proof (munch_refl ([] : list ivl) m') as MU'. pose proof (wmono_refl asegs m') as WM'.
    (* [comment removed for export] *)
    (zstep_to [658332]; zstep). if_cases KS; [eapply KG| eapply KM]; exact EJ'.
    all: match goal with |- ?g => idtac "CMP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MODS : mpi_mod_mpi_stmtA_sz asegs R HIA A_MPI_MOD_MPI.
  Hypothesis LFN3 : (length LF + 3 <= 512)%nat.
  Hypothesis SZJ : Z.max (md_n dA) (md_n dN) + 3 <= SZB.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L10239831877.8L36861863765.800000G00^S1R3HIA1h2hc1f2f'2H62HfS1R3HIA1h2hc1v2v'2H52Hv". (* [comment removed for export] *)
  #[using="Type d"] Lemma hrel_weaken : forall hc v f v' f', HREL hc v f -> v <= v' -> f <= f' -> HREL hc v' f'.
  Proof. (intros hc v f v' f' dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & H5 & H6); intros Hv Hf). unfold HREL. repeat (split; [assumption|]). split; [clear - H5 Hv; lia| clear - H6 Hf; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L17863669337.9 L38569812941.1 L41886271693.1 L59657045483.1100000F00K00P016S2sp2dX2lo3DSX3sp13SP1S3dXcS3dXcS1R3HIA2sp2lo3SLO5NEEDE3sp12hc3SP11a1S". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SLL DSX d SPA NSX XW XL0 UW0 UWX"] Lemma emj_xself : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.P,(6<.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4:.R;.R3.R2.)(0.(77.R9.R9.Vlo,R>.)(0.(78.(79.VR,)(6=.$2:.R;.(7:.VLF,))Vlo,(25.R9.)+10.)P,(1.$39.(3:.R9.)$7;.)(78.(79.VR,)(6=.$2:.R<.(7:.VLF,))Vlo,(3=.R:.)(3>.+4.(3?.R:.)))))")
(* [comment removed for export] *).
  Proof.
    intros sp1 T hc LBc mc dXc dRc slA slB ts v f EJ HR.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    ddestruct EJ as (_ & _ & _ & J & _). ddestruct J as (_ & AD & _).
    destruct XWc as [CWc XPc].
    assert (OH : md_own dXc <> LNull -> md_own dXc = LHeap) by (intros NN; destruct (md_own dXc); [exfalso; exact (NN eq_refl)| reflexivity| exfalso; exact (NSc eq_refl)]).
    split. { unfold opnd_sep. split; [intros NN; exact (XPc (OH NN))|]. split; [exact XPc|]. split; [left; reflexivity|]. split; [rewrite AD; clear - DSX SP1 SLO NEEDE; lia| exact XLc]. }
    split. { intros a Ha. destruct (CWc a Ha) as [S|[D|B]]; [left; clear - S SP1 SLO NEEDE; lia| right; left; exact D| right; right; exact B]. }
    intros EH. pose proof MXc as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
    eapply client_range_block; [apply in_or_app; left; exact HIN| clear; lia| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@L10268130018.2  L11966358048.11 L11967260278.7  L11967260278.8  L11968507292.13 L11968893094.14 L13738244421.4  L13738244435.4  L13739537107.5  L1601062831.2   L19237575590.8  L20178123189.7  L20178643381.5  L20619246266.4  L23153701914.3  L24652142338.8  L29010569222.241L31188595651.6  L31571928837.7  L31571928837.8  L31572140883.12 L31574224111.14 L31574584559.15 L31574610389.15 L3173786800.4   L3482791583.7   L3483319967.3   L41221909427.3  L47110352746.7  L5035427872.5   L5046093606.9   L5048087968.12  L54296017491.4  L54300097155.10 L54300116921.16 L54300477369.14 L54302114131.3  L54302114131.5  L54302558213.8  L56238802910.6  L58775898692.9  L58778450114.12 L58782565698.5  L59311123693.3  L62799502113.0  L64883681958.4  L66151426447.10 L66151427842.16 L66947011490.1  L6970806972.5   00000600700800900d00e01101=01>01G01f02;02<02=02H02I02J02[02\02]02^02_03P03Q03a03b03c03d03e03f03g03h04:04;04<04=04>04?04@04W04X04Y04Z04[04\04]04n05J05N05^S1d2D0FFFS1R3HIA1h3PHI2dN4BUDT2dA2hc3dXc1v2HV3HV12PMFS1R2dX1d3UWXS1R1d2dN3UWNFS2LF4LFN3S2dN3SZB2dA3SZJ3dXc3SZc3dX23NSZS1R2sp2lo3SLO3sp13SP1FFS2dX2dN3SXNFFS2FR1d2dN2dA1f2HFFFFFS1R3HIA1h2FR1d2dN5BUDFT2dA2hc3dXc1f2HF4HFR12D02FMFS2dA3dXc3SZc3NRXFFFFFFFS2LB4C24J3LBc4C24cFFFFFFS2dN2dA3dXc3SZc3dX23NSZFFFFSFS1r3RNG2r02KT1q1HS3sp12r04SP1M1q1r1H2H02q02H4S2dNS3PHI2dN2dA1v2HV". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 NSX XW XL0 TPV UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN HND ZF MPIFREE SZB RRX BUDT BUDFT UWN ROIMG C24J MODS LFN3 SZJ d"] Lemma em_mod : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc dRc : mpd) (slA slB ts : list word) (v f : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    EMJ sp1 T hc LBc mc dXc dRc slA slB ts -> HREL hc v f -> JSLOTSX T slA -> md_n dXc <= md_n dA ->
    v + mod_mpi_PHIn (md_n dA) (md_n dN) + 2 * AVOL_CALL <= PHI ->
    f + mod_mpi_FRn (md_n dA) (md_n dN) (d + 1) + (fr_charge (d + 1) + fr_charge (Z.max (d + 1) 28)) <= FR ->
    (forall (h2 : HST asegs R HIA) (LB2 : list blk) (m2 : mem) (dX2 : mpd) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
       EMJ sp1 T h2 LB2 m2 dX2 dRc slA slB ts -> HREL h2 (v + mod_mpi_PHIn (md_n dA) (md_n dN)) (f + mod_mpi_FRn (md_n dA) (md_n dN) (d + 1)) ->
       md_n dX2 <= Z.max (md_n dA) (md_n dN) + 2 ->
       aevtA asegs (KF asegs R HIA h2 mo) POSTA
         (MS (RJ (Z_to_bv 64 658352) sp1 y0 y1 y2 (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658356) fc None m2 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo) POSTA
      (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658336) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JS SZc HV HF K.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_xself _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (OSX & CRX & CRXL).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & SPN & OSN' & CRN' & CRNL' & ODN').
    ddestruct VN as (_ & _ & _ & NRN & _ & _ & _ & _ & _ & _ & _ & MNc).
    pose proof (emj_cnt24 _ _ _ _ _ _ _ _ _ _ EJ) as C24c.
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as ((S5 & S6 & S7 & S8 & S9 & S10 & S11) & S3 & S4).
    dpose EJ as (_ & _ & _ & J & _). dpose J as (_ & AD & _ & _ & NMc & _).
    pose proof MXc as [(_ & _ & _ & _ & NRX & _) _]. unfold MPI_MAX_LIMBS in NRX.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (mod_mpi_PHIn_mono (md_n dXc) (md_n dN) (md_n dA) (md_n dN) SZc ltac:(clear; lia)) as PM.
    pose proof (mod_mpi_FRn_mono (md_n dXc) (md_n dN) (d + 1) (md_n dA) (md_n dN) (d + 1) ltac:(clear - NRX SZc; lia) ltac:(clear; lia) ltac:(clear - D0; lia)) as FM.
    (* [comment removed for export] *)
    zstep_to [658340]. zstep_to [658344]. zstep_to [658348]. zstep_to [656560].
    pose proof MODS as MD'. unfold mpi_mod_mpi_stmtA_sz, mpi_binop_stmtA_sz in MD'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply MD' with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (dA := dXc) (dB := dN) (lo := lo) (d := d + 1) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD;
        first [ exact HHc | exact HK1 | exact MXc | exact MNc | exact NSc | exact OSX | exact OSN' | exact SPN | exact CRN' | exact CRNL' | exact XWc | exact XLc | exact STc | exact LOS | exact TPV
              | exact MIc | exact OXc | exact ODN' | exact IMN | exact UWc | exact TOPc | reflexivity
              | left; reflexivity
              | rewrite <- AD; exact CRX | exact CRXL
              | clear - LFN3; lia
              | intros _; clear - SXN; lia
              | intros _; split; [exact SSc| split; [exact SSL| exact SLL]]
              | intros ES; exfalso; exact (NSc ES)
              | clear - SP1 SLO NEEDE; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | unfold uw_obj in *; clear - UWX; lia | unfold uw_obj in *; clear - UWN; lia
              | clear - HV1 HV BUDT PM; unfold AVOL_CALL in *; lia | clear - HFR1 HF BUDFT FM D0; unfold fr_charge in *; lia
              | clear - C24c C24J; lia
              | match goal with |- ?g => idtac "MOD-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E' & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite AD in HP2.
    replace (ret_pc (Z_to_bv 64 658352)) with (Z_to_bv 64 658352 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    ddestruct CR as [[[CRV RNG] BK] NSZ]. unfold mod_mpi_nz in NSZ.
    destruct (emj_call sp1 T hc LBc mc dXc dRc slA slB ts v f h2 LB2 m2 dX2 _ _ EJ HR MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as (EJ2 & HR2).
    pose proof (hrel_weaken _ _ _ _ _ HR2 ltac:(apply Z.add_le_mono_l; exact PM) ltac:(apply Z.add_le_mono_l; exact FM)) as HR2'.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    (zstep_to [658352]; zstep). if_cases KT; zify_cond KT.
    - eapply (em_clean sp1 T h2 LB2 m2 dX2 dRc slA slB ts _ _ r); first [exact EJ2| exact HR2'| exact S6| exact S7| clear - HV; lia| clear - HF; unfold fr_charge in *; lia| exact RNG| clear - NSZ SZc SZJ; lia| match goal with |- ?g => idtac "MOD-CLEAN-LEFT:" g end].
    - assert (R0 : r = 0) by (clear - KT RNG; Z.div_mod_to_equations; lia). subst r.
      eapply K; [exact EJ2| exact HR2'| clear - NSZ SZc; lia].
    all: match goal with |- ?g => idtac "MOD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis GROW : mpi_grow_stmtA_c asegs R HIA A_MPI_GROW.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0@L13738244421.4  L20623814586.6  L21870408481.0  L22594986486.2  L23929266568.5  L23929269012.8  L24346769590.2  L29956516996.0  L31188595651.4  L3482346814.8   L3482349474.3   L38569812941.1  L40738020923.4  L49043110421.4  L5045880347.5   L5045881991.10  L5048087968.12  L54300097155.10 L54300162054.12 L54302081956.9  L54302083384.3  L54302114131.5  L54302182149.11 L58641002120.190L62484994806.2  L66151427842.16 L6970806972.4   L7374872921.6   L7374872921.7   L7375195020.11  L7375390985.13  L7377399854.11  L7377402546.5   L7377402546.6   L7377500303.10  L7377500303.11  Q16285785003.193Q17968854497.192Q17969015064.193Q17969358874.190Q31816089576.190Q39212284437.193Q51752217908.192Q60305443321.193Q60511567613.193Q9538787269.190 00000<00S00T00\00]01601>01?01J01K01L01Q01c02202302402502602702802902:02;02X02`03<03I03J03K03o04004104204304T04U04k05>05Q05d06706J06]07007C07VS1R2dX1d3UWXS2dN3SZB2dA3SZJ3dXc3SZcSS2dN3NRNFS1R2sp2lo3SLO3sp13SP13NERS2dN3dXcSS2FR1d1f2HFFFS3dXcS2LB4C24J3LBc4C24qS2dN2dA3dXc3SZcFFFFFFFFFS2LF2sp2dN3LFN2dA4LFN33sp12NBS2dN3NRNS3sp12r04SP1M1q1r1H2H02q02H4S3PHI2dN1v2HVFFS1R3HIA1h2FR1d5BUDFT2hc1f2HF4HFR12D0FFFFS1R3HIA1h3PHI2dN4BUDT2hc1v2HV3HV1FS2LF2dN3LFN2dA4LFN32NBS2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 NSX XW XL0 TPV UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN HND ZF MPIFREE SZB RRX BUDT BUDFT LFN ROIMG C24J LFN3 SZJ GROW d"] Lemma em_grow : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc dRc : mpd) (slA slB ts : list word) (v f : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    EMJ sp1 T hc LBc mc dXc dRc slA slB ts -> HREL hc v f -> JSLOTSX T slA -> md_n dXc <= Z.max (md_n dA) (md_n dN) + 2 ->
    v + grow_PHI (md_n dN) + 2 * AVOL_CALL <= PHI ->
    f + grow_FR (d + 1) + (fr_charge (d + 1) + fr_charge (Z.max (d + 1) 28)) <= FR ->
    (forall (h2 : HST asegs R HIA) (LB2 : list blk) (m2 : mem) (dX2 : mpd) (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
       EMJ sp1 T h2 LB2 m2 dX2 dRc slA slB ts -> HREL h2 (v + grow_PHI (md_n dN)) (f + grow_FR (d + 1)) ->
       md_n dN <= md_n dX2 <= Z.max (md_n dA) (md_n dN) + 2 ->
       aevtA asegs (KF asegs R HIA h2 mo) POSTA
         (MS (RJ (Z_to_bv 64 658384) sp1 y0 y1 y2 (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658388) fc None m2 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo) POSTA
      (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658356) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JS SZc HV HF K.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & _).
    ddestruct VN as (CN & _ & _ & NRN & _ & NB & _ & NAL & ON & _ & _ & MNc).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as ((S5 & S6 & S7 & S8 & S9 & S10 & S11) & S3 & S4).
    dpose EJ as (_ & _ & _ & J & _). dpose J as (_ & AD & _).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof EJ as (EB & LA & _). dpose EB as (_ & _ & _ & _ & CHS & _). pose proof (Forall_inv CHS) as CHA. cbn [fst snd map] in CHA.
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    cbn [nth_error] in S8, S9. cbn [map] in CHA. injection S8 as ->. injection S9 as ->.
    shadow_byte ON (N + 10) 2 as k RD HK. zstep. zstep. clear RD. step_to_if.
    lazymatch goal with
    | |- aevtA ?segs _ _ (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
        lazymatch decode_at segs (slow + 4)%Z with
        | Some (OpImm ALU_AND ?tmp _ _, _) =>
            let pt := eval vm_compute in (bv_key tmp) in
            lazymatch decode_at segs (slow + 12)%Z with
            | Some (Branch BC_LT _ ?kr _, _) =>
                let pk := eval vm_compute in (bv_key kr) in
                merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro)
            end
        end
    end;
    [ let Kz := fresh "Kz" in
      if_cases Kz; zify_cond Kz;
      [ zstep; step_to_if;
        lazymatch goal with
        | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
            replace cnd with true by (symmetry; eapply (shadow_slow_takenN (N + 10) _ k _ HK Kz); qlia); cbv iota
        end;
        apply evtA_done; eexists; eexists; reflexivity
      | apply evtA_done; eexists; eexists; reflexivity ]
    | intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k ].
    zstep_to [658376]. rewrite zx16_small by (clear - NRN; lia). zstep_to [658380]. zstep_to [635868].
    pose proof GROW as GR'. unfold mpi_grow_stmtA_c, mpi_xop_stmtA_c in GR'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GR' with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (v := md_n dN) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD;
        first [ exact HHc | exact HK1 | exact MXc | exact NSc | exact XWc | exact XLc | exact STc | exact LOS | exact TPV | exact MIc | exact OXc | exact UWc | exact TOPc | reflexivity
              | clear - NRN; lia
              | clear - SP1 SLO NEEDE NER; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | unfold uw_obj in *; clear - UWX; lia
              | clear - HV1 HV BUDT; unfold AVOL_CALL in *; lia | clear - HFR1 HF BUDFT D0; unfold fr_charge in *; lia
              | (lazymatch goal with |- cnt24 _ + _ <= C24MAX => idtac end; pose proof (emj_cnt24 _ _ _ _ _ _ _ _ _ _ EJ) as C24q; unfold C24_COPY_c, C24_GROW_c, C24_MOD_MPI in *; clear - C24q C24J; lia)
              | match goal with |- ?g => idtac "GROW-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E' & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite AD in HP2.
    replace (ret_pc (Z_to_bv 64 658384)) with (Z_to_bv 64 658384 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    destruct CR as [CR1 CFR].
    assert (BK : binop_keep LBc dXc dX2).
    { unfold binop_keep. split; [exact (proj1 OUT2)|]. destruct CR1 as [(_ & _ & CN' & CP & _)|(_ & ->)]; [split; [exact CP|]; split; [exact CFR| rewrite CN'; clear; lia]| split; [reflexivity|]; split; [exact CFR| clear; lia]]. }
    destruct (emj_call sp1 T hc LBc mc dXc dRc _ slB ts v f h2 LB2 m2 dX2 _ _ EJ HR MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as (EJ2 & HR2).
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    (zstep_to [658384]; zstep).
    destruct CR1 as [(-> & _ & CN' & _)|(-> & ->)].
    - eapply K; [exact EJ2| exact HR2| rewrite CN'; clear - SZc; lia].
    - eapply (em_clean sp1 T h2 LB2 m2 dXc dRc _ slB ts _ _ (-16)); first [exact EJ2| exact HR2| exact S6| exact S7| clear - HV; lia| clear - HF; unfold fr_charge in *; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| clear - SZc SZJ; lia| match goal with |- ?g => idtac "GROW-CLEAN-LEFT:" g end].
    all: match goal with |- ?g => idtac "GROW-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  (* [comment removed for export] *)
  Definition HARR (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (sp1 B k : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "(0.(30.(23.$2.$2.)(24.$2.$2.O2.O1.)O5.)(0.(34.=O2.)(0.(8.(:.O2.O1.)Vlo,)(0.(34.(:.O2.O1.)(5;.+2.+40.))(0.(32.(8.(:.O2.O1.)Vlo,)(8.O3.O2.))(0.(62.$4.(1=.VR,)(7.$4.VR,VHIA,O6.)O4.O2.O1.)(0.(92.(79.VR,)(6=.$2:.O5.(7:.VLF,))(20.VR,)(3.$4.VR,VHIA,O6.)O2.O1.)(78.(79.VR,)(6=.$2:.O5.(7:.VLF,))Vlo,O2.O1.))))))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L39686996155.5L47010974703.2L61923340120.1L64604774881.700000>00C00F00[S1R1B1k3ACV2BLS1B1kS1BS1R2lo3LOS1B1k3ALO2BL". (* [comment removed for export] *)
  #[using="LOS d"] Lemma harr_of_in : forall hc LBc mc sp1 B k, HM asegs R HIA hc LBc LF mc -> In (B, k) LBc -> HARR hc LBc mc sp1 B k.
  Proof.
    intros hc LBc mc sp1 B k HHc HIN. pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc B k ltac:(apply in_or_app; left; exact HIN)) as BL.
    destruct (hm_apart asegs R HIA hc LBc LF mc HHc) as [HFA _]. rewrite Forall_forall in HFA. destruct (HFA _ ltac:(apply in_or_app; left; exact HIN)) as (P0 & _). cbn [fst] in P0.
    unfold HARR. split; [exact HIN|]. split; [exact P0|]. split; [clear - BL ALO LOS; lia|]. split; [clear - BL ACV; lia|]. split; [left; clear - BL ALO LOS; lia|].
    split; [exact (hm_aobj_block asegs R HIA hc LBc LF mc _ _ HHc HIN)|].
    split; [eapply client_wrange_block; [apply in_or_app; left; exact HIN| clear; lia| clear; lia]| eapply client_range_block; [apply in_or_app; left; exact HIN| clear; lia| clear; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L22195965685.5 L2602216163.3  L26483622524.3 L48132467214.7 L59308587542.16L59308644817.13L59315284336.11L62077484021.5 00000?00L00W01201d02I03403CS2dE2dN1T3dXc1QS3dXc3NRX3N1XS3dXc3dRc1QS1R2sp2lo3LOS3SLO5NEEDE3ALOS1R2sp2lo3LOS3SLO5NEEDE3dXc3ALO1a1n3Ha22BC1x2Hx2HsS1R3dXc1a1n3Ha13Ha22BI1x2Hx3Hd12D12D2S3dXc1a1n3Ha13Ha21x2Hx2B'2k'2Hr1Q2FB2n'3Hr2S2dE2dN1T3dRc1Q". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SLL d SPA MX0 NSX XW XL0 UW0 UWX HND DIMG"] Lemma emj_blk3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.P,(6<.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4:.R;.R3.R2.)P,(1.$39.(3:.R9.)$7;.)P,(1.$39.(3:.R9.)$7;.)(0.(93.R>.R=.R<.R10.(3=.R;.)(3>.+4.(3?.R;.)))(0.(93.R>.R=.R<.R10.(3=.R:.)(3>.+4.(3?.R:.)))(0.(93.R>.R=.R<.R10.R?.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(0.(32.(8.(:.(3=.R;.)(3>.+4.(3?.R;.)))R?.)(8.(:.R?.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(3=.R;.)))(0.(32.(8.(:.(3=.R:.)(3>.+4.(3?.R:.)))R?.)(8.(:.R?.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(3=.R:.)))(0.(32.(8.(:.(3=.R:.)(3>.+4.(3?.R:.)))(3=.R;.))(8.(:.(3=.R;.)(3>.+4.(3?.R;.)))(3=.R:.)))(0.(6;.$4.R<.(3=.R;.)(94.R;.))(0.(1.$2.(59.(18.(16.&40.)(94.R;.)))(3?.R;.))(0.(1.$2.(>.(3=.R;.)+10.)=)(0.(0.(8.+1.(3?.R;.))(8.(3?.R;.)+2710.))(0.(6;.$4.R<.(3=.R:.)(94.R:.))(0.(1.$2.(59.(18.(16.&40.)(94.R:.)))(3?.R:.))(0.(1.$2.(>.(3=.R:.)+10.)=)(0.(8.+1.(3?.R:.))(0.Pa,$2.Pn,$2.P,(8.(3=.R=.)R2.)P,(8.(:.R3.R2.)(:.(3=.R>.)(3>.+4.(3?.R>.))))(8<.VR,(22.VLB,VdX,)VLF,(=.&40.Vsp,)(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))R4.R3.)(0.Pa,$2.Pn,$2.P,(8.R11.R2.)P,(8.(:.R3.R2.)(:.R12.(3>.(49.(3?.VdN,)(3?.VdE,))+4.)))(8<.VR,(22.VLB,VdX,)VLF,(=.&40.Vsp,)(11.(23.$2.$2.)(24.$2.$2.(25.VdX,)(:.(25.VdX,)+10.))(14.(23.$2.$2.)))R4.R3.)(0.(32.(8.(:.(25.VdX,)+10.)(3=.R;.))(8.(:.(3=.R;.)(3>.+4.(3?.R;.)))(25.VdX,)))(32.(8.(:.R?.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(25.VdX,))(8.(:.(25.VdX,)+10.)R?.)))))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros sp1 T hc LBc mc dXc dRc slA slB ts v f EJ HR EHX EHR.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    ddestruct EJ as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB).
    ddestruct J as (_ & AD & PD & NS & NM & FRA & FRS & OXa & O3 & O4 & O5 & OEX & NDE).
    pose proof (art_lo asegs R HIA) as ALO.
    pose proof (HND _ _ _ _ HHc) as ND. destruct (hm_apart asegs R HIA hc LBc LF mc HHc) as [_ BA0]. pose proof (blocks_apart_app_l _ _ BA0) as BA.
    pose proof MXc as [(_ & _ & _ & LENX & NRX & OWX) _]. rewrite EHX in OWX. ddestruct OWX as (N1X & XIN & XP16 & XARR). unfold MPI_MAX_LIMBS in NRX.
    pose proof MR as [(_ & _ & _ & LENR & _ & OWR) _]. rewrite EHR in OWR. ddestruct OWR as (N1R & RIN & RP16 & RARR).
    ddestruct (OEX (T, WL * 4) (or_introl eq_refl)) as (TIN & TFR & TNX & TK0). cbn [fst snd] in TFR, TK0.
    ddestruct (OEX (md_p dRc, 4 * md_n dRc) ltac:(right; unfold mpd_blk; rewrite EHR; left; reflexivity)) as (_ & RFR & RNX & _).
    assert (PEQ : forall B k1 k2, In (B, k1) LBc -> In (B, k2) LBc -> (B, k1) = (B, k2)) by (intros B k1 k2 H1 H2; rewrite (nodup_fst LBc B k1 k2 ND H1 H2); reflexivity).
    assert (NEXT : md_p dXc <> T). { intros E. apply TNX. unfold mpd_blk. rewrite EHX. left. rewrite E in *. exact (PEQ _ _ _ XIN TIN). }
    assert (NEXR : md_p dXc <> md_p dRc). { intros E. apply RNX. unfold mpd_blk. rewrite EHX. left. rewrite E in *. exact (PEQ _ _ _ XIN RIN). }
    assert (NERT : md_p dRc <> T). { intros E. inversion NDE as [|? ? NI _]. apply NI. unfold mpd_blk. rewrite EHR. left. rewrite E in *. exact (PEQ _ _ _ RIN TIN). }
    split; [apply harr_of_in; assumption|]. split; [apply harr_of_in; assumption|]. split; [apply harr_of_in; assumption|].
    split; [pose proof (blocks_apart_in2 LBc _ _ _ _ BA XIN TIN NEXT) as Q; clear - Q; lia|].
    split; [pose proof (blocks_apart_in2 LBc _ _ _ _ BA RIN TIN NERT) as Q; clear - Q; lia|].
    split; [pose proof (blocks_apart_in2 LBc _ _ _ _ BA RIN XIN ltac:(intros E; exact (NEXR (eq_sym E)))) as Q; clear - Q; lia|].
    split; [exact XARR|]. split; [exact LENX|]. split; [exact XP16|]. split; [clear - N1X NRX; lia|].
    split; [exact RARR|]. split; [exact LENR|]. split; [exact RP16|]. split; [exact N1R|].
    split. { intros a n Ha1 Ha2. destruct (FRA (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EHX; left; reflexivity)) as [Hb|HFRA].
             - (* [comment removed for export] *)
               unfold mpd_blk in Hb. destruct (md_own dX) eqn:EOX; try (destruct Hb; fail). destruct Hb as [Eb|[]]. injection Eb as E1 E2.
               pose proof MX0 as [(_ & _ & _ & _ & _ & OW0) _]. rewrite EOX in OW0. ddestruct OW0 as (_ & XIN0 & _). rewrite E1, E2 in XIN0.
               destruct (hm_apart asegs R HIA h LB LF m HH0) as [HFA0 BA00]. rewrite Forall_forall in HFA0.
               destruct (HFA0 _ ltac:(apply in_or_app; left; exact XIN0)) as (_ & _ & BC & BI). cbn [fst snd] in BC, BI.
               intros x Hx Hc _. destruct Hc as [Hs|[[Hd1 Hd2]|(bq & Hbq & Hr)]].
               + clear - Hs Hx Ha1 Ha2 BC ALO LOS SLO NEEDE. lia.
               + destruct DIMG as [D1 D2]. clear - Hd1 Hd2 Hx Ha1 Ha2 BI D1 D2. lia.
               + apply in_app_iff in Hbq. destruct Hbq as [Hbq|Hbq].
                 * pose proof (In_mpd_keep _ _ _ Hbq) as HbL. pose proof (keep_not_blk _ _ _ Hbq) as HbN. destruct bq as [B' k']. cbn [fst snd] in Hr.
                   assert (NE : B' <> md_p dXc). { intros ->. apply HbN. unfold mpd_blk. rewrite EOX. left. rewrite E1, E2. rewrite (nodup_fst LB _ _ _ (HND _ _ _ _ HH0) XIN0 HbL). reflexivity. }
                   pose proof (blocks_apart_in2 LB _ _ _ _ (blocks_apart_app_l _ _ BA00) HbL XIN0 NE) as Q. clear - Q Hr Hx Ha1 Ha2. lia.
                 * ddestruct (in_fdata_hull LF bq x Hbq Hr) as ([FB n'] & Hfb & Hr2). cbn [fst snd] in Hr2.
                   destruct (blocks_apart_app_lr LB LF _ _ FB n' BA00 XIN0 Hfb) as [Q|Q]; clear - Q Hr2 Hx Ha1 Ha2; lia.
             - cbn [fst snd] in HFRA. eapply (wcover_fresh R KEEP LF _ _ a n _ _ HFRA); [exact Ha1| exact Ha2| clear - ALO LOS SLO NEEDE; lia]. }
    split. { intros a n Ha1 Ha2. eapply (wcover_fresh R KEEP LF _ _ a n _ _ (fresh_apart_keep R LB LF dX _ _ TFR)); [exact Ha1| exact Ha2| clear - ALO LOS SLO NEEDE; lia]. }
    split; [destruct XWc as [_ XPc]; rewrite AD in XPc; exact (XPc EHX)|].
    destruct (x_vs_fresh _ _ (fresh_apart_keep R LB LF dX _ _ TFR) TK0) as [Q|Q]; [left; exact Q| right; exact Q].
    all: match goal with |- ?g => idtac "BLK3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L15756354262.4L21779523644.2L23266369800.3L30616158697.2L37155788761.2L42742284694.8L44153091978.4L44157549711.2L48736977024.4L51165555193.2L59308567674.3L59311071632.3L59311123687.2L59957207461.3L8927507728.4 00000>00F00P00W00^01501B01H01W01^01h02302;02D02SS1R2lo3LOS3ALOS2dq3NRqS2dq3dXc1CS2dq2N1S2dq2N1S1R2dE2dN2dq1T2TI2R12R2S1R2dq2BL3ACVS2dq1QS2dq2N13PB03PBBS2dq2N1S2dq2N12OWS2dq2N13PBqS2dX3SXDS2dX2dq1CS2dq2N13PB03PBB". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SLL d SPA MI0 NSX XW XL0 UW0 UWX ROIMG"] Lemma emj_oarr : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Pdq,$68.Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.P,(6<.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4:.R;.R3.R2.)P,(1.$39.(3:.R9.)$7;.)P,(8.+1.(3?.R10.))P,(4=.$4.Vm,VLB,R11.)P,(32.(8.(:.(25.VdX,)+10.)(25.R12.))(8.(:.(25.R12.)+10.)(25.VdX,)))P,(77.VdX,R13.Vlo,(=.&40.Vsp,))P,(78.(79.VR,)(6=.$2:.VLB,(7:.VLF,))Vlo,(25.R14.)+10.)P,P,(1.$39.(3:.R15.)$7;.)(78.(79.VR,)(6=.$2:.VLB,(7:.VLF,))Vlo,(3=.R16.)(3>.+4.(3?.R16.)))P,(76.$4.(1=.VR,)(7.$4.VR,VHIA,Vh,)Vm,R16.)P,(7<.R17.)(0.(95.$4.R13.(3=.R18.)(96.(94.R18.)))(0.(1.$2.(59.(18.(16.&40.)(94.R18.)))(3?.R18.))(0.(8.(3?.R18.)+2710.)(0.(1.$2.(>.(3=.R18.)+4.)=)(0.(34.=(3=.R18.))(0.(34.(:.(3=.R18.)(3>.+4.(3?.R18.)))(5;.+2.+40.))(0.(32.(8.(:.(3=.R18.)(3>.+4.(3?.R18.)))Vlo,)(8.R17.(3=.R18.)))(0.(62.$4.(1=.VR,)(7.$4.VR,VHIA,R15.)R13.(3=.R18.)(3>.+4.(3?.R18.)))(0.(32.(8.(:.(3=.R18.)(3>.+4.(3?.R18.)))R16.)(8.(:.R16.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(3=.R18.)))(0.(32.(8.(:.(3=.R18.)(3>.+4.(3?.R18.)))(3=.R12.))(8.(:.(3=.R12.)(3>.+4.(3?.R12.)))(3=.R18.)))(32.(78.(79.VR,)(6=.$2:.R14.(7:.VLF,))Vlo,(3=.R18.)(3>.+4.(3?.R18.)))(0.Pi,$2.P,(0.(8.=R1.)(34.R1.(3>.+4.(3?.R19.))))(1.$82.(97.$4.(36.(:.(3=.R1:.)R2.)))$84.)(1.$82.(83.(3=.R18.)(3>.+4.(3?.R18.)))$84.)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros dq sp1 T hc LBc mc dXc dRc slA slB ts v f EJ HR EHX N1 MD SXD OS CRD CRDL OD IMD.
    destruct (emj_opnd dq _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MD SXD OS CRD CRDL OD IMD) as (VW & SPq & OSq & CRq & CRLq & ODq).
    ddestruct VW as (CE & BY & LENq & NRq & SGq & BD & PBq & DAL & OSs & OLq & PBB & MDq).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    ddestruct EJ as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB).
    ddestruct J as (_ & AD & PD & NS & NM & FRA & FRS & OXa & O3 & O4 & O5 & OEX & NDE).
    pose proof (art_lo asegs R HIA) as ALO. dpose OS as (OS1 & OS2 & OS3 & OS4 & OS5). dpose OSq as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct PBq as [PBq|[PB0 PB4]]; [exfalso; clear - PBq N1; lia|].
    assert (NNq : md_own dq <> LNull) by (intros EN; pose proof MDq as [(_ & _ & _ & _ & _ & OW) _]; rewrite EN in OW; clear - OW N1; lia).
    ddestruct (OEX (T, WL * 4) (or_introl eq_refl)) as (TIN & TFR & _ & TK0). cbn [fst snd] in TFR, TK0.
    split; [exact BY|]. split; [exact LENq|]. split; [clear - NRq; lia|]. split; [exact PB4|]. split; [exact PB0|].
    split. { pose proof MDq as MDq'. destruct MDq' as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dq) eqn:EOD; [exfalso; exact (NNq eq_refl)| |].
             - ddestruct OW as (_ & HIN & _). pose proof (hm_blocks_low asegs R HIA hc LBc LF mc HHc _ _ ltac:(apply in_or_app; left; exact HIN)) as BL. pose proof (alloc_ceiling_val R) as ACV. clear - BL ACV. lia.
             - pose proof (mpd_at_static47 mc LBc dq MDq EOD) as Q. clear - Q. lia. }
    split; [exact (Q5 NNq)|]. split; [exact (OLq N1)|].
    (* [comment removed for export] *)
    split. { pose proof MD as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dq) eqn:EOD; [exfalso; exact (NNq eq_refl)| |].
             - assert (CRLk : client_range L (KEEP ++ fdata LF) lo (md_p dq) (4 * md_n dq)).
               { apply (client_range_keep L LB LF lo dX (md_p dq) (4 * md_n dq) (CRDL eq_refl)).
                 intros EX. destruct OS3 as [C|[C|[C|C]]]; [exfalso; subst dq; clear - SXD; lia| exfalso; exact (C EX)| discriminate C| clear - C; lia]. }
               destruct (fresh_apart_client R KEEP LF lo (md_p dq) (4 * md_n dq) _ _ (fresh_apart_keep R LB LF dX _ _ TFR) CRLk ltac:(clear - N1; lia) TK0 ltac:(clear - ALO LOS; lia)) as [Q|Q]; [right| left]; exact Q.
             - ddestruct OW as (_ & _ & _ & _ & RO).
               destruct (hm_apart asegs R HIA hc LBc LF mc HHc) as [HFA _]. rewrite Forall_forall in HFA.
               destruct (HFA _ ltac:(apply in_or_app; left; exact TIN)) as (_ & _ & _ & TI). cbn [fst snd] in TI.
               pose proof (ROIMG (md_p dq + 0) (RO 0 ltac:(clear - N1; lia)) ltac:(clear - PB0 PBB N1; lia)) as R1.
               pose proof (ROIMG (md_p dq + (4 * md_n dq - 1)) (RO (4 * md_n dq - 1) ltac:(clear - N1; lia)) ltac:(clear - PB0 PBB N1; lia)) as R2.
               clear - TI R1 R2. lia. }
    split. { destruct Q3 as [C|[C|[C|C]]]; [exfalso; rewrite <- C in SXD; rewrite AD in SXD; clear - SXD; lia| exfalso; exact (C EHX)| exfalso; exact (NNq C)| clear - C; lia]. }
    pose proof MD as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dq) eqn:EOD; [exfalso; exact (NNq eq_refl)| left; exact (CRLq eq_refl)| right].
    ddestruct OW as (_ & _ & _ & _ & RO). split; [exact RO| exact (IMD EOD)].
    all: match goal with |- ?g => idtac "OARR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition set_limbs (dq : mpd) (xs : list word) : mpd := mkMPD (md_addr dq) (md_sg dq) (md_n dq) (md_p dq) xs (md_pad dq) (md_own dq).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L15756354262.4 L16498102502.9 L23898603878.1 L25672897670.13L26270917519.2 L26336259793.2 L26489964535.5 L26866551603.5 L26868649008.5 L30418472034.5 L34842551787.7 L34977101891.6 L34979112605.7 L34979200832.5 L35653441506.7 L36637934947.9 L38235734261.1 L38569812941.1 L43493386919.13L48362162033.4 L52868778719.11L54012259297.5 L54923395197.11L55784057588.3 L60098763854.3 L6203415987.11 L62083823730.7 L62236367456.3 L9080220944.4  00000>00N00Q01=01E01N01a01b02002C02X02Y03403503M03c03g03l04X04g05Q05_06I06U06_06d07907E07TS1R2lo3LOS3ALOS2lo3sp13dRc3RBLS1TS1R2sp2lo3SLO5NEEDE2dE2dN3sp11T1k2Hk3TBL3SP1S2lo3sp1S3dXc3NRXS3dXc3dRc2an3Han2RXFS2dE2dN1T1k2HkS2dX3dXc2an3Han3XPXS2dX2dE2dN1T1k2Hk3TXXFS1R2sp2lo3SLO5NEEDE3sp13SP1FS1R3HIA1h2sp2lo3TOP4HTOPS2sp2dX2lo3DSX3sp13SP1S2loS3dXcS1R2sp2lo3SLO5NEEDE2dE2dN3sp11T1k2Hk3TBL3SP1S2sp2lo3sp13SP1S1R2sp2lo3SLO5NEEDE3sp13dXc2an3Han3XBL3SP1S2dE2dN1T1k2HkS1R2sp2lo3SLO5NEEDE3sp13dXc2an3Han3XBL3SP1S3dXc2an3HanS1R2lo3LOSS3sp1S2dE2dN1T3dRc1k2Hk2RTS3dXc2an3HanS2sp2lo3sp13SP1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA MX0 NSX XW XL0 UW0 UWX HND LFN DIMG"] Lemma emj_core_m : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Pm',P,(16.&40.)(2;.(16.&8.))Pan,$2.Pk,$2.Pxs',(28.(16.&40.))Pts',(28.(16.&40.))P,(6<.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(4:.R10.R8.R7.)P,(1.$39.(3:.R>.)$7;.)P,(1.$39.(3:.R>.)$7;.)P,(0.(8.+1.R8.)(8.R8.(3?.R10.)))P,(0.(8.+1.R8.)(8.R8.(49.(3?.VdN,)(3?.VdE,))))P,(5?.(11.(23.$2.$2.)(24.$2.$2.(3=.R12.)(:.(3=.R12.)(3>.+4.R:.)))(11.(23.$2.$2.)(24.$2.$2.R16.(:.R16.(3>.+4.R9.)))(11.(23.$2.$2.)(24.$2.$2.Vlo,R17.)(14.(23.$2.$2.)))))R13.R;.)P,(60.$4.R14.R<.)P,(1:.$4.R=.)P,(19.$4.R>.Vlo,R1:.)P,(?.$4.VR,VHIA,R19.R18.VLF,R?.)P,(6;.$4.R10.(3=.R17.)R=.)P,(1.$17.(18.(16.&40.)R>.)(18.(16.&40.)(94.R18.)))P,(6;.$4.R12.R1=.R>.)P,(1.$17.(18.(16.&40.)R?.)(18.(16.&40.)R16.))(6<.R20.R1?.R1>.R1=.R14.(98.R1;.R11.)R1:.R19.R18.R10.)")
(* [comment removed for export] *).
  Proof.
    intros sp1 T hc LBc mc dXc dRc slA slB ts v f m' an k xs' ts' EJ HR EHX EHR Han Hk MU WM MI' ST' HH' XA' LX' TA' LT'.
    destruct (emj_blk3 _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX EHR) as (HAX & HAR & HAT & XT & RT & RX & XARR & LENX & XP16 & NRX & RARR & LENR & RP16 & N1R & WCX & WCT & XPX & TXX).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    ddestruct EJ as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose J as (_ & AD & PD & NS & NM & FRA & FRS & OXa & O3 & O4 & O5 & OEX & NDE).
    dpose EB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PRES).
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hcs_ok asegs R HIA hc) as CSOKc.
    pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    ddestruct HAX as (XIN & XP0 & XBL & _ & _ & OXL & _). ddestruct HAT as (TIN & TP0 & TBL & _ & _ & OTL & _). ddestruct HAR as (RIN & RP0 & RBL & _).
    set (W := [(md_p dXc, md_p dXc + 4 * an); (T, T + 4 * k); (lo, sp1)]) in *.
    assert (WC : w_client (hcs asegs R HIA hc) W).
    { unfold w_client, W. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OXL)| clear; lia| clear - Han; lia]|].
      apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OTL)| clear; lia| clear - Hk; lia]|].
      apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]| apply Forall_nil]. }
    unfold EMJ.
    split. { eapply (embs_munch EM_POISON_RR sp1 hc LBc mc _ W m'); [reflexivity| exact EB| exact HCS1| exact HS1| exact MU| exact WM| exact MI'| exact ST'| exact HH'| exact WC| | |]; unfold W.
             - repeat (apply Forall_cons; [cbn [fst snd]; first [clear - Han; lia| clear - Hk; lia| clear - SP1 SLO NEEDE; lia]|]). apply Forall_nil.
             - repeat (apply Forall_cons; [cbn [fst snd]; first [clear - XBL Han SP1 SLO NEEDE; lia| clear - TBL Hk SP1 SLO NEEDE; lia| clear; lia]|]). apply Forall_nil.
             - apply Forall_cons; [cbn [fst snd]; apply WCX; [clear; lia| clear - Han; lia]|].
               apply Forall_cons; [cbn [fst snd]; apply WCT; [clear; lia| clear - Hk; lia]|].
               apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. eapply (wcover_of_stack asegs R HIA h); [exact PRES| clear - LOS ALO; lia| clear - SP1; lia]. }
    split; [exact LA|]. split; [exact LBl|].
    split. { unfold XST, set_limbs. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpd_blk. cbn [md_own md_p md_n].
             split. { pose proof MXc as [(CX & XAL & X0 & LEN & NR & OW) SG].
                      apply mpd_at_rebuild; [exact NS| | exact XAL| exact X0| rewrite <- LEN, LX'; reflexivity| exact NR| exact SG| intros EN; rewrite EN in EHX; discriminate EHX|].
                      - eapply rw_cells_transport; [exact CX| exact MU| exact WM|]. unfold mpi_cells, W. cbn [cells_size csize Nat.add disjoint_from]. rewrite AD.
                        split; [clear - XPX Han; lia|]. split; [clear - TXX Hk; lia|]. split; [clear - DSX SP1 SLO NEEDE; lia| exact I].
                      - intros _. split; [clear - NRX; lia|]. split; [exact XIN|]. split; [exact XP16| exact XA']. }
             split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|]. split; [exact FRA|]. split; [exact FRS|].
             split; [eapply (aobj_munch asegs AL _ CSOKc _ mc m'); [exact WC| exact MU| exact OXa]|].
             split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. split; [exact OEX| exact NDE]. }
    split. { eapply mpd_at_munch_any; [exact MR| exact MU| exact WM| |].
             - rewrite AR. unfold W. cbn [disjoint_from]. split; [clear - XBL Han SP1 SLO NEEDE; lia|]. split; [clear - TBL Hk SP1 SLO NEEDE; lia|]. split; [clear; lia| exact I].
             - intros _. unfold W. cbn [disjoint_from]. split; [clear - RX Han; lia|]. split; [clear - RT Hk; lia|]. split; [clear - RBL SP1 SLO NEEDE; lia| exact I]. }
    split; [exact AR|]. split; [exact NSR|]. split; [exact TA'|]. split; [rewrite LT'; exact TL| exact WLB].
    all: match goal with |- ?g => idtac "COREM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L1540877545.3  L19230717839.7 L21474879437.1 L23615739305.3 L24459976397.1 L25672897670.13L25875002337.13L26336259793.2 L26489964535.5 L26892418956.1 L2953146085.6  L29852667366.16L30418472034.5 L34842551787.7 L35513731400.1 L36335950365.14L37622513746.5 L40281191306.3 L48132467214.7 L50794956004.6 L54923395197.11L61832203402.15L62018535662.1 L62083823730.7 L67028235242.8 00000<00P00U00_00d01Q02A02J02]02a03303g04:04P04U05F05W05`06;06R07<07o08208H08gS2sp3sp13SP1S2dE2dN1T2an2Hk1x2H2S3dRcS1R3HIA2hcS3dRcS1R2sp2lo3SLO5NEEDE2dE2dN3sp11T2an2Hk3TBL3SP1S1R2sp2lo3SLO5NEEDE3sp13dXc2an3Han3XBL3SP12ac2C1S3dXc3NRXS3dXc3dRc2an3Han2RXS2spS1R3HIA3sp12hc1a1SS1R2sp2lo3SLO5NEEDE2dE2dN3sp11T2an2Hk3TBL3SP11a1n2H1S2dX3dXc2an3Han3XPXS2dX2dE2dN1T2an2Hk3TXXS3sp1S1R2sp2lo3SLO5NEEDE3sp13dXc2an3Han3XBL3SP11a1n2H1S3dXc2an3Han1x2H1S1R3HIA1hS1R2sp2lo3LOS3SLO5NEEDE3ALOS1R2sp2lo3LOS3SLO5NEEDES1R2sp2lo3SLO5NEEDE3sp13dXc2an3Han3XBL3SP1S1R2sp2lo3SLO5NEEDE2dE2dN3sp11T2an2Hk3TBL3SP12ac2C1S1RS2dE2dN1T3dRc2an2Hk2RTS1R2sp2lo3LOS3SLO5NEEDE3sp13SP1". (* [comment removed for export] *)
  #[using="LOS SLO NEEDE TOP HH0 SSL SLL DSX PHI FR d SPA MX0 NSX XW XL0 UW0 UWX BUDL BUDFL SXN HND SXE DIMG"] Lemma emj_core_p : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.PT,$2.Phc,(29.$4.VR,VHIA,)PLBc,(28.$2:.)Pmc,P,(16.&40.)(2;.(16.&8.))PdXc,$68.PdRc,$68.PslA,(28.(16.&40.))PslB,(28.(16.&40.))Pts,(28.(16.&40.))Pv,$2.Pf,$2.Ph',(29.$4.VR,VHIA,)Pm',P,(16.&40.)(2;.(16.&8.))Pan,$2.Pxs',(28.(16.&40.))Pts',(28.(16.&40.))P,(6<.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(4:.R10.R8.R7.)P,(1.$39.(3:.R>.)$7;.)P,(1.$39.(3:.R>.)$7;.)P,(0.(8.+1.R7.)(8.R7.(3?.R10.)))P,(8.(:.(3>.+2.R8.)+1.)(49.(3?.VdN,)(3?.VdE,)))P,(1:.$4.R:.)P,(19.$4.R;.Vlo,R18.)P,(2?.$4.VR,R16.VLF,R19.(20.VR,)(5.$4.VR,VHIA,R17.)(11.(23.$2.$2.)(24.$2.$2.(3=.R14.)(:.(3=.R14.)(3>.+4.R;.)))(11.(23.$2.$2.)(24.$2.$2.R18.(:.R18.(3>.+4.(:.(3>.+2.R;.)+1.))))(14.(23.$2.$2.))))R15.R<.)P,(6;.$4.R=.(3=.R15.)R;.)P,(1.$17.(18.(16.&40.)R<.)(18.(16.&40.)(94.R16.)))P,(6;.$4.R?.R1;.R<.)P,(1.$17.(18.(16.&40.)R=.)(18.(16.&40.)R14.))P,(?.$4.VR,VHIA,R12.R1;.VLF,R11.)P,(1.P,$2.Sp(7.$4.VR,VHIA,R13.)(7.$4.VR,VHIA,R1=.))P,(1.$2.(3.$4.VR,VHIA,R14.)(3.$4.VR,VHIA,R1>.))P,(1.$2.(5.$4.VR,VHIA,R15.)(5.$4.VR,VHIA,R1?.))P,(1.$2.(6.$4.VR,VHIA,R16.)(6.$4.VR,VHIA,R20.))P,(1.$2.(9.$4.VR,VHIA,R17.)(9.$4.VR,VHIA,R21.))P,(1.$2.(;.$4.VR,VHIA,R18.)(;.$4.VR,VHIA,R22.))(0.(6<.R25.R24.R19.R22.R18.(98.R20.R16.)R1?.R1>.R1=.R15.)(4:.R19.R1;.R1:.))")
(* [comment removed for export] *).
  Proof.
    intros sp1 T hc LBc mc dXc dRc slA slB ts v f h' m' an xs' ts' EJ HR EHX EHR Han Hk MI' ST' HP XA' LX' TA' LT' HH' Ecs Etop Estk Eflag Evol Efr.
    destruct (emj_blk3 _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX EHR) as (HAX & HAR & HAT & XT & RT & RX & XARR & LENX & XP16 & NRX & RARR & LENR & RP16 & N1R & WCX & WCT & XPX & TXX).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    pose proof (fun b => xst_keep _ hc LBc mc dXc b (proj1 (proj2 (proj2 (proj2 EJ))))) as KK.
    ddestruct EJ as (EB & LA & LBl & J & MR & AR & NSR & TA & TL & WLB).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose J as (_ & AD & PD & NS & NM & FRA & FRS & OXa & O3 & O4 & O5 & OEX & NDE).
    pose proof (art_lo asegs R HIA) as ALO.
    ddestruct HAX as (XIN & XP0 & XBL & _ & _ & OXL & _). ddestruct HAT as (TIN & TP0 & TBL & _ & _ & OTL & _). ddestruct HAR as (RIN & RP0 & RBL & _).
    ddestruct (OEX (T, WL * 4) (or_introl eq_refl)) as (_ & TFR & _ & TK0). cbn [fst snd] in TFR, TK0.
    assert (HR' : HREL h' v f).
    { unfold HREL. split; [rewrite Etop; exact HT1|]. split; [rewrite Estk; exact HS1|]. split; [rewrite Eflag; exact HF1|]. split; [rewrite Ecs; exact HCS1|]. split; [rewrite Evol; exact HV1| rewrite Efr; exact HFR1]. }
    split; [| exact HR'].
    assert (KC : forall b, In b KEEP -> In b LBc) by (intros b Hb; exact (In_mpd_keep _ _ _ (KK b Hb))).
    (* [comment removed for export] *)
    assert (HPE : presA asegs R KEEP LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [] mc m').
    { assert (HP1 : presA asegs R KEEP LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(md_p dXc, md_p dXc + 4 * md_n dXc); (T, T + WL * 4)] mc m').
      { rewrite <- HS1. eapply presA_weaken; [exact HP| exact KC| intros b Hb; exact Hb| clear - SP1; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in *. ddestruct Hx as (H1 & H2 & _). split; [clear - H1 Han; lia|]. split; [clear - H2 Hk; lia| exact I]. }
      eapply (presA_drop_fresh asegs R HIA h KEEP LF [] T (WL * 4)); [| apply fresh_apart_keep; exact TFR| clear - LOS SLO NEEDE; lia].
      assert (HP2 : presA asegs R KEEP LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(T, T + WL * 4); (md_p dXc, md_p dXc + 4 * md_n dXc)] mc m').
      { eapply presA_weaken; [exact HP1| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|]. intros x Hx; clear - Hx; cbn [outside] in *. tauto (* [comment removed for export] *). }
      eapply presA_weaken; [| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x Hx; exact Hx].
      assert (HP3 : presA asegs R KEEP LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(md_p dXc, md_p dXc + 4 * md_n dXc); (T, T + WL * 4)] mc m') by exact HP1.
      clear HP2.
      assert (HP4 : presA asegs R KEEP LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(T, T + WL * 4)] mc m').
      { destruct (FRA (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EHX; left; reflexivity)) as [Hb|HFRA].
        - unfold mpd_blk in Hb. destruct (md_own dX) eqn:EOX; try (destruct Hb; fail). destruct Hb as [Eb|[]]. injection Eb as E1 E2.
          pose proof MX0 as [(_ & _ & _ & _ & _ & OW0) _]. rewrite EOX in OW0. ddestruct OW0 as (_ & XIN0 & _). rewrite E1, E2 in XIN0.
          eapply (presA_drop_freed asegs R HIA h LB LF KEEP [(T, T + WL * 4)] (md_p dXc) (4 * md_n dXc) m mc m'); [exact HH0| exact XIN0| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDE; lia| exact HP3].
          intros bq xq Hbq _. split; [exact (In_mpd_keep _ _ _ Hbq)|]. intros Eq. apply (keep_not_blk _ _ _ Hbq). unfold mpd_blk. rewrite EOX. left. rewrite E1, E2. symmetry. exact Eq.
        - cbn [fst snd] in HFRA. eapply (presA_drop_fresh asegs R HIA h KEEP LF [(T, T + WL * 4)] (md_p dXc) (4 * md_n dXc)); [exact HP3| exact HFRA| clear - LOS SLO NEEDE; lia]. }
      exact HP4. }
    unfold EMJ.
    split. { eapply embs_call with (LBp := LBc) (W' := [(md_p dXc, md_p dXc + 4 * an); (T, T + 4 * (2 * an + 1))]) (WE := ([] : list ivl)) (LBe := KEEP);
               [reflexivity| exact EB| exact MI'| exact ST'| rewrite <- HS1; exact HP| exact KC| | | exact HPE| intros b Hb; exact Hb| intros x _; exact I| exact HH'].
             - intros a n H1 H2. cbn [disjoint_from]. split; [clear - H1 XBL Han SP1 SLO NEEDE; lia|]. split; [clear - H1 TBL Hk SP1 SLO NEEDE; lia| exact I].
             - ddestruct EB as (_ & _ & _ & _ & _ & CHI & _). rewrite Forall_forall in *. intros ac Hac. destruct (CHI ac Hac) as [C1 C2]. cbn [disjoint_from].
               split; [clear - C1 XBL Han SP1 SLO NEEDE; lia|]. split; [clear - C1 TBL Hk SP1 SLO NEEDE; lia| exact I]. }
    split; [exact LA|]. split; [exact LBl|].
    split. { unfold XST, set_limbs. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpd_blk. cbn [md_own md_p md_n].
             split. { pose proof MXc as [(CX & XAL & X0 & LEN & NR & OW) SG].
                      apply mpd_at_rebuild; [exact NS| | exact XAL| exact X0| rewrite <- LEN, LX'; reflexivity| exact NR| exact SG| intros EN; rewrite EN in EHX; discriminate EHX|].
                      - eapply (presA_rw_cells asegs R); [exact HP| exact CX| |].
                        + destruct XWc as [CWc _]. unfold mpi_cells. cbn [cells_size csize Nat.add]. intros a Ha. destruct (CWc a Ha) as [S|[D|B]]; [left; clear - S; lia| right; left; exact D| right; right; exact B].
                        + unfold mpi_cells. cbn [cells_size csize Nat.add disjoint_from]. rewrite AD. split; [clear - XPX Han; lia|]. split; [clear - TXX Hk; lia| exact I].
                      - intros _. split; [clear - NRX; lia|]. split; [exact XIN|]. split; [exact XP16| exact XA']. }
             split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|]. split; [exact FRA|]. split; [exact FRS|].
             split. { rewrite Ecs. eapply (presA_aobj asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP| exact OXa| | clear - SP1 SLO NEEDE LOS; lia| intros x Hx; eapply hcs_below_top; exact Hx].
                      destruct XWc as [CWc _]. rewrite AD in CWc. intros a Ha. destruct (CWc a Ha) as [S|[D|B]]; [left; clear - S; lia| right; left; exact D| right; right; exact B]. }
             split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. split; [exact OEX| exact NDE]. }
    split. { eapply (mpd_at_heap_presx asegs L mc m' LBc (LBc ++ fdata LF) LBc sp1 _ dRc);
               [exact MR| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP)| exact MIc| exact MI'| rewrite AR; apply client_range_stack; clear; lia| | | | intros b Hb; pose proof MR as [(_ & _ & _ & _ & _ & OW) _]; unfold mpd_blk in Hb; rewrite EHR in *; destruct Hb as [<-|[]]; exact (proj1 (proj2 OW))].
             - intros _. eapply client_range_block; [apply in_or_app; left; exact RIN| clear; lia| clear; lia].
             - rewrite AR. cbn [disjoint_from]. split; [clear - XBL Han SP1 SLO NEEDE; lia|]. split; [clear - TBL Hk SP1 SLO NEEDE; lia| exact I].
             - intros _. cbn [disjoint_from]. split; [clear - RX Han; lia|]. split; [clear - RT Hk; lia| exact I]. }
    split; [exact AR|]. split; [exact NSR|]. split; [exact TA'|]. split; [rewrite LT'; exact TL| exact WLB].
    all: match goal with |- ?g => idtac "COREP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis TOM : mpi_core_to_mont_rep_stmtA asegs R HIA A_MPI_CORE_TO_MONT_REP.
  Hypothesis CEM : mpi_core_exp_mod_stmtA asegs R HIA A_MPI_CORE_EXP_MOD.
  Hypothesis FROM : mpi_core_from_mont_rep_stmtA asegs R HIA A_MPI_CORE_FROM_MONT_REP.
  #[using="Type d"] Lemma set_sg_id : forall dq, set_sg dq (md_sg dq) = dq.
  Proof. intros []. reflexivity. Qed.
  #[using="LF sp dN LFN dA LFN3 d"] Lemma wl_ge : forall an en, 0 <= an -> 2 * an + 1 <= exp_mod_working_limbs an en.
  Proof. intros an en Ha. unfold exp_mod_working_limbs, exp_mod_welem. destruct (79 <? 32 * en); nia. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L24364708814.7  L27940405558.7  L3482791583.7   L35653441506.7  L38143154590.8  L38143334840.9  L38145403672.10 L38235734261.1  L47492451383.191L57122948516.2  L60098763854.3  L65258828961.0  L66151427842.16 L9080220944.4   Q18152175808.195Q28250671888.194Q2991847834.194 Q31600242951.195Q66946765603.194Q66946854044.19500000K00f00g01?01@01b01c01g02A02H02R02S02o03>03Q03d04704a05405GS1R2sp2lo3SLO5NEEDE3sp13SP1S1R2sp2lo3SLO5NEEDE3sp13SP1FS1R3HIA1h2sp2lo3TOP4HTOPFS1R2sp2lo3SLO5NEEDE2dN3sp13SP13NPSFS2loS2LF2sp2dN3LFN2dA4LFN33sp1S2dN2N1S1R2lo3LOSSS3sp12r04SP1M1q1r1H2H02q02H4S2sp2lo3sp13SP1S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3S2LF2sp2dN3LFN2dA4LFN33sp14SP1R2NB3NAL3NP0S2LF2dN3LFN2dA4LFN3S2LF2dN3LFN2dA4LFN3". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA MI0 NSX XW XL0 UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN LFN dA ROIMG LFN3"] Lemma em_mminit : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc dRc : mpd) (slA slB ts : list word) (v f : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    EMJ sp1 T hc LBc mc dXc dRc slA slB ts -> HREL hc v f -> md_own dXc = LHeap -> 1 <= md_n dN ->
    (forall (m' : mem) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
       EMJ sp1 T hc LBc m' dXc dRc slA slB ts ->
       aevtA asegs (KF asegs R HIA hc mo) POSTA
         (MS (RJ (Z_to_bv 64 658404) sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658404) fc None m' (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo) POSTA
      (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658388) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR EHX N1 K.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & _).
    ddestruct VN as (CN & _ & _ & NRN & _ & NB & _ & NAL & ON & _ & _ & MNc).
    destruct (emj_oarr dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX N1 MN0 SXN OSN CRN CRNL ODN IMN) as (BYN & LENN & _ & NP4 & NP0 & NP64 & NPS & ONL & _).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep_to [676884].
    pose proof (A_mpi_core_montmul_init_spec AL IMG) as SPI. unfold mpi_core_montmul_init_stmtA, A_MPI_CORE_MONTMUL_INIT in SPI.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { eapply SPI with (CS := hcs asegs R HIA hc) (N := md_p dN) (lo := lo) (ns := md_limbs dN);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold MPI_CORE_MONTMUL_INIT_STACK_A;
        first [ exact BYN | exact NP4 | exact NP0 | exact MIc | exact CSOKc | exact (hm_abase asegs R HIA hc LBc LF mc HHc) | exact (art_alwf asegs R HIA) | exact STc | reflexivity
              | rewrite LENN; exact N1
              | eapply aobj_sub; [exact ONL| apply Z.le_refl| clear - N1; lia]
              | eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
              | clear - SP1 SLO NEEDE; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite LENN; clear - NPS SP1 SLO NEEDE; lia
              | match goal with |- ?g => idtac "MMI-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_core_montmul_init_postA, MPI_CORE_MONTMUL_INIT_STACK_A in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m' & -> & MUc & WMc & MI' & ST').
    replace (ret_pc (Z_to_bv 64 658404)) with (Z_to_bv 64 658404 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    eapply K. eapply (emj_pure sp1 T hc LBc mc dXc dRc slA slB ts v f (sp1 - 16) m' EJ HR); [clear - SP1 SLO NEEDE; lia| exact MUc| exact WMc| exact MI'| exact ST'].
    all: match goal with |- ?g => idtac "MMI-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04\0@D3953997537.254 D3953997537.255 D60189065437.254D60189065437.255K47293664555.254K47293664555.255K66088614017.254K66088614017.255L11264021790.6  L11265926719.5  L11266090559.5  L11266140195.5  L11266286169.5  L11266286681.6  L11266287167.4  L11268023358.7  L11268187198.7  L11268281503.12 L11268380569.5  L11268383282.5  L11360676701.4  L11370797594.4  L11370798106.5  L11371206240.4  L11372895345.5  L11372898778.5  L11372931804.11 L11372931804.12 L11373189757.5  L11373353597.5  L12159438251.9  L12159549905.9  L12159551441.9  L12161483190.10 L12161581494.10 L12161648570.9  L12161659409.9  L12161757463.15 L12161757463.16 L12939667878.5  L12939669414.7  L12939813852.6  L12939832768.4  L12941664096.11 L12941664096.12 L12941761638.6  L12941765069.5  L12941832129.8  L12941930433.7  L12946054881.7  L15967921241.4  L15968069667.5  L15968071203.3  L15969871940.5  L15969970244.6  L15970163683.4  L15970168392.3  L16497922726.7  L16497923238.6  L16498040540.6  L16498118848.4  L16498282688.5  L16500020429.6  L16500023654.6  L16500122208.11 L16500122208.12 L16500216513.7  L16500380353.8  L16504382433.7  L1685717371.0   L17771860548.4  L17772271678.4  L17772273214.4  L17773911641.5  L17774075481.5  L17774368853.4  L17774374398.4  L18102976209.8  L18103151926.10 L18103315766.9  L18103410071.14 L18103410071.15 L18105491755.8  L18105609041.8  L18105609553.9  L21194954052.6  L21195117892.5  L21195182920.4  L21195187939.4  L21197134169.4  L21197280035.4  L21197280547.5  L21477599162.3  L21547003058.3  L22189559154.5  L22189722494.5  L22189735637.6  L22191669615.5  L22594986486.2  L23933476191.9  L23933587749.10 L23933589285.8  L23935324482.10 L23935488322.11 L23935590883.15 L23935590883.16 L23935686478.8  L23935689445.9  L2437508296.4   L24446230945.0  L26786418512.1  L27204354735.8  L27204765909.8  L27204767445.8  L27206405810.9  L27206504114.9  L27206778387.14 L27206778387.15 L27207343445.8  L28401028998.9  L29467392662.1  L33824001175.14 L33824001175.15 L33824275510.9  L33824439350.10 L33824452561.7  L33824452561.8  L33826077265.7  L33826077777.9  L33826451499.8  L3480673688.5   L3482346814.9   L3482348255.4   L3482348767.5   L3482349241.4   L3482709689.4   L3482722469.4   L3482775225.6   L3482807993.4   L3484442399.4   L3484445364.4   L3484806328.6   L3484904632.6   L35394346383.246L35653441506.7  L39188636933.0  L3934439888.7   L3934441424.8   L3934553002.7   L3936583446.14  L3936735159.9   L3936833463.9   L3937016912.7   L41392044326.1  L41814970463.3  L41816922702.4  L41816928229.4  L41887942832.3  L45855443592.5  L45855443592.6  L46531815739.2  L47278198764.2  L47492451383.246L50113579094.7  L50113677398.7  L50113951991.13 L50113951991.14 L50114039386.7  L50114051057.7  L50115676759.7  L50115709527.6  L50115757131.6  L50115775063.7  L50116134961.6  L50116135511.6  L50116136497.7  L50126207350.6  L51842906259.3  L51842907795.5  L51843019497.4  L51844992339.4  L51845003512.3  L51845070580.6  L51845168884.5  L52920769950.6  L52920772661.6  L52920806195.12 L52920966034.8  L52921064338.8  L52922864148.9  L52922866067.5  L52922866677.7  L52922867189.6  L52922964371.7  L52922980239.6  L52923062675.5  L52923160979.5  L52925065906.7  L54328148356.244L54379423251.246L57698627611.2  L59597572393.4  L60098763854.3  L60315874144.4  L60316024602.4  L60317826941.5  L60317925245.5  L60318108890.5  L60318120305.5  L62081643631.5  L62083659890.6  L62083823730.5  L62083877845.6  L62083890814.6  L63124129830.1  L66099886662.2  L66151427842.16 L66151427842.17 L67576727545.6  L67620384339.4  L82394020.17    L9582510895.12  P57713046236.254P57713046236.255Q10149575540.254Q10149575540.255Q11801279589.254Q11801279589.255Q12386486278.251Q1430934683.251 Q15515733206.252Q17971260310.251Q18152175808.252Q20535714715.251Q21915034933.250Q23255371202.252Q23399781729.252Q23927705296.254Q23927705296.255Q24165444223.251Q24167257676.252Q27882953602.254Q27882953602.255Q27940670726.251Q28252440732.251Q28465177121.251Q28465177121.252Q2994141718.251 Q31600242951.252Q3419689062.254 Q3419689062.255 Q3421936230.253 Q3421936230.254 Q35294351003.251Q3573031455.252 Q36112325839.251Q3851065094.251 Q39180574961.254Q39180574961.255Q41176579691.251Q41178939992.252Q42439443119.254Q42439443119.255Q46192266046.251Q51087705995.254Q51087705995.255Q5129158642.254 Q5129158642.255 Q51749417795.251Q5265442331.252 Q5265442331.253 Q55415036769.254Q55415036769.255Q57037327601.254Q57037327601.255Q57228775306.253Q57228775306.254Q57230951818.254Q57230951818.255Q57387891900.251Q58125335435.254Q58125335435.255Q59865321072.254Q59865321072.255Q6186103236.254 Q6186103236.255 Q62011970312.254Q62011970312.255Q64041402609.254Q64041402609.255Q64683667846.254Q64683667846.255Q65314988264.252Q66946854044.252Q66948665519.251Q7528619688.250 Q7845954958.254 Q7845954958.255 Q8699115497.254 Q8699115497.255 00002W05A07h0:R0<S0>U0@V0BX0BY0BZ0B[0B\0B]0B^0Bm0Bn0Bo0C00C10C20C@0CA0CB0CC0CD0CE0CF0CG0CH0CI0CJ0CK0CL0CM0CN0CO0CP0CQ0CR0CS0CT0CU0Ce0Cf0Cg0Ch0Ci0Cj0Ck0Cl0Cm0Cn0Co0D00D10D20D30D40D50D60DF0DG0DH0DI0DJ0DK0DL0DM0DN0DO0DP0DQ0DR0DS0DT0DU0DV0DW0DX0DY0DZ0D[0D\0D]0D^0D_0D`0Da0Db0Dc0Dd0De0E00E;0EK0EL0EM0EN0EV0EW0EX0EY0EZ0E[0E\0E]0E^0E_0Em0En0F30F40F50F60F70F80F90F:0F;0F]0Fb0Fc0Fd0Fe0Ff0Fg0Fh0Fi0Fj0Fk0Fl0Fm0Fn0Fo0G00G10G20G30G40G50G60G70G80Hj0IB0IC0ID0IE0IF0IG0IH0II0IJ0IO0IZ0I[0I\0Ig0J90J:0JA0JB0L40L50L60L70L80L90L:0L;0LO0LP0LQ0LR0LS0LT0LU0La0Lb0Lc0Ld0Le0Lf0Lg0Lh0Li0Lj0Lk0Ll0MJ0MK0ML0MM0MN0MO0MP0MQ0MR0OD0Q60Q70QE0QO0QP0Q]0Q^0Q_0Q`0Qa0Qb0Qc0R30R40R50R:0R;0Ro0S00SD0SQ0Sm0TP0VS0XW0ZY0\\0\]0\^0^_0`T0bY0d@0eg0g\0i]0i^0kf0n810M12413[13\13]15^17E1981:k1<R1>W1@]1Bd1Dj1G11Hf1JM1L41N51PM1Rh1TO1V61X:1ZA1[h1]d1_a1_b1_c1aJ1c>1e21g51i91kI1m\1ol22?24O26b28I2:E2<B2<C2<D2>J2@Q2BM2DL2F\2Ho2KE2M^2OE2Pl2RS2TH2VD2XA2ZW2]0S1R3HIA1h2LF2sp2dX3TOP2dN3LFN2dA4LFN33sp11T2hc3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP14SP1R2NB3HT12LA3LBl2X03SPR2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3TOP2dN3LFN2dA4LFN33sp11T2hc3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP14SP1R2NB3HT12LA3LBl2X03SPR2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3LOS3SLO5NEEDE2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP14SP1R2NB2LA3LBl2X03SPR2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3LOS3SLO5NEEDE2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP14SP1R2NB2LA3LBl2X03SPR2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB4DSN12HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB4DSN12HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB4DSX12HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB4DSX12HB5Ha_st5Hl_stFFFFFFS2lo2dN3sp13NPSFFFFFS2dE2dN1T4TP64FFFFFFFFFFFFFFFFFFFFFS2lo3sp13dXc3XPSFFFFFFFFFFFFFFFFFS2lo3sp13dRc3RPSFFFFFFFFSFFFFFFFFFFFFFFFFFFFFFFS2dN3dRc2NRS2dN3NN42N1S2dE2dN1T3dXc2XTFFFS2dN3NRNFFFFFFFFFS2dN3dXc2N12NXSS3sp1FFFFFFFFS1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1S3sp1FFFFFFFFFFFFFFFFFFFFFFS2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R3HIA1h2sp2lo3TOP4HTOPSFFFFFFFS3sp1S2dE2dN3WLGFFS2dN3dXc2NXS2dN3dXc2NX2aq3HaqFS2dN2N1FS2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBFFFFFFFS2lo2dE2dN3sp11T3TPSFFFFFFS2dN3dXc3NXqFFFFFFFFFFFS1R2sp2lo3SLO3sp13SP14NRAM3NERFFFFFFFFS2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBFS2dE2dN2N13WLGS1R2lo3LOSFS2dE2dN1T3NTqFFFFFFS2dE2dN1T3dRc2RTFFS3sp1FS3dXc2r04XP161q1r1H2H02q02H43dRc4RP161T3T163sp14SP1MFS2dE2dN1T3WLG2aq3HaqS2dE2dN1T3WLGS1R2dN2r03NAL1q1r1H2H02q02H4S1R2sp2lo3SLO5NEEDE2dN3sp13SP11Q2Q0S1R2LF2sp2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB2HB5Ha_st5Hl_stFFS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2NB3NAL2LA3LBl2X03SPR2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBFS2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2NB2LA3LBl2AD3XAL2X03SPR2XBS1R3HIA1h2LF2sp2dX3TOP2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3TOP2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBFFS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2LA3LBl2XB2HBS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2LA3LBl2XB2HBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2NB3NAL2LA3LBl2X03SPR2XBS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS1R2LF2sp2dX2lo3LOS3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl3ALO2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3LOS3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl3ALO2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX3slo3SSL2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX3slo3SSL2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB2HB5Ha_st5Hl_stFFS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_stS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_stS1R2LF2sp2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB2HB5Ha_st5Hl_stFFS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2dX2dN3LFN2dA4LFN31T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS2LF2dX2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm2LA3LBl2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP2dN3LFN2dA4LFN33sp11T1b2b02b12b22b32b42b62b72b82b93b103b113b123b133b143b153b163b173b183b192mm3SP12LA3LBl4HTOP2XB2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA MI0 MX0 NSX XW XL0 OX0 UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN NN4 HND LFN ROIMG LFN3 DIMG TOM dA"] Lemma em_tomont : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : bv 64 -> option (bv 8)) (dXc dRc : mpd) (slA slB ts : list word) (v f : Z) (mm xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word), EMJ sp1 T hc LBc mc dXc dRc slA slB ts -> HREL hc v f -> JSLOTSX T slA -> md_own dXc = LHeap -> md_own dRc = LHeap -> 1 <= md_n dN -> md_n dN <= md_n dXc -> md_n dN <= md_n dRc -> (forall (m' : bv 64 -> option (bv 8)) (slA' xs' ts' : list word) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word), EMJ sp1 T hc LBc m' (set_limbs dXc xs') dRc slA' slB ts' -> JSLOTSX2 T slA' -> aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ (Z_to_bv 64 658488) sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 mm y3 y4 y5 y6) F (Z_to_bv 64 658488) fc None m' (seg_rom asegs))) -> aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ xra sp1 t0 t1 t2 mm a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658404) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JS EHX EHR N1 NX NR K.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & _ & OSN' & _).
    ddestruct VN as (CN & _ & _ & NRN & _ & NB & _ & NAL & ON & _ & _ & MNc).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as ((S5 & S6 & S7 & S8 & S9 & S10 & S11) & S3 & S4).
    dpose EJ as (EB & LA & LBl & J & MR & AR & _). dpose J as (_ & AD & _).
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    repeat (destruct slB as [|? slB]; [discriminate LBl|]). destruct slB; [| discriminate LBl].
    cbn [nth_error] in S3, S4, S5, S6, S7, S8, S9, S10, S11. injection S3 as ->. injection S4 as ->. injection S5 as ->. injection S6 as ->. injection S7 as ->. injection S8 as ->. injection S9 as ->. injection S10 as ->. injection S11 as ->.
    dpose EB as (_ & _ & _ & SAVE & CHS & _ & SThi & STlo & _ & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. pose proof (Forall_inv (Forall_inv_tail CHS)) as CHB. cbn [fst snd map] in CHA, CHB.
    pose proof MXc as [(CX & XAL & X0 & _ & _ & _) SGX]. rewrite AD in CX. unfold mpi_cells in CX.
    pose proof MR as [(CR & _) _]. rewrite AR in CR. unfold mpi_cells in CR.
    destruct XWc as [CW _]. rewrite AD in CW. destruct OXc as [OXa _]. rewrite AD in OXa.
    pose proof (aobj_crange _ _ _ _ _ _ OXa) as CRXc. pose proof (aobj_crange _ _ _ _ _ _ (proj1 OX0)) as CRX0.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (rw_cells_bound _ _ _ _ CX) as XB. cbn [cells_size csize Nat.add] in XB.
    assert (DSX1 : X + 16 <= sp1 \/ sp1 + 288 <= X) by (clear - DSX SP1 SLO NEEDE; lia).
    assert (DSN1 : N + 16 <= sp1 \/ sp1 + 288 <= N) by (ddestruct OSN' as (_ & _ & _ & Q & _); clear - Q SP1 OSN SLO NEEDE; ddestruct OSN as (_ & _ & _ & Q0 & _); lia).
    unfold EM_POISON_RR in SHC.
    pose proof (munch_refl [(sp1, sp1 + 40); (X, X + 16)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    assert (E10 : Z.shiftr (N + 10) 3 + al_sb AL = Z.shiftr N 3 + al_sb AL + 1) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - NAL; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    zstep_to [658448].
    (* [comment removed for export] *)
    rewrite E10. zstep_to [681652]. rewrite zx16_small by (clear - NRN; lia).
    lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo sp1, H3 : HM _ _ _ hc LBc LF ?m2, H4 : stk asegs ?m2 (sp1 + 216) _ |- _ =>
      lazymatch type of CHA with rw_cells _ _ _ ?csA => lazymatch type of CHB with rw_cells _ _ _ ?csB =>
        let wsA := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) csA) in
        let wsB := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) csB) in
        assert (EJ2 : EMJ sp1 T hc LBc m2 dXc dRc wsA wsB ts);
          [ rewrite <- (set_sg_id dXc);
            eapply (emj_upd sp1 T hc LBc mc dXc dRc _ _ ts v f m2 wsA (md_sg dXc) EJ HR); [| reflexivity| exact MU| exact WM| exact CX| exact SGX];
            unfold EMBs; refine (conj SP1 (conj SP1M (conj H3 (conj SAVE (conj _ (conj _ (conj H4 (conj H2 (conj H1 (conj SHC (conj SSlo (conj SShi (conj SNlo (conj SNhi PRES))))))))))))));
            [ repeat (apply Forall_cons; [cbn [fst snd]; first [exact CHA| exact CHB]|]); apply Forall_nil
            | repeat (apply Forall_cons; [unfold chunk_in; cbn [fst snd cells_size csize map Nat.add]; clear; lia|]); apply Forall_nil ]
          | ]
      end end end.
    lazymatch type of EJ2 with EMJ _ _ _ _ ?m2 _ _ ?wsA _ _ => rename m2 into mq; set (slA2 := wsA) in * end.
    assert (JS2 : JSLOTSX2 T slA2) by (unfold slA2, JSLOTSX2, JSLOTSX, JSLOTS; cbn [nth_error]; repeat first [exact eq_refl| split]).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ2 HR) as (_ & _ & _ & HHq & MXq & _ & _ & _ & STq & MIq & _ & _ & _ & TOPq).
    destruct (emj_blk3 _ _ _ _ _ _ _ _ _ _ _ _ EJ2 HR EHX EHR) as (HAX & HAR & HAT & XT & RT & RX & XARR & LENX & XP16 & NRX & RARR & LENR & RP16 & N1R & _ & _ & _ & _).
    destruct (emj_oarr dN _ _ _ _ _ _ _ _ _ _ _ _ EJ2 HR EHX N1 MN0 SXN OSN CRN CRNL ODN IMN) as (BYN & LENN & _ & NP4 & NP0 & NP64 & NPS & ONL & NTq & NXq & _).
    ddestruct HAX as (XIN & XP0 & XBL & XP64 & XPS & OXL & CWXL & _). ddestruct HAT as (TIN & TP0 & TBL & TP64 & TPS & OTL & CWTL & _). ddestruct HAR as (RIN & RP0 & RBL & RP64 & RPS & ORL & _).
    dpose EJ2 as (_ & _ & _ & _ & _ & _ & _ & TAq & TLq & WLBq & T16).
    pose proof (wl_ge (md_n dN) (md_n dE) ltac:(clear - N1; lia)) as WLG.
    pose proof (arl_need_rt_amem R) as NRAM. pose proof (arl_need_ecp_rt R) as NER.
    pose proof TOM as TM'. unfold mpi_core_to_mont_rep_stmtA in TM'.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { eapply TM' with (LB := LBc) (LF := LF) (X := md_p dXc) (A := md_p dXc) (RR := md_p dRc) (N := md_p dN) (an := md_n dN) (T := T) (lo := lo)
                      (xs := md_limbs dXc) (ys := md_limbs dXc) (rs := md_limbs dRc) (ns := md_limbs dN) (ts := ts);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?LENX, ?LENR, ?LENN, ?TLq; unfold MPI_CORE_MONTMUL_STACK_A;
        first [ exact HHq | exact XARR | exact (u32arr_ro _ _ _ _ XARR) | exact (u32arr_ro _ _ _ _ RARR) | exact BYN | exact TAq | exact STq | exact LOS | exact MIq | exact TOPq | exact NX | exact NR | reflexivity
              | exact NP4 | exact NP0 | exact XP0 | exact RP0 | exact TP0 | exact XP64 | exact RP64 | exact NP64
              | clear - N1 NN4; lia | clear - NX; lia | clear - WLG; lia
              | clear - XT; lia | clear - RT; lia | clear - NTq; lia | clear - NXq; lia
              | clear - XP16; Z.div_mod_to_equations; lia | clear - RP16; Z.div_mod_to_equations; lia | clear - T16; Z.div_mod_to_equations; lia
              | intros aq Haq; apply CWXL; clear - Haq NX; lia | intros aq Haq; apply CWTL; clear - Haq WLG; lia
              | eapply aobj_sub; [exact OXL| apply Z.le_refl| clear - NX; lia] | eapply aobj_sub; [exact ORL| apply Z.le_refl| clear - NR; lia]
              | exact ONL | eapply aobj_sub; [exact OTL| apply Z.le_refl| clear - WLG; lia]
              | clear - TP64; lia | clear - XPS; lia | clear - RPS; lia | clear - NPS; lia | clear - TPS; lia
              | clear - SP1 SLO NEEDE NRAM NER; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | match goal with |- ?g => idtac "TOM-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_core_montmul_postA in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m' & xs' & ts' & -> & MUc & WMc & MI' & XA' & LX' & _ & TA' & LT' & _ & ST' & HH').
    replace (ret_pc (Z_to_bv 64 658488)) with (Z_to_bv 64 658488 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (emj_core_m sp1 T hc LBc mq dXc dRc _ _ ts v f m' (md_n dN) (2 * md_n dN + 1) xs' ts' EJ2 HR EHX EHR ltac:(clear - N1 NX; lia) ltac:(clear - N1 WLG; lia) MUc WMc MI' ST' HH' XA' LX' TA' LT') as EJ3.
    eapply (K m' slA2 xs' ts'); [exact EJ3| exact JS2].
    all: match goal with |- ?g => idtac "TOM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04]0@L10572669655.6  L10582737360.3  L10582790372.5  L10582790646.5  L10582791056.6  L10582791568.6  L10582905334.4  L10582905744.6  L10582906256.5  L10583085558.5  L10583249398.5  L10584888827.6  L10584891472.6  L10584925014.12 L10585183223.7  L10585347063.7  L11264021790.6  L11265926719.5  L11266090559.5  L11266286169.5  L11266286681.6  L11266287167.4  L11266287405.6  L11266368089.6  L11266368601.6  L11266602521.3  L11268023358.7  L11268187198.7  L11268281503.12 L11268380569.5  L11268383282.5  L11360676701.4  L11366963837.3  L11370797422.5  L11370797594.4  L11370798106.5  L11370912282.4  L11370912794.5  L11372895345.5  L11372898778.5  L11372931804.11 L11372931804.12 L11373189757.5  L11373353597.5  L12939520422.5  L12939521958.7  L12939667878.5  L12939668690.6  L12939669414.7  L12939832768.4  L12940028336.3  L12941664096.11 L12941664096.12 L12941761638.6  L12941765069.5  L12941832129.8  L12941930433.7  L12946054881.7  L13879654961.6  L13883771665.7  L13883869969.7  L13883936029.5  L13883947190.5  L13884046256.11 L13885462838.2  L13885868304.4  L13885933840.6  L13885966608.4  L13885983030.7  L13886031874.5  L13886032144.4  L13886032758.6  L13886033270.5  L13886212368.4  L13886212982.6  L13886213494.5  L15968069667.5  L15968070487.4  L15968071203.3  L15968217123.5  L15968218659.3  L15968759349.1  L15969871940.5  L15969970244.6  L15970163683.4  L15970168392.3  L16497299888.3  L16497808038.7  L16497808550.6  L16497922514.6  L16497922726.7  L16497923238.6  L16498118848.4  L16498282688.5  L16500020429.6  L16500023654.6  L16500122208.11 L16500122208.12 L16500216513.7  L16500380353.8  L16504382433.7  L17433199252.3  L17437672179.4  L17437753735.5  L17437754099.4  L17437754611.5  L17439392404.5  L17439556244.5  L17439851672.5  L17439863091.5  L17767718489.1  L17772156990.4  L17772158526.4  L17772271678.4  L17772272970.4  L17772273214.4  L17773911641.5  L17774075481.5  L17774368853.4  L17774374398.4  L18301555504.4  L18303656836.3  L21194954052.6  L21195117892.5  L21195182920.4  L21195187939.4  L21197280035.4  L21197280547.5  L21197280855.4  L21197361955.4  L21197362467.5  L21197903413.1  L21477599162.3  L21547003058.3  L22189559154.5  L22189722494.5  L22189735637.6  L22191459075.4  L22191820385.6  L22594986486.2  L23933589700.15 L24281954516.2  L2437508296.4   L34120414369.0  L3480673688.5   L3482348255.4   L3482348767.5   L3482349241.4   L3482349483.4   L3482495711.4   L3482496223.5   L3482496697.4   L3482709689.4   L3482775225.6   L3482791583.7   L3482807993.4   L3483319967.1   L3484442399.4   L3484445364.4   L3484806328.6   L3484904632.6   L35394346383.279L35653441506.7  L36459744067.279L36927857204.2  L37491807754.14 L39188636933.0  L408340789.11   L414675729.15   L41887942832.3  L44437063317.13 L45355707097.2  L45855443592.5  L45855443592.7  L46531815739.2  L47492451383.279L49756027778.16 L50113579094.7  L50113677398.7  L50113951991.13 L50113951991.14 L50114039386.7  L50114051057.7  L50115676759.7  L50115709527.6  L50115775063.7  L50115987505.6  L50115988055.6  L50115989041.7  L50116134961.6  L50116135511.6  L50116135749.7  L50116136497.7  L50119903318.5  L50126207350.6  L50290522665.4  L51842906259.3  L51842907623.5  L51842907795.5  L51843266693.2  L51844992339.4  L51845003512.3  L51845070580.6  L51845168884.5  L52436379978.9  L54379423251.279L59030765931.4  L60098763854.3  L60316023918.5  L60316024602.4  L60317826941.5  L60317925245.5  L60318108890.5  L60318120305.5  L60320120701.3  L60453601745.4  L60453614714.5  L60453898205.5  L60454062045.6  L60455698874.4  L60455699662.4  L60455700410.5  L60455780794.3  L60455782330.5  L60456321452.2  L62081366787.4  L62081792865.6  L62083659890.6  L62083823730.5  L62083877845.6  L62083890814.6  L62565132042.14 L64065391367.13 L64410470777.4  L66151427842.16 L66151427842.17 L66946395423.3  L6998669830.15  L82394020.17    Q10914232702.295Q12392821858.294Q13398662114.294Q1437329663.294 Q15515733206.295Q17981642738.294Q18152175808.295Q19398994018.294Q20550492159.294Q20610658431.294Q21925520610.294Q23255371202.295Q23399781729.295Q23400601547.295Q23836106860.294Q24167257676.295Q24171697691.294Q25298584980.294Q25593364264.295Q28237870328.294Q2996258418.294 Q30049685376.294Q31506339365.295Q31600242951.295Q33074015515.294Q33077898572.295Q33604169251.295Q34423045936.295Q34719659487.295Q35240268201.295Q3573031455.295 Q36114522283.294Q36470067325.295Q37064386742.295Q38289833759.295Q38405645238.295Q3849005922.294 Q39516323787.295Q41178939992.295Q41182888463.294Q41414995486.294Q4447376314.295 Q44635400178.295Q46198667098.294Q51747278631.294Q53150795557.295Q53214747871.295Q53883130879.294Q54301645903.295Q55596576637.295Q57385681112.294Q58200053588.295Q59026489535.294Q59030962408.295Q59963313787.295Q6426749160.295 Q65314988264.295Q66946854044.295Q66950671563.294Q68602471072.294Q7522328447.294 Q8448591602.295 00000100200300400500600E00F00G00H00I00J00K00L00M00N00O00P00Q00R00S00b00c00d00e00f00g00h00i00j00k01901:01;01<01=01>01?01@01A01B01C01D01E01F01G01H01I01J01Z01[01\01]01^01_01`01a01b01c01d01e01f01g01h01i01j01k01l02G02H02I02J02K02L02M02N02O02P02Q02R02S02T02U02V02W02X02Y02Z02[02\02]02^02n02o03003103203303403503603703D03E03F03G03H03I03J03K03L03M03N03O03P03Q03R03S03T03U03V03a03b03c03d03e03f03g03h03i03j03k04604A04Q04R04S04T04U04]04^04e05305405505605705805905:05;05<05=05>05?05@05A05B05C05D05E06j07B08g08n08o09009109h0:30:40:<0:N0:O0:V0<;0<<0<=0<>0<?0<@0<A0<B0<C0<W0<X0<Y0<Z0<[0<\0<]0<^0<_0<`0<a0<o0=;0=<0==0=>0=?0=@0=A0=B0=`0?E0?I0?S0?T0?a0?b0?c0?d0?e0?f0?g0?h0?i0?j0?k0?l0?m0@90@:0@;0@<0@=0@>0@N0@O0@P0@Q0@R0@Y0AM0AN0AR0AS0B60B70Cm0Ec0GO0Ic0KA0L_0NU0PA0Qm0Sc0Sd0V70V80WV0Y40ZR0\00]N0^l0`J0ah0ai0d10eO0fm0fn0hL0hM0hN0il0kJ0kK0kL0kM0kN0mD0mE0nc10A11_13[13\15:16X16Y16Z18F18G18H19f19g1;E1<c1<d1<e1>C1?a1A?1B]1DI1DJFFFFFFS2lo2dE3sp13EPSFFFFFFFFFFFFFFS2lo2dN3sp13NPSFFFFFFFFFS2dE2dN1T4TP64FFFFFFFFFFFFFFFFFS2lo3sp13dXc3XPSFFFFFFFFFFFFFFFFFFS1R2sp2lo3SLO5NEEDE3sp13SP1FFFFFFFFFFFFFFFFFFFFFFFS2lo3sp13dRc3RPSFFFFFFFFFS2dE2dN1T3ETqFFFFFFFFFFFFFFFFFFS2dE2E13NREFFFFFFFFFFS2dN3dRc2NRS2dN3NN42N1S2dE2dN1T3dXc2XTFFFFS2dN3NRNFS2dE2dNS2dN3dXc2N12NXSFFFFFFFFFFFFFFFFFS1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R3HIA1h2sp2lo3TOP4HTOPS1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS2dE2dNFSFS1R3HIA1h2sp2lo3SLO5NEEDE3TOP2dN2hc3dXc2NX3XBL3HT14HT16S2dN3dXc2NXFS2dE3NRES2dN3dXc2NX2aq3HaqFS2dN2N1S1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFFFFFFFFS2lo2dE2dN3sp11T3TPSFFFFFFFFFFS2dE2dN2N13WLGS2dN3dXc3NXqFFFFFFFS1R2sp2lo3SLO3sp13SP14NRAM3NERS1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS2dES1R2lo3LOSFS2dE2dN1T3NTqFFFFFFFFFFFFS2dE3dXc3EXqFFFFFS2dE2dN1T3dRc2RTFFFFS2dE2dNS3dXc2r04XP161q1r1H2H02q02H43dRc4RP161T3T163sp14SP1MFS2dNFS1R2dN2r03NAL1q1r1H2H02q02H42dE3EALFS1R2LF2sp2dX2lo3SLO5NEEDE2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2sp2dX2lo2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts4SP1R2NB3NAL3EBd3XP03RP03TP03NP03EP02LA3LBl2X02XB3SPR3EALS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2sp2dX2lo2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2sp2dX2lo2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBFS1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts4SP1R2NB3EBd3XP03RP03TP03NP03EP02LA3LBl2AD3XAL2X02XB3SPRFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFS1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts4SP1R2NB3NAL3EBd3RP03TP03NP02LA3LBl2X02XB3SPRS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFFFFS1R2LF2sp2dX2lo3SLO5NEEDE2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2sp2dX2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3EBd3EAL3RP03NP02LA3LBl2X02XB3SPRFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFFS1R2LF2sp2dX2lo2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBFFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBFFS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dE2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2sp2dX2lo2dE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBF". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA MI0 MX0 NSX XW XL0 UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN NN4 HND LFN ME0 SXE OSE CRE CREL ODE IME ROIMG LFN3 DIMG CEM dA"] Lemma em_cexp : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : bv 64 -> option (bv 8)) (dXc dRc : mpd) (slA slB ts : list word) (v f : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word), EMJ sp1 T hc LBc mc dXc dRc slA slB ts -> HREL hc v f -> JSLOTSX2 T slA -> md_own dXc = LHeap -> md_own dRc = LHeap -> 1 <= md_n dN -> 1 <= md_n dE -> md_n dN <= md_n dXc -> md_n dN <= md_n dRc -> (forall (m' : bv 64 -> option (bv 8)) (xs' ts' : list word) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word), EMJ sp1 T hc LBc m' (set_limbs dXc xs') dRc slA slB ts' -> aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ (Z_to_bv 64 658612) sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658612) fc None m' (seg_rom asegs))) -> aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658488) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JS EHX EHR N1 E1 NX NR K.
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & _).
    ddestruct VN as (CN & _ & _ & NRN & _ & NB & _ & NAL & ON & _ & _ & MNc).
    destruct (emj_opnd dE _ _ _ _ _ _ _ _ _ _ _ _ EJ HR ME0 SXE OSE CRE CREL ODE IME) as (VE & _).
    ddestruct VE as (CEc & _ & _ & NRE & _ & EBd & _ & EAL & OEs & _ & _ & MEc).
    destruct (emj_blk3 _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX EHR) as (HAX & HAR & HAT & XT & RT & RX & XARR & LENX & XP16 & NRX & RARR & LENR & RP16 & N1R & _ & _ & _ & _).
    destruct (emj_oarr dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX N1 MN0 SXN OSN CRN CRNL ODN IMN) as (BYN & LENN & _ & NP4 & NP0 & NP64 & NPS & ONL & NTq & NXq & _).
    destruct (emj_oarr dE _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX E1 ME0 SXE OSE CRE CREL ODE IME) as (BYE & LENE & _ & EP4 & EP0 & EP64 & EPS & OEL & ETq & EXq & _).
    ddestruct HAX as (XIN & XP0 & XBL & XP64 & XPS & OXL & CWXL & _). ddestruct HAT as (TIN & TP0 & TBL & TP64 & TPS & OTL & CWTL & _). ddestruct HAR as (RIN & RP0 & RBL & RP64 & RPS & ORL & _).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as (((S5 & S6 & S7 & S8 & S9 & S10 & S11) & S3 & S4) & S2).
    dpose EJ as (EB & LA & LBl & J & MR & AR & _ & TAq & TLq & WLBq & T16). dpose J as (_ & AD & _).
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    cbn [nth_error] in S2, S3, S4, S5, S6, S7, S8, S9, S10, S11. injection S2 as ->. injection S3 as ->. injection S4 as ->. injection S5 as ->. injection S6 as ->. injection S7 as ->. injection S8 as ->. injection S9 as ->. injection S10 as ->. injection S11 as ->.
    dpose EB as (_ & _ & _ & SAVE & CHS & _ & SThi & STlo & _ & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. cbn [fst snd map] in CHA.
    pose proof MXc as [(CX & XAL & X0 & _ & _ & _) SGX]. rewrite AD in CX. unfold mpi_cells in CX.
    pose proof MR as [(CR & _) _]. rewrite AR in CR. unfold mpi_cells in CR.
    destruct OXc as [OXa _]. rewrite AD in OXa. pose proof (aobj_crange _ _ _ _ _ _ OXa) as CRXc. pose proof (rw_cells_bound _ _ _ _ CX) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    assert (E10 : Z.shiftr (N + 10) 3 + al_sb AL = Z.shiftr N 3 + al_sb AL + 1) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - NAL; Z.div_mod_to_equations; lia).
    assert (E10e : Z.shiftr (E + 10) 3 + al_sb AL = Z.shiftr E 3 + al_sb AL + 1) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - EAL; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    zstep_to [658516].
    (* [comment removed for export] *)
    rewrite E10. zstep_to [658552].
    (* [comment removed for export] *)
    rewrite E10e. zstep_to [679480]. rewrite zx16_small by (clear - NRN NRE; lia). rewrite zx16_small by (clear - NRN NRE; lia).
    pose proof (wl_ge (md_n dN) (md_n dE) ltac:(clear - N1; lia)) as WLG.
    pose proof (arl_need_rt_amem R) as NRAM. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (hm_top16 asegs R HIA hc LBc LF mc HHc) as HT16.
    assert (W4 : 4 * Z.of_nat (length ts) = WL * 4) by (rewrite TLq; clear; lia).
    pose proof CEM as CM'. unfold mpi_core_exp_mod_stmtA in CM'.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { eapply CM' with (LB := LBc) (LF := LF) (X := md_p dXc) (A := md_p dXc) (N := md_p dN) (an := md_n dN) (E := md_p dE) (en := md_n dE) (RR := md_p dRc) (T := T) (lo := lo)
                      (xs := md_limbs dXc) (ys := md_limbs dXc) (ns := md_limbs dN) (es := md_limbs dE) (rs := md_limbs dRc) (ts := ts);
        [exact HHc| ..];
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A; rewrite ?W4;
        first [ reflexivity | exact LOS | exact TOPc
              | lazymatch goal with |- context [P_mpi_core_exp_mod.mpi_core_exp_mod_pre] => idtac end;
                unfold P_mpi_core_exp_mod.mpi_core_exp_mod_pre, P_mpi_core_exp_mod.MPI_CORE_EXP_MOD_STACK; rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?LENX, ?LENR, ?LENN, ?LENE, ?TLq;
                repeat (split; [first [ exact XARR | exact (u32arr_ro _ _ _ _ XARR) | exact (u32arr_ro _ _ _ _ RARR) | exact BYN | exact BYE | exact TAq | exact STc | exact MIc | exact NX | exact NR
                                      | exact NP4 | exact EP4 | exact NP0 | exact EP0 | exact XP0 | exact RP0 | exact TP0 | exact XP64 | exact RP64 | exact NP64 | exact EP64
                                      | clear - N1 NN4; lia | clear - E1 NRE; lia | clear - NX; lia | clear; lia
                                      | clear - XT; lia | clear - RT; lia | clear - NTq; lia | clear - NXq; lia | clear - ETq; lia | clear - EXq; lia
                                      | clear - XP16; Z.div_mod_to_equations; lia | clear - RP16; Z.div_mod_to_equations; lia | clear - T16; Z.div_mod_to_equations; lia
                                      | clear - TP64; lia | clear - XPS; lia | clear - RPS; lia | clear - NPS; lia | clear - EPS; lia | clear - TPS; lia
                                      | clear - SP1 SLO NEEDE; lia | clear - SP1M; Z.div_mod_to_equations; lia
                                      | match goal with |- ?g => idtac "CEM-PRE0-LEFT:" g end ]|]);
                first [ rewrite unsigned_lit by (clear; lia); reflexivity | match goal with |- ?g => idtac "CEM-PRE0-LAST:" g end ]
              | clear - SP1 SLO NEEDE NRAM NER; lia
              | intros aq Haq; apply CWXL; clear - Haq NX; lia | exact CWTL
              | eapply aobj_sub; [exact OXL| apply Z.le_refl| clear - NX; lia] | eapply aobj_sub; [exact ORL| apply Z.le_refl| clear - NR; lia]
              | exact ONL | exact OEL | replace (4 * exp_mod_working_limbs (md_n dN) (md_n dE)) with (WL * 4) by (clear; lia); exact OTL
              | clear - XBL NX HT16 TOP HT1 SLO NEEDE; lia
              | match goal with |- ?g => idtac "CEM-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_core_exp_mod_postA in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m' & xs' & ts' & -> & MUc & WMc & MI' & XA' & LX' & _ & TA' & LT' & ST' & HH').
    replace (ret_pc (Z_to_bv 64 658612)) with (Z_to_bv 64 658612 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (emj_core_m sp1 T hc LBc mc dXc dRc _ slB ts v f m' (md_n dN) (Z.of_nat (length ts)) xs' ts' EJ HR EHX EHR ltac:(clear - N1 NX; lia) ltac:(rewrite TLq; clear - WLG N1; lia) MUc WMc MI' ST' HH' XA' LX' TA' LT') as EJ3.
    eapply (K m' xs' ts'); exact EJ3.
    all: match goal with |- ?g => idtac "CEM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type d"] Lemma aevtA_kf_equiv : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Phc,(29.$4.VR,VHIA,)Ph',(29.$4.VR,VHIA,)PQ,P,$99.SpPms,$9:.P,Pmo1,$9;.(9<.(9=.$4.VR,VHIA,R4.R1.)(9=.$4.VR,VHIA,R5.R1.))P,(41.$4.(42.$4.VR,VHIA,R4.Vmo,)R3.R2.)(41.$4.(42.$4.VR,VHIA,R6.Vmo,)R4.R3.)")
(* [comment removed for export] *).
  Proof. intros hc h' Q ms EQ H mo1 [HK1 MF1]. apply H. split; [apply EQ; exact HK1| exact MF1]. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03T0@L11264021790.6  L11265926719.5  L11266286169.5  L11266286681.6  L11266287167.4  L11266602521.3  L11268023358.7  L11268281503.12 L11268380569.5  L11268383282.5  L12148977814.9  L12159386551.11 L12159452087.11 L12159549905.9  L12159550391.10 L12159551441.9  L12159551536.15 L12159551543.14 L12159584967.7  L12161483190.10 L12161648570.9  L12161659409.9  L12161757463.15 L12161757463.16 L12939667878.5  L12939669414.7  L12939832768.4  L12940028336.3  L12941664096.11 L12941664096.12 L12941761638.6  L12941765069.5  L12941930433.7  L12946054881.7  L15968069667.5  L15968071203.3  L15968759349.1  L15969871940.5  L15970163683.4  L15970168392.3  L17767718489.1  L17772271678.4  L17772273214.4  L17774075481.5  L17774368853.4  L17774374398.4  L21547003058.3  L22189559154.5  L22189722494.5  L22189735637.6  L22191459075.4  L22594986486.2  L23931330658.10 L23933163315.7  L23933227843.10 L23933424451.12 L23933587749.10 L23933588291.10 L23933589285.8  L23933589699.14 L23933589700.15 L23935324482.10 L23935590883.15 L23935590883.16 L23935686478.8  L23935689445.9  L24281954516.2  L2437508296.4   L3480673688.5   L3482346809.8   L3482346814.9   L3482348255.4   L3482348767.5   L3482349241.4   L3482709689.4   L3482775225.6   L3483319967.1   L3484442399.4   L3484445364.4   L3484806328.6   L35653441506.7  L36461449783.4  L36465447862.11 L36465447862.12 L36465479856.5  L36465485083.5  L36465713943.5  L36467581808.4  L36467582320.5  L36471939863.3  L37485096620.9  L37489352588.9  L37489618733.14 L37489618733.15 L37489711488.7  L37489716267.8  L37491120637.6  L37491383693.11 L37491449229.9  L37491807754.14 L37491807757.13 L37491808747.7  L37491809677.9  L37491810283.9  L38140069211.4  L38140080368.4  L39188636933.0  L41814970463.3  L41887942832.3  L45855443592.5  L45855443592.6  L46531815739.2  L47492451383.265L49027030194.7  L49036984245.3  L49037419539.8  L49037419540.9  L49037421557.6  L49037422069.7  L49037422483.5  L49037520787.7  L49037586323.5  L49039416627.12 L49039515189.6  L49039518622.6  L49039682962.8  L50113677398.7  L50113951991.13 L50113951991.14 L50114039386.7  L50114051057.7  L50115709527.6  L50115775063.7  L50116134961.6  L50116135511.6  L50116136497.7  L50119903318.5  L50126207350.6  L50545063073.0  L51842906259.3  L51842907795.5  L51843266693.2  L51844992339.4  L51845003512.3  L51845168884.5  L54379423251.265L60098763854.3  L60316024602.4  L60317826941.5  L60318108890.5  L60318120305.5  L60320120701.3  L64063730593.8  L64065388672.8  L64065389286.8  L64065389798.7  L64065391360.12 L64065391367.13 L64065749120.9  L64065814656.10 L64066984560.5  L64067486861.7  L64067498278.7  L64067596832.14 L64067846785.9  L65414927625.10 L65415124233.10 L65415287151.8  L65415288073.9  L65415288687.8  L65415290505.13 L65415290510.14 L65416908793.6  L65417221896.9  L65417384196.8  L65417389231.8  L65417488297.14 L65417488297.15 L65429612072.8  L66151427842.16 L66151427842.17 L67576727545.6  L67620384339.4  L68419195026.8  L68419461171.12 L68419557022.6  L68419560245.6  L68420682421.3  L68421227155.7  L68421292691.5  L68421652725.7  L68421653139.5  L68421654261.6  L68421654804.9  L68431716786.7  L82394020.17    Q10914232702.278Q1431038248.277 Q15515733206.278Q17971156517.277Q18152175808.278Q21915034933.277Q23255371202.278Q23399781729.278Q24165406668.277Q24167257676.278Q27940712629.277Q28252550447.277Q2994161573.277 Q31506339365.278Q31600242951.278Q34719659487.278Q35294327592.277Q3573031455.278 Q36112425340.277Q3851102901.277 Q41176597464.277Q41178939992.278Q46192375437.277Q51749375728.277Q55596576637.278Q57387778319.277Q58200053588.278Q6426749160.278 Q65314988264.278Q66946854044.278Q66948574492.277Q7528619688.277 00000100200300400C00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00R00S00T00U00V00W00X00h00i00j00k00l00m00n00o01001101201301401501601701801901:01;01F01V01W01X01Y01a01b01c01d01e01f01g01h01i01j01k01l01m01n01o02602D02E02F02G02H02I02J02K02L02M02N02O02P02h03603703803903:03;03<03=03>03?03@03A03B03C03D03E03F03G03H03I03J03K03L03M03N03O03Z03e04704804?05g05h05i06B06C06D06E06F06G06H06I06J06K06L06M06N06O06P06Q06e06f06g06h06i06j06k06l07807907:07;07<07=08e08o09<09=09>09?09@09A09B09C09D09E09F09G09H09I09J09K09L09M09N09O09P09Q09R09S09T09U09V09W09X09Y09Z09[0:F0:G0:[0:h0:i0:j0:k0:l0:m0:n0:o0;00;10;20;P0;Q0;m0;n0=]0?d0AE0Bf0D_0D`0Fj0HK0Il0Ke0MF0Ng0Nh0Pk0Pl0R[0T<0U]0WV0Y70ZX0\90]Z0][0_<0_=0_>0`_0b@0ca0ePFFFFS2lo2dN3sp13NPSFFFFFFFFFFFFFFFFFFFFFS2lo3sp13dXc3XPSFFFFFFFFFFFFFFFFFFFS2dN3NN42N1S2dE2dN1T3dXc2XTFFFS2dN3NRNFFFFFFFFFFFFFFS2dE2dNS2dN3dXc2N12NXFFFFFFFFFFFFS1R3HIA1h2sp2lo3TOP4HTOPS2dE2dN1T4TP64FFFFFFFFFFFFFFFFFFFFFFFFSS2dE2dN3WLGS2dN3dXc2NXS2dN3dXc2NX2aq3HaqFS2dN2N1S1R2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBFFS1R2sp2lo3SLO3sp13SP13NESFFFFFFFFFFFFFFFS2lo2dE2dN3sp11T3TPSFFFFFFSS2dN3dXc3NXqFFFFFS1R2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2lo3LOSS2dE2dN1T3NTqFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS3dXc2r04XP161q1r1H2H02q02H41T3T163sp14SP1MFS2dE2dN1T3WLG2aq3HaqS2dE2dN1T3WLGFFFFFFFFFFS1R2sp2lo3SLO3sp13SP14NRAM3NERFS1R2dN2r03NAL1q1r1H2H02q02H4FS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts4SP1R2NB3NAL3XP03TP03NP02LA3LBl2X02XB3SPRS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBFS1R2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts4SP1R2NB3XP03TP03NP02LA3LBl2AD3XAL2X02XB3SPRS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBFS1R2LF2sp2dX2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts4SP1R2NB3NAL3TP03NP02LA3LBl2X02XB3SPRFS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts3SP12LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBFS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBFFS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN31T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts2LA3LBl2XBS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp11T3dXc3dRc1b2b02b12b32b42b62b72b82b93b103b113b123b133b143slB2ts3SP12LA3LBl2XB". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SPA MI0 MX0 NSX XW XL0 TPV UW0 UWX BUDL BUDFL MN0 SXN OSN CRN CRNL ODN IMN NN4 HND LFN SXE ROIMG LFN3 DIMG FROM"] Lemma em_frommont :
    forall (sp1 T : Z) (hc : (HST asegs R HIA)) (LBc : (list blk)) (mc : word -> (option (bv 8))) (dXc dRc : mpd) (slA slB ts : (list word)) (v f : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    (EMJ sp1 T hc LBc mc dXc dRc slA slB ts) ->
    (HREL hc v f) ->
    (JSLOTSX2 T slA) ->
    ((md_own dXc) = LHeap) ->
    ((md_own dRc) = LHeap) ->
    (1 <= (md_n dN)) ->
    ((md_n dN) <= (md_n dXc)) ->
    (forall (h' : (HST asegs R HIA)) (m' : word -> (option (bv 8))) (xs' ts' : (list word)) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word), (EMJ sp1 T h' LBc m' (set_limbs dXc xs') dRc slA slB ts') -> (HREL h' v f) -> (aevtA asegs (KF asegs R HIA h' mo) POSTA (MS (RJ (Z_to_bv 64 658676) sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658676) fc None m' (seg_rom asegs)))) ->
    (aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658612) fc None mc (seg_rom asegs)))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JSX EHX EHR N1 NX K. destruct JSX as ((JS & S3 & S4) & S2).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & _).
    ddestruct VN as (CN & _ & _ & NRN & _ & NB & _ & NAL & ON & _ & _ & MNc).
    destruct (emj_blk3 _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX EHR) as (HAX & HAR & HAT & XT & RT & RX & XARR & LENX & XP16 & NRX & RARR & LENR & RP16 & N1R & _ & _ & _ & _).
    destruct (emj_oarr dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX N1 MN0 SXN OSN CRN CRNL ODN IMN) as (BYN & LENN & _ & NP4 & NP0 & NP64 & NPS & ONL & NTq & NXq & NCR).
    ddestruct HAX as (XIN & XP0 & XBL & XP64 & XPS & OXL & CWXL & CRXL). ddestruct HAT as (TIN & TP0 & TBL & TP64 & TPS & OTL & CWTL & CRTL).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as (S5 & S6 & S7 & S8 & S9 & S10 & S11).
    dpose EJ as (EB & LA & LBl & J & MR & AR & _ & TAq & TLq & WLBq & T16). dpose J as (_ & AD & _).
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    cbn [nth_error] in S2, S7, S8, S9. injection S2 as ->. injection S7 as ->. injection S8 as ->. injection S9 as ->.
    dpose EB as (_ & _ & _ & SAVE & CHS & _ & SThi & STlo & _ & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. cbn [fst snd map] in CHA.
    pose proof MXc as [(CX & XAL & X0 & _ & _ & _) SGX]. rewrite AD in CX. unfold mpi_cells in CX.
    destruct OXc as [OXa _]. rewrite AD in OXa. pose proof (aobj_crange _ _ _ _ _ _ OXa) as CRXc. pose proof (rw_cells_bound _ _ _ _ CX) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    assert (E10 : Z.shiftr (N + 10) 3 + al_sb AL = Z.shiftr N 3 + al_sb AL + 1) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - NAL; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    zstep_to [658616]. zstep_to [658620]. zstep_to [658624]. zstep_to [658628]. zstep_to [658632]. zstep_to [658636]. zstep_to [658640]. zstep_to [658644].
    (* [comment removed for export] *)
    rewrite E10. zstep_to [658648]. zstep_to [658652]. zstep_to [658656]. zstep_to [658660]. rewrite zx16_small by (clear - NRN; lia). zstep_to [658664]. zstep_to [658668]. zstep_to [658672]. zstep_to [681676].
    pose proof (wl_ge (md_n dN) (md_n dE) ltac:(clear - N1; lia)) as WLG.
    pose proof (arl_need_rt_amem R) as NRAM. pose proof (arl_need_ecp_rt R) as NER. pose proof (arl_need_ecp_smalloc R) as NES.
    assert (W4 : 4 * Z.of_nat (length ts) = WL * 4) by (rewrite TLq; clear; lia).
    pose proof FROM as FM'. unfold mpi_core_from_mont_rep_stmtA in FM'.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { eapply FM' with (LB := LBc) (LF := LF) (X := md_p dXc) (A := md_p dXc) (N := md_p dN) (an := md_n dN) (T := T) (lo := lo)
                      (xs := md_limbs dXc) (ys := md_limbs dXc) (ns := md_limbs dN) (ts := ts);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?LENX, ?LENN, ?W4; unfold MPI_CORE_FROM_MONT_REP_STACK_A;
        first [ exact HHc | exact LFN | clear - LFN; lia | exact XARR | exact (u32arr_ro _ _ _ _ XARR) | exact BYN | exact TAq | exact STc | exact LOS | exact MIc | exact TOPc | exact TPV | exact NX | reflexivity
              | exact NP4 | exact NP0 | exact XP0 | exact TP0 | exact XP64 | exact NP64 | exact CRXL | exact CRTL | exact NCR
              | clear - N1 NN4; lia | clear - NX; lia | rewrite TLq; clear - WLG; lia | clear; lia
              | clear - XT; lia | clear - NTq; lia | clear - NXq; lia
              | clear - XP16; Z.div_mod_to_equations; lia | clear - T16; Z.div_mod_to_equations; lia
              | clear - TP64; lia | clear - XPS; lia | clear - NPS; lia | clear - TPS; lia
              | clear - SP1 SLO NEEDE NRAM NER; lia | clear - SP1 SLO NEEDE NES; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | intros aq Haq; apply CWXL; clear - Haq NX; lia | intros aq Haq; apply CWTL; clear - Haq WLG; lia
              | eapply aobj_sub; [exact OXL| apply Z.le_refl| clear - NX; lia]
              | exact ONL | eapply aobj_sub; [exact OTL| apply Z.le_refl| clear - WLG; lia]
              | match goal with |- ?g => idtac "FROM-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_core_from_mont_rep_postA in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m' & h' & xs' & ts' & -> & MI' & ST' & HP' & XA' & LX' & _ & TA' & LT' & _ & HH' & Ecs & Etop & Estk & Eflag & Evol & Efr & HKE).
    replace (ret_pc (Z_to_bv 64 658676)) with (Z_to_bv 64 658676 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    destruct (emj_core_p sp1 T hc LBc mc dXc dRc _ slB ts v f h' m' (md_n dN) xs' ts' EJ HR EHX EHR ltac:(clear - N1 NX; lia) WLG MI' ST' HP' XA' LX' TA' LT' HH' Ecs Etop Estk Eflag Evol Efr) as (EJ3 & HR3).
    apply (aevtA_kf_equiv hc h' _ _ HKE).
    eapply (K h' m' xs' ts'); [exact EJ3| exact HR3].
    all: match goal with |- ?g => idtac "FROM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L15043131708.252L2397676628.0   L35653441506.7  L36459744067.243L41096692127.254L41799544228.245L41800247978.242L43930071228.241L43935886280.244L44076027870.2  L59314841581.251L60098763854.3  Q12555063191.249Q13282358506.249Q13393705457.246Q19003545521.249Q20614042220.246Q22045774855.246Q22055801988.249Q22056749181.246Q23831167615.246Q26295627581.249Q34423045936.247Q39212284437.249Q40778775571.246Q41269915798.246Q43655564650.253Q4447376314.247 Q45401511455.246Q50458135125.249Q5376549916.247 Q54216140090.246Q59030879829.249Q59030962408.247Q59030977244.253Q59031429804.246Q60511567613.249Q62495047012.249Q68615291059.246Q7376909067.246 Q8944060766.246 Q9532511812.246 00001J01K01c03904S06E08709T0;10;80=00=:0>L0?[0AD0BW0D40EC0FR0Ga0I00J?0KN0L]0Mo0OL0Pb0RG0SV0Te0Tf0V50WD0XS0Yf0[50\D0]V0^e0`N0a]0blS2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBl3ULESS1R3HIA1h2sp2lo3TOP4HTOPS2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBl3ULES2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2E14SP1R3EBd3EP04EP642LA3LBl2A03SPRS2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2E14SP1R3EBd3EP04EP642LA3LBl2A03SPRS2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBl2A03A64S2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBl2A03A64S2dX2XBS2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2E14SP1R3EBd4LENE3EP02LA3LBl2A03SPR3ULE1NS1R2lo3LOSS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2E12LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS1R2LF2sp2lo3SLO5NEEDE2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB3SP12LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB3EP02LA3LBlS2LF2sp2lo2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB3SP12LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2E12LA3LBlS2LF2sp2lo2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB3SP12LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2E12LA3LBl3ULES2LF2sp2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB3EBd3EAL2LA3LBl2A03SPRS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlFS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBl3ULES2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBl2A0S2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS1R2LF2sp2lo3SLO5NEEDE2dE2dN3LFN2dA4LFN33sp11b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB3SP12LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBlS2LF2dE2dN3LFN2dA4LFN31b2b02b12b22b32b42b52b62b73b103b113b123b133b143slB2LA3LBl". (* [comment removed for export] *)
  #[using="MPIFREE IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 NSX XW XL0 TPV UW0 UWX HND ZF RRX BUDT BUDFT LFN MA0 SXA OSA CRA CRAL ODA IMA ME0 SXE OSE CRE CREL ODE IME ROIMG LFN3 d"] Lemma em_asign :
    forall (sp1 T : Z) (hc : (HST asegs R HIA)) (LBc : (list blk)) (mc : word -> (option (bv 8))) (dXc dRc : mpd) (slA slB ts : (list word)) (v f : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    (EMJ sp1 T hc LBc mc dXc dRc slA slB ts) ->
    (HREL hc v f) ->
    (JSLOTSX2 T slA) ->
    ((md_own dXc) = LHeap) ->
    (1 <= (md_n dE)) ->
    ((md_n dXc) <= SZB) ->
    ((v + (2 * AVOL_CALL)) <= PHI) ->
    ((f + ((fr_charge (d + 1)) + (fr_charge (Z.max (d + 1) 28)))) <= FR) ->
    (forall (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word), (aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ xra sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs6 y3 y4 y5 y6) F (Z_to_bv 64 658788) fc None mc (seg_rom asegs)))) ->
    (aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658676) fc None mc (seg_rom asegs)))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JSX EHX E1 HSZ HV HF K. destruct JSX as ((JS & S3 & S4) & S2).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_opnd dE _ _ _ _ _ _ _ _ _ _ _ _ EJ HR ME0 SXE OSE CRE CREL ODE IME) as (VE & _).
    ddestruct VE as (CEc & BYE0 & _ & NRE & _ & EBd & _ & EAL & OEs & _ & _ & MEc).
    destruct (emj_oarr dE _ _ _ _ _ _ _ _ _ _ _ _ EJ HR EHX E1 ME0 SXE OSE CRE CREL ODE IME) as (BYE & LENE & _ & EP4 & EP0 & EP64 & EPS & OEL & _).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as (S5 & S6 & S7 & S8 & S9 & S10 & S11).
    dpose EJ as (EB & LA & LBl & J & _). dpose J as (_ & AD & _).
    assert (AV : exists pA sgA nA padA, rw_cells asegs mc A [C8 pA; C2 (Z_to_bv 64 sgA); C2 nA; C4 padA] /\ (sgA = 1 \/ sgA = -1)
                   /\ aobj asegs AL (hcs asegs R HIA hc) mc A 16 /\ A mod 8 = 0 /\ 0 < A /\ A + 16 <= 2^64).
    { destruct SXA as [EQA|SXA'].
      - assert (EA : A = X) by (rewrite <- EQA; reflexivity). rewrite EA.
        pose proof MXc as [(CX & XAL & X0 & _) SGX]. rewrite AD in CX. unfold mpi_cells in CX.
        pose proof (rw_cells_bound _ _ _ _ CX) as XB. cbn [cells_size csize Nat.add] in XB.
        deexists 4. split; [exact CX|]. split; [exact SGX|]. split; [rewrite <- AD; exact (proj1 OXc)|]. rewrite AD in XAL, X0. split; [exact XAL|]. split; [exact X0| clear - XB; lia].
      - destruct (emj_opnd dA _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MA0 SXA' OSA CRA CRAL ODA IMA) as (VA & _).
        ddestruct VA as (CA & _ & _ & _ & SGA & ABd & _ & AAL & OAs & _).
        deexists 4. split; [exact CA|]. split; [exact SGA|]. split; [exact OAs|]. split; [exact AAL| exact ABd]. }
    ddestruct AV as (pA & sgA & nA & padA & CA & SGA & OAs & AAL & A0 & A64).
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    cbn [nth_error] in S10. injection S10 as ->.
    dpose EB as (_ & _ & _ & SAVE & CHS & _ & SThi & STlo & _ & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. cbn [fst snd map] in CHA.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (aobj_crange _ _ _ _ _ _ OAs) as CRAc.
    assert (TOCLEAN : forall (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 y3 y4 y5 y6 : word),
              aevtA asegs (KF asegs R HIA hc mo) POSTA
                (MS (RJ xra sp1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 y3 y4 y5 y6)
                    F (Z_to_bv 64 658780) fc None mc (seg_rom asegs))).
    { intros. zstep_to [658784]. zstep_to [658060].
      eapply (em_clean1 sp1 T hc LBc mc dXc dRc _ slB ts v f 0); [exact EJ| exact HR| exact S7| exact S6| exact HV| exact HF| clear; lia| exact HSZ]. }
    (* [comment removed for export] *)
    zstep_to [658692]. zstep_to [658696]. zstep_to [658700]. shadow_chk OAs (A + 8) 2.
    (* [comment removed for export] *)
    destruct SGA as [-> | ->].
    { zstep_to [658712]. zstep_to [658716]. zstep_to [658720]. zstep_to [658780]. eapply TOCLEAN. }
    zstep_to [658712]. zstep_to [658716]. zstep_to [658720]. zstep_to [658728].
    (* [comment removed for export] *)
    zstep_to [658732]. zstep_to [658736]. zstep. zstep_to [658752]. zstep_to [658756]. zstep_to [658760]. shadow_chk OEL (md_p dE) 4.
    (* [comment removed for export] *)
    pose proof (u32s_length (md_limbs dE)) as ULE. pose proof (u32ro_bound _ _ _ _ BYE) as BEB.
    rd8 BYE 0. zstep_to [658776]. (zstep_to [658776]; zstep). if_cases K1; [eapply K| eapply TOCLEAN].
    all: match goal with |- ?g => idtac "ASIGN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis ADDS : add_sub_mpi_stmtA_osz 1 asegs R HIA A_ADD_SUB_MPI.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?L13738244421.4 L13738244435.4 L13739537107.5 L14178214172.12L14178643691.7 L14178643691.8 L14180017036.13L14180407355.14L19237575590.8 L2397676628.0  L25498677823.4 L29956516996.0 L31188595651.4 L3482346814.8  L44169409993.7 L48823579041.0 L49426903397.4 L5045881991.10 L5048087968.12 L54300097155.10L54300162054.12L54300475700.14L54302081956.9 L54302114131.5 L55658718845.4 L57332318417.3 L58776240613.10L58778450114.12L61215149332.8 L66151427842.16L6970806972.5  L7374872921.6  L7375195020.11 L7375390985.13 L7375532734.14 L7377399854.11 00000<00H00I00J00K00L01701801W01X01Y01Z01e01f01g01h02702802902:02;02<02=02>02P02[02\02]03603R03b03c04G04H04I04JS1R2dX1d3UWXS1R1d2dN3UWNFFFFS1R3HIA1h3PHI2dN4BUDT2dA2hc3dXc1v2HV3HV12PBFS2dN3SZB2dA3SZJ3dXc3SZc3dX23NSZSFSS2FR1d1f2HFFFSS2dN2dA3dXc3SZcFFFFFFFS2LB4C24J3LBc4C24cS2dX2dN3SXNFFS1R2sp2lo3SLO3sp13SP13NERS3sp12r04SP1M1q1r1H2H02q02H4S3PHI2dN2dA1v2HVFS1R3HIA1h2FR1d5BUDFT2hc1f2HF4HFR12D0FFF". (* [comment removed for export] *)
  #[using="MPIFREE IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 NSX XW XL0 TPV UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN HND ZF SZB RRX BUDT BUDFT UWN ROIMG C24J SZJ ADDS d"] Lemma em_addfix :
    forall (sp1 T : Z) (hc : (HST asegs R HIA)) (LBc : (list blk)) (mc : word -> (option (bv 8))) (dXc dRc : mpd) (slA slB ts : (list word)) (v f : Z) (t0 t1 t2 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    (EMJ sp1 T hc LBc mc dXc dRc slA slB ts) ->
    (HREL hc v f) ->
    (JSLOTSX2 T slA) ->
    (((md_n dN) <= (md_n dXc)) /\ ((md_n dXc) <= ((Z.max (md_n dA) (md_n dN)) + 2))) ->
    (((v + ((grow_PHI (md_n dN)) + (3 * (grow_PHI ((Z.max (md_n dA) (md_n dN)) + 4))))) + (2 * AVOL_CALL)) <= PHI) ->
    (((f + (add_sub_FR (d + 1))) + ((fr_charge (d + 1)) + (fr_charge (Z.max (d + 1) 28)))) <= FR) ->
    (aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ (Z_to_bv 64 658884) sp1 t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 N) (Z_to_bv 64 X) (Z_to_bv 64 1) a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 A_ADD_SUB_MPI) fc None mc (seg_rom asegs)))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JSX SZc HV HF. destruct JSX as ((JS & S3 & S4) & S2).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    destruct (emj_xself _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (OSX & CRX & CRXL).
    destruct (emj_opnd dN _ _ _ _ _ _ _ _ _ _ _ _ EJ HR MN0 SXN OSN CRN CRNL ODN IMN) as (VN & SPN & OSN' & CRN' & CRNL' & ODN').
    ddestruct VN as (_ & _ & _ & NRN & _ & _ & _ & _ & _ & _ & _ & MNc).
    pose proof (emj_cnt24 _ _ _ _ _ _ _ _ _ _ EJ) as C24c.
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as (S5 & S6 & S7 & S8 & S9 & S10 & S11).
    dpose EJ as (_ & _ & _ & J & _). dpose J as (_ & AD & _).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0. pose proof (arl_need_ecp_rt R) as NER.
    assert (PB : add_sub_PHI dXc dN dXc <= grow_PHI (md_n dN) + 3 * grow_PHI (Z.max (md_n dA) (md_n dN) + 4)).
    { unfold add_sub_PHI, A_mpi_add_abs_W.add_abs_PHI, grow_PHI. clear - SZc. lia. }
    pose proof ADDS as AS'. unfold add_sub_mpi_stmtA_osz in AS'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply AS' with (h := hc) (LB := LBc) (LF := LF) (dX := dXc) (dA := dN) (dB := dXc) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AD;
        first [ exact HHc | exact HK1 | exact MXc | exact MNc | exact NSc | exact OSX | exact OSN' | exact SPN | exact CRN' | exact CRNL' | exact XWc | exact XLc | exact STc | exact LOS | exact TPV
              | exact MIc | exact OXc | exact ODN' | exact UWc | exact TOPc | reflexivity
              | apply opnd_atA_mpd; exact MXc
              | left; reflexivity
              | unfold mpd_sep; rewrite ?AD; right; clear - SXN; lia
              | rewrite <- AD; exact CRX | exact CRXL
              | intros _ ES; exact (IMN ES) | intros ES _; exact (IMN ES)
              | intros ES; exfalso; exact (NSc ES)
              | clear - SP1 SLO NEEDE NER; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | rewrite unsigned_lit by (clear; lia); reflexivity
              | unfold uw_obj in *; clear - UWX; lia | unfold uw_obj in *; clear - UWN; lia
              | clear - HV1 HV BUDT PB; unfold AVOL_CALL in *; lia | clear - HFR1 HF BUDFT D0; unfold fr_charge in *; lia
              | clear - C24c C24J; unfold C24_ADDSUB, C24_MOD_MPI in *; lia
              | match goal with |- ?g => idtac "ADDS-PRE-LEFT:" g end ]. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E' & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & CR).
    injection E' as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite AD in HP2.
    replace (ret_pc (Z_to_bv 64 658884)) with (Z_to_bv 64 658884 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    destruct CR as [[CRV BK] NSZ]. unfold addsub_nz in NSZ.
    destruct (emj_call sp1 T hc LBc mc dXc dRc slA slB ts v f h2 LB2 m2 dX2 _ _ EJ HR MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as (EJ2 & HR2).
    pose proof (hrel_weaken _ _ _ _ _ HR2 ltac:(apply Z.add_le_mono_l; exact PB) ltac:(apply Z.le_refl)) as HR2'.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    zstep_to [658056].
    eapply (em_clean sp1 T h2 LB2 m2 dX2 dRc slA slB ts _ _ r); [exact EJ2| exact HR2'| exact S7| exact S6| clear - HV; lia| clear - HF; lia| | clear - NSZ SZc SZJ; lia].
    destruct CRV as [(-> & _)| ->]; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia].
    all: match goal with |- ?g => idtac "ADDS-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01H0@D26706871854.278D61573083454.278D67038978349.278K14461423358.278K29219025976.278K7750690063.278 L138610065.8    L138691770.3    L139379143.2    L140900119.10   L14447004729.2  L15968070472.2  L15968759349.1  L1670971415.2   L1685717371.0   L23072471841.0  L24364708814.7  L26786418512.1  L27938665392.11 L27940405558.7  L27940847645.4  L27940933942.2  L28401028998.9  L28922983928.268L29217191679.2  L29467392662.1  L3482349492.3   L3482791583.7   L3483319967.1   L35653441506.7  L36581952677.9  L36618624238.2  L38235734261.1  L39188636933.0  L54379423251.240L58640895946.239L60098763854.3  L66151427842.16 L66151427842.17 L66949481604.7  L66951690025.14 L66952208249.5  L7737701347.2   L82394020.17    L9080220944.4   Q10149575540.278Q11801279589.278Q12477889258.244Q14211868145.245Q14211868145.273Q14308027860.244Q14308272604.245Q14308272604.273Q14308316771.272Q15515733206.245Q15515733206.273Q21912936637.244Q23399781729.245Q23927705296.278Q24167257676.245Q24167502404.244Q26706871854.278Q26708823086.277Q32981943281.272Q32982186054.244Q34719659487.245Q38413739931.245Q38479773201.244Q42418669555.274Q42418784243.274Q42439443119.278Q45416566600.274Q45416648520.274Q46194471685.244Q49698585326.276Q57037327601.278Q57389876359.244Q59865321072.278Q61573083454.278Q61575035710.277Q6186103236.278 Q62011970312.278Q63774139624.275Q64041402609.278Q64683667846.278Q65314988264.245Q7526521632.244 Q7845954958.278 00002104206X08[0:^0<l0<m0<n0<o0=00=10=20=30=<0==0=>0=Y0=^0=_0>:0>;0><0>^0@P0@Q0@V0@W0@X0@Y0A10AT0A]0Aa0Ab0CT0EI0ES0F80F90F:0F;0F<0F=0FY0Fh0Hl0Jf0LQ0N<0Og0QR0S=0Th0VS0XY0Z_0\b0^[0`o0bZ0dE0f?0h90id0kO0kP0kQ0m<0ng10R12T14?15j17U19I1;[1=F1=G1?A1A;1CC1E=1Fn1I@1KX1MC1O<1Q:S1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3LOS3SLO5NEEDE2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP14SP1R2LA3LBl2X03XP02XB3SPR2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB4DSX12HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB4DSX12HB5Ha_st5Hl_stS1R2LF2sp2dX2lo3SLO5NEEDE3DSX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stFFFFFFFS3dXc3NRXSSS1R2sp2lo3SLO5NEEDE3sp13SP1S3sp1FS1R2sp2lo3SLO5NEEDE3sp13SP1FFS1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1S1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBFS3sp1FFFS1R3HIA1h2sp2lo3TOP4HTOPS1R2sp2lo3SLO5NEEDE3sp13dXc3SP13XBLS3dXc3NRXS2loSS1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2X02XBS1R2lo3LOSS3dXc2r04XP161q1r1H2H02q02H43sp14SP1MFFFFFS1R2dX2r03XAL1q1r1H2H02q02H4S2sp2lo3sp13SP1S1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2LA3LBl3XAL2X03XP02XB3SPRS1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b194SP1R2LA3LBl3XAL2X03XP02XB3SPRS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS1R2LF2sp2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl3XAL2X02XBS1R3HIA1h2LF2sp2dX3TOP2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB4HTOP2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBFFS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX3slo3SSL2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_stS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBFS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2X02XB2HBS1R2LF2sp2dX2lo3SLO5NEEDE2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2dX3slo3TOP2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XB4HTOP2HB5Ha_st5Hl_stS1R2LF2dX2dN3LFN2dA4LFN33dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XBS1R2LF2sp2dX2lo2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b193SP12LA3LBl2XBS1R2LF2dX2dN3LFN2dA4LFN33sp13dXc1b2b02b12b32b42b52b62b72b82b93b103b113b123b133b143b153b163b173b183b192LA3LBl2XB2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="MPIFREE IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 NSX XW XL0 OX0 TPV UW0 UWX MN0 SXN OSN CRN CRNL ODN IMN HND ZF SZB RRX BUDT BUDFT LFN UWN ROIMG C24J LFN3 SZJ ADDS d"] Lemma em_signfix :
    forall (sp1 T : Z) (hc : (HST asegs R HIA)) (LBc : (list blk)) (mc : word -> (option (bv 8))) (dXc dRc : mpd) (slA slB ts : (list word)) (v f : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    (EMJ sp1 T hc LBc mc dXc dRc slA slB ts) ->
    (HREL hc v f) ->
    (JSLOTSX2 T slA) ->
    ((md_own dXc) = LHeap) ->
    (((md_n dN) <= (md_n dXc)) /\ ((md_n dXc) <= ((Z.max (md_n dA) (md_n dN)) + 2))) ->
    (((v + ((grow_PHI (md_n dN)) + (3 * (grow_PHI ((Z.max (md_n dA) (md_n dN)) + 4))))) + (2 * AVOL_CALL)) <= PHI) ->
    (((f + (add_sub_FR (d + 1))) + ((fr_charge (d + 1)) + (fr_charge (Z.max (d + 1) 28)))) <= FR) ->
    (aevtA asegs (KF asegs R HIA hc mo) POSTA (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658788) fc None mc (seg_rom asegs)))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JSX EHX SZc HV HF. pose proof JSX as ((JS & S3 & S4) & S2).
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ HR) as (SP1 & SP1M & SP1R & HHc & MXc & NSc & XWc & XLc & STc & MIc & OXc & UWc & SSc & TOPc).
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    dpose JS as (S5 & S6 & S7 & S8 & S9 & S10 & S11).
    dpose EJ as (EB & LA & LBl & J & _). dpose J as (_ & AD & _).
    pose proof MXc as [(CX & XAL & X0 & LENX & NRX & OWX) SGX]. rewrite AD in CX, XAL, X0. unfold mpi_cells in CX. unfold MPI_MAX_LIMBS in NRX.
    rewrite EHX in OWX. ddestruct OWX as (N1X & XIN & XP16 & XARR).
    destruct (harr_of_in hc LBc mc sp1 _ _ HHc XIN) as (_ & XP0 & XBL & XP64 & XPS & OXL & _).
    repeat (destruct slA as [|? slA]; [discriminate LA|]). destruct slA; [| discriminate LA].
    repeat (destruct slB as [|? slB]; [discriminate LBl|]). destruct slB; [| discriminate LBl].
    cbn [nth_error] in S2, S4. injection S2 as ->. injection S4 as ->.
    dpose EB as (_ & _ & _ & SAVE & CHS & _ & SThi & STlo & _ & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. cbn [fst snd map] in CHA.
    destruct OXc as [OXa _]. rewrite AD in OXa. pose proof (aobj_crange _ _ _ _ _ _ OXa) as CRXc.
    pose proof (rw_cells_bound _ _ _ _ CX) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HS1 in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    assert (E10x : Z.shiftr (X + 10) 3 + al_sb AL = Z.shiftr X 3 + al_sb AL + 1) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - XAL; Z.div_mod_to_equations; lia).
    assert (E8 : Z.shiftr (X + 8) 3 + al_sb AL = Z.shiftr X 3 + al_sb AL + 1) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear - XAL; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    zstep_to [658792]. zstep_to [658796]. zstep_to [658800]. zstep_to [658804]. zstep_to [658808]. zstep_to [658812]. rewrite E10x. zstep_to [658816]. zstep_to [658820]. zstep_to [658824]. zstep_to [658828]. rewrite zx16_small by (clear - NRX; lia). zstep_to [658832]. zstep_to [681472].
    pose proof (A_mpi_core_check_zero_ct_spec AL IMG) as SPZ. unfold mpi_core_check_zero_ct_stmtA, A_MPI_CORE_CHECK_ZERO_CT in SPZ.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo).
    { eapply SPZ with (CS := hcs asegs R HIA hc) (A := md_p dXc) (n := md_n dXc) (lo := lo) (xs := md_limbs dXc);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold MPI_CORE_CHECK_ZERO_CT_STACK_A; rewrite ?LENX;
        first [ exact (u32arr_ro _ _ _ _ XARR) | exact XP0 | exact MIc | exact CSOKc | exact (hm_abase asegs R HIA hc LBc LF mc HHc) | exact (art_alwf asegs R HIA) | exact OXL | exact STc | reflexivity
              | clear - NRX; lia | clear; lia | clear - XP16; Z.div_mod_to_equations; lia
              | eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
              | clear - SP1 SLO NEEDE; lia | clear - SP1M; Z.div_mod_to_equations; lia
              | left; clear - XBL SP1 SLO NEEDE; lia
              | match goal with |- ?g => idtac "CZ-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold mpi_core_check_zero_ct_postA, MPI_CORE_CHECK_ZERO_CT_STACK_A in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m1 & zz & -> & MUc & WMc & MI1 & -> & _ & _ & ST1).
    replace (ret_pc (Z_to_bv 64 658836)) with (Z_to_bv 64 658836 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (emj_pure sp1 T hc LBc mc dXc dRc _ _ ts v f (sp1 - 16) m1 EJ HR ltac:(clear - SP1 SLO NEEDE; lia) MUc WMc MI1 ST1) as EJ1.
    clear SAVE CHS SThi STlo SHC SSlo SShi SNlo SNhi PRES CHA CX OXa CRXc MU WM XARR OXL MUc WMc.
    (* [comment removed for export] *)
    destruct (emj_xfacts _ _ _ _ _ _ _ _ _ _ _ _ EJ1 HR) as (_ & _ & _ & HH1 & MX1 & _ & XW1 & _ & _ & _ & OX1 & _).
    pose proof EJ1 as (EB1 & _). 
    dpose EB1 as (_ & _ & _ & SAVE & CHS & _ & SThi & STlo & _ & SHC & SSlo & SShi & SNlo & SNhi & PRES).
    pose proof (Forall_inv CHS) as CHA. pose proof (Forall_inv (Forall_inv_tail CHS)) as CHB. cbn [fst snd map] in CHA, CHB.
    pose proof MX1 as [(CX & _) _]. rewrite AD in CX. unfold mpi_cells in CX.
    destruct XW1 as [CW _]. rewrite AD in CW. destruct OX1 as [OXa _]. rewrite AD in OXa.
    pose proof (aobj_crange _ _ _ _ _ _ OXa) as CRXc. pose proof (aobj_crange _ _ _ _ _ _ (proj1 OX0)) as CRX0.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_stack asegs R HIA h) as SCS0.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (DSX1 : X + 16 <= sp1 \/ sp1 + 320 <= X) by (clear - DSX SP1 SLO NEEDE; lia).
    unfold EM_POISON_RR in SHC.
    pose proof (munch_refl [(sp1, sp1 + 40); (X, X + 16)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep_to [658840]. rewrite E8. zstep_to [658844]. zstep_to [658848].
    assert (FIN : forall m2 (sg' : Z) (q0 q1 q2 qa4 qa5 qa6 qa7 q3 q4 q5 q6 : word) cA cB,
              (sg' = 1 \/ sg' = -1) ->
              rw_cells asegs m2 X [C8 (Z_to_bv 64 (md_p dXc)); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 (md_n dXc)); C4 (md_pad dXc)] ->
              munch [(sp1, sp1 + 40); (X, X + 16)] m1 m2 -> wmono asegs m1 m2 ->
              EMBs EM_POISON_RR sp1 hc LBc m2 [(sp1, cA); (sp1 + 176, cB)] ->
              cA = map C8 [b; b0; SH X; b2; SH (X + 8); b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18] -> cB = map C8 [b19; b20; b21; b22; b23] ->
              aevtA asegs (KF asegs R HIA hc mo) POSTA
                (MS (RJ (Z_to_bv 64 0xa0dc4) sp1 q0 q1 q2 (Z_to_bv 64 X) (Z_to_bv 64 N) (Z_to_bv 64 X) (Z_to_bv 64 1) qa4 qa5 qa6 qa7 xs6 q3 q4 q5 q6) F (Z_to_bv 64 A_ADD_SUB_MPI) fc None m2 (seg_rom asegs))).
    { intros m2 sg' q0 q1 q2 qa4 qa5 qa6 qa7 q3 q4 q5 q6 cA cB SG' CX2 MU2 WM2 EB2 -> ->.
      pose proof (emj_upd sp1 T hc LBc m1 dXc dRc _ _ ts v f m2 _ sg' EJ1 HR EB2 eq_refl MU2 WM2 CX2 SG') as EJ2.
      eapply (em_addfix sp1 T hc LBc m2 (set_sg dXc sg') dRc _ _ ts v f); [exact EJ2| exact HR| exact JSX| exact SZc| exact HV| exact HF]. }
    unfold ct_mask. destruct (Z.eqb_spec zz 0) as [Ez|Nz]; (zstep_to [658852]; zstep_to [658856]; zstep_to [658860]; zstep_to [658864]; zstep_to [658868]; zstep_to [658872]; zstep_to [658876]; zstep_to [658880]; zstep_to [649696]; unfold A_ADD_SUB_MPI in FIN;
      lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo sp1, H3 : HM _ _ _ hc LBc LF ?m2, H4 : stk asegs ?m2 (sp1 + 216) _ |- _ =>
        lazymatch type of CX with rw_cells _ _ _ [_; C2 (Z_to_bv 64 ?sgv); _; _] =>
          eapply (FIN m2 sgv); [first [left; reflexivity| right; reflexivity]| exact CX| exact MU| exact WM| | reflexivity| reflexivity];
          unfold EMBs; refine (conj SP1 (conj SP1M (conj H3 (conj SAVE (conj _ (conj _ (conj H4 (conj H2 (conj H1 (conj SHC (conj SSlo (conj SShi (conj SNlo (conj SNhi PRES))))))))))))));
          [ repeat (apply Forall_cons; [cbn [fst snd]; first [exact CHA| exact CHB]|]); apply Forall_nil
          | repeat (apply Forall_cons; [unfold chunk_in; cbn [fst snd cells_size csize map Nat.add]; clear; lia|]); apply Forall_nil ]
        end end).
    all: match goal with |- ?g => idtac "SIGNFIX-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition em_V1 : Z := vchg (WL * 4) + em_GP.
  Definition em_V2 : Z := em_V1 + copy_PHI dA.
  Definition em_V3 : Z := em_V2 + mod_mpi_PHIn (md_n dA) (md_n dN).
  Definition em_V4 : Z := em_V3 + grow_PHI (md_n dN).
  Definition em_V5 : Z := em_V4 + (grow_PHI (md_n dN) + 3 * grow_PHI (Z.max (md_n dA) (md_n dN) + 4)).
  Definition em_F1 : Z := fr_charge (d + 1) + em_GF.
  Definition em_F2 : Z := em_F1 + copy_FR d.
  Definition em_F3 : Z := em_F2 + mod_mpi_FRn (md_n dA) (md_n dN) (d + 1).
  Definition em_F4 : Z := em_F3 + grow_FR (d + 1).
  Definition em_F5 : Z := em_F4 + add_sub_FR (d + 1).
  Hypothesis BUDJ : em_V5 + 2 * AVOL_CALL <= PHI.
  Hypothesis BUDJF : em_F5 + (fr_charge (d + 1) + fr_charge (Z.max (d + 1) 28)) <= FR.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0>L11246032124.8L19802665843.4L20043016835.5L20043016835.6L20043016835.7L21496092212.4L21824241726.2L22890275614.2L31823593655.2L34257660976.5L34257660976.6L34257660976.7L38271553838.4L38342920114.4L4781719053.2 L54127846631.8L55482611467.4L56239276150.4L59308550641.5L59311123927.6L64491265552.2L64964637722.6L8303040765.2 L8303042173.2 00000G00X00h01;01Q01b01h01n02702E02V02j03603E03K03d03n04=04M04a04g05>05G05PS3PHI2dN2dA2P32P42P52BJS2dN2dA4NRN04NRA0S2FR1d2dN2dA3BJFS2FR1d2dN2dA2Q53BJFS2FR1d2dN2dA2Q42Q53BJFS2dN2dA4NRN04NRA0S1d2D0S1d2D0S2dA4NRA0S3PHI2dN2dA2BJS3PHI2dN2dA2P52BJS3PHI2dN2dA2P42P52BJS1d2dN2dA2Q3S2dN2dA3dX43SZ4S1d2D0S2FR1d2dN2dA2Q32Q42Q53BJFS2dN2dA2P3S2dN2dA3dX23SZ2S2dN3dRc1Q2N12NRS2dN2dA2N13dX41Q3SZ4S1d2D0S2dN3SZB2dA3SZJ3dX43SZ4S2dA4NRA0S2dN4NRN0". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX SSMAP SPA SS0 MI0 MX0 NSX XW XL0 OX0 TPV UW0 UWX BUDL BUDFL MN0 SXN OSN CRN CRNL ODN IMN NN4 HND ZF MPIFREE SZB RRX BUDT BUDFT LFN UWN SZ0 MA0 SXA OSA CRA CRAL ODA IMA NXA ME0 SXE OSE CRE CREL ODE IME ROIMG C24J COPY MODS LFN3 SZJ GROW DIMG TOM CEM FROM ADDS BUDJ BUDJF d"] Lemma em_journey : forall (sp1 T : Z) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dRc : mpd) (slA slB ts : list word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6 : word),
    EMJ sp1 T hc LBc mc dX dRc slA slB ts -> HREL hc em_V1 em_F1 -> JSLOTS T slA ->
    1 <= md_n dN -> 1 <= md_n dE -> md_n dN <= md_n dRc ->
    aevtA asegs (KF asegs R HIA hc mo) POSTA
      (MS (RJ xra sp1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 t3 t4 t5 t6) F (Z_to_bv 64 658040) fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EJ HR JS N1 E1 NR.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0.
    pose proof MN0 as [(_ & _ & _ & _ & NRN0 & _) _]. pose proof MA0 as [(_ & _ & _ & _ & NRA0 & _) _]. unfold MPI_MAX_LIMBS in NRN0, NRA0.
    assert (P2 : 0 <= copy_PHI dA) by (unfold copy_PHI, grow_PHI, AVOL_CALL; clear - NRA0; lia).
    assert (P3 : 0 <= mod_mpi_PHIn (md_n dA) (md_n dN)) by (unfold mod_mpi_PHIn; clear - NRA0 NRN0; lia).
    assert (P4 : 0 <= grow_PHI (md_n dN)) by (unfold grow_PHI, AVOL_CALL; clear - NRN0; lia).
    assert (P5 : 0 <= grow_PHI (md_n dN) + 3 * grow_PHI (Z.max (md_n dA) (md_n dN) + 4)) by (unfold grow_PHI, AVOL_CALL; clear - NRA0 NRN0; lia).
    assert (Q2 : 0 <= copy_FR d) by (unfold copy_FR, calls_FR, fr_charge; clear - D0; lia).
    assert (Q3 : 0 <= mod_mpi_FRn (md_n dA) (md_n dN) (d + 1)) by (apply mod_mpi_FRn_nonneg; [clear - NRA0; lia| clear - D0; lia]).
    assert (Q4 : 0 <= grow_FR (d + 1)) by (unfold grow_FR, calls_FR, fr_charge; clear - D0; lia).
    assert (Q5 : 0 <= add_sub_FR (d + 1)) by (unfold add_sub_FR, A_mpi_add_abs_W.add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    assert (QA : fr_charge (Z.max (d + 1) 28) <= add_sub_FR (d + 1)) by (unfold add_sub_FR, A_mpi_add_abs_W.add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
    assert (FC1 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - D0; lia).
    assert (FM : fr_charge (d + 1) <= fr_charge (Z.max (d + 1) 28)) by (unfold fr_charge; clear; lia).
    pose proof BUDJ as BJ. pose proof BUDJF as BJF. unfold em_V5, em_V4, em_V3, em_V2 in BJ. unfold em_F5, em_F4, em_F3, em_F2 in BJF.
    assert (RH : md_own dRc = LHeap).
    { ddestruct EJ as (_ & _ & _ & _ & MR & _ & NSR & _). destruct MR as [(_ & _ & _ & _ & _ & OW) _].
      destruct (md_own dRc); [exfalso; destruct OW as (_ & Q); clear - Q NR N1; lia| reflexivity| exfalso; exact (NSR eq_refl)]. }
    (* [comment removed for export] *)
    assert (GROWPART : forall hq LBq mq dXq slAq (q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 : word) (qra qs6 : word),
              EMJ sp1 T hq LBq mq dXq dRc slAq slB ts -> HREL hq em_V3 em_F3 -> JSLOTSX T slAq -> md_n dXq <= Z.max (md_n dA) (md_n dN) + 2 ->
              aevtA asegs (KF asegs R HIA hq mo) POSTA
                (MS (RJ qra sp1 q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 qs6 q3 q4 q5 q6) F (Z_to_bv 64 658356) fc None mq (seg_rom asegs))).
    { intros hq LBq mq dXq slAq q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 qra qs6 EJq HRq JSq SZq.
      eapply (em_grow sp1 T hq LBq mq dXq dRc slAq slB ts em_V3 em_F3); [exact EJq| exact HRq| exact JSq| exact SZq| unfold em_V3, em_V2; clear - BJ P5; lia| unfold em_F3, em_F2; clear - BJF QA Q5 FC1 FM; lia|].
      intros h4 LB4 m4 dX4 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 EJ4 HR4 SZ4. fold em_V4 em_F4 in HR4.
      assert (XH : md_own dX4 = LHeap).
      { ddestruct EJ4 as (_ & _ & _ & J4 & _). ddestruct J4 as (MX4 & _ & _ & NS4 & _). destruct MX4 as [(_ & _ & _ & _ & _ & OW) _].
        destruct (md_own dX4); [exfalso; destruct OW as (_ & Q); clear - Q SZ4 N1; lia| reflexivity| exfalso; exact (NS4 eq_refl)]. }
      eapply (em_mminit sp1 T h4 LB4 m4 dX4 dRc slAq slB ts em_V4 em_F4); [exact EJ4| exact HR4| exact XH| exact N1|].
      intros m5 z0 z1 z2 mm za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 EJ5.
      eapply (em_tomont sp1 T h4 LB4 m5 dX4 dRc slAq slB ts em_V4 em_F4 mm); [exact EJ5| exact HR4| exact JSq| exact XH| exact RH| exact N1| clear - SZ4; lia| exact NR|].
      intros m6 slA6 xl6 ts6 w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 EJ6 JS6.
      eapply (em_cexp sp1 T h4 LB4 m6 (set_limbs dX4 xl6) dRc slA6 slB ts6 em_V4 em_F4); [exact EJ6| exact HR4| exact JS6| exact XH| exact RH| exact N1| exact E1| cbn [md_n set_limbs]; clear - SZ4; lia| exact NR|].
      intros m7 xs7 ts7 u0 u1 u2 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 EJ7.
      eapply (em_frommont sp1 T h4 LB4 m7 _ dRc slA6 slB ts7 em_V4 em_F4); [exact EJ7| exact HR4| exact JS6| exact XH| exact RH| exact N1| cbn [md_n set_limbs]; clear - SZ4; lia|].
      intros h8 m8 xs8 ts8 p0 p1 p2 pa0 pa1 pa2 pa3 pa4 pa5 pa6 pa7 p3 p4 p5 p6 EJ8 HR8.
      eapply (em_asign sp1 T h8 LB4 m8 _ dRc slA6 slB ts8 em_V4 em_F4); [exact EJ8| exact HR8| exact JS6| exact XH| exact E1| cbn [md_n set_limbs]; clear - SZ4 SZJ; lia| unfold em_V4, em_V3, em_V2; clear - BJ P5; lia| unfold em_F4, em_F3, em_F2; clear - BJF Q5 QA FC1 FM; lia|].
      intros r0 r1 r2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 r3 r4 r5 r6.
      eapply (em_signfix sp1 T h8 LB4 m8 _ dRc slA6 slB ts8 em_V4 em_F4); [exact EJ8| exact HR8| exact JS6| exact XH| cbn [md_n set_limbs]; exact SZ4| unfold em_V4, em_V3, em_V2; clear - BJ; lia| unfold em_F4, em_F3, em_F2; clear - BJF QA FC1 FM; lia]. }
    eapply (em_copy sp1 T hc LBc mc dRc slA slB ts em_V1 em_F1); [exact EJ| exact HR| exact JS| clear - BJ P3 P4 P5; lia| clear - BJF QA Q3 Q4 Q5 FC1 FM; lia|].
    intros h2 LB2 m2 dX2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 EJ2 HR2 SZ2. fold em_V2 em_F2 in HR2.
    eapply (em_sgn sp1 T h2 LB2 m2 dX2 dRc slA slB ts em_V2 em_F2); [exact EJ2| exact HR2| exact JS|].
    intros m3 slA3 EJ3 JS3.
    eapply (em_cmp sp1 T h2 LB2 m3 (set_sg dX2 1) dRc slA3 slB ts em_V2 em_F2); [exact EJ3| exact HR2| |].
    - intros m4 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 EJ4.
      eapply (em_mod sp1 T h2 LB2 m4 (set_sg dX2 1) dRc slA3 slB ts em_V2 em_F2); [exact EJ4| exact HR2| exact JS3| cbn [md_n set_sg]; exact SZ2| unfold em_V2; clear - BJ P4 P5; lia| unfold em_F2; clear - BJF QA Q4 Q5 FC1 FM; lia|].
      intros h5 LB5 m5 dX5 w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 EJ5 HR5 SZ5. fold em_V3 em_F3 in HR5.
      eapply GROWPART; [exact EJ5| exact HR5| exact JS3| exact SZ5].
    - intros m4 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 EJ4.
      eapply GROWPART; [exact EJ4| eapply hrel_weaken; [exact HR2| unfold em_V3; clear - P3; lia| unfold em_F3; clear - Q3; lia]| exact JS3| cbn [md_n set_sg]; clear - SZ2; lia].
    all: match goal with |- ?g => idtac "JOURNEY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RR4 : Rr (-4) dX.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L23250245443.9 L23984723757.2 L29038974481.4 L3374242837.8  L35791252591.15L38000921400.8 L38948636245.0 L39188636933.0 L39332637397.0 L40622469209.2 L46836419316.3 L519294241.8   L63922259462.9 L8224808951.4  00000R00Y00e01<02002M02N02O02P02W02b03A03c03oS1R2sp2dX2lo3SLO5NEEDE3sp13SP13DSPS2dX2NPS1R2dX3sp11QS1R3sp11T2ts1Q2dE2dN2TLS1R2sp2lo3LOS3SLO5NEEDE2dE2dN3sp11T2ts3SP12TL3ALO2BLS1R3HIA1h2sp3TOP3sp13SP14HTOPSSSS1R3sp1S2dE2dN3WL0S1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S1R2sp2dX2lo3SLO5NEEDE3DSX3sp13SP1S1R2dX3sp11Q". (* [comment removed for export] *)
  #[using="m lo LOS SLO NEEDE TOP HH0 DSX XL0 OX0 d"] Lemma rr1_carry : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Ph1,(29.$4.VR,VHIA,)PLB1,(28.$2:.)Pm1,P,(16.&40.)(2;.(16.&8.))Pm2,P,(16.&40.)(2;.(16.&8.))PT,$2.Pts,(28.(16.&40.))P,(0.(8.(<.(=.&40.Vsp,)+150.)R7.)(8.R7.(<.(=.&40.Vsp,)+140.)))P,(4:.R7.(4;.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))(4<.(:.Vd,+1.)))P,(?.$4.VR,VHIA,R8.R7.VLF,R6.)P,(30.(23.$2.$2.)(24.$2.$2.R5.(3>.(49.(3?.VdN,)(3?.VdE,))+4.))R8.)P,(1.$2.(59.(18.(16.&40.)R5.))(49.(3?.VdN,)(3?.VdE,)))P,(34.=(49.(3?.VdN,)(3?.VdE,)))P,(5?.(11.(23.$2.$2.)(24.$2.$2.R=.(:.R=.+=8.))(11.(23.$2.$2.)(24.$2.$2.(:.(1;.(:.R=.+60.)+3.)(1<.(1=.VR,)))(:.(:.(1;.(:.R=.+60.)+3.)(1<.(1=.VR,)))+<.))(14.(23.$2.$2.))))R:.R9.)P,(60.$4.R;.R:.)P,(4=.$4.R<.VLB,VdX,)P,(6;.$4.R=.R;.R:.)(0.(4=.$4.R=.VLB,VdX,)(6;.$4.R=.R<.R;.))")
(* [comment removed for export] *).
  Proof.
    intros sp1 h1 LB1 m1 m2 T ts SP1 HR HH1 TIN TL WL0 MU WM MX1 TA.
    dpose HR as (HT1 & HS1 & HF1 & HCS1 & HV1 & HFR1).
    pose proof (hcs_ok asegs R HIA h1) as CSOK1. pose proof (art_lo asegs R HIA) as ALO.
    pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    pose proof (hcs_stack asegs R HIA h1) as SCS01. rewrite HS1 in SCS01.
    assert (SCW : crange (hcs asegs R HIA h1) (sp1 + 96) (8 * 12)) by (eapply crange_sub; [exact SCS01| clear - SP1 SLO NEEDE LOS; lia| clear - SP1 TOP HTOP; lia]).
    assert (SHE : Z.shiftr (sp1 + 96) 3 + al_sb AL = shadow_of AL (sp1 + 96)) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
    pose proof (aobj_crange _ _ _ _ _ _ (proj1 OX0)) as CRX0.
    split.
    - eapply mpd_at_munch_any; [exact MX1| exact MU| exact WM| |].
      + cbn [disjoint_from].
        destruct (apart_shadow_client AL (hcs asegs R HIA h1) X 16 (sp1 + 96) _ 12 CSOK1 ltac:(eapply crange_mono; [exact HCS1| exact CRX0]) SCW SHE ltac:(clear; lia) ltac:(clear; lia)) as [Q|Q];
          (split; [clear - DSX SP1 SLO NEEDE; lia| split; [clear - Q; lia| exact I]]).
      + intros NN. ddestruct (XL0 NN) as (CRP & NP & DSP). cbn [disjoint_from].
        destruct (apart_shadow_client AL (hcs asegs R HIA h1) (md_p dX) (4 * md_n dX) (sp1 + 96) _ 12 CSOK1 ltac:(eapply crange_mono; [exact HCS1| exact CRP]) SCW SHE ltac:(clear - NP; lia) ltac:(clear; lia)) as [Q|Q];
          (split; [clear - DSP SP1 SLO NEEDE; lia| split; [clear - Q; lia| exact I]]).
    - eapply (u32arr_transport asegs _ m1 m2); [exact TA| exact MU| exact WM|].
      pose proof (hm_blocks_low asegs R HIA h1 LB1 LF m1 HH1 T (WL * 4) ltac:(apply in_or_app; left; exact TIN)) as BL.
      pose proof (aobj_crange _ _ _ _ _ _ (hm_aobj_block asegs R HIA h1 LB1 LF m1 _ _ HH1 TIN)) as CRT.
      cbn [disjoint_from].
      destruct (apart_shadow_client AL (hcs asegs R HIA h1) T (WL * 4) (sp1 + 96) _ 12 CSOK1 CRT SCW SHE ltac:(clear - WL0; lia) ltac:(clear; lia)) as [Q|Q];
        (split; [clear - BL TL ALO LOS SP1 SLO NEEDE; lia| split; [clear - Q TL; lia| exact I]]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L15516709496.3 L18468879494.3 L19617693571.36L32272634655.2 L32272634655.3 L46069865747.0 L4856509588.3  L62869071527.2 L64188749938.2 L7526226142.3  L8173850292.8  00000;00F00G00M00N00O00Z00c00j01501NS2dN3NN42N1S2dE2dN3WLBFS2FR1QFSS2dE2dN3WLBS2dE4NRE0S3PHI1QS2dE2dN3WLBS1R2dE2dN3WLB1T2F02F13ACV". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE TOP HH0 SSL SLL DSX d SSMAP SPA SS0 MI0 MX0 NSX XW XL0 OX0 TPV UW0 UWX LSET BUDL BUDFL RRL MN0 SXN OSN CRN CRNL ODN IMN NN4 CALLOC RR16 BUDA BUDFA C24A BUDA2 BUDFA2 HND ZF MPIFREE SZB RRX BUDT BUDFT GMR LFN UWN C24G SZ0 BUDGP BUDGF MA0 SXA OSA CRA CRAL ODA IMA NXA ME0 SXE OSE CRE CREL ODE IME ROIMG C24J COPY MODS LFN3 SZJ GROW DIMG TOM CEM FROM ADDS BUDJ BUDJF RR4"] Lemma em_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_S_c24 ()) "Psp1,$2.Pmq,P,(16.&40.)(2;.(16.&8.))Psl,(28.(16.&40.))Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)P,(40.VR,VHIA,Vh,VLB,VLF,Vm,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VdX,Vlo,Vslo,R11.R10.R?.)(41.$4.(42.$4.VR,VHIA,Vh,Vmo,)(43.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VRr,VPHI,VFR,Vlo,Vm,Vmo,)(44.(45.(27.&40.+:083<.)(27.&40.R12.)Vgp,Vtp,R?.R>.R=.Vsp,(27.&40.=)(27.&40.(:2.(:3.VdN,)))R<.R;.R:.R9.R8.R7.R6.(27.&40.(25.VdN,))(27.&40.(25.VdX,))(27.&40.(25.VdE,))(27.&40.(25.VdA,))(27.&40.-4.)(27.&40.=)(27.&40.(:.(1;.(:.R12.+60.)+3.)(1<.(1=.VR,))))(27.&40.(1<.(1=.VR,)))Vs10,Vs11,R5.R4.R3.R2.)VF,(27.&40.+:0844.)Vfc,(38.(16.&40.))R11.(46.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EB.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0.
    pose proof ME0 as [(_ & _ & _ & _ & NRE0 & _) _]. unfold MPI_MAX_LIMBS in NRE0.
    eapply (em_checks R HIA IMG h LB LF m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dX lo slo) with (dA := dA) (dE := dE) (dN := dN) (sl := sl);
      first [ eassumption | exact (aobj_crange _ _ _ _ _ _ (proj1 OX0))
            | destruct BUDL as [_ Q]; unfold grow_PHI, AVOL_CALL in Q; clear - Q; lia
            | destruct BUDFL as [_ Q]; unfold lset_FR, calls_FR, fr_charge in Q; clear - Q; lia
            | clear - SLO; lia | idtac ].
    - (* [comment removed for export] *)
      (intros m' sl' yt0 yt1 yt2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EB' dd_H; ddestruct dd_H as (SL8 & SL9 & SL10 & SL11); intros N1 E1).
      assert (WLB : 0 < WL <= 60000) by (unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); clear - NN4 N1; lia).
      eapply (em_alloc sp1 m' sl'); [exact EB'| exact N1| clear - NRE0; lia|].
      intros h1 m1 sl1 T yra zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 EBc1 HR1 MX1 TC1 T16 FRT S6a S7 SOTH.
      dpose EBc1 as (SP1 & _ & HH1 & _).
      assert (TR : 0 <= T < 2^64).
      { ddestruct FRT as (F0 & F1 & _). pose proof (alloc_ceiling_val R) as ACV. clear - F0 F1 ACV WLB. lia. }
      eapply (em_rr1 sp1 h1 ((T, WL * 4) :: LB) m1 sl1 T); [exact EBc1| eexists; eexists; exact HR1| exact S6a| exact S7| exact TR|].
      intros m2 slA slB j4 wt0 wt1 wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 EBs2 LA LBl LJ S5 S6 S7A SA MU2 WM2.
      assert (TA1 : u32arr asegs m1 T (repeat (Z_to_bv 64 0) (Z.to_nat WL))).
      { eapply u32arr_of_cells; [exact TC1|]. rewrite u32s_repeat0. f_equal. clear - WLB. lia. }
      assert (TL1 : Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat WL))) = WL) by (rewrite repeat_length; clear - WLB; lia).
      destruct (rr1_carry sp1 h1 _ m1 m2 T _ SP1 HR1 HH1 (or_introl eq_refl) TL1 ltac:(clear - WLB; lia) MU2 WM2 MX1 TA1) as (MX2 & TA2).
      assert (SAk : forall k w, (k < 20)%nat -> k <> 5%nat -> k <> 6%nat -> k <> 7%nat -> nth_error sl' k = Some w -> nth_error slA k = Some w).
      { intros k w K20 K5 K6 K7 Hk. rewrite (SA k K5 K6 K20). rewrite (SOTH k K6 K7). exact Hk. }
      eapply (em_rr2 sp1 h1 m2 slA slB j4 T _); [exact EBs2| exact HR1| exact LJ| exact LA| exact LBl| exact S6| exact S7A
        | exact MX2| exact TA2| exact TL1| exact WLB| exact FRT| exact T16|].
      intros h3 LB3 m3 dR3 y0 y1 y2 ya1' ya2' ya3' ya4' ya5' ya6' ya7' y3 y4 y5 y6 EJ3 HR3 NR3.
      eapply (em_journey sp1 T h3 LB3 m3 dR3 slA slB _); [exact EJ3| exact HR3| | exact N1| exact E1| exact NR3].
      unfold JSLOTS. split; [exact S5|]. split; [exact S6|]. split; [exact S7A|].
      split; [apply (SAk 8%nat); [clear; lia| discriminate| discriminate| discriminate| exact SL8]|].
      split; [apply (SAk 9%nat); [clear; lia| discriminate| discriminate| discriminate| exact SL9]|].
      split; [apply (SAk 10%nat); [clear; lia| discriminate| discriminate| discriminate| exact SL10]|].
      apply (SAk 11%nat); [clear; lia| discriminate| discriminate| discriminate| exact SL11].
    - (* [comment removed for export] *)
      intros m' sl' yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EB' _ _ _.
      eapply (em_lset sp1 m' sl'). exact EB'.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WES.
