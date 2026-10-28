(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_free P_ecp_point_free P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_ecp_grp_id_list P_ecp_mul_mod P_pk_ecparams_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_defs A_pk_defs A_mpi_free A_mpi_lset A_mpi_bitlen A_mpi_cmp_mpi A_asn1_get_tag_stmt A_asn1_get_int_loops A_asn1_get_mpi A_oid A_oid_ec_grp A_ecp_group_init A_ecp_group_free A_ecp_point_free A_ecp_grp_id_list A_pk_ecparams_aux A_free_seq A_pk_ecc_set_group A_pk_ecc_set_pubkey A_ecp_grp_facts A_pk_tmp A_pk_ecparams_stmt A_pk_ecparams_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_pk_ecparams_B () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_grp_id_list.ecp_ids_state"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.lb_ext"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "Corelib.Init.Datatypes.app"; "WalkEP.Call.wx_fresh"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "WalkEP.Call.EB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_d"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_Q"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_A.EP_SH0"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_FR"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.P.P_pk_ecparams_A.ecparams_result"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_grp"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.grp_factsA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_facts.ECP_MAX_N"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_use_ecparams_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_FR"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Nat.add"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell_at"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.lb_free_mpds"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_point_free.A_ECP_POINT_FREE"; "WalkEP.Call.EP_SH_G"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L38557618280.2L43279177847.2L50762911644.200000600900?S1z2HzS1zS1z2Hz". (* [comment removed for export] *)
Lemma sx32_small_ep : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Z.sub].
  rewrite Z.mod_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section WalkEP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variables (IDONE IDS : Z).
  Hypothesis IDOK : ids_okA R IDONE IDS.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PKA PAR lo d : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 640 - arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis HH0 : HM asegs R HIA h LB LF m.
  Hypothesis MI0 : mem_inv asegs m.
  (* [comment removed for export] *)
  Variables (FB sp1 : Z).
  Hypothesis SP1 : bv_unsigned sp - 272 <= sp1 <= bv_unsigned sp - 256.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 1024.

  Local Notation LF' := ((FB, 1024) :: LF).
  Local Notation SHB := (Z.shiftr FB 3 + al_sb AL).
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation W0 := [(IDONE, IDONE + 1); (IDS, IDS + 56)].

  Ltac rt_facts :=
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Definition EB (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (v f : Z) (SH SL : list cell) (CH : list (Z * list cell)) (T : list blk) (WE : list ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "(0.(1.$2.VR,VHIA,O:.O9.(3.(4.$5.$5.)(6.$5.$5.VFB,+400.)VLF,)O8.)(0.(0.(7.$5.(8.$2.VR,VHIA,O:.)(8.$2.VR,VHIA,Vh,))(0.(7.$5.(9.$2.VR,VHIA,O:.)(9.$2.VR,VHIA,Vh,))(7.$5.(:.$2.VR,VHIA,O:.)(:.$2.VR,VHIA,Vh,))))(0.Px,$5.P,(;.$2.VR,VHIA,Vh,R1.)(;.$2.VR,VHIA,O:.R2.)(0.(0.(<.(=.$2.VR,VHIA,O:.)(>.(=.$2.VR,VHIA,Vh,)O7.))(<.(?.$2.VR,VHIA,O:.)(>.(?.$2.VR,VHIA,Vh,)O6.)))(0.(10.(11.&40.)Lw0,(11.&40.)(10.(11.&40.)Lw1,(11.&40.)(10.(11.&40.)Lw2,(11.&40.)(12.$2.O8.VFB,(3.$13.(14.R3.)(3.$13.(14.R2.)(3.$13.(14.R1.)(15.$13.))))))))(0.(0.(12.$2.O8.(>.(16.VFB,+3.)(17.(18.VR,)))O5.)(7.$19.(1:.O5.)#50.))(0.(12.$2.O8.(>.(>.(16.VFB,+3.)(17.(18.VR,)))+50.)(3.$13.(1;.#30.(1<.(11.&8.)(1=.&8.=)#30.))(15.$13.)))(0.(12.$2.O8.(>.(1>.&40.Vsp,)-68.)(3.$13.(14.Vs11,)(3.$13.(14.Vs10,)(3.$13.(14.Vs9,)(3.$13.(14.Vs8,)(3.$13.(14.Vs7,)(3.$13.(14.Vs6,)(3.$13.(14.Vs5,)(3.$13.(14.Vs4,)(3.$13.(14.Vs3,)(3.$13.(14.Vs2,)(3.$13.(14.Vs1,)(3.$13.(14.Vs0,)(3.$13.(14.Vra,)(15.$13.)))))))))))))))(0.(0.(12.$2.O8.(>.Vsp1,+8.)O4.)(7.$19.(1:.O4.)#90.))(0.(1?.$2.O8.Vsp1,(>.Vsp1,+8.))(0.(1?.$2.O8.(>.Vsp1,+98.)(>.(1>.&40.Vsp,)-68.))(0.(1?.$2.O8.Vlo,Vsp1,)(0.(20.$2.O8.)(0.(21.$2.VR,VHIA,O:.VLB,VLF,(1>.&40.Vsp,)(22.VR,)O1.Vm,O8.)(0.(23.$2.VIDONE,VIDS,O8.)(0.(24.(4.$5.(25.$13.))Lac,(4.$5.(25.$13.))(0.(12.$2.O8.(26.$5.(25.$13.)R1.)(27.$5.(25.$13.)R1.))(0.(<.(>.VFB,+20.)(26.$5.(25.$13.)R1.))(<.(>.(26.$5.(25.$13.)R1.)(28.(1:.(27.$5.(25.$13.)R1.))))(>.VFB,+3?8.))))O3.)(0.(29.VLB,O2.O9.)Pb,$2:.P,(2;.$2:.R1.O2.)(2<.VR,VLB,VLF,(26.$5.$5.R2.)(27.$5.$5.R2.)))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition wx_fresh (w : ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "(2=.(0.(<.VFB,(26.$5.$5.O1.))(<.(27.$5.$5.O1.)(>.VFB,+400.)))(10.$5.LN,$5.(10.$5.Lk,$5.(0.(2<.VR,VLB,VLF,R2.R1.)(0.(<.R2.(26.$5.$5.O1.))(<.(27.$5.$5.O1.)(>.R2.R1.)))))))")
(* [comment removed for export] *).

  #[using="FRSH"] Lemma presA_drop_wx : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "PLBx,(25.$2:.)PSPx,$5.PTOPx,$5.PWX,(25.$2>.)PW,(25.$2>.)Pma,P,(11.&40.)(2?.(11.&8.))Pmb,P,(11.&40.)(2?.(11.&8.))P,(30.$2.VR,R7.VLF,R6.(22.VR,)R5.(31.$2>.R4.R3.)R2.R1.)P,(24.$2>.$32.R5.)P,PN,$5.Pk,$5.P,(2<.VR,VLB,VLF,R2.R1.)(2<.VR,R<.VLF,R3.R2.)P,(<.(33.(34.VR,))R9.)(30.$2.VR,R;.VLF,R:.(22.VR,)R9.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros LBx SPx TOPx WX. induction WX as [|[a b] WX IH]; intros W ma mb HP HW FRX HS; [exact HP|].
    inversion HW as [|? ? Hw HWr]; subst. cbn [app] in HP. apply IH; [| exact HWr| exact FRX| exact HS].
    destruct Hw as [[H1 H2]|(N & k & FN & H1 & H2)]; cbn [fst snd] in *.
    - eapply (presA_drop_fresh_gen R _ _ _ _ _ _ FB 1024); [exact HP| apply FRX; exact FRSH| exact H1| exact H2| exact HS].
    - eapply (presA_drop_fresh_gen R _ _ _ _ _ _ N k); [exact HP| apply FRX; exact FN| exact H1| exact H2| exact HS].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L37838938635.6 L39188636933.0 L43782036732.2 L50026752442.16L6188244917.6  L66151427842.16L9356559676.12 00000D00E00M00f01;01U02DS1R2lo3LOS2FB3ALO2F1SS2sp3SPRS2FB2r02F81q1r1H2H02q02H4S1R2sp2lo3SLO3sp13SP1S2FB2r03F641q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NER3SPR". (* [comment removed for export] *)
  #[using="HIA IMG NEEDR h LB LF LOS SLO SP1 F64 FRSH"] Lemma eb_frame_facts : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "(0.(35.=VFB,)(0.(<.(>.VFB,+400.)(33.(34.VR,)))(0.(2=.(<.(>.VFB,+400.)(36.(34.VR,)))(<.(37.(34.VR,))VFB,))(0.(7.$5.(38.VFB,+8.)=)(0.(<.(>.VFB,+400.)Vlo,)(0.(<.(33.(34.VR,))(22.VR,))(0.(0.(<.=Vsp1,)(35.Vsp1,(39.+2.+40.)))(0.(<.Vlo,(3:.(3:.Vsp1,+170.)(3;.VR,)))(0.(35.(1>.&40.Vsp,)(39.+2.+40.))(0.(<.(3<.VR,)(3;.VR,))(7.$5.(16.(>.VFB,+280.)+3.)(>.(16.VFB,+3.)+50.))))))))))))")
(* [comment removed for export] *).
  Proof.
    rt_facts. ddestruct FRSH as (F0 & F1 & F2 & _).
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact F8|]. split; [clear - F1 ALO LOS; lia|]. split; [exact ALO|].
    split; [clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia|]. split; [clear - SP1 SLO; lia|]. split; [clear - SPR; lia|]. split; [exact NER|].
    rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. clear - F8. Z.div_mod_to_equations. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L26892418956.1L48132321165.8L62018535662.1L65184156961.300000400S00V00`S2spS1R5NEEDR2sp2lo3LOS3SLO3ALO3NERS1RS1R3HIA2hk". (* [comment removed for export] *)
  #[using="IMG NEEDR h lo LOS SLO sp1 SP1 F64 FRSH"] Lemma eb_pres_step : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBp,(25.$2:.)PSPx,$5.PWXf,(25.$2>.)PWXe,(25.$2>.)PWE,(25.$2>.)PWE',(25.$2>.)Pma,P,(11.&40.)(2?.(11.&8.))Pmb,P,(11.&40.)(2?.(11.&8.))P,(21.$2.VR,VHIA,R9.VLB,VLF,(1>.&40.Vsp,)(22.VR,)R4.Vm,R2.)P,(30.$2.VR,R9.(3.(4.$5.$5.)(6.$5.$5.VFB,+400.)VLF,)R8.(22.VR,)(9.$2.VR,VHIA,R:.)(31.$2>.R7.R6.)R3.R2.)P,Pb,$2:.P,(2;.$2:.R1.VLB,)(2;.$2:.R2.R<.)P,(<.R:.(1>.&40.Vsp,))P,(24.$2>.$32.R:.)P,Px,$5.P,(3>.R9.R1.)(3>.R<.R2.)P,Px,$5.P,(3>.R:.R1.)(3>.R<.R2.)(21.$2.VR,VHIA,R10.VLB,VLF,(1>.&40.Vsp,)(22.VR,)R:.Vm,R8.)")
(* [comment removed for export] *).
  Proof.
    (intros hk LBp SPx WXf WXe WE WE' ma mb dd_H; ddestruct dd_H as (P & C1 & C2 & C3); intros HP SUB HS HW HE1 HE2).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & _).
    split; [| split; [exact C1| split; [exact C2| exact C3]]].
    eapply presA_trans.
    - eapply presA_weaken; [exact P| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| exact HE2].
    - eapply (presA_drop_wx LB (bv_unsigned sp) _ WXf WE'); [| exact HW| intros N k H; exact H| clear - ALO LOS SLO NEEDR NER; lia].
      eapply presA_weaken; [exact HP| exact SUB| intros b Hb; right; exact Hb| exact HS| clear; lia| clear; lia|].
      intros x Hx. apply outside_app in Hx. apply outside_app. split; [exact (proj1 Hx)| exact (HE1 x (proj2 Hx))].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L37508970891.62L37508970891.6500000W01BS1R2sp2FB3sp11u1v1a1n2A12A22F02F22W12W2S1R2sp2FB3sp11u1v1a1n2A12A22F01N1k2FD2W12W2". (* [comment removed for export] *)
  #[using="HIA IMG NEEDR h sp lo LOS SLO sp1 SP1 F64 FRSH"] Lemma ids_fresh_dj : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "PWX,(25.$2>.)Pa,$5.Pn,$5.P,(24.$2>.$32.R3.)P,(0.(<.(36.(34.VR,))R3.)(<.(>.R3.R2.)(37.(34.VR,))))(3?.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros WX a n HW [A1 A2]. dpose eb_frame_facts as (F0 & F1 & F2 & _).
    induction WX as [|[u v] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? Hw HWr]; subst.
    split; [| exact (IH HWr)]. destruct Hw as [[W1 W2]|(N & k & (_ & _ & FD & _) & W1 & W2)]; cbn [fst snd] in *; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L2793096253.3 L52792927696.8L6345413065.3 00000:00U00aS3IDS1a2HaS1R5IDONE3IDS2I12I22I31a2HaS5IDONE1a2Ha". (* [comment removed for export] *)
  #[using="IDOK"] Lemma ids_presA_gen : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "PLBp,(25.$2:.)PLFx,(25.$2:.)PSPx,$5.PSSPx,$5.PTOPx,$5.PWX,(25.$2>.)Pma,P,(11.&40.)(2?.(11.&8.))Pmb,P,(11.&40.)(2?.(11.&8.))P,(23.$2.VIDONE,VIDS,R2.)P,(30.$2.VR,R9.R8.R7.R6.R5.R4.R3.R2.)P,(3?.R5.VIDONE,+1.)P,(3?.R6.VIDS,+38.)(23.$2.VIDONE,VIDS,R5.)")
(* [comment removed for export] *).
  Proof.
    (intros LBp LFx SPx SSPx TOPx WX ma mb dd_H; ddestruct dd_H as (b & bs & H1 & H2 & H3); intros HP D1 D2).
    ddestruct IDOK as (I1 & I2 & I3 & I4 & _).
    dexists b, bs. split; [| split; [| exact H3]].
    - eapply (presA_rw_cells asegs R); [exact HP| exact H1| | exact D1].
      intros a Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Ha. right; left. split; [clear - Ha I1 I2 I3; lia| apply I4; left; clear - Ha; lia].
    - eapply (presA_rw_cells asegs R); [exact HP| exact H2| | exact D2].
      intros a Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. right; left. split; [clear - Ha I1 I2 I3; lia| apply I4; right; clear - Ha; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L12241130255.2 L135196561.6   L13948747720.1 L1540877545.3  L16255647091.3 L18678294768.11L18678294768.16L18678294768.19L20728242168.9 L2184537823.10 L24128180555.1 L25018301805.6 L27797056548.10L3177134184.1  L33177279630.3 L37312170392.9 L52045659405.3 L53577728712.1 L54971811087.1 L565330731.1   L56813410348.10L56887394084.10L6203936179.1  L66151427842.16L67028776265.0 L68694423824.2 L6899380056.1  L8464343071.10 L9631767084.2  00000700M00R00^00g01801O01g02C02k02o03E03f03j04404P04\04a04e04i05405U05Z06306406:06>06_06fS2FB2F0S1R5IDONE3IDS2I12I22I3S3sp1S2sp3sp13SP1S2FB1c2HcS1R1u1w1a1n2A12HwS1R2FB1u1w2F11a1n2A12W2S1R1u1w1a1n2A11N1k2FC2W2S1R3HIA1h2hk1v2h22dv3HVk3HV2S1R5NEEDR2sp2lo3LOS3sp13SP13ALO4SLO13NERS2FBS1R5IDONE3IDS2I12I22I3S1R5NEEDR2lo3LOS3sp13ALO4SLO13NERS2FBS2FB2ac2B2S1R3HIA1h2hk1f2h22df3HFk3HF2S2sp3sp13SP1S3sp1S2FBS2FBS2FB1u1w2HwS1R5NEEDR2lo3LOS3sp13ALO4SLO13NERS3sp1S2FB2r02F81q1r1H2H02q02H4SS1R2FBS2FBS1R5NEEDR2lo3LOS3sp13ALO4SLO13NERS2FB2F0". (* [comment removed for export] *)
  #[using="IMG NEEDR IDOK LOS SLO SP1 F64 FRSH"] Lemma eb_step : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))Pv,$5.Pf,$5.PSH,(25.$13.)PSL,(25.$13.)PCH,(25.(4.$5.(25.$13.)))PT,(25.$2:.)PWE,(25.$2>.)Ph2,(3=.$2.VR,VHIA,)PLB2,(25.$2:.)Pm2,P,(11.&40.)(2?.(11.&8.))Pdv,$5.Pdf,$5.PT2,(25.$2:.)PLBp,(25.$2:.)PWXf,(25.$2>.)PWXe,(25.$2>.)PWE',(25.$2>.)P,(40.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)P,(1.$2.VR,VHIA,R;.R:.(3.(4.$5.$5.)(6.$5.$5.VFB,+400.)VLF,)R9.)P,(20.$2.R:.)P,(1?.$2.R;.Vlo,Vsp1,)P,(30.$2.VR,R8.(3.(4.$5.$5.)(6.$5.$5.VFB,+400.)VLF,)Vsp1,(22.VR,)(9.$2.VR,VHIA,R18.)(31.$2>.R7.R6.)R16.R<.)P,(7.$5.(8.$2.VR,VHIA,R?.)(8.$2.VR,VHIA,R19.))P,(7.$5.(9.$2.VR,VHIA,R10.)(9.$2.VR,VHIA,R1:.))P,(7.$5.(:.$2.VR,VHIA,R11.)(:.$2.VR,VHIA,R1;.))P,Px,$5.P,(;.$2.VR,VHIA,R1=.R1.)(;.$2.VR,VHIA,R14.R2.)P,(<.(=.$2.VR,VHIA,R13.)(>.(=.$2.VR,VHIA,R1=.)R10.))P,(<.(?.$2.VR,VHIA,R14.)(>.(?.$2.VR,VHIA,R1>.)R10.))P,Pb,$2:.P,(2;.$2:.R1.VLB,)(2;.$2:.R2.R11.)P,(24.$2>.$32.R?.)P,Px,$5.P,(3>.R?.R1.)(3>.R11.R2.)P,Px,$5.P,(3>.R10.R1.)(3>.R1;.R2.)P,(24.(4.$5.$5.)Lw,(4.$5.$5.)(<.(27.$5.$5.R1.)(33.(34.VR,)))R11.)P,(3?.R12.VIDONE,+1.)P,(3?.R13.VIDS,+38.)P,(24.(4.$5.$5.)Lw,(4.$5.$5.)(2=.(<.(27.$5.$5.R1.)VFB,)(<.(>.VFB,+18.)(26.$5.$5.R1.)))(31.$2>.R15.R14.))P,(24.(4.$5.(25.$13.))Lac,(4.$5.(25.$13.))(3?.(31.$2>.R17.R16.)(26.$5.(25.$13.)R1.)(28.(1:.(27.$5.(25.$13.)R1.))))R20.)P,(29.VLB,R19.R1=.)P,Pb,$2:.P,(2;.$2:.R1.R1;.)(2<.VR,VLB,VLF,(26.$5.$5.R2.)(27.$5.$5.R2.))(40.R20.R1?.R1>.(>.R27.R1=.)(>.R26.R1<.)R25.R24.R23.R1;.R17.)")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T WE h2 LB2 m2 dv df T2 LBp WXf WXe WE' EBk HH2 MI2 ST2 HP ET ES EF HCS2 HV2 HF2 SUB HWX HE1 HE2 HWC DI1 DI2 HWH HCD EXT2 FR2.
    set (WX := WXf ++ WXe) in *.
    ddestruct EBk as (HHk & (ETk & ESk & EFk) & HCSk & (HVk & HFk) & (w0 & w1 & w2 & FHD) & (FSH & NSH) & FSHR & SAVE & (SLOTS & NSL) & STlo & SThi & STb & MIk & PRES & IDSk & CHk & EXTk & FRk).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    assert (CFBk : crange (hcs asegs R HIA hk) FB 1024) by (exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))).
    assert (CSHD : forall c, FB <= c < FB + 1024 -> cshd R LBp LF' (arl_stklo R) (hstkhi asegs R HIA hk) c).
    { intros c Hc. right; right; left. exists (FB, 1024). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJS : forall a n, alloc_ceiling <= a -> disjoint_from WX a n).
    { intros a n A1. unfold WX. apply PkTmp.disjoint_from_app.
      - clear - HWX F1 A1. induction WXf as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWX as [|? ? Hw HWr]; subst.
        split; [| exact (IH HWr)]. destruct Hw as [[W1 W2]|(N & k & (_ & FC & _) & W1 & W2)]; cbn [fst snd] in *; lia.
      - clear - HWC A1. induction WXe as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWC as [|? ? Hw HWr]; subst. cbn [fst snd] in Hw.
        split; [lia| exact (IH HWr)]. }
    unfold EB.
    split; [exact HH2|].
    split; [split; [rewrite ET; exact ETk| split; [rewrite ES; exact ESk| rewrite EF; exact EFk]]|].
    split; [intros x Hx; apply HCS2, HCSk, Hx|].
    split; [split; [clear - HVk HV2; lia| clear - HFk HF2; lia]|].
    split. { dexists w0, w1, w2. eapply (presA_rw_cells asegs R); [exact HP| exact FHD| |].
             - eapply client_range_block; [apply in_app_iff; right; left; reflexivity| clear; lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Z.min_l by (clear; lia); clear; lia].
             - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - HWH. induction WX as [|[u w] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWH as [|? ? Hw HWr]; subst. cbn [fst snd] in Hw. split; [lia| exact (IH HWr)]. }
    split. { split; [| exact NSH]. eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hk)); [exact CSOKk| | exact F8| clear - F0; lia| exact HP| exact FSH|].
             - rewrite NSH. eapply crange_sub; [exact CFBk| clear; lia| clear; lia].
             - rewrite NSH. intros c Hc. apply CSHD. clear - Hc. lia. }
    split. { replace (SHB + 80) with (Z.shiftr (FB + 640) 3 + al_sb AL) in * by (rewrite SH640; clear; lia).
             eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hk)); [exact CSOKk| | clear - F8; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP| exact FSHR|].
             - cbn [cells_size csize Nat.add]. eapply crange_sub; [exact CFBk| clear; lia| clear; lia].
             - cbn [cells_size csize Nat.add]. intros c Hc. apply CSHD. clear - Hc. lia. }
    split. { eapply (presA_rw_cells asegs R); [exact HP| exact SAVE| apply client_range_stack; clear - SP1; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split. { split; [| exact NSL]. eapply (presA_rw_cells asegs R); [exact HP| exact SLOTS| apply client_range_stack; clear; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split. { eapply (presA_stk asegs R); [exact HP| exact STlo| clear; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split. { eapply (presA_stk asegs R); [exact HP| exact SThi| clear; lia| apply DJS; clear - ALO LOS SLO1 SP1 NER NEEDR; lia]. }
    split; [exact ST2|]. split; [exact MI2|].
    split. { eapply (presW_hmono R HIA hk h2); [| exact HCS2| exact ES].
             eapply eb_pres_step; [exact PRES| exact HP| exact SUB| clear - SP1; lia| exact HWX| exact HE1| exact HE2]. }
    split. { ddestruct IDOK as (I1 & I2 & I3 & _).
             eapply ids_presA_gen; [exact IDSk| exact HP| |]; unfold WX; apply PkTmp.disjoint_from_app; try assumption.
             - apply (ids_fresh_dj WXf IDONE 1 HWX); clear - I1 I2 I3; lia.
             - apply (ids_fresh_dj WXf IDS 56 HWX); clear - I1 I2 I3; lia. }
    split. { rewrite Forall_forall in CHk, HCD |- *. intros ac Hac. ddestruct (CHk ac Hac) as (Hc & B1 & B2). split; [| split; [exact B1| exact B2]].
             eapply (presA_rw_cells asegs R); [exact HP| exact Hc| | exact (HCD ac Hac)].
             eapply client_range_block; [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| exact B1| clear - B2; lia]. }
    split; [exact EXT2| exact FR2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15978554537.9L67535073559.900000K00]S1R5IDONE3IDS2FB1n2SB2I22I3S1R3IDS2FB1n2SB2I3". (* [comment removed for export] *)
  #[using="IDOK"] Lemma ids_munch_sh : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Pma,P,(11.&40.)(2?.(11.&8.))Pmb,P,(11.&40.)(2?.(11.&8.))Pn,$5.P,(23.$2.VIDONE,VIDS,R3.)P,(41.(3.(4.$5.$5.)(6.$5.$5.(>.(16.VFB,+3.)(17.(18.VR,)))(>.(>.(16.VFB,+3.)(17.(18.VR,)))R2.))(15.(4.$5.$5.)))R4.R3.)P,(42.$2.R5.R4.)P,(<.(37.(34.VR,))(>.(16.VFB,+3.)(17.(18.VR,))))(23.$2.VIDONE,VIDS,R6.)")
(* [comment removed for export] *).
  Proof.
    (intros ma mb n dd_H; ddestruct dd_H as (b & bs & H1 & H2 & H3); intros MU WM SB). ddestruct IDOK as (I1 & I2 & I3 & _).
    dexists b, bs. split; [| split; [| exact H3]].
    - eapply (rw_cells_transport asegs); [exact H1| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. clear - SB I1 I2 I3. lia.
    - eapply (rw_cells_transport asegs); [exact H2| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SB I1 I2 I3. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L50195633356.700000DS1R2FB1n2AP2ac2B12B2". (* [comment removed for export] *)
  #[using="Type"] Lemma ch_munch_sh : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Pma,P,(11.&40.)(2?.(11.&8.))Pmb,P,(11.&40.)(2?.(11.&8.))Pn,$5.PCH,(25.(4.$5.(25.$13.)))P,(24.(4.$5.(25.$13.))Lac,(4.$5.(25.$13.))(0.(12.$2.R5.(26.$5.(25.$13.)R1.)(27.$5.(25.$13.)R1.))(0.(<.(>.VFB,+20.)(26.$5.(25.$13.)R1.))(<.(>.(26.$5.(25.$13.)R1.)(28.(1:.(27.$5.(25.$13.)R1.))))(>.VFB,+3?8.))))R1.)P,(41.(3.(4.$5.$5.)(6.$5.$5.(>.(16.VFB,+3.)(17.(18.VR,)))(>.(>.(16.VFB,+3.)(17.(18.VR,)))R3.))(15.(4.$5.$5.)))R5.R4.)P,(42.$2.R6.R5.)P,(2=.(<.(>.(>.(16.VFB,+3.)(17.(18.VR,)))R5.)VFB,)(<.(>.VFB,+400.)(>.(16.VFB,+3.)(17.(18.VR,)))))(24.(4.$5.(25.$13.))Lac,(4.$5.(25.$13.))(0.(12.$2.R8.(26.$5.(25.$13.)R1.)(27.$5.(25.$13.)R1.))(0.(<.(>.VFB,+20.)(26.$5.(25.$13.)R1.))(<.(>.(26.$5.(25.$13.)R1.)(28.(1:.(27.$5.(25.$13.)R1.))))(>.VFB,+3?8.))))R5.)")
(* [comment removed for export] *).
  Proof.
    intros ma mb n CH HC MU WM AP. rewrite Forall_forall in HC |- *. intros ac Hac. ddestruct (HC ac Hac) as (Hc & B1 & B2).
    split; [| split; [exact B1| exact B2]].
    eapply (rw_cells_transport asegs); [exact Hc| exact MU| exact WM|]. cbn [disjoint_from]. split; [clear - AP B1 B2; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis LFB : (length LF + 1 < 512)%nat.
  Hypothesis SF5 : arl_setf5 R = 0x6b330.
  Hypothesis NSH : arl_need_setsh R <= arl_need_rt R.
  Variables (info C LEN : Z) (idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ : word).
  Local Notation KPI := (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Hypothesis HPKA0 : rw_cells asegs m PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)].
  Hypothesis CRP : client_range L (LB ++ fdata LF) lo PKA 16.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis DPI : PKA + 16 <= IDONE \/ IDS + 56 <= PKA.
  Hypothesis DPC : PKA + 16 <= C \/ C + 256 <= PKA.
  Hypothesis KP0 : ecp_keypair_at asegs A_MT m LB C KPI.
  Hypothesis INC : In (C, 256) LB.

  Local Notation WF := [(C, C + 192); (IDONE, IDONE + 1); (IDS, IDS + 56)].
  Local Notation POST := (pk_use_ecparams_postA asegs R HIA A_MT A_CA A_ONE IDONE IDS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF PKA info C KPI LEN lo d m mo0).

  (* [comment removed for export] *)
  #[using="HIA h LB LF m HH0 INC"] Lemma kp_block_facts : 0 < C /\ C + 256 <= alloc_ceiling /\ (C + 256 <= hl_img_lo L \/ hl_img_hi L <= C).
  Proof.
    destruct (hm_apart asegs R HIA h LB LF m HH0) as [HBR _]. rewrite Forall_forall in HBR.
    destruct (HBR _ ltac:(apply in_app_iff; left; exact INC)) as (C0 & _ & CAC & CIM). cbn [fst snd] in *. auto.
  Qed.

  (* [comment removed for export] *)
  #[using="R DIMG IDONE IDS sp PKA lo sp1 SP1 C DSP DPI DPC"] Lemma ecp_group_at_relist : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Psegs,(25.$43.)PMT,(25.$44.)Pmm,P,(11.&40.)(2?.(11.&8.))PLBa,(25.$2:.)PLBb,(25.(4.$5.$5.))PG,$5.Pg,$45.P,(46.R7.R6.R5.R4.R2.R1.)P,Pe,$47.P,(2;.$47.R1.(48.R3.))P,(7.$49.(4:.R2.)$4;.)(2;.(4.$5.$5.)(6.$5.$5.(4<.R3.)(4=.+4.(4>.R3.)))R7.)(46.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros segs MT mm LBa LBb G g HG KEEP.
    ddestruct HG as (HD & AL8 & POS & EP & EA & EB' & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & REST).
    assert (RB : forall e, In e (grp_mpds g) -> mpdr_at segs mm LBa e -> mpdr_at segs mm LBb e).
    { intros e He Me. eapply mpdr_at_LB_one'; [exact Me| intros O; exact (KEEP e He O)]. }
    unfold grp_mpds, pt_mpds in RB. cbn [app In] in RB.
    refine (conj HD (conj AL8 (conj POS (conj EP (conj EA (conj EB' (conj EN _))))))).
    split; [apply RB; [clear; tauto| exact MP]|]. split; [apply RB; [clear; tauto| exact MA]|]. split; [apply RB; [clear; tauto| exact MB]|].
    split; [refine (conj EX (conj EY (conj EZ _))); split; [apply RB; [clear; tauto| exact MX]| split; [apply RB; [clear; tauto| exact MY]| apply RB; [clear; tauto| exact MZ]]]|].
    split; [apply RB; [clear; tauto| exact MN]| exact REST].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L11036440459.1 L21926499533.1 L24502405210.1 L24711474703.1 L37666135473.11L54262396250.1 L54526232525.1 L63918187566.1 L6450286553.1  L64515521675.1 L7237223214.1  00000300600900<00P00S00V00Y00\00_00bS1CS1CS1CS1CS1C1u1v2D11A1n2H12H2S1CS1CS1CS1CS1CS1C". (* [comment removed for export] *)
  #[using="DIMG IDONE IDS sp PKA lo sp1 SP1 DSP DPI DPC"] Lemma kp_presA : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "PLBx,(25.$2:.)PSPx,$5.PSSPx,$5.PTOPx,$5.PWX,(25.$2>.)Pma,P,(11.&40.)(2?.(11.&8.))Pmb,P,(11.&40.)(2?.(11.&8.))PLBa,(25.$2:.)PLBb,(25.(4.$5.$5.))Pg',$45.P,(4?.$2.$50.R5.R3.VC,(51.R1.(52.(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))(54.(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))))P,(30.$2.VR,R;.VLF,R:.R9.R8.R7.R6.R5.)P,(20.$2.R7.)P,(20.$2.R7.)P,(2;.(4.$5.$5.)(6.$5.$5.VC,+100.)R>.)P,(3?.R;.VC,+100.)P,Pe,$47.P,(2;.$47.R1.(48.R8.))P,(7.$49.(4:.R2.)$4;.)(0.(2;.(4.$5.$5.)(6.$5.$5.(4<.R3.)(4=.+4.(4>.R3.)))R;.)(0.(2;.(4.$5.$5.)(6.$5.$5.(4<.R3.)(4=.+4.(4>.R3.)))R13.)(0.(<.+1.(4>.R3.))(3?.R?.(4<.R3.)(4=.+4.(4>.R3.))))))(4?.$2.$50.R;.R9.VC,(51.R8.(52.(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))(54.(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))))")
(* [comment removed for export] *).
  Proof.
    (intros LBx SPx SSPx TOPx WX ma mb LBa LBb g' dd_H; ddestruct dd_H as (HG & ED & MD & FD & HQ & FQ); intros HP MIa MIb INX DJ HPB).
    cbn [kp_grp kp_d kp_Q kp_init] in *.
    assert (CRC : forall A n, C <= A -> A + n <= C + 256 -> client_range L (LBx ++ fdata LF) SPx A n).
    { intros A n Ho Hn. eapply client_range_block; [apply in_app_iff; left; exact INX| exact Ho| exact Hn]. }
    assert (DJC : forall A n, C <= A -> A + n <= C + 256 -> disjoint_from WX A n).
    { intros A n H1 H2. clear - DJ H1 H2. induction WX as [|[u v] W IH]; cbn [disjoint_from] in *; [exact I|]. destruct DJ as [D1 D2]. split; [lia| exact (IH D2)]. }
    split.
    { pose proof (ecp_group_at_relist asegs A_MT ma LBa (LBx ++ fdata LF) C g' HG
                    ltac:(intros e He O; apply in_app_iff; left; exact (proj1 (proj2 (HPB e He O))))) as G2.
      eapply (P_ecp_mul_mod.ecp_group_at_presx asegs L A_MT ma mb (LBx ++ fdata LF) LBb SPx WX C g'); [exact G2| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP)| exact MIa| exact MIb| apply CRC; clear; lia| apply DJC; clear; lia|].
      intros e He O. ddestruct (HPB e He O) as (I1 & _ & _ & D1). split; assumption. }
    split; [exact ED|]. split; [| split; [exact FD| split; [| exact FQ]]].
    - eapply (mpdr_init_presA R LBx LF _ _ _ _ ma mb LBa LBb); [exact MD| exact HP| apply CRC; clear; lia| apply DJC; clear; lia].
    - ddestruct HQ as (EX & EY & EZ & MX & MY & MZ). cbn [pt_init pt_X pt_Y pt_Z] in *.
      split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [eapply (mpdr_init_presA R LBx LF _ _ _ _ ma mb LBa LBb); [exact MX| exact HP| apply CRC; clear; lia| apply DJC; clear; lia]|].
      split; [eapply (mpdr_init_presA R LBx LF _ _ _ _ ma mb LBa LBb); [exact MY| exact HP| apply CRC; clear; lia| apply DJC; clear; lia]
             | eapply (mpdr_init_presA R LBx LF _ _ _ _ ma mb LBa LBb); [exact MZ| exact HP| apply CRC; clear; lia| apply DJC; clear; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis CFB : crange CS FB 1024.

  #[using="Type"] Lemma nodup_of_fst : forall (l : list blk), List.NoDup (map fst l) -> List.NoDup l.
  Proof. intros l. apply NoDup_map_inv. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L16505515210.3L19527361228.9L26892418956.1L28297679697.9L38720931794.8L40281191306.3L62018535662.1L62241145367.800000;00W00[01101J01S01V01nS2LB3LBk2CIS5IDONE3IDS3PKA1C3DPI3DPC2I2S2spS5IDONE3IDS3PKA3DPI2I2S1R3HIA1h3LEN2hk1v3HVk2VBS1R3HIA1hS1RS1R3HIA1h1d2hk1f3HFk3FB'". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP HH0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC INC CFB"] Lemma ep_exit : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))Pv,$5.Pf,$5.Pv1,(11.&40.)Pv2,(11.&40.)Pv3,(11.&40.)Pv4,(11.&40.)Pv5,(11.&40.)Pv6,(11.&40.)Pv7,(11.&40.)Pv8,(11.&40.)Pv9,(11.&40.)Pv10,(11.&40.)Pv11,(11.&40.)Pv12,(11.&40.)Pv13,(11.&40.)Pv14,(11.&40.)Pv15,(11.&40.)Pv16,(11.&40.)Pv17,(11.&40.)Pv18,(11.&40.)Pr,$5.Pg',$45.PNB,(25.$2:.)PWE,(25.$2>.)PCH,(25.(4.$5.(25.$13.)))Pxra,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pa0v,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Ps3v,(11.&40.)Ps5v,(11.&40.)Ps6v,(11.&40.)Ps7v,(11.&40.)Ps8v,(11.&40.)Ps11v,(11.&40.)P,(40.R32.R31.R30.R2?.R2>.$55.(3.$13.(14.R2=.)(3.$13.(14.R2<.)(3.$13.(14.R2;.)(3.$13.(14.R2:.)(3.$13.(14.R29.)(3.$13.(14.R28.)(3.$13.(14.R27.)(3.$13.(14.R26.)(3.$13.(14.R25.)(3.$13.(14.R24.)(3.$13.(14.R23.)(3.$13.(14.R22.)(3.$13.(14.R21.)(3.$13.(14.R20.)(3.$13.(14.R1?.)(3.$13.(14.R1>.)(3.$13.(14.R1=.)(3.$13.(14.R1<.)(15.$13.)))))))))))))))))))R17.R19.R18.)P,(2=.(7.(25.$2>.)R19.(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))(7.(25.$2>.)R19.(3.(4.$5.$5.)(6.$5.$5.VC,(>.VC,+<0.))(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))))P,(<.R31.(56.VLEN,))P,(<.R31.(57.Vd,))P,(0.(35.(58.(39.+2.+1?.))R1?.)(<.R1?.=))P,(4?.$2.$50.R35.R36.VC,(51.R1?.(52.(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))(54.(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))))P,(59.(48.R20.))P,(7.(25.$2:.)(5:.R21.)R20.)P,(5;.$5<.$5=.VC,(5>.(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))R23.R22.R21.)P,P,(7.$5.R24.=)(5?.R24.$60.)P,(7.$5.(61.R23.)=)(62.$2.(63.$2.VR,VHIA,R3=.Vmo0,)(64.$2.VR,VHIA,$50.$5<.$5=.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(65.(66.R21.(1=.&40.Vsp1,)Vgp,Vtp,R20.R1?.R1>.Vsp,(1=.&40.Vsp1,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(1=.&40.VFB,)R11.(1=.&40.(>.(16.VFB,+3.)(17.(18.VR,))))R10.R?.R>.R=.(1=.&40.VFB,)(1=.&40.R26.)R<.R15.R14.R13.R12.)VF,(1=.&40.+;1310.)Vfc,(67.(11.&40.))R3;.(68.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros EBk WEC VB FB' RR KPk APk GBk ERk GFk C24k.
    ddestruct EBk as (HHk & (ETk & ESk & EFk) & HCSk & (HVk & HFk) & (w0 & w1 & w2 & FHD) & (FSH & NSH') & FSHR & SAVE & (SLOTS & NSL) & STlo & SThi & STb & MIk & PRES & IDSk & CHk & EXTk & FRk).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    dpose kp_block_facts as (C0 & CAC & CIM).
    assert (SUBK : forall b, In b LB -> In b LBk) by (intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb]).
    pose proof (fresh_apart_relist_sg R HIA hk LB LBk LF mk FB 1024 FRSH HHk) as FRSHk.
    pose proof (hm_fresh_frame_apart asegs R HIA hk LBk LF mk FB 1024 HHk) as AP.
    pose proof (presW_init_at R HIA hk _ _ LBk LF mk (bv_unsigned sp) (arl_stklo R) [] hk HHk
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRES2.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { eapply (epi_walk R HIA IMG NS1 NEEDR h LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LOS SLO TOP LFB SF5 NSH)
        with (h3 := hk) (LBa := LB) (LBb := LBk) (m0 := m) (m2x := mk) (WA := WE) (WB := @nil ivl) (FB := FB) (sp1 := sp1);
        first [ exact HHk | exact HCSk | exact ETk | exact ESk | exact PRES | exact PRES2 | exact FRSH | exact FRSHk | exact CFB | exact AP | exact SUBK
              | exact SP1 | exact SP1M | exact F64 | exact FHD | exact FSH | exact FSHR | exact SAVE | exact SLOTS | exact STlo | exact SThi
              | exact STb | exact MIk | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold pk_use_ecparams_postA.
    deexists 14. dexists m9, mo9, h4, r, g', NB, LBk.
    pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES9) as HPF. rewrite ESk in HPF.
    pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES29) as HPF2.
    destruct EXTk as [EXT1 EXT2].
    split; [reflexivity|]. split; [exact RR|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split. { eapply presA_weaken; [exact HPF| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
             intros x Hx. destruct WEC as [-> | ->]; [cbn [outside] in Hx |- *; clear - Hx; tauto| exact Hx]. }
    split; [rewrite E4top; exact ETk|]. split; [rewrite E4stk; exact ESk|]. split; [rewrite E4flag; exact EFk|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSk x Hx)|].
    split; [rewrite E4vol; clear - HVk VB; lia|]. split; [rewrite E4fr; clear - HFk FB'; lia|].
    split; [exact HH4|].
    split; [exact EXT1|].
    split; [intros b Hb; split; [exact (EXT2 b Hb)| exact (FRk b Hb)]|].
    split. { pose proof (nodup_of_fst _ (HND _ _ _ _ HHk)) as NDk.
             pose proof (cnt24_incl LBk (NB ++ LB) NDk ltac:(intros b Hb; apply in_app_iff; exact (proj1 (EXT1 b) Hb))) as CI.
             rewrite cnt24_app, C24k in CI. clear - CI. lia. }
    split.
    { eapply (kp_presA LBk (bv_unsigned sp) _ _ [] mk m9 LBk LBk g'); [exact KPk| exact HPF2| exact MIk| exact MI9| apply SUBK; exact INC| cbn; exact I|].
      intros e He O. destruct KPk as (HGk & _). cbn [kp_grp] in HGk.
      pose proof (ecp_group_at_heap_in asegs A_MT mk LBk C g' e HGk He O) as IN.
      split; [exact IN|]. split; [exact IN|]. split; [| cbn; exact I].
      ddestruct HGk as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & _).
      assert (MDe : mpdr_at asegs mk LBk e) by (unfold grp_mpds, pt_mpds in He; cbn in He; destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption).
      ddestruct MDe as (_ & _ & _ & _ & _ & OW). rewrite O in OW. exact (proj1 OW). }
    split; [exact APk|]. split; [exact GBk|]. split; [exact ERk|]. split; [exact GFk|].
    split.
    { eapply (presA_rw_cells asegs R _ _ _ _ _ _ m m9 _ _ HPF); [exact HPKA0| eapply client_range_sep; [exact CRP| intros b Hb; exact Hb| exact DSP]|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. destruct WEC as [-> | ->]; cbn [disjoint_from]; clear - DPC DPI IDOK; ddestruct IDOK as (_ & I2 & _); lia. }
    eapply (ids_presA_gen LBk LF _ _ _ [] mk m9); [exact IDSk| exact HPF2| cbn; exact I| cbn; exact I].
    all: match goal with |- ?g => idtac "EXIT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis HSG : pk_ecc_set_group_stmtA asegs R HIA A_MT A_CA A_ONE A_EC_INFOS A_PK_ECC_SET_GROUP.
  Hypothesis EI : In info A_EC_INFOS.
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis NZP : 0 < PKA.
  Hypothesis OPKA0 : aobj asegs AL CS m PKA 16.
  Hypothesis BUD : havol asegs R HIA h + pk_ecparams_PHI LEN <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + pk_ecparams_FR d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_PK_USE_ECPARAMS <= C24MAX.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L28297679697.5 L39995675452.10L40100108667.10L50790761713.8 00000F00n01R01mS5IDONE3IDS3PKA3DPI2I2S1R5NEEDR2sp3PKA2lo3sp13SP13DSP4SLO13NERS1R5IDONE3IDS1C3CIM2I12I22I33DI13DI2S1R5NEEDR2sp2lo3LOS3SLO3NER". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG IDOK LOS SLO HH0 MI0 SP1 F64 FRSH HPKA0 CRP DSP DPI DPC KP0 INC OPKA0"] Lemma eb_entry_objs : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))Pv,$5.Pf,$5.PSH,(25.$13.)PSL,(25.$13.)PCH,(25.(4.$5.(25.$13.)))PT,(25.$2:.)P,(40.R9.R8.R7.R6.R5.R4.R3.R2.R1.(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))(0.(12.$2.R8.VPKA,(3.$13.(14.(1=.&40.Vinfo,))(3.$13.(14.(1=.&40.VC,))(15.$13.))))(0.(69.$2.(18.VR,)(;.$2.VR,VHIA,R:.)R8.VPKA,+10.)(0.(4?.$2.$50.R8.R9.VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))(0.(2;.(4.$5.$5.)(6.$5.$5.VC,+100.)R9.)(6:.(34.VR,)(31.$2:.R9.(6;.(3.(4.$5.$5.)(6.$5.$5.VFB,+400.)VLF,)))Vlo,VPKA,+10.)))))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk v f SH SL CH T EBk.
    ddestruct EBk as (HHk & (ETk & ESk & EFk) & HCSk & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIk & PRES & _ & _ & EXTk & _).
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & _).
    dpose kp_block_facts as (C0 & CAC & CIM). ddestruct IDOK as (I1 & I2 & I3 & I4 & _). destruct DIMG as [DI1 DI2].
    pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES) as HP.
    assert (SUBK : forall b, In b LB -> In b LBk) by (intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb]).
    assert (CRPs : client_range L (LB ++ fdata LF) (bv_unsigned sp) PKA 16) by (eapply client_range_sep; [exact CRP| intros b Hb; exact Hb| exact DSP]).
    split. { eapply (presA_rw_cells asegs R _ _ _ _ _ _ m mk _ _ HP); [exact HPKA0| exact CRPs|].
             cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from]. clear - DPI I2. lia. }
    split. { eapply aobj_cs_mono; [exact HCSk|].
             eapply (presA_aobj asegs R CS); [exact (hcs_ok asegs R HIA h)| exact HP| exact OPKA0| exact CRPs| clear - ALO LOS SLO NEEDR NER; lia| intros x Hx; rewrite ESk; eapply hcs_below_top; exact Hx]. }
    split. { eapply (kp_presA LB (bv_unsigned sp) _ _ W0 m mk LB LBk (kp_grp KPI)); [exact KP0| exact HP| exact MI0| exact MIk| exact INC| |].
             - cbn [disjoint_from]. clear - CIM I1 I2 I3 DI1 DI2. lia.
             - intros e He O. exfalso. rewrite (grp_init_noheap _ _ _ _ _ _ _ _ _ _ e He) in O. discriminate O. }
    split; [apply SUBK; exact INC|].
    eapply client_range_sep; [exact CRP| | clear - DSP SLO1 SP1 NER NEEDR; lia].
    intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac eb_open EBk :=
    destruct EBk as (HHk & (ETk & ESk & EFk) & HCSk & (HVk & HFk) & (w0 & w1 & w2 & FHD) & (FSH & NSH') & FSHR & SAVE & (SLOTS & NSL) & STlo & SThi & STb & MIk & PRES & IDSk & CHk & EXTk & FRk).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L11971861749.3  L18140531390.9  L18142890645.9  L19726054483.4  L19980016842.7  L24123163929.184L244387256.2    L29271889909.10 L30830368281.14 L34356152036.3  L34528482292.6  L36021046681.2  L49858401057.0  L52101672047.10 L52438557291.4  L53419693873.3  L61272165064.17 L61274436457.15 L66151427842.16 Q19635562150.188Q26763037879.18800000800U01201D01\03:03;03_03`03h04?04G04H04l05;05D05E05F05b07508HS2FB1C1KS1R3HIA1h3LEN3BUD2hk1v3HVk2VBS1R3HIA1h1d4BUDF2hk1f3HFk3FB'S2LB4C24H3LBk4C24kS1R3HIA1h2sp3TOP3sp13SP1S2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLSS1R5IDONE3IDS1C3CIM2I12I22I33DI13DI2SS2FB1C1KS2sp3PKA2lo3sp13SP13DSPS2LF3LFBSS1R5IDONE3IDS1C3CIM2I12I22I33DI13DI2S1R2lo3sp14SLO1S1R1C3CACSSS3sp12r04SP1M1q1r1H2H02q02H4S2LF2FB3LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSLS2LF2FB3LFB2v12v22v32v42v52v62v72v82v93v103v113v123v133v143v153v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H"] Lemma ep_setgrp : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))Pv,$5.Pf,$5.Pv1,(11.&40.)Pv2,(11.&40.)Pv3,(11.&40.)Pv4,(11.&40.)Pv5,(11.&40.)Pv6,(11.&40.)Pv7,(11.&40.)Pv8,(11.&40.)Pv9,(11.&40.)Pv10,(11.&40.)Pv11,(11.&40.)Pv12,(11.&40.)Pv13,(11.&40.)Pv14,(11.&40.)Pv15,(11.&40.)Pv16,(11.&40.)Pv17,(11.&40.)Pv18,(11.&40.)Pid,$5.Pgj',(11.&40.)Pxra,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pa0v,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Ps8v,(11.&40.)Ps5v,(11.&40.)Ps6v,(11.&40.)Ps10v,(11.&40.)Ps11v,(11.&40.)P,(40.R2>.R2=.R2<.R2;.R2:.$55.(3.$13.(14.R29.)(3.$13.(14.R28.)(3.$13.(14.R27.)(3.$13.(14.R26.)(3.$13.(14.R25.)(3.$13.(14.R24.)(3.$13.(14.R23.)(3.$13.(14.R22.)(3.$13.(14.R21.)(3.$13.(14.R20.)(3.$13.(14.R1?.)(3.$13.(14.R1>.)(3.$13.(14.R1=.)(3.$13.(14.R1<.)(3.$13.(14.R1;.)(3.$13.(14.R1:.)(3.$13.(14.R19.)(3.$13.(14.R18.)(15.$13.)))))))))))))))))))(3.(4.$5.(25.$13.))(6.$5.(25.$13.)(>.VFB,+270.)(3.$13.(6<.(1=.&40.R17.))(3.$13.(6<.R16.)(15.$13.))))(15.(4.$5.(25.$13.))))(15.$2:.)(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))P,(0.(<.=R18.)(35.R18.(39.+2.+1?.)))P,(<.(>.R2=.$6=.)(56.VLEN,))P,(<.(>.R2=.$6>.)(57.Vd,))(62.$2.(63.$2.VR,VHIA,R32.Vmo0,)(64.$2.VR,VHIA,$50.$5<.$5=.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(65.(66.R19.(1=.&40.Vsp1,)Vgp,Vtp,R18.R17.R16.Vsp,(1=.&40.Vsp1,)R15.R14.R13.R12.R11.R10.R?.R>.(1=.&40.VFB,)(1=.&40.VPKA,)(1=.&40.(>.(16.VFB,+3.)(17.(18.VR,))))R8.R7.(1=.&40.(>.VFB,+270.))R9.(1=.&40.VFB,)R6.R5.R=.R<.R;.R:.)VF,(1=.&40.+;1300.)Vfc,(67.(11.&40.))R30.(68.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros EBk IDB VB FB'.
    destruct (eb_entry_objs _ _ _ _ _ _ _ _ _ EBk) as (HPKAk & OPKAk & KPk & INCk & CRPk).
    pose proof EBk as EBk0.
    eb_open EBk.
    dpose (Forall_inv CHk) as (GID & _ & _). cbn [fst snd] in GID.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    dpose kp_block_facts as (C0 & CAC & CIM).
    pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    assert (CFBk : crange (hcs asegs R HIA hk) FB 1024) by (exact (hcs_fake asegs R HIA hk LBk _ mk FB 1024 HHk ltac:(left; reflexivity))).
    pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTOPk. rewrite ETk, ESk in HTOPk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    zstep. zstep. zstep.
    assert (SUBK : forall b, In b LB -> In b LBk) by (intros b Hb; eapply lb_ext_sub; [exact EXTk| exact Hb]).
    assert (C24k : cnt24 LBk <= cnt24 LB).
    { pose proof (nodup_of_fst _ (HND _ _ _ _ HHk)) as NDk. apply (cnt24_incl LBk LB NDk).
      intros b Hb. destruct (proj1 (proj1 EXTk b) Hb) as [[]|K]; exact K. }
    (* [comment removed for export] *)
    pose proof HSG as SG'. unfold pk_ecc_set_group_stmtA, A_PK_ECC_SET_GROUP in SG'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG' with (h := hk) (LB := LBk) (LF := LF') (PKA := PKA) (info := info) (C := C) (id := id) (lo := lo)
                      (idpad := idpad) (pP := pP) (pA := pA) (pB := pB) (pX := pX) (pY := pY) (pZ := pZ) (pN := pN) (hpad := hpad) (pd := qd) (qX := qX) (qY := qY) (qZ := qZ);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HK1 | exact HHk | exact HPKAk | exact ALP | exact NZP | exact EI | exact OPKAk | exact CRPk | exact DPC | exact KPk | exact INCk | exact IDB
              | exact STb | exact LOS | exact TPV | exact MIk | reflexivity | exact (sx32_small_ep id IDB)
              | lazymatch goal with
                | |- (length LF' < 512)%nat => cbn [length]; clear - LFB; lia
                | |- PKA + 16 <= lo \/ _ => clear - DSP SP1; lia
                | |- lo <= _ => clear - SLO1; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVk VB; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFk FB'; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_PK_USE_ECPARAMS in C24H; clear - C24H C24k; lia
                end
              | match goal with |- ?g => idtac "SG-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    unfold pk_ecc_set_group_postA in PO.
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & r & g' & NB & LB2
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & LEQ & LNEW & KP2 & AP2 & GB2 & RES & HPKA2).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb130c)) with (Z_to_bv 64 0xb130c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R. unfold ECP_GROUP_SIZE in HP2.
    assert (SUB2 : forall b, In b LBk -> In b LB2) by (intros b Hb; apply LEQ; right; exact Hb).
    assert (EXT2 : lb_ext LB NB LB2).
    { destruct EXTk as [E1 E2]. split.
      - intros b. rewrite (LEQ b). split; [intros [K|K]; [left; exact K| destruct (proj1 (E1 b) K) as [[]|K']; right; exact K']| intros [K|K]; [left; exact K| right; apply (proj2 (E1 b)); right; exact K]].
      - intros b Hb C'. exact (proj1 (LNEW b Hb) (SUBK b C')). }
    assert (FR2 : forall b, In b NB -> fresh_apart R LB LF (fst b) (snd b)).
    { intros b Hb. destruct (LNEW b Hb) as [_ (G0 & G1 & G2 & G3)]. split; [exact G0|]. split; [exact G1|]. split; [exact G2|].
      intros B j Hj. apply G3. apply in_app_iff in Hj. apply in_app_iff. destruct Hj as [Hj|Hj]; [left; apply SUBK; exact Hj| right; eapply fdata_incl; [| exact Hj]; intros fb Hfb; right; exact Hfb]. }
    assert (EB2 : EB h2 LB2 m2 (v + pk_set_group_PHI) (f + pk_set_group_FR) EP_SH0
                    [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10; C8 v11; C8 v12; C8 v13; C8 v14; C8 v15; C8 v16; C8 v17; C8 v18] [(FB + 624, [C4 (Z_to_bv 64 id); C4 gj'])] NB WF).
    { eapply (eb_step hk LBk mk v f _ _ _ [] W0 h2 LB2 m2 _ _ NB LBk [] [(C, C + 192)] WF); [exact EBk0| exact HH2| exact MI2| exact ST2| cbn [app]; exact HP2
        | exact HT2| exact HS2| exact HF2| exact HCS2| exact HV2| exact HFR2| exact SUBK| apply Forall_nil
        | intros x Hx; cbn [outside] in Hx |- *; clear - Hx; tauto| intros x Hx; cbn [outside] in Hx |- *; clear - Hx; tauto
        | apply Forall_cons; [cbn [snd]; clear - CAC; lia| apply Forall_nil]
        | ddestruct IDOK as (I1 & I2 & I3 & _); destruct DIMG as [DI1 DI2]; cbn [disjoint_from]; clear - CIM I1 I2 I3 DI1 DI2; lia
        | ddestruct IDOK as (I1 & I2 & I3 & _); destruct DIMG as [DI1 DI2]; cbn [disjoint_from]; clear - CIM I1 I2 I3 DI1 DI2; lia
        | | | exact EXT2| exact FR2].
      - cbn [app]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        ddestruct FRSH as (_ & _ & _ & G3). destruct (G3 C 256 ltac:(apply in_app_iff; left; exact INC)) as [K|K]; clear - K; lia.
      - apply Forall_cons; [| apply Forall_nil]. cbn [app fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from].
        ddestruct FRSH as (_ & _ & _ & G3). destruct (G3 C 256 ltac:(apply in_app_iff; left; exact INC)) as [K|K]; clear - K; lia. }
    clear HHk FHD FSH FSHR SAVE SLOTS STlo SThi STb MIk PRES IDSk LAWS KINV MU WM EBk0 GID CHk.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep.
    assert (RR : -2^31 < r <= 0).
    { clear - RES. unfold gl_result, MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE, MBEDTLS_ERR_MPI_ALLOC_FAILED in RES. decompose [and or ex] RES; subst; cbn; lia. }
    eapply (ep_exit h2 LB2 m2 _ _ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 r g' NB WF);
      first [ exact EB2 | (right; reflexivity) | exact VB | exact FB' | exact RR | exact KP2 | exact AP2 | exact GB2
            | (left; exists id; split; [exact IDB| exact RES])
            | idtac ].
    - intros R0. subst r. destruct KP2 as (HG2 & _). cbn [kp_grp] in HG2.
      exact (grp_factsA_of_gl_result_at R HIA h2 LB2 LF' m2 A_MT id C g' NB HH2 HG2 RES).
    - clear - RES. unfold gl_result in RES. decompose [and or ex] RES; subst; reflexivity.
    all: match goal with |- ?g => idtac "SG-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis MFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Hypothesis D0 : 0 <= d.
  Local Notation G := (FB + 368).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L16009136946.6L31775325020.4L9631767084.2 00000A00M00TS2FB1A2g01n2EA2HBS2FB1A2g02EAS2FB2F0". (* [comment removed for export] *)
  #[using="IMG NEEDR h LB LF sp lo LOS SLO sp1 SP1 F64 FRSH"] Lemma sh_aobj : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)Pmk,P,(11.&40.)(2?.(11.&8.))PSH,(25.$13.)PA,$5.Pg0,$19.Pn,$19.P,(12.$2.R5.(>.(16.VFB,+3.)(17.(18.VR,)))R4.)P,(6?.(;.$2.VR,VHIA,R7.)VFB,+400.)P,(7.$5.R5.(>.VFB,(4=.+8.(28.R4.))))P,(<.(4=.+8.(28.(70.R5.R4.)))+400.)P,Pi,$19.P,(71.R1.R6.)(7.(2?.$13.)(72.R:.(70.R8.R2.))(73.$13.(74.(1=.&8.=))))(69.$2.(18.VR,)(;.$2.VR,VHIA,R;.)R:.R8.(4=.+8.(28.R6.)))")
(* [comment removed for export] *).
  Proof.
    intros hk mk SH A g0 n FSH CFBk EA HB HZ. dpose eb_frame_facts as (F0 & F1 & F2 & F8 & _).
    eapply (aobj_of_zero_shadow_sh asegs AL (hcs asegs R HIA hk) mk FB SH A g0 n (hcs_ok asegs R HIA hk)); [exact FSH| | exact F8| clear - F0; lia| exact EA| exact HZ].
    eapply crange_sub; [exact CFBk| clear - EA; lia| clear - EA HB; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma eb_blk_apart : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))PB,$5.Pk,$5.P,(1.$2.VR,VHIA,R5.R4.(3.(4.$5.$5.)(6.$5.$5.VFB,+400.)VLF,)R3.)P,(2;.(4.$5.$5.)(6.$5.$5.R3.R2.)R5.)(2=.(<.(>.R4.R3.)VFB,)(<.(>.VFB,+400.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk B k HH HIn. destruct (hm_apart asegs R HIA hk _ _ _ HH) as [_ BA].
    pose proof (blocks_apart_app2 LBk LF' (B, k) (FB, 1024) BA HIn ltac:(left; reflexivity)) as X. cbn [fst snd] in X. exact X.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L10383309542.1 L17923996936.3 L19980016842.7 L22670022979.3 L23641086487.4 L24217117176.9 L26547906112.3 L28257718979.3 L29294044996.1 L32482273556.6 L39028691827.5 L39280637297.0 L40087511212.3 L41509918501.1 L42859311166.3 L45141363574.5 L46014214580.9 L4863643788.6  L49716460308.6 L50208671168.3 L56140970060.6 L58002997669.2 L635024086.1   L66151427842.16L66668349941.1 L6897470952.1  L753901287.1   L8461351180.5  L8928654781.2  L897379353.3   00000400<00T00_00n01K01V01a01d02702D02E02P02S02\02o03L03^04304>04Q04W04Z05605905=05A05N05U05_S2FBS2dd1x1QS1R3HIA1h2sp3TOP3sp13SP1S2FB2dd3DB2S2FB2dd3DB13DB2S1R3HIA1h1d4BUDF2hk1f3HFk3FB'S2FB2dd3DB1S2FB2dd3DB1S1xS1R2lo3sp14SLO13NERS2FB2dd3DB11KSS2FB2dd3DB2S1fS2FB2dd1KS2FB2dd3DB11x1K3DB2S1R3HIA1h3LEN3BUD2hk1v3HVk2VBS2FB2dd2ac2B11K2B2S2FB2dd3DB13DB22ac2B3S2FB2dd3DB1S2FB2dd1x3XB11K3XB2S1x2NxS1xS3sp12r04SP1M1q1r1H2H02q02H4S1vS2FBS2ddS2FB2dd3DB21KS2dd2NdS2dd1x3SEP". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO TOP TPV SP1 SP1M F64 FRSH BUD BUDF MFREE"] Lemma eb_free1 : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))Pv,$5.Pf,$5.PSH,(25.$13.)PSL,(25.$13.)PCH,(25.(4.$5.(25.$13.)))Pdd,$47.Pds,(25.$47.)PRET,$5.Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pxs0,(11.&40.)Pxs1,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pxs2,(11.&40.)Pxs3,(11.&40.)Pxs4,(11.&40.)Pxs5,(11.&40.)Pxs6,(11.&40.)Pxs7,(11.&40.)Pxs8,(11.&40.)Pxs9,(11.&40.)Pxs10,(11.&40.)Pxs11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)P,(40.R25.R24.R23.R22.R21.R20.R1?.R1>.(75.(3.$47.R1=.R1<.))(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))P,(76.$2.R24.R25.(>.VFB,+170.)+<0.(3.$47.R1>.R1=.))P,(24.(4.$5.(25.$13.))Lac,(4.$5.(25.$13.))(2=.(<.(>.(26.$5.(25.$13.)R1.)(28.(1:.(27.$5.(25.$13.)R1.))))(>.VFB,+170.))(<.(>.(>.VFB,+170.)+<0.)(26.$5.(25.$13.)R1.)))R20.)P,(69.$2.(18.VR,)(;.$2.VR,VHIA,R28.)R26.(77.R20.)+10.)P,(0.(<.=R1?.)(35.R1?.(39.+2.+40.)))P,(7.$5.(38.R20.+2.)=)P,(<.R28.(56.VLEN,))P,(<.(>.R28.+3.)(57.Vd,))P,Ph2,(3=.$2.VR,VHIA,)PLB2,(25.$2:.)Pm2,P,(11.&40.)(2?.(11.&8.))Py0,(11.&40.)Py1,(11.&40.)Py2,(11.&40.)Py3,(11.&40.)Py4,(11.&40.)Py5,(11.&40.)Py6,(11.&40.)Py7,(11.&40.)Py8,(11.&40.)Py9,(11.&40.)Py10,(11.&40.)Py11,(11.&40.)Py12,(11.&40.)Py13,(11.&40.)Py14,(11.&40.)P,(40.R12.R11.R10.R3<.(>.R3;.+3.)R3:.R39.R38.(75.R36.)(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))P,(76.$2.R11.R12.(>.VFB,+170.)+<0.R37.)(62.$2.(63.$2.VR,VHIA,R14.Vmo0,)(64.$2.VR,VHIA,$50.$5<.$5=.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(65.(66.(1=.&40.R37.)(1=.&40.Vsp1,)Vgp,Vtp,R11.R10.R?.R33.R32.R>.R=.R<.R;.R:.R9.R8.R7.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R6.R5.R4.R3.)VF,(1=.&40.R37.)Vfc,(67.(11.&40.))R12.(68.$2.)))(62.$2.(63.$2.VR,VHIA,R2>.Vmo0,)(64.$2.VR,VHIA,$50.$5<.$5=.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(65.(66.(1=.&40.R24.)(1=.&40.Vsp1,)Vgp,Vtp,R23.R22.R21.R20.R1?.(1=.&40.(77.R26.))R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(1=.&40.$78.)Vfc,(67.(11.&40.))R2<.(68.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EBk TOK CHG OX RETr RETe VB FB' CONT.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTOPk. rewrite ETk, ESk in HTOPk.
    pose proof (HND _ _ _ _ HHk) as NDk.
    destruct (hm_apart asegs R HIA hk _ _ _ HHk) as [_ BAk].
    dpose TOK as (T1 & T2 & T3 & T4 & T5 & T6).
    pose proof (Forall_inv T1) as MDd. pose proof (Forall_inv_tail T1) as T1'. dpose (Forall_inv T2) as (DNS & DB1 & DB2). pose proof (Forall_inv_tail T2) as T2'.
    pose proof MDd as [MDr _].
    assert (BLK : md_own dd = LHeap -> In (md_p dd, 4 * md_n dd) LBk /\ 1 <= md_n dd) by (intros O; exact (mpd_at_blk_in asegs mk LBk dd MDd O)).
    assert (BLA : md_own dd = LHeap -> md_p dd + 4 * md_n dd <= FB \/ FB + 1024 <= md_p dd).
    { intros O. destruct (BLK O) as [I1 _]. exact (eb_blk_apart hk LBk mk _ _ HHk I1). }
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    (* [comment removed for export] *)
    pose proof MFREE as SF. unfold mpi_free_stmtA in SF.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SF with (h := hk) (LB := LBk) (LF := LF') (X := md_addr dd) (sw := Z_to_bv 64 (md_sg dd)) (n := md_n dd) (P := md_p dd) (limbs := md_limbs dd) (pad := md_pad dd) (own := md_own dd) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HK1 | exact HHk | exact MDr | exact DNS | exact STb | exact LOS | exact TPV | exact MIk | exact OX | reflexivity
              | lazymatch goal with
                | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [apply in_app_iff; right; exact INFD| clear - DB1; lia| clear - DB2; lia]
                | |- md_own dd = LHeap -> _ => intros O; destruct (BLA O) as [K|K]; [right| left]; clear - K DB1 DB2; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold AVOL_CALL; clear - BUD HVk VB; lia
                | |- uw_obj _ _ _ _ => eapply (uw_obj_block asegs R HIA hk LBk LF' mk FB 1024); [exact HHk| apply in_app_iff; right; left; reflexivity| clear - DB1; lia| clear - DB2; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold fr_charge; clear - BUDF HFk FB'; lia
                end
              | match goal with |- ?g => idtac "FREE-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & HY2).
    rewrite ?(unsigned_lit sp1) in ST2, PXl by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    change (mpi_free_LB (md_own dd) (md_p dd) (md_n dd) LBk) with (lb_free_mpd dd LBk) in PXl, HH2.
    assert (NHD : forall b, In b (mpd_blk dd) -> ~ In b (tmp_blocks ds)) by (exact (tmp_ok_head_fresh asegs mk LBk G 192 dd ds TOK)).
    assert (EXT2 : lb_ext LB (tmp_blocks ds) (lb_free_mpd dd LBk)).
    { apply lb_ext_free; [exact EXTk| exact NDk| exact NHD]. }
    assert (SUBp : forall b, In b LB -> In b (lb_free_mpd dd LBk)) by (intros b Hb; eapply lb_ext_sub; [exact EXT2| exact Hb]).
    assert (FR2 : forall b, In b (tmp_blocks ds) -> fresh_apart R LB LF (fst b) (snd b)).
    { intros b Hb. apply FRk. unfold tmp_blocks in *. cbn [flat_map]. apply in_app_iff. right. exact Hb. }
    assert (WXF : Forall wx_fresh ((md_addr dd, md_addr dd + 16) :: mpi_free_X (md_own dd) (md_p dd) (md_n dd))).
    { apply Forall_cons; [left; cbn [fst snd]; clear - DB1 DB2; lia|].
      unfold mpi_free_X. destruct (md_own dd) eqn:O; [apply Forall_nil| | apply Forall_nil].
      apply Forall_cons; [| apply Forall_nil]. right. dexists (md_p dd), (4 * md_n dd). split; [| cbn [fst snd]; clear; lia].
      apply (FRk (md_p dd, 4 * md_n dd)). unfold tmp_blocks. cbn [flat_map]. apply in_app_iff. left. unfold mpd_blk. rewrite O. left. reflexivity. }
    assert (WXH : Forall (fun w => snd w <= FB \/ FB + 24 <= fst w) (((md_addr dd, md_addr dd + 16) :: mpi_free_X (md_own dd) (md_p dd) (md_n dd)) ++ [])).
    { rewrite app_nil_r. apply Forall_cons; [right; cbn [fst snd]; clear - DB1; lia|].
      unfold mpi_free_X. destruct (md_own dd) eqn:O; [apply Forall_nil| | apply Forall_nil].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. destruct (BLA eq_refl) as [K|K]; clear - K; lia. }
    assert (EB2 : EB h2 (lb_free_mpd dd LBk) m2 (v + AVOL_CALL) (f + fr_charge 0) SH SL CH (tmp_blocks ds) W0).
    { eapply (eb_step hk LBk mk v f SH SL CH _ W0 h2 _ m2 _ _ (tmp_blocks ds) (lb_free_mpd dd LBk) _ [] W0);
        [exact EBk0| exact HH2| exact MI2| exact ST2| rewrite app_nil_r; exact PXl| exact HT3| exact HS3| exact HF3| exact HCS3| exact HV3| exact HFR3| exact SUBp
        | exact WXF| intros x _; exact I| intros x Hx; exact Hx| apply Forall_nil| exact I| exact I| exact WXH| | exact EXT2| exact FR2].
      rewrite app_nil_r. rewrite Forall_forall in CHk, CHG |- *. intros ac Hac. ddestruct (CHk ac Hac) as (_ & B1 & B2). pose proof (CHG ac Hac) as B3.
      cbn [disjoint_from]. split; [clear - B3 DB1 DB2; lia|]. unfold mpi_free_X. destruct (md_own dd) eqn:O; cbn [disjoint_from]; [exact I| | exact I].
      split; [| exact I]. destruct (BLA eq_refl) as [K|K]; clear - K B1 B2; lia. }
    replace (v + AVOL_CALL) with v in EB2 by (unfold AVOL_CALL; clear; lia). replace (f + fr_charge 0) with (f + 3) in EB2 by (unfold fr_charge; clear; lia).
    assert (TOK2 : tmp_ok asegs m2 (lb_free_mpd dd LBk) G 192 ds).
    { eapply (tmp_ok_presA asegs L mk m2 LBk (lb_free_mpd dd LBk) G 192 ds sp1 _ (lb_free_mpd dd LBk ++ fdata LF'));
        [exact (tmp_ok_tail asegs mk LBk G 192 dd ds TOK)| exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXl)| exact MIk| exact MI2| | |].
      - eapply client_range_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia].
      - intros x Hx. pose proof (proj1 (Forall_forall _ _) T2' _ Hx) as (_ & XB1 & XB2).
        assert (NE : x <> dd).
        { intros EQ. rewrite EQ in Hx. cbn [map] in T6. apply NoDup_cons_iff in T6. destruct T6 as [NI _]. apply NI. apply in_map. exact Hx. }
        pose proof (T4 x dd (or_intror Hx) (or_introl eq_refl) NE) as SEP.
        cbn [disjoint_from]. split; [clear - SEP; lia|]. unfold mpi_free_X. destruct (md_own dd) eqn:O; cbn [disjoint_from]; [exact I| | exact I].
        split; [| exact I]. destruct (BLA eq_refl) as [K|K]; clear - K XB1 XB2; lia.
      - intros x Hx Ox. pose proof (proj1 (Forall_forall _ _) T1' _ Hx) as MX.
        destruct (mpd_at_blk_in asegs mk LBk x MX Ox) as (Ix & Nx).
        assert (NEa : md_addr x <> md_addr dd).
        { intros E. cbn [map] in T6. apply NoDup_cons_iff in T6. destruct T6 as [NI _]. apply NI. rewrite <- E. apply in_map. exact Hx. }
        assert (INp : In (md_p x, 4 * md_n x) (lb_free_mpd dd LBk)).
        { apply lb_free_mpd_keep; [exact Ix|]. intros Od. exact (T5 x dd (or_intror Hx) (or_introl eq_refl) NEa Ox Od). }
        split; [exact INp|]. split; [eapply client_range_block; [apply in_app_iff; left; exact INp| clear; lia| clear; lia]|].
        destruct (eb_blk_apart hk LBk mk _ _ HHk Ix) as [K|K].
        + cbn [disjoint_from]. split; [clear - K DB1; lia|]. unfold mpi_free_X. destruct (md_own dd) eqn:O; cbn [disjoint_from]; [exact I| | exact I].
          split; [| exact I]. destruct (BLK eq_refl) as [Id Nd].
          assert (NEQ : (md_p x, 4 * md_n x) <> (md_p dd, 4 * md_n dd)) by (intros E; injection E as E1 E2; exact (T5 x dd (or_intror Hx) (or_introl eq_refl) NEa Ox O E1)).
          destruct (blocks_apart_neq (LBk ++ LF') _ _ BAk ltac:(apply in_app_iff; left; exact Ix) ltac:(apply in_app_iff; left; exact Id) NEQ ltac:(cbn; clear - Nx; lia) ltac:(cbn; clear - Nd; lia)) as [Q|Q]; cbn in Q; clear - Q; lia.
        + cbn [disjoint_from]. split; [clear - K DB2; lia|]. unfold mpi_free_X. destruct (md_own dd) eqn:O; cbn [disjoint_from]; [exact I| | exact I].
          split; [| exact I]. destruct (BLK eq_refl) as [Id Nd].
          assert (NEQ : (md_p x, 4 * md_n x) <> (md_p dd, 4 * md_n dd)) by (intros E; injection E as E1 E2; exact (T5 x dd (or_intror Hx) (or_introl eq_refl) NEa Ox O E1)).
          destruct (blocks_apart_neq (LBk ++ LF') _ _ BAk ltac:(apply in_app_iff; left; exact Ix) ltac:(apply in_app_iff; left; exact Id) NEQ ltac:(cbn; clear - Nx; lia) ltac:(cbn; clear - Nd; lia)) as [Q|Q]; cbn in Q; clear - Q; lia. }
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply CONT; [exact EB2| exact TOK2].
    all: match goal with |- ?g => idtac "FREE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis PFREE : ecp_point_free_stmtA asegs R HIA A_ECP_POINT_FREE.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lb_ext_frees : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Pds,(25.$47.)PLBi,(25.$2:.)PT,(25.$2:.)P,(29.VLB,(31.$2:.(75.R3.)R1.)R2.)P,(79.$5.(7:.(4.$5.$5.)$5.(26.$5.$5.)R3.))P,(79.$5.(7:.(4.$5.$5.)$5.(26.$5.$5.)(75.R5.)))P,Pb,$2:.P,(2;.$2:.R1.(75.R7.))(7;.(2;.$2:.R2.R6.))(29.VLB,R5.(7<.R7.R6.))")
(* [comment removed for export] *).
  Proof.
    induction ds as [|x ds IH]; intros LBi T EXT ND NDT NT; [exact EXT|].
    cbn [lb_free_mpds]. apply IH.
    - apply lb_ext_free; [unfold tmp_blocks in EXT; cbn [flat_map] in EXT; rewrite <- app_assoc in EXT; exact EXT| exact ND|].
      intros b Hb Hc. apply in_app_iff in Hc. destruct Hc as [Hc|Hc].
      + unfold tmp_blocks in NDT. cbn [flat_map] in NDT. rewrite map_app in NDT.
        destruct (mpd_blk_in _ _ Hb) as [Ox ->]. rewrite (mpd_blk_heap _ Ox) in NDT. cbn [map app fst] in NDT. apply NoDup_cons_iff in NDT. destruct NDT as [NI _].
        apply NI. change (md_p x) with (fst (md_p x, 4 * md_n x)). apply in_map. exact Hc.
      + apply (NT b); [unfold tmp_blocks; cbn [flat_map]; apply in_app_iff; left; exact Hb| exact Hc].
    - apply lb_free_mpd_nodup. exact ND.
    - unfold tmp_blocks in NDT |- *. cbn [flat_map] in NDT. rewrite map_app in NDT. apply NoDup_app_remove_l in NDT. exact NDT.
    - intros b Hb. apply NT. unfold tmp_blocks. cbn [flat_map]. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L10470408908.9 L11800675683.3 L19980016842.7 L20991912468.6 L21678748020.3 L21710830420.1 L36115804772.1 L37478058068.1 L37996622676.1 L38568648267.9 L39280637297.0 L46112830340.1 L56657201993.1 L63496995273.1 L64174541735.1 L64546054715.1 L66151427842.16L6726008016.1  00000M00W00o01B01N01R01U01Y01]02:02;02?02C02G02J02N02j02nS1R3HIA1h1d4BUDF2hk1f3HFk3FB'S2FB2ac2B3S1R3HIA1h2sp3TOP3sp13SP1S1R2lo3sp14SLO13NERS2lo2FB4FBLOS2FBS1vS2FBS2FBS1R3HIA1h3LEN3BUD2hk1v3HVk2VBSS2FBS2FBS2FBS1fS2FBS3sp12r04SP1M1q1r1H2H02q02H4S2FB". (* [comment removed for export] *)
  #[using="IMG NEEDR HND IDOK LOS SLO TOP TPV SP1 SP1M F64 FRSH BUD BUDF PFREE"] Lemma eb_pfree : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))Pv,$5.Pf,$5.PSH,(25.$13.)PSL,(25.$13.)PCH,(25.(4.$5.(25.$13.)))PdX,$47.PdY,$47.PdZ,$47.PRET,$5.Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pxs0,(11.&40.)Pxs1,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pxs2,(11.&40.)Pxs3,(11.&40.)Pxs4,(11.&40.)Pxs5,(11.&40.)Pxs6,(11.&40.)Pxs7,(11.&40.)Pxs8,(11.&40.)Pxs9,(11.&40.)Pxs10,(11.&40.)Pxs11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)P,(40.R26.R25.R24.R23.R22.R21.R20.R1?.(75.(3.$47.R1>.(3.$47.R1=.(3.$47.R1<.(15.$47.)))))(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))P,(76.$2.R25.R26.(>.VFB,+170.)+<0.(3.$47.R1?.(3.$47.R1>.(3.$47.R1=.(15.$47.)))))P,(24.(4.$5.(25.$13.))Lac,(4.$5.(25.$13.))(2=.(<.(>.(26.$5.(25.$13.)R1.)(28.(1:.(27.$5.(25.$13.)R1.))))(>.VFB,+170.))(<.(>.(>.VFB,+170.)+<0.)(26.$5.(25.$13.)R1.)))R21.)P,(7.$5.(77.R21.)(>.(>.VFB,+170.)+38.))P,(7.$5.(77.R21.)(>.(>.VFB,+170.)+48.))P,(7.$5.(77.R21.)(>.(>.VFB,+170.)+58.))P,(69.$2.(18.VR,)(;.$2.VR,VHIA,R2<.)R2:.(>.(>.VFB,+170.)+38.)+30.)P,(0.(<.=R22.)(35.R22.(39.+2.+40.)))P,(7.$5.(38.R23.+2.)=)P,(<.R2<.(56.VLEN,))P,(<.(>.R2<.+9.)(57.Vd,))P,Ph2,(3=.$2.VR,VHIA,)PLB2,(25.$2:.)Pm2,P,(11.&40.)(2?.(11.&8.))Py0,(11.&40.)Py1,(11.&40.)Py2,(11.&40.)Py3,(11.&40.)Py4,(11.&40.)Py5,(11.&40.)Py6,(11.&40.)Py7,(11.&40.)Py8,(11.&40.)Py9,(11.&40.)Py10,(11.&40.)Py11,(11.&40.)Py12,(11.&40.)Py13,(11.&40.)Py14,(11.&40.)P,(40.R12.R11.R10.R40.(>.R3?.+9.)R3>.R3=.R3<.(15.$2:.)(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))(62.$2.(63.$2.VR,VHIA,R13.Vmo0,)(64.$2.VR,VHIA,$50.$5<.$5=.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(65.(66.(1=.&40.R39.)(1=.&40.Vsp1,)Vgp,Vtp,R10.R?.R>.R35.R34.R=.R<.R;.R:.R9.R8.R7.R6.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R5.R4.R3.R2.)VF,(1=.&40.R39.)Vfc,(67.(11.&40.))R11.(68.$2.)))(62.$2.(63.$2.VR,VHIA,R32.Vmo0,)(64.$2.VR,VHIA,$50.$5<.$5=.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(65.(66.(1=.&40.R27.)(1=.&40.Vsp1,)Vgp,Vtp,R26.R25.R24.R23.R22.(1=.&40.(>.(>.VFB,+170.)+38.))R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)VF,(1=.&40.$7=.)Vfc,(67.(11.&40.))R30.(68.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros EBk TOK CHG EX EY EZ OX RETr RETe VB FB' CONT.
    pose proof EBk as EBk0. eb_open EBk.
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    pose proof (hm_top asegs R HIA hk _ _ _ HHk) as HTOPk. rewrite ETk, ESk in HTOPk.
    pose proof (HND _ _ _ _ HHk) as NDk.
    dpose TOK as (T1 & T2 & T3 & T4 & T5 & T6).
    assert (INFD : In (FB + 32, 984) (fdata LF')) by (cbn [fdata]; right; left; reflexivity).
    set (p := mkPT dX dY dZ).
    assert (PAT : ecp_point_at asegs mk LBk (G + 56) p).
    { unfold ecp_point_at, p. cbn [pt_X pt_Y pt_Z]. rewrite Forall_forall in T1.
      split; [exact EX|]. split; [rewrite EY; clear; lia|]. split; [rewrite EZ; clear; lia|].
      split; [exact (proj1 (T1 dX ltac:(cbn; auto)))|]. split; [exact (proj1 (T1 dY ltac:(cbn; auto)))| exact (proj1 (T1 dZ ltac:(cbn; auto)))]. }
    assert (PFR : pt_freeable p).
    { unfold pt_freeable, p, pt_mpds. cbn [pt_X pt_Y pt_Z]. rewrite Forall_forall in T2 |- *. intros x Hx. exact (proj1 (T2 x Hx)). }
    assert (EXT2 : lb_ext LB [] (pt_free_LB p LBk)).
    { unfold pt_free_LB, p, pt_mpds. cbn [pt_X pt_Y pt_Z]. apply lb_ext_frees; [rewrite app_nil_r; exact EXTk| exact NDk| exact (tmp_ok_blocks_nodup asegs mk LBk G 192 _ TOK)| intros b _ []]. }
    assert (SUBp : forall b, In b LB -> In b (pt_free_LB p LBk)) by (intros b Hb; eapply lb_ext_sub; [exact EXT2| exact Hb]).
    (* [comment removed for export] *)
    pose proof PFREE as SF. unfold ecp_point_free_stmtA, A_ECP_POINT_FREE, ECP_POINT_SIZE in SF.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SF with (h := hk) (LB := LBk) (LF := LF') (A := G + 56) (p := p) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HK1 | exact HHk | exact PAT | exact PFR | exact T5 | exact STb | exact LOS | exact TPV | exact MIk | exact OX | reflexivity
              | lazymatch goal with
                | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [apply in_app_iff; right; exact INFD| clear; lia| clear; lia]
                | |- _ + 48 <= lo \/ _ => left; clear - FBLO; lia
                | |- lo <= _ => clear - SLO1 NER NEEDR; lia
                | |- _ <= htop _ _ _ _ => rewrite ETk; clear - TOP SP1; lia
                | |- _ mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold PF_PHI, AVOL_CALL; clear - BUD HVk VB; lia
                | |- uw_obj _ _ _ _ => eapply (uw_obj_block asegs R HIA hk LBk LF' mk FB 1024); [exact HHk| apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold PF_FR, fr_charge; clear - BUDF HFk FB'; lia
                end
              | match goal with |- ?g => idtac "PFREE-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold ecp_point_free_postA, ECP_POINT_SIZE in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PXl & HT3 & HS3 & HF3 & HK2 & HCS3 & HV3 & HFR3 & HH2 & PAT2).
    rewrite ?(unsigned_lit sp1) in ST2, PXl by exact SP1R.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETr| exact RETe]).
    assert (EB2 : EB h2 (pt_free_LB p LBk) m2 (v + PF_PHI) (f + PF_FR 0) SH SL CH [] W0).
    { eapply (eb_step hk LBk mk v f SH SL CH _ W0 h2 _ m2 _ _ [] (pt_free_LB p LBk) [(G + 56, G + 56 + 48)] [] W0);
        [exact EBk0| exact HH2| exact MI2| exact ST2| exact PXl| exact HT3| exact HS3| exact HF3| exact HCS3| exact HV3| exact HFR3| exact SUBp
        | apply Forall_cons; [left; cbn [fst snd]; clear; lia| apply Forall_nil]| intros x _; exact I| intros x Hx; exact Hx| apply Forall_nil| exact I| exact I
        | apply Forall_cons; [right; cbn [fst snd]; clear; lia| apply Forall_nil]| | exact EXT2| intros b []].
      rewrite Forall_forall in CHG |- *. intros ac Hac. pose proof (CHG ac Hac) as B3. cbn [app disjoint_from]. split; [clear - B3; lia| exact I]. }
    replace (v + PF_PHI) with v in EB2 by (unfold PF_PHI, AVOL_CALL; clear; lia). replace (f + PF_FR 0) with (f + 9) in EB2 by (unfold PF_FR, fr_charge; clear; lia).
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply CONT; exact EB2.
    all: match goal with |- ?g => idtac "PFREE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition EP_SH_G : list cell := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "(3.$13.(74.(1=.&8.+?1.))(3.$13.(74.(1=.&8.+?1.))(3.$13.(74.(1=.&8.+?1.))(3.$13.(74.(1=.&8.+?1.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?8.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.=))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+?2.))(3.$13.(74.(1=.&8.+4.))(3.$13.(74.(1=.&8.+?3.))(15.$13.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03?0@C53807985733.259C53807985733.260L10515057222.4  L12414779970.0  L13738328481.0  L15195629121.1  L15796291696.4  L1685717371.0   L16908924412.211L17524925726.256L17524925726.257L17935831712.1  L18095303840.1  L19345944507.3  L19348303760.5  L20613147259.18 L20613311099.18 L21444186492.250L2354636449.0   L23952587329.1  L24023900370.0  L25317535195.2  L26368079009.0  L28948604668.214L29010569984.251L31595477152.1  L32586543723.0  L34259272700.250L35668120898.7  L36667852792.0  L37312774224.4  L37312938064.6  L40110006688.1  L405945248.1    L42411609006.0  L42849193485.3  L43862018479.1  L47513520362.256L47513520362.257L4809163568.4   L49379278409.0  L49629343297.1  L49788159649.0  L51624893551.3  L55607612363.19 L55607907275.19 L55882670497.0  L56494227009.1  L58573668988.217L59301701491.19 L59302061939.19 L59308586248.2  L59308586248.4  L59308586248.5  L60098763854.3  L63667055128.0  L66151426447.10 L6670631903.4   L8848476737.1   L8980426178.0   L957827166.0    P22976122839.259P22976122839.260Q10277028445.254Q10378454015.220Q10980424452.217Q11360114729.254Q11799173861.259Q11799173861.260Q1209316766.254 Q12239312894.254Q13145930644.254Q13342201113.254Q13617618477.254Q1391447166.254 Q15026967797.217Q16378781055.214Q17204041764.254Q17205621449.254Q17367682989.254Q17485408678.254Q17659182717.254Q19017694852.220Q19189730361.254Q19314997093.254Q19460344126.254Q20000947061.220Q20364844244.254Q20377295060.256Q20546391641.254Q21138727438.254Q22208514180.254Q22224774057.254Q22297922500.254Q22521513988.214Q2283278961.250 Q22940771486.254Q24216502906.254Q2477493657.254 Q26086659700.254Q26391896441.254Q26984203566.254Q2767599277.254 Q28054021028.254Q28160402148.254Q28342961998.254Q28345929501.254Q28525969917.254Q30134573029.254Q30204361421.254Q31214822484.254Q31413195225.254Q31686777581.254Q31988692366.254Q32097844381.254Q32277886845.254Q33073221636.254Q33091570473.254Q3342181181.254 Q33947166577.254Q34347029405.255Q35274522505.254Q36936645108.254Q37043026228.254Q37258889465.254Q39125883166.255Q40293674089.254Q41009930590.254Q41174972478.254Q42079719380.254Q42185903892.254Q42277861721.254Q42551435885.254Q4359140991.217 Q44298944140.251Q44298944140.255Q44301027056.259Q44301027056.260Q45053362670.254Q46002313320.214Q46141507337.254Q46303319021.254Q46414826461.254Q47228431932.259Q47228431932.260Q48119910507.259Q48119910507.260Q48125615682.254Q48275351437.254Q48377109886.254Q50057590350.254Q51144219844.254Q51160479721.254Q52025136397.254Q52041761726.254Q54300172794.254Q54487832473.255Q55256112523.255Q55903349102.254Q5596578838.259 Q5596578838.260 Q56979388895.254Q57006173833.254Q57279533917.254Q57461631549.254Q58021947240.217Q58422939109.254Q59080925726.254Q59617553652.254Q59619599055.254Q60346759705.254Q60922288590.254Q61992100932.254Q62098483076.254Q63012415579.254Q63122260654.254Q6339342500.254 Q63435846322.255Q6355594057.254 Q64041668840.220Q64210404297.254Q64228675114.258Q64228675114.259Q64228946346.259Q64228946346.260Q65872527924.254Q65959841140.254Q66192497977.254Q66344247373.254Q66942122546.251Q66942122546.255Q66956788302.259Q66956788302.260Q67300381685.214Q67854622564.254Q67892150791.255Q68126749454.254Q68309499325.254Q6912043754.256 Q8017761716.254 Q8322999481.254 Q8430350046.254 Q8472628173.254 Q8915310702.254 Q9933143375.254 Q9935237393.250 Q9947771764.254 00000100200A00B00C00G00U00V01`01a01b01f01j02302402502603@03A03E03F03M03N04X04Y04]04^05h06?06@06N06O06S06W06X06b06f08R0:>0:L0:M0:Q0:R0:\0:]0:^0:_0:c0;m0;n0;o0<50<A0<P0<Z0<[0<k0=90==0=>0=?0>Y0@30@40A@0BR0BS0Cm0EG0EH0EI0FL0FM0FN0FO0G`0Hl0Io0J00J10J20J30KE0KF0LM0LN0M_0Nb0P60P70P80Q;0Q<0R?0SQ0TT0TU0U\0U]0V`0Va0Vb0Vc0Wf0Xi0Xj0Xk0Xl0Xm0Xn0Z10Z20Z30Z40Z50Z60[90[:0[;0\e0^?0^@0_C0`F0`G0`H0`I0`J0`K0aN0bQ0bR0bS0c_0dg0eo0gI0hc0hd0j?0j@0jA0jB0k`0m>0o410j10k10l10m10n12112212312413;14c14d14e14f14g15j15k15l15m17H18O18P18Q18R18S18T19W1:Z1<<1<=1=@1=A1=B1>]1>^1@h1C21EB1GR1HU1IX1IY1IZ1Jb1Kj1MD1N^1Oo1Q21Q31Q41Q51RI1SL1SM1SN1SO1SP1TS1UV1VYFFS3LEN1v2VB4PSG0SSS2FBS1d1f3FB'4FSG0SS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFS2FBS2FBS1d1f3FB'FFFS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLSS2FBSS2g02G2SS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFS2FBSS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R3HIA1h2sp2lo3TOP3HT0SS1d1f3FB'4FSG0FS2FBS2FBSS3LEN1v2VBS2FBS1R2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1d1f3FB'4FSG0SS2FBSS1R2FB3APSFFSS2FBS2LF2sp3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFS1i2HiS2G12G21i2HiS2g02G12G21i2HiS1R2lo3LOSSS1r2RR2r02KR1q1HS1d1f3FB'4FSG0S2FBSSS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184SP1R4NSH'3NSLS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183SPR4NSH'3NSLFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFS2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184SP1R4NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFFS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183SPR4NSH'3NSLFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFS2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF2sp3PKA2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183SPR4NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184SLO13NER4NSH'3NSL2HB5Ha_st5Hl_stS1R2LF2sp3PKA2lo2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184SP1R4NSH'3NSLS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstFS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184SLO13NER4NSH'3NSLFFFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183ALO4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183ALO4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3LOS3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183ALO3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R5NEEDR2LF2sp3PKA2lo3SLO2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v183NER4NSH'3NSL2HB5Ha_st5Hl_stFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184SLO13NER4NSH'3NSLS2LF3PKA2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS1R2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFS1R5NEEDR2LF3PKA2lo2FB3sp13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184SLO13NER4NSH'3NSLFS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2v12v22v32v42v52v62v72v82v93v103v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2v12v22v32v42v52v62v72v82v93v103v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2v12v22v32v42v52v62v72v82v93v103v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8stS1R5NEEDR2LF2sp3PKA2lo3SLO3SPA2FB3sp13LFB3NZP2v12v22v32v42v52v62v72v82v93v103v163v173v182F02F84FBLO4SP1R3NER4NSH'3NSL2HB5Ha_st5Hl_st5SAEst5CM8stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HBS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_st5SAEstS2LF2sp3PKA2lo2FB3sp13SP13LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFS1R2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL2HB5Ha_st5Hl_stS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLFFFFS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSLS2LF3PKA2FB3LFB2v12v22v32v42v52v62v72v82v93v103v163v173v184NSH'3NSL". (* [comment removed for export] *)
  #[using="IMG NEEDR DIMG HND IDOK LOS SLO TOP SPA TPV HH0 MI0 SP1 SP1M F64 FRSH NS1 LFB SF5 NSH HPKA0 CRP DSP DPI DPC KP0 INC CFB HSG EI ALP NZP OPKA0 BUD BUDF C24H MFREE PFREE"] Lemma ep_cleanup : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_B ()) "Phk,(3=.$2.VR,VHIA,)PLBk,(25.$2:.)Pmk,P,(11.&40.)(2?.(11.&8.))Pv,$5.Pf,$5.PdN,$47.PdP,$47.PdA,$47.PdB,$47.PdX,$47.PdY,$47.PdZ,$47.Pv1,(11.&40.)Pv2,(11.&40.)Pv3,(11.&40.)Pv4,(11.&40.)Pv5,(11.&40.)Pv6,(11.&40.)Pv7,(11.&40.)Pv8,(11.&40.)Pv9,(11.&40.)Pv10,(11.&40.)Ps7v,(11.&40.)Pv16,(11.&40.)Pv17,(11.&40.)Pv18,(11.&40.)Pr,$5.Pid,$5.Pgj',(11.&40.)Pxra,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pa0v,(11.&40.)Pa1,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Ps3v,(11.&40.)Ps5v,(11.&40.)Ps6v,(11.&40.)Ps11v,(11.&40.)P,(40.R30.R2?.R2>.R2=.R2<.$7>.(3.$13.(14.R24.)(3.$13.(14.R23.)(3.$13.(14.R22.)(3.$13.(14.R21.)(3.$13.(14.R20.)(3.$13.(14.R1?.)(3.$13.(14.R1>.)(3.$13.(14.R1=.)(3.$13.(14.R1<.)(3.$13.(14.R1;.)(3.$13.(14.(1=.&40.VPKA,))(3.$13.(14.(1=.&40.(>.(>.VFB,+170.)+28.)))(3.$13.(14.(1=.&40.(>.(>.VFB,+170.)+18.)))(3.$13.(14.(1=.&40.(>.VFB,+270.)))(3.$13.(14.(1=.&40.(>.(>.VFB,+170.)+8.)))(3.$13.(14.R19.)(3.$13.(14.R18.)(3.$13.(14.R17.)(15.$13.)))))))))))))))))))(3.(4.$5.(25.$13.))(6.$5.(25.$13.)(>.VFB,+270.)(3.$13.(6<.(1=.&40.R15.))(3.$13.(6<.R14.)(15.$13.))))(15.(4.$5.(25.$13.))))(75.(3.$47.R2;.(3.$47.R2:.(3.$47.R29.(3.$47.R28.(3.$47.R27.(3.$47.R26.(3.$47.R25.(15.$47.)))))))))(3.(4.$5.$5.)(6.$5.$5.VIDONE,(>.VIDONE,+1.))(3.(4.$5.$5.)(6.$5.$5.VIDS,(>.VIDS,+38.))(15.(4.$5.$5.)))))P,(76.$2.R2?.R30.(>.VFB,+170.)+<0.(3.$47.R2<.(3.$47.R2;.(3.$47.R2:.(3.$47.R29.(3.$47.R28.(3.$47.R27.(3.$47.R26.(15.$47.)))))))))P,(7.$5.(77.R2=.)(>.(>.VFB,+170.)+68.))P,(7.$5.(77.R2=.)(>.(>.VFB,+170.)+8.))P,(7.$5.(77.R2=.)(>.(>.VFB,+170.)+18.))P,(7.$5.(77.R2=.)(>.(>.VFB,+170.)+28.))P,(7.$5.(77.R2=.)(>.(>.VFB,+170.)+38.))P,(7.$5.(77.R2=.)(>.(>.VFB,+170.)+48.))P,(7.$5.(77.R2=.)(>.(>.VFB,+170.)+58.))P,(0.(35.(58.(39.+2.+1?.))R1?.)(<.R1?.=))P,P,(7.$5.R20.=)(0.(<.=R20.)(35.R20.(39.+2.+1?.)))P,(<.(>.R38.$6=.)(56.VLEN,))P,(<.(>.(>.R38.+15.)$6>.)(57.Vd,))(62.$2.(63.$2.VR,VHIA,R3=.Vmo0,)(64.$2.VR,VHIA,$50.$5<.$5=.VIDONE,VIDS,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(53.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)VLEN,Vlo,Vd,Vm,Vmo0,)(65.(66.R20.(1=.&40.Vsp1,)Vgp,Vtp,R1?.R1>.R1=.Vsp,(1=.&40.Vsp1,)R1<.R1;.(1=.&40.(>.(>.VFB,+170.)+68.))R1:.R19.R18.R17.R16.(1=.&40.VFB,)R11.(1=.&40.(>.(16.VFB,+3.)(17.(18.VR,))))R10.R?.R27.(1=.&40.(>.(>.VFB,+170.)+38.))(1=.&40.VFB,)(1=.&40.R23.)R>.R15.R14.R13.R12.)VF,(1=.&40.+;1268.)Vfc,(67.(11.&40.))R3;.(68.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros EBk TOK EN EP EA EB' EX EY EZ RR IDR VB FB'.
    assert (PSG0 : 0 <= pk_set_group_PHI) by (unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (FSG0 : 0 <= pk_set_group_FR) by (unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia).
    assert (CHG : Forall (fun ac : Z * list cell => fst ac + Z.of_nat (cells_size (snd ac)) <= G \/ G + 192 <= fst ac) [(FB + 624, [C4 (Z_to_bv 64 id); C4 gj'])]).
    { apply Forall_cons; [right; cbn [fst]; clear; lia| apply Forall_nil]. }
    dpose eb_frame_facts as (F0 & F1 & F2 & F8 & FBLO & ALO & SP1R & SLO1 & SPR & NER & SH640).
    (* [comment removed for export] *)
    assert (OXM : forall (hq : HST asegs R HIA) LBq mq vq fq SLq CHq Tq (g0 : nat) A, EB hq LBq mq vq fq EP_SH_G SLq CHq Tq W0 ->
                    A = FB + 8 * Z.of_nat g0 -> (46 <= g0)%nat -> (g0 + 2 <= 70)%nat -> aobj asegs AL (hcs asegs R HIA hq) mq A 16).
    { intros hq LBq mq vq fq SLq CHq Tq g0 A EBq EA0 G1 G2. ddestruct EBq as (HHq & _ & _ & _ & _ & (FSHq & _) & _).
      change 16 with (8 * Z.of_nat 2).
      eapply (sh_aobj hq mq EP_SH_G A g0 2); [exact FSHq| exact (hcs_fake asegs R HIA hq LBq _ mq FB 1024 HHq ltac:(left; reflexivity))| exact EA0| clear - G2; lia|].
      intros i Hi. unfold EP_SH_G. clear - G1 G2 Hi.
      do 46 (destruct g0 as [|g0]; [exfalso; lia|]). do 23 (destruct g0 as [|g0]; [destruct i as [|[|i]]; [reflexivity| reflexivity| exfalso; lia]|]). exfalso. lia. }
    pose proof EBk as EBk0. eb_open EBk.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    assert (SCSk : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (FB + 472) with (md_addr dN) by (rewrite EN; clear; lia).
    eapply (eb_free1 hk LBk mk v f _ _ _ dN [dP; dA; dB; dX; dY; dZ] 0xb1270);
      [exact EBk0| exact TOK| exact CHG| rewrite EN; eapply (OXM hk _ _ _ _ _ _ _ 59%nat); [exact EBk0| clear; lia| clear; lia| clear; lia]
      | clear; lia| reflexivity| clear - VB PSG0; lia| clear - FB' FSG0; lia|].
    intros h1 LB1 m1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EB1 TOK1.
    clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM SCSk. clear w0 w1 w2.
    pose proof EB1 as EBk0. eb_open EB1.
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (SCSk : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (FB + 376) with (md_addr dP) by (rewrite EP; clear; lia).
    eapply (eb_free1 h1 LB1 m1 _ _ _ _ _ dP [dA; dB; dX; dY; dZ] 0xb1278);
      [exact EBk0| exact TOK1| exact CHG| rewrite EP; eapply (OXM h1 _ _ _ _ _ _ _ 47%nat); [exact EBk0| clear; lia| clear; lia| clear; lia]
      | clear; lia| reflexivity| clear - VB PSG0; lia| clear - FB' FSG0; lia|].
    intros h2 LB2 m2 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB2 TOK2.
    clear TOK1. clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM SCSk. clear w0 w1 w2.
    clear y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14. rename z0 into y0, z1 into y1, z2 into y2, z3 into y3, z4 into y4, z5 into y5, z6 into y6, z7 into y7, z8 into y8, z9 into y9, z10 into y10, z11 into y11, z12 into y12, z13 into y13, z14 into y14.
    pose proof EB2 as EBk0. eb_open EB2.
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (SCSk : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (FB + 392) with (md_addr dA) by (rewrite EA; clear; lia).
    eapply (eb_free1 h2 LB2 m2 _ _ _ _ _ dA [dB; dX; dY; dZ] 0xb1280);
      [exact EBk0| exact TOK2| exact CHG| rewrite EA; eapply (OXM h2 _ _ _ _ _ _ _ 49%nat); [exact EBk0| clear; lia| clear; lia| clear; lia]
      | clear; lia| reflexivity| clear - VB PSG0; lia| clear - FB' FSG0; lia|].
    intros h3 LB3 m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB3 TOK3.
    clear TOK2. clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM SCSk. clear w0 w1 w2.
    clear y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14. rename z0 into y0, z1 into y1, z2 into y2, z3 into y3, z4 into y4, z5 into y5, z6 into y6, z7 into y7, z8 into y8, z9 into y9, z10 into y10, z11 into y11, z12 into y12, z13 into y13, z14 into y14.
    pose proof EB3 as EBk0. eb_open EB3.
    pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    assert (SCSk : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (FB + 408) with (md_addr dB) by (rewrite EB'; clear; lia).
    eapply (eb_free1 h3 LB3 m3 _ _ _ _ _ dB [dX; dY; dZ] 0xb1288);
      [exact EBk0| exact TOK3| exact CHG| rewrite EB'; eapply (OXM h3 _ _ _ _ _ _ _ 51%nat); [exact EBk0| clear; lia| clear; lia| clear; lia]
      | clear; lia| reflexivity| clear - VB PSG0; lia| clear - FB' FSG0; lia|].
    intros h4 LB4 m4 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB4 TOK4.
    clear TOK3. clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM SCSk. clear w0 w1 w2.
    clear y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14. rename z0 into y0, z1 into y1, z2 into y2, z3 into y3, z4 into y4, z5 into y5, z6 into y6, z7 into y7, z8 into y8, z9 into y9, z10 into y10, z11 into y11, z12 into y12, z13 into y13, z14 into y14.
    pose proof EB4 as EBk0. eb_open EB4.
    pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    assert (SCSk : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    replace (FB + 424) with (G + 56) by (clear; lia).
    eapply (eb_pfree h4 LB4 m4 _ _ _ _ _ dX dY dZ 0xb1290);
      [exact EBk0| exact TOK4| exact CHG| exact EX| exact EY| exact EZ| | clear; lia| reflexivity| clear - VB PSG0; lia| clear - FB' FSG0; lia|].
    { ddestruct EBk0 as (HHq & _ & _ & _ & _ & (FSHq & _) & _). change 48 with (8 * Z.of_nat 6).
      eapply (sh_aobj h4 m4 EP_SH_G (G + 56) 53 6); [exact FSHq| exact (hcs_fake asegs R HIA h4 LB4 _ m4 FB 1024 HHq ltac:(left; reflexivity))| clear; lia| clear; lia|].
      intros i Hi. unfold EP_SH_G. do 6 (destruct i as [|i]; [reflexivity|]). exfalso. clear - Hi. lia. }
    intros h5 LB5 m5 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 EB5.
    clear TOK4. clear EBk0 HHk ETk ESk EFk HCSk HVk HFk FHD FSH NSH' FSHR SAVE SLOTS NSL STlo SThi STb MIk PRES IDSk CHk EXTk FRk LAWS KINV MU WM SCSk. clear w0 w1 w2.
    pose proof EB5 as EBk0. eb_open EB5.
    pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl [(SHB, SHB + 80)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    assert (SCSk : crange (hcs asegs R HIA h5) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCSk|]. eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia|]. pose proof (hm_top asegs R HIA h _ _ _ HH0) as HT0. clear - HT0 TOP. lia. }
    pose proof (fresh_apart_relist_sg R HIA h5 LB LB5 LF m5 FB 1024 FRSH HHk) as FRSHk.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA h5) h5 LB5 LF m5 FB 1024 lo HHk eq_refl FRSHk F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & INF & INH & IND & AP & _ & _ & _ & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
    pose proof (hm_wlow asegs R HIA h5 _ _ _ HHk) as WLk.
    pose proof (hcs_ok asegs R HIA h5) as CSOKk.
    unfold EP_SH_G in FSH.
    (* [comment removed for export] *)
    do 27 zstep.
    match goal with H : rw_cells _ _ SHB _ |- _ => norm_b8 H; rename H into FSH6 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    assert (EB6 : EB h5 LB5 m6 v (f + 3 + 3 + 3 + 3 + 9) EP_SH0
                    [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10; C8 (Z_to_bv 64 PKA); C8 (Z_to_bv 64 (G + 40)); C8 (Z_to_bv 64 (G + 24));
                     C8 (Z_to_bv 64 (FB + 624)); C8 (Z_to_bv 64 (G + 8)); C8 v16; C8 v17; C8 v18]
                    [(FB + 624, [C4 (Z_to_bv 64 id); C4 gj'])] [] W0).
    { unfold EB. split; [exact HHk|]. split; [exact (conj ETk (conj ESk EFk))|]. split; [exact HCSk|]. split; [exact (conj HVk HFk)|].
      split; [dexists w0, w1, w2; exact FHD|]. split; [split; [unfold EP_SH0; cbn [repeat app]; exact FSH6| reflexivity]|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [split; [exact SLOTS| reflexivity]|]. split; [exact STlo|]. split; [exact SThi|]. split; [exact STb|]. split; [exact MIk|].
      split; [exact PRES|].
      split; [eapply (ids_munch_sh m5 m6 80); [exact IDSk| exact MU| exact WM| exact (proj1 SBND)]|].
      split; [eapply (ch_munch_sh m5 m6 80); [exact CHk| exact MU| exact WM| clear - APS; lia]|].
      split; [exact EXTk| exact FRk]. }
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      assert (RNZ : r <> 0).
      { intros ->. clear - KR. first [apply KR; reflexivity| (vm_compute in KR; congruence)]. }
      destruct (eb_entry_objs _ _ _ _ _ _ _ _ _ EB6) as (_ & _ & KP6 & _ & _).
      eapply (ep_exit h5 LB5 m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r (kp_grp KPI) [] W0 _);
        first [ exact EB6 | (left; reflexivity) | exact RR | exact KP6 | reflexivity | (clear - VB PSG0; lia) | (clear - FB' FSG0; lia)
              | (right; split; [exact RNZ| split; reflexivity])
              | (intros R0; exfalso; exact (RNZ R0))
              | idtac ].
      intros d1 d2 H1 H2 NE O1 O2. exfalso. rewrite (grp_init_noheap _ _ _ _ _ _ _ _ _ _ d1 H1) in O1. discriminate O1.
    - (* [comment removed for export] *)
      assert (RZ : r = 0).
      { clear - KR RR. Z.div_mod_to_equations. lia. }
      subst r.
      eapply (ep_setgrp h5 LB5 m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ id gj');
        first [ exact EB6 | exact (IDR eq_refl) | (clear - VB; lia) | (clear - FB'; lia) | idtac ].
    all: match goal with |- ?g => idtac "CL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkEP.
