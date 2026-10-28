(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_lset P_mpi_read_binary P_ecp_group_free P_ecp_red P_ecp_mul_mod P_ecp_derive_y P_ecp_point_read_binary.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_mpi_lset A_mpi_read_binary_stmt A_mpi_read_binary A_mpi_read_binary_le A_mpi_free A_mpi_set_bit A_mpi_bitlen A_ecp_mul_mod A_ecp_journey A_ecp_journey2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_read_binary_stmt_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_ecp_point_read_binary_c24 () : Init.string Init.list := ["Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_G"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_point_read_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_MUL_COUNT"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.EJ"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "PRB.PR_REGS"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey2.etri"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_xop_stmtA"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey2.eslot"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "PRB.PRI"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.point_read_PHIn"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.point_read_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_dy_sz"; "PRB.PR_POST"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt_c24.mpi_read_binary_stmtA_r_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_FR"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_read_binary.chars_to_limbs"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.derive_y_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.derive_y_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_derive_y.ECP_FEATURE_UNAVAILABLE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_grp_preA"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.grp_nle"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_SW_DERIVE_Y"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Z"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_set_bit.A_MPI_SET_BIT_E"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset.mpi_lset_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_READ_BINARY_LE"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_derive_y_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_point_read_binary_stmtA"].

Definition zchk_new : list Z := [0xcb414; 0xcb420; 0xcb424; 0xcb428; 0xcb4b0; 0xcb4d4; 0xcb4d8; 0xcb4dc; 0xcb4e0; 0xcb4e4; 0xcb570;
  0xcb58c; 0xcb590; 0xcb594; 0xcb620; 0xcb624; 0xcb628; 0xcb680; 0xcb6a0; 0xcb6a4; 0xcb6e0; 0xcb720].
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Local Ltac zchk_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail
      | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Local Ltac zlia := zchk_clear; lia.
Local Ltac zchk_dec :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; zlia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; zlia) ]
  | |- context [Z.leb ?a ?b] =>
      first [ replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; zlia)
            | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; zlia) ]
  end.
Local Ltac zchk_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zchk_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zchk_rec
  | _ => first [ reflexivity | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.leb_le; zlia | apply Z.leb_gt; zlia
               | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ]
  end.
Local Ltac zchk_ul :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia
         end.
Local Ltac zchk_solve :=
  rewrite ?zchk_land7; zchk_dec;
  first [ reflexivity
        | unfold_cond; fold_lit_ux; zchk_ul;
          rewrite ?OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.ZBridge.zb_lxor_ones by zlia; zchk_ul;
          rewrite ?zchk_land7; zchk_rec ].
Local Ltac zchk_if :=
  lazymatch goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xcb72c else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; zchk_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0xcb72c) _ _ _ _) =>
      replace c with true; [cbv_concl_iota | symmetry; zchk_solve]
  end.
Local Ltac zabsorb :=
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) zchk_new) with true => step; zsimp end
  end.
Local Ltac zpre := repeat (first [ zchk_if | zabsorb ]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Definition A_MPI_SIZE_PRB : Z := 0x9c91c.   (* [comment removed for export] *)
Section PRB.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variable MT : list modp_ent.
  Hypothesis HLSET : mpi_lset_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis HRB : mpi_read_binary_stmtA_r_c asegs R HIA A_MPI_READ_BINARY.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (G Q B : Z) (g : ecp_grp) (p : ecp_pt) (bs : list byte) (N lo d slo : Z).
  Local Notation MC := A_MUL_COUNT.
  Local Notation XO := [(Q, Q + 48); (MC, MC + 8)].
  Definition PR_REGS : list cell := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis EC0 : forall jk : list byte, ECA R HIA h LB LF m (bv_unsigned sp) lo 96 (C8 s10 :: PR_REGS) XO MC.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis D0 : 0 <= d.
  Hypothesis GAT : ecp_group_at asegs MT m LB G g.
  Hypothesis GCR : client_range L (LB ++ fdata LF) lo G 192.
  Hypothesis GSP : G + 192 <= lo \/ bv_unsigned sp <= G.
  Hypothesis GMC : MC + 8 <= G \/ G + 192 <= MC.
  Hypothesis PAT : ecp_point_at asegs m LB Q p.
  Hypothesis PNULL : Forall (fun e => md_own e = LNull) (pt_mpds p).
  Hypothesis PSG : Forall (fun e => md_sg e = 1 \/ md_sg e = -1) (pt_mpds p).
  Hypothesis QCW : client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) Q 48.
  Hypothesis QSP : Q + 48 <= lo \/ bv_unsigned sp <= Q.
  Hypothesis QMC : MC + 8 <= Q \/ Q + 48 <= MC.
  Hypothesis QUW : uw_obj R Q 48 d.
  Hypothesis QG : md_p (pt_X (g_G g)) <> 0 -> Q + 48 <= G \/ G + 192 <= Q.
  Hypothesis QGL : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "P,(0.(1.$2.(3.(4.(5.Vg,)))=))Pe,$6.P,(7.$6.R1.(8.Vg,))P,(1.$9.(:.R2.)$;.)(<.(=.(>.VQ,+30.)(3.R3.))(=.(>.(3.R3.)(?.+4.(10.R3.)))VQ,))")
(* [comment removed for export] *).
  Hypothesis SLO2 : lo <= bv_unsigned sp - 1504 - arl_need_ecp R.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis BUD : havol asegs R HIA h + point_read_PHIn N (Z.of_nat (length bs)) <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + point_read_FRn N d <= FR_MAX.

  Definition PR_POST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "(11.$12.VR,VHIA,VMT,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VG,Vg,VQ,Vp,Vbs,$13.VN,Vlo,Vd,Vm,Vmo,)")
(* [comment removed for export] *).
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -96)).

  (* [comment removed for export] *)
  Definition PRI (jk : list byte) (v f : Z) (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (dX dY dZ : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "(14.(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.O8.O7.O6.O5.O4.)(1>.VR,VHIA,VLB,VLF,O6.O5.O4.VQ,O3.(>.VQ,+10.)O2.(>.VQ,+20.)O1.))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L22286003249.6L27824359356.7L37622523289.6L54611064490.500000B00Y00k01<S1Q3off2O02O11a2HaS2sp1Q2lo3QSP3off2O02O1S1Q3off2O02O11x2HxS1Q3QMC3off2O02O1". (* [comment removed for export] *)
  #[using="QCW QSP QMC"] Lemma pr_slot : forall off, 0 <= off -> off + 16 <= 48 -> eslot R HIA h LB LF (bv_unsigned sp) lo XO MC (Q + off).
  Proof.
    intros off O0 O1. unfold eslot.
    split; [intros a Ha; apply QCW; clear - Ha O0 O1; lia|]. split; [clear - QSP O0 O1; lia|].
    split; [intros x Hx; cbn [outside fst snd] in *; split; [clear - Hx O0 O1; lia| exact I]| clear - QMC O0 O1; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation EJ0 := (EJ R HIA h LB LF m (bv_unsigned sp) lo 96 (C8 s10 :: PR_REGS) XO MC).
  Local Notation TRI := (etri R HIA LB LF).
  Local Notation SLOT := (eslot R HIA h LB LF (bv_unsigned sp) lo XO MC).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L10013910539.3L10014387595.4L10014387595.7L19002855022.6L27060592511.3L37009172011.3L37009255851.4L37009255851.7L43781953404.6L43782036732.2L59617066704.600000100200300@00I00J00K00L00M00U00mFFFS1R5NEEDR3NERS1Q2X02ZBFFFFS2sp3SPRS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  #[using="HIA h LB LF m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 p EC0 PAT SLO2"] Lemma pr_base : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "(14.(=.=Vlo,)(14.(=.Vlo,(1?.(16.&40.Vsp,)+5>0.))(14.(20.(16.&40.Vsp,)(21.+2.+40.))(14.(=.=(22.VR,))(14.(=.(23.VR,)Vlo,)(14.(20.=VQ,)(=.(>.VQ,+30.)(21.+2.+40.))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof (EC0 []) as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC (EC0 [])) as (LO0 & ALO & ACP & MCLO & SPHI).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (arl_need_ecp_rt R) as NER.
    assert (QB : 0 < Q /\ Q + 48 <= 2^64).
    { ddestruct PAT as (EX & _ & EZ & MX & _ & MZ). ddestruct MX as (_ & _ & X0 & _). destruct MZ as (CZ & _).
      pose proof (rw_cells_bound _ _ _ _ CZ) as ZB. unfold mpi_cells in ZB. cbn [cells_size csize Nat.add] in ZB. rewrite EX in X0. rewrite EZ in ZB. clear - X0 ZB. lia. }
    repeat split; try assumption; first [clear - SLO2 NER NEEDR; lia | clear - SPR; lia | clear - NER NEEDR; lia | exact (proj1 QB) | exact (proj2 QB)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="PAT"] Lemma pr_qal : Q mod 8 = 0.
  Proof. ddestruct PAT as (EX & _ & _ & MX & _ & _). ddestruct MX as (_ & AL8 & _). rewrite EX in AL8. exact AL8. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L16015024961.3 L16321903457.1 L18975063279.5 L22352253106.7 L27214106967.5 L29558281123.9 L3813375827.10 L42254643250.5 L46815531094.3 L58331465648.1 L66151427842.16L6966896546.3  00000<00?00O00l01<01X02602K02U02Y03303?S2sp2lo4LOSPS1QS1R1Q2A13QA23GU1S1R2sp2lo4SLO25STACK4HSTK3NERS1R3HIA1h2sp3TOPS1R3HIA1h1d3FRC1f2hk2HF4HFRkS1R3HIA1h3PHI1v2hk2d11z2HV3HVkS2sp2lo3LO04LOSP4SP64S1Q2Q03Q48S2spS2sp2r03SPA1q1r1H2H02q02H4S2sp2lo4LOSP". (* [comment removed for export] *)
  #[using="p EC0 TPV PAT QUW SLO2 SPA"] Lemma pr_xop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "PENTRY,$2.PSTACK,$2.PPX,P,$2.SpPPHI,P,$6.P,$2.$2.PFRC,P,$2.$2.PRr,P,(24.$25.)P,$6.P,$2.P,$2.P,$6.SpP,(26.$12.VR,VHIA,R6.R5.R4.R3.R2.R1.)Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.Pz,$2.PRET,$2.Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pc1,(27.&40.)Pxa0,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pc2,(27.&40.)Pc3,(27.&40.)Pc4,(27.&40.)Pc5,(27.&40.)Pc6,(27.&40.)Pc7,(27.&40.)Pc8,(27.&40.)Pc9,(27.&40.)Pc10,(27.&40.)Pc11,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)PQ',P,$2:.SpP,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R27.R26.R25.R24.R23.)P,(1>.VR,VHIA,VLB,VLF,R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R24.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R23.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R22.)P,(<.(=.(>.R27.+10.)R25.)(=.(>.R25.+10.)R27.))P,(<.(=.(>.R28.+10.)R24.)(=.(>.R24.+10.)R28.))P,(=.VQ,R29.)P,(=.(>.R2:.+10.)(>.VQ,+30.))P,A1.R36.R25.P,(=.R38.+480.)P,(=.=A2.R37.R2<.R27.)P,(=.=A1.R37.Vd,)P,(=.(>.(2<.$12.VR,VHIA,Vh,)(>.R34.A2.R39.R2>.R29.))$2=.)P,(=.(>.(2>.$12.VR,VHIA,Vh,)(>.R34.A1.R39.Vd,))$2?.)P,(14.(=.=R2:.)(20.R2:.(21.+2.+40.)))P,(1.$2.(30.R2;.+2.)=)P,Ph',(28.$12.VR,VHIA,)PLB',(24.$25.)Pm',P,(27.&40.)(29.(27.&8.))Pd1',$6.Pr,$2.Pt0',(27.&40.)Pt1',(27.&40.)Pt2',(27.&40.)Pa1',(27.&40.)Pa2',(27.&40.)Pa3',(27.&40.)Pa4',(27.&40.)Pa5',(27.&40.)Pa6',(27.&40.)Pa7',(27.&40.)Pt3',(27.&40.)Pt4',(27.&40.)Pt5',(27.&40.)Pt6',(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.(>.R4;.A2.R50.R45.R40.)(>.R4:.A1.R4?.Vd,)R13.R12.R11.)P,(1>.VR,VHIA,VLB,VLF,R14.R13.R12.R47.R11.R45.R44.R43.R42.)P,A5.R50.R4:.R47.R42.R11.R12.(31.$12.(32.$12.VR,VHIA,R16.Vmo,)R28.(33.(34.(35.&40.R42.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R11.R10.R?.(35.&40.VQ,)R3>.(35.&40.R12.)R>.R=.R<.R;.R:.R9.R8.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R7.R6.R5.R4.)VF,(35.&40.R42.)Vfc,(36.(27.&40.))R14.(37.$12.)))P,(1.(27.&40.)R28.(35.&40.R34.))(31.$12.(32.$12.VR,VHIA,R38.Vmo,)R14.(33.(34.(35.&40.R2>.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R2=.R2<.R2;.(35.&40.VQ,)R2:.R29.(35.&40.R2?.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)VF,(35.&40.R42.)Vfc,(36.(27.&40.))R36.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros ENTRY STACK PX PHI FRC Rr HC. intros until Q'. intros J T S1 S2 S3 S12 S13 QA1 QA2 HPX HSTK HPHI HFRC HV HF HRET HRE K E0. subst xa0.
    pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. pose proof (arl_need_ecp_rt R) as NER.
    pose proof T as (T1 & _). dpose S1 as (CW1 & SL1 & _ & _).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk A1 d1 (bv_unsigned sp + -96) J T1 CW1 SL1 ltac:(clear - LOSP; lia))
      as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (UW1 : uw_obj R A1 16 d) by (destruct QUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1 QA2; lia| exact GU2]| right; exact GU]).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_xop_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (v := z) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by (clear - LO0 LOSP SP64; lia).
      - exact HHk.
      - exact HK1.
      - exact XM.
      - exact XNS.
      - exact HPX.
      - exact XWR.
      - exact XLSq.
      - replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 HSTK NER. lia.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - clear - HV HVk. lia.
      - eapply uw_obj_uwc; [exact QUW| rewrite unsigned_lit by (clear - Q0 Q48; lia); clear; lia].
      - rewrite XAD. exact UW1.
      - clear - HF HFRk. lia.
      - rewrite XAD. reflexivity.
      - reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HP2 by (clear - LO0 LOSP SP64; lia). rewrite XAD in HP2.
    rewrite (ret_pc_even RET HRET HRE).
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in ST2' by (clear; lia).
    destruct (etri_call R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk A1 d1 A2 d2 A3 d3 m2 h2 LB2 dX2 (bv_unsigned sp + -96) (PHI d1 z) (FRC d)
                J T S1 S2 S3 S12 S13 ltac:(clear - LOSP; lia) HPHI HFRC MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 FRA2) as [J2 T2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; eassumption.
    all: match goal with |- ?g => idtac "XOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L35693534892.2L39595771183.7L52615975131.5L52938123213.3L59314923118.6L60900445136.300000700O00\00c01201;S1G3GMCS1R3DI13DI23MC13MC21e2BIS2sp1G1a2Ha1KS1Q1e1KS1G2lo1a2Ha1S1KS1G1Q3QGs". (* [comment removed for export] *)
  #[using="EC0 GAT GCR GSP GMC QG QGL"] Lemma pr_grp : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R5.R4.R3.R2.R1.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))(38.$12.VMT,R3.R4.VG,Vg,)")
(* [comment removed for export] *).
  Proof.
    intros jk v f hk LBk mk J GXNZ. pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
    { intros a Ha. destruct (GCR a Ha) as [S|[D|Bk]]; [| right; left; exact D| right; right; exact Bk].
      destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    pose proof (QG GXNZ) as QGs.
    eapply (ecp_group_at_presx asegs L MT m mk (LB ++ fdata LF) LBk (bv_unsigned sp) XO G g).
    - ddestruct GAT as (HD & GAL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & REST).
      pose proof (fun e (Hm : mpdr_at asegs m LB e) => mpdr_at_LB_one asegs m LB (LB ++ fdata LF) e Hm) as RB.
      assert (RB' : forall e, mpdr_at asegs m LB e -> mpdr_at asegs m (LB ++ fdata LF) e).
      { intros e Hm. apply RB; [exact Hm|]. intros EO. ddestruct Hm as (_ & _ & _ & _ & _ & OW). rewrite EO in OW. apply in_or_app. left. exact (proj1 (proj2 OW)). }
      split; [exact HD|]. split; [exact GAL|]. split; [exact POS|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EN|].
      split; [exact (RB' _ MP)|]. split; [exact (RB' _ MA)|]. split; [exact (RB' _ MB)|].
      split; [exact (conj EX (conj EY (conj EZ (conj (RB' _ MX) (conj (RB' _ MY) (RB' _ MZ))))))|].
      split; [exact (RB' _ MN)| exact REST].
    - exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXk).
    - exact MIm.
    - exact MIk.
    - exact CRS.
    - cbn [disjoint_from fst snd]. split; [clear - QGs; lia| split; [clear - GMC; lia| exact I]].
    - intros e He EO. pose proof (grp_blocks_in asegs MT m LB G g e GAT He EO) as IN. split; [exact (SUBk _ IN)|].
      destruct (hm_apart asegs R HIA h LB LF m HH) as [HF0 _]. rewrite Forall_forall in HF0.
      destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (_ & _ & _ & BI). cbn [fst snd] in BI. ddestruct MCOK as (MC1 & MC2 & _).
      cbn [disjoint_from fst snd]. split; [pose proof (QGL GXNZ e He EO) as K; clear - K; lia| split; [destruct DIMG as [DI1 DI2]; clear - BI MC1 MC2 DI1 DI2; lia| exact I]].
    all: match goal with |- ?g => idtac "GRP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@L19687428440.171L20775533352.9  L25465666776.171L28125529944.171L29025845208.171L31686769240.171L35663928186.7  L36180290948.1  L52253708504.171L57978561187.1  L60098763854.3  L60536975922.1  L60692334296.171L61063055714.9  L61601561944.171L62134525906.4  L62505661912.171L64270350808.171L65178513496.171Q15645341323.174Q18359718027.174Q18380971240.174Q21890219752.174Q24383187816.174Q27595506315.174Q27909213544.174Q30400477672.174Q31256953867.174Q32657489291.174Q33911823336.174Q36436182120.174Q3836573544.174 Q39937631848.174Q41141761931.174Q44655022603.174Q4544190859.174 Q51221294859.174Q59241966347.174Q59828537611.174Q66536663272.174Q9837151720.174 00000>00X00f01401B01P01e01i02702;02E02I02W03103?03K03Y03g04504C04Q04d05705J05X05k06>06L06Z06m07@07S07f08408B08P08^08l09:09M09`S2ra2sp2jk3JK8S1R3HIA1h2bs1N1v2hk2HV3HVkS2ra2sp2jk3JK8S2ra2sp2jk3JK8S2ra2sp2jk3JK8S2ra2sp2jk3JK8S1R3HIA1h2sp2lo3TOP1HS2spS2ra2sp2jk3JK8S2spS1R2lo3LOSS2spS2ra2sp2jk3JK8S1R3HIA1h1N1d1f2hk2HF4HFRkS2ra2sp2jk3JK8S2sp2lo4LOSPS2ra2sp2jk3JK8S2ra2sp2jk3JK8S2ra2sp2jk3JK8S2sp2lo2jk3JK8S2sp2lo2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo2jk3JK8S2sp2lo2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo2jk3JK8S2sp2lo2jk3JK8S2sp2lo2jk3JK8S2sp2lo2jk3JK8S2sp2lo2jk3JK8S2sp2lo2jk3JK8S2sp2lo4LOSP2jk3JK8S2sp2lo4LOSP2jk3JK8". (* [comment removed for export] *)
  #[using="IMG EC0 GAT GCR GSP GMC PAT QG QGL SLO2"] Lemma pr_exit : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PdX,$6.PdY,$6.PdZ,$6.Pr,$2.Pxra,(27.&40.)Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxs0',(27.&40.)Pxs1,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxs2,(27.&40.)Pxs3,(27.&40.)Pxs4,(27.&40.)Pxs5,(27.&40.)Pxs6,(27.&40.)Pxs7,(27.&40.)Pxs8,(27.&40.)Pxs9,(27.&40.)Pxs10,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(1.$39.(3:.(27.&8.)R24.)#8.)P,(3;.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(14.(20.(3<.(21.+2.+1?.))R1>.)(=.R1>.=))P,(=.R27.(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.R27.(3?.VN,Vd,))P,P,(1.$2.R21.=)(14.(=.(10.R25.)(40.VN,))(14.(=.(10.R24.)(40.VN,))(=.(10.R23.)(40.VN,))))(31.$12.(32.$12.VR,VHIA,R28.Vmo,)$41.(33.(34.R21.(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R20.R1?.R1>.R1=.R1<.(35.&40.R22.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.Vs11,R;.R:.R9.R8.)VF,(35.&40.+<;6?4.)Vfc,(36.(27.&40.))R26.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros until xt6. intros JK8 [J T] GXNZ HR HV HF SZS. basic_factsA hk.
    pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose T as ((MXk & EAX & NSX & FRSX & OAX) & (MYk & EAY & NSY & FRSY & OAY) & (MZk & EAZ & NSZ & FRSZ & OAZ) & D12 & D13 & D23 & COV).
    pose proof (pr_grp jk v f hk LBk mk J GXNZ) as GATk.
    pose proof (hm_top asegs R HIA hk LBk LF mk HHk) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HSk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (stk_release asegs mk lo (bv_unsigned sp - 96) (C8 s10 :: PR_REGS) STk FRk ltac:(clear - LOSP LO0; lia)) as STR.
    unfold PR_REGS in FRk, STR. cbn [cells_size csize Nat.add] in STR. replace (bv_unsigned sp - 96 + Z.of_nat 96) with (bv_unsigned sp) in STR by (clear; lia).
    replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FRk, STk by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    pose proof (conj MCk I) as MCbox. pose proof (conj GATk I) as GRbox. pose proof (conj MXk (conj MYk (conj MZk I))) as MXbox. clear J T MXk MYk MZk MCk GATk.
    do 11 zstep.
    zstep.
    replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold PR_POST, ecp_point_read_postA.
    destruct MCbox as [MC1' _]. destruct GRbox as [GR1' _]. ddestruct MXbox as (MX' & MY' & MZ' & _).
    deexists 14. dexists mk, mo9, hk, LBk, (mkPT dX dY dZ), r, ck.
    split; [reflexivity|]. split; [exact MIk|]. split; [exact STR|]. split; [exact MF9|]. split; [exact PXk|].
    split; [exact HTk|]. split; [exact HSk|]. split; [exact HFk|]. split; [exact HK9|]. split; [exact HCSk|].
    split; [clear - HVk HV; lia|]. split; [clear - HFRk HF; lia|]. split; [exact HHk|].
    split; [unfold ecp_point_at; cbn [pt_X pt_Y pt_Z]; exact (conj EAX (conj EAY (conj EAZ (conj (proj1 MX') (conj (proj1 MY') (proj1 MZ'))))))|].
    split; [unfold pt_freeable, pt_mpds, mpd_freeable; cbn [pt_X pt_Y pt_Z]; repeat (apply Forall_cons; [assumption|]); apply Forall_nil|].
    split; [unfold pt_mpds; cbn [pt_X pt_Y pt_Z]; apply Forall_cons; [exact (proj2 MX')| apply Forall_cons; [exact (proj2 MY')| apply Forall_cons; [exact (proj2 MZ')| apply Forall_nil]]]|].
    split; [unfold pt_dis; cbn [pt_X pt_Y pt_Z]; split; [intros O1 O2 E; injection E as E1 _; exact (D12 O1 O2 E1)| split; [intros O1 O2 E; injection E as E1 _; exact (D13 O1 O2 E1)| intros O1 O2 E; injection E as E1 _; exact (D23 O1 O2 E1)]]|].
    split; [intros R0; ddestruct (SZS R0) as (SZX & SZY & SZZ); unfold pt_mpds; cbn [pt_X pt_Y pt_Z]; apply Forall_cons; [exact SZX| apply Forall_cons; [exact SZY| apply Forall_cons; [exact SZZ| apply Forall_nil]]]|].
    split; [exact SUBk|].
    split; [intros b Hb; destruct (COV b Hb) as [K|K]; [left; exact K| right; unfold pt_blocks, pt_mpds; cbn [pt_X pt_Y pt_Z flat_map]; rewrite app_nil_r; exact K]|].
    split.
    { intros b Hb. unfold pt_blocks, pt_mpds in Hb. cbn [pt_X pt_Y pt_Z flat_map] in Hb. rewrite app_nil_r in Hb. rewrite !in_app_iff in Hb.
      destruct Hb as [Hb|[Hb|Hb]]; [exact (FRSX b Hb)| exact (FRSY b Hb)| exact (FRSZ b Hb)]. }
    split; [exact GR1'|]. split; [exact MC1'|].
    split; [intros C; exfalso; exact (GXNZ C)| exact HR].
    all: match goal with |- ?g => idtac "EXIT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis BYT : bytes_at asegs m B bs.
  Hypothesis B0 : 0 < B.
  Hypothesis B63 : B + Z.of_nat (length bs) < 2^63.
  Hypothesis BCR : client_range L (LB ++ fdata LF) lo B (Z.of_nat (length bs)).
  Hypothesis BSP : B + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= B.
  Hypothesis BQ : B + Z.of_nat (length bs) <= Q \/ Q + 48 <= B.
  Hypothesis BMC : MC + 8 <= B \/ B + Z.of_nat (length bs) <= MC.
  Hypothesis BOB : Z.of_nat (length bs) = 0 \/ aobj asegs AL (hcs asegs R HIA h) m B (Z.of_nat (length bs)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L17396075838.3L50790580594.6L52615975131.6L5281856140.4 L59314923118.700000:00K00[00f018S1B2bs3BMCS1R2sp2lo3LOS3SLOS2sp1B2bs1a2Ha1KS1Q1B2bs2BQS1B2bs2lo1a2Ha1S1K". (* [comment removed for export] *)
  #[using="EC0 BYT BCR BSP BQ BMC BOB"] Lemma pr_bytes : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R5.R4.R3.R2.R1.)(14.(42.$12.R2.VB,Vbs,)(14.(43.(44.VR,)(45.$25.R3.(46.VLF,))Vlo,VB,(3>.(3:.(27.&8.)Vbs,)))(<.(1.$2.(3>.(3:.(27.&8.)Vbs,))=)(47.$12.(48.VR,)(49.$12.VR,VHIA,R4.)R2.VB,(3>.(3:.(27.&8.)Vbs,))))))")
(* [comment removed for export] *).
  Proof.
    intros jk v f hk LBk mk J. pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) B (Z.of_nat (length bs))).
    { intros a Ha. destruct (BCR a Ha) as [S|[D|Bk]]; [| right; left; exact D| right; right; exact Bk].
      destruct BSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    split.
    - eapply (presA_bytes_at asegs R); [exact PXk| exact BYT| exact CRS|].
      cbn [disjoint_from fst snd]. split; [clear - BQ; lia| split; [clear - BMC; lia| exact I]].
    - split.
      + intros a Ha. destruct (BCR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [| exact Hr]].
        apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBk b Hb)| right; exact Hb].
      + destruct BOB as [Z0|OB]; [left; exact Z0| right].
        eapply aobj_cs_mono; [exact HCSk|].
        eapply (presA_aobj0 asegs R); [exact (hcs_ok asegs R HIA h)| exact PXk| exact OB| intros x Hx; eapply hcs_below_top; exact Hx|].
        right. split; [exact CRS| clear - LOS SLO FR0; lia].
    all: match goal with |- ?g => idtac "BYTES-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L36174425776.77L36955947269.7700000a01MS2ra2sp1G1Q1B2bs3GMC3QMC2BQ3BMC1A1l1i1k2Hi2Hk3HikS2ra2sp1G1Q1B2bs3GMC3QMC2BQ3BMC1l1i1k2Hi3Hik". (* [comment removed for export] *)
  #[using="ra sp G Q B bs GMC QMC BQ BMC"] Lemma bytes_at_subA : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pmm,P,(27.&40.)(29.(27.&8.))PA,$2.Pl,(24.(27.&8.))Pi,$2.Pk,$2.P,(42.$12.R5.R4.R3.)P,(=.=R3.)P,(=.=R3.)P,(=.(>.R5.R4.)(3>.(3:.(27.&8.)R6.)))(14.(42.$12.R9.(>.R8.R6.)(4:.(27.&8.)(4;.R5.)(4<.(27.&8.)(4;.R6.)R7.)))(1.$39.(3:.(27.&8.)(4:.(27.&8.)(4;.R5.)(4<.(27.&8.)(4;.R6.)R7.)))(4;.R5.)))")
(* [comment removed for export] *).
  Proof.
    intros mm A l i k H Hi Hk Hik. split; [| rewrite firstn_length, skipn_length; lia].
    rewrite <- (firstn_skipn (Z.to_nat i) l) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite firstn_length in H.
    replace (A + Z.of_nat (Nat.min (Z.to_nat i) (length l))) with (A + i) in H by lia.
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) l)) in H. apply bytes_at_app in H. exact (proj1 H).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis B47 : Z.of_nat (length bs) = 0 \/ B + Z.of_nat (length bs) + 8 <= 2^47.

  Hypothesis C24H : cnt24 LB + C24_ECP_POINT_READ <= C24MAX.     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L15756354262.4 L16015024961.3 L18975063279.5 L22110851875.4 L25373077975.9 L27214106967.5 L27455238532.2 L3239433262.11 L40741407973.3 L41724633378.6 L42254643250.5 L42256698918.7 L4923939807.7  L4957641651.5  L51159590045.4 L5246360089.2  L53258413131.12L58331465648.1 L59308873939.3 L60200447195.9 L61953102669.8 L64491265552.2 L66151427842.16L66254310303.8 L66558098759.2 L6966896546.3  L977192228.8   00000>00J00Z00i01>01N01U02502A02R02g03<03Q03c04504<04b04f05105H05c05i06C06[06b06n07ES1R2lo3LOS3ALOS2sp2lo4LOSPS1R1Q2A13QA23GU1S1B2B03off4HOFFS1B2bs2d13off4HOFF2K1S1R3HIA1h2sp3TOPS1k3HK0S2sp1B2bs2lo3BSP3off1k4HOFF4HLENS1B3off4HOFFS1B2bs3off1k4HLENS2sp2lo3LO04LOSP4SP64S1B2bs3B633off1k4HLENS1B2bs3off1k4HLEN3K47S1R2sp2lo4SLO23NERS2LB4C24H3LBk4C24kS2d12N1S1Q1B2bs2BQ2A13off1k3QA13QA24HOFF4HLENS2spS2bs3HLP2Z0S1B2bs2d13off1k4HLEN2K1S1B2bs3off1k4HOFF4HLEN1a2HaS1d2D0S2sp2r03SPA1q1r1H2H02q02H4S1R3HIA1h1d1f2hk2HF4HFRkS1k3HK0S2sp2lo4LOSPS1R3HIA1h1v2hk1k2HV3HVk". (* [comment removed for export] *)
  #[using="G p EC0 TPV D0 GMC PAT QMC QUW SLO2 SPA BYT B0 B63 BCR BSP BQ BMC BOB B47 C24H"] Lemma pr_rb : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "PENTRY,$2.P,(4=.$12.VR,VHIA,R1.)Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.Poff,$2.Pk,$2.PRET,$2.Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pc1,(27.&40.)Pxa0,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pc2,(27.&40.)Pc3,(27.&40.)Pc4,(27.&40.)Pc5,(27.&40.)Pc6,(27.&40.)Pc7,(27.&40.)Pc8,(27.&40.)Pc9,(27.&40.)Pc10,(27.&40.)Pc11,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)PQ',P,$2:.SpP,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R29.R28.R27.R26.R25.)P,(1>.VR,VHIA,VLB,VLF,R28.R27.R26.R25.R24.R23.R22.R21.R20.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R26.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R25.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R24.)P,(<.(=.(>.R29.+10.)R27.)(=.(>.R27.+10.)R29.))P,(<.(=.(>.R2:.+10.)R26.)(=.(>.R26.+10.)R2:.))P,(=.VQ,R2;.)P,(=.(>.R2<.+10.)(>.VQ,+30.))P,(=.=R27.)P,(=.=R27.)P,(=.(>.R29.R28.)(3>.(3:.(27.&8.)Vbs,)))P,(20.=(3>.(3:.(27.&8.)Vbs,)))P,(=.(>.(2<.$12.VR,VHIA,Vh,)(>.R36.(4>.R2:.)))$2=.)P,(=.(>.(2>.$12.VR,VHIA,Vh,)(>.R36.(4?.Vd,)))$2?.)P,(14.(=.=R2;.)(20.R2;.(21.+2.+40.)))P,(1.$2.(30.R2<.+2.)=)P,Ph',(28.$12.VR,VHIA,)PLB',(24.$25.)Pm',P,(27.&40.)(29.(27.&8.))Pd1',$6.Pr,$2.Pt0',(27.&40.)Pt1',(27.&40.)Pt2',(27.&40.)Pa1',(27.&40.)Pa2',(27.&40.)Pa3',(27.&40.)Pa4',(27.&40.)Pa5',(27.&40.)Pa6',(27.&40.)Pa7',(27.&40.)Pt3',(27.&40.)Pt4',(27.&40.)Pt5',(27.&40.)Pt6',(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.(>.R4=.(4>.R41.))(>.R4<.(4?.Vd,))R13.R12.R11.)P,(1>.VR,VHIA,VLB,VLF,R14.R13.R12.R49.R11.R47.R46.R45.R44.)P,(<.(1.$2.R11.=)(1.$2.R11.$50.))P,P,(1.$2.R12.=)(14.(1.$2.(51.R14.)+1.)(1.$2.(10.R14.)(52.R45.)))(31.$12.(32.$12.VR,VHIA,R17.Vmo,)R29.(33.(34.(35.&40.R44.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R12.R11.R10.(35.&40.VQ,)R40.(35.&40.R13.)R?.R>.R=.R<.R;.R:.R9.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R8.R7.R6.R5.)VF,(35.&40.R44.)Vfc,(36.(27.&40.))R15.(37.$12.)))P,(1.(27.&40.)R29.(35.&40.R36.))P,(1.(27.&40.)R29.(35.&40.(>.VB,R31.)))P,(1.(27.&40.)R29.(35.&40.R31.))(31.$12.(32.$12.VR,VHIA,R3<.Vmo,)R16.(33.(34.(35.&40.R31.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R30.R2?.R2>.(35.&40.VQ,)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)VF,(35.&40.R41.)Vfc,(36.(27.&40.))R3:.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros ENTRY HRBG. intros until Q'. intros J T S1 S2 S3 S12 S13 QA1 QA2 HOFF HK0 HLEN HLP HV HF HRET HRE K E0 E1 E2. subst xa0 xa1 xa2.
    pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. pose proof (arl_need_ecp_rt R) as NER.
    pose proof T as (T1 & _). dpose S1 as (CW1 & SL1 & _ & _).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk A1 d1 (bv_unsigned sp + -96) J T1 CW1 SL1 ltac:(clear - LOSP; lia))
      as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (pr_bytes jk v f hk LBk mk J) as (BYk & BCRk & BOBk).
    destruct (bytes_at_subA mk B bs off k BYk HOFF HK0 HLEN) as [IBY ILEN].
    set (ibs := firstn (Z.to_nat k) (skipn (Z.to_nat off) bs)) in *.
    assert (ILZ : Z.of_nat (length ibs) = k) by (rewrite ILEN; clear - HK0; lia).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    pose proof (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC v f hk LBk mk A1 d1 J T1) as BLK1.
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    assert (UW1 : uw_obj R A1 16 d) by (destruct QUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1 QA2; lia| exact GU2]| right; exact GU]).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HRBG as HC. unfold mpi_read_binary_stmtA_r_c in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (B := B + off) (ibs := ibs) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by (clear - LO0 LOSP SP64; lia); rewrite ?ILZ.
      - exact HHk.
      - exact HK1.
      - exact (proj1 XM).
      - exact XNS.
      - exact XWR.
      - exact IBY.
      - clear - B0 HOFF. lia.
      - clear - B63 HOFF HLEN. lia.
      - intros a Ha. apply BCRk. clear - Ha HOFF HLEN. lia.
      - rewrite XAD. clear - BQ QA1 QA2 HOFF HLEN HK0. lia.
      - intros EO. ddestruct (BLK1 EO) as (_ & N1 & _ & _ & _ & _ & FRA).
        destruct (fresh_apart_client R LB LF lo B (Z.of_nat (length bs)) _ _ FRA BCR HLP ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K1|K1]; [right| left]; clear - K1 HOFF HLEN HK0; lia.
      - clear - BSP HOFF HLEN HK0 LOSP. lia.
      - right. destruct B47 as [Z0|K47]; [exfalso; clear - Z0 HLP; lia| clear - K47 HOFF HLEN; lia].
      - replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 NER. lia.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - rewrite XAD. pose proof (proj1 XAO) as OX. rewrite XAD in OX. exact OX.
      - destruct BOBk as [Z0|OB]; [exfalso; clear - Z0 HLP; lia| eapply aobj_sub; [exact OB| clear - HOFF; lia| clear - HOFF HLEN; lia]].
      - clear - HV HVk. lia.
      - rewrite XAD. exact UW1.
      - clear - HF HFRk. lia.
      - dpose T as (_ & _ & _ & _ & _ & _ & COVc).
        pose proof (ej_cnt24 R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk [d1; d2; d3] J ltac:(intros b Hb; destruct (COVc b Hb) as [Kc|Kc]; [left; exact Kc| right; cbn [flat_map]; rewrite app_nil_r; exact Kc])) as C24k.
        cbn [length] in C24k. unfold C24_RB_c. unfold C24_ECP_POINT_READ in C24H. clear - C24H C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_read_binary_postA_c in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & RC2 & ROK2 & FRA2 & CNT2).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HP2 by (clear - LO0 LOSP SP64; lia). rewrite XAD in HP2. rewrite ?ILZ in HV2.
    rewrite (ret_pc_even RET HRET HRE).
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in ST2' by (clear; lia).
    destruct (etri_call R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk A1 d1 A2 d2 A3 d3 m2 h2 LB2 dX2 (bv_unsigned sp + -96) (MPI_RB_PHI k) (MPI_RB_FR d)
                J T S1 S2 S3 S12 S13 ltac:(clear - LOSP; lia) ltac:(unfold MPI_RB_PHI; unfold AVOL_CALL; clear - HK0; lia) ltac:(unfold MPI_RB_FR, fr_charge; clear - D0; lia)
                MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 FRA2) as [J2 T2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J2| exact T2| exact RC2| rewrite ILZ in ROK2; exact ROK2].
    all: match goal with |- ?g => idtac "RB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L40669651966.74L59308586248.7600000?00NS2ra2sp2bs1A2H1S2ra2sp2bs1i2Hi". (* [comment removed for export] *)
  #[using="ra sp bs"] Lemma rw_cells_nilA : forall mm A, 0 <= A -> A <= 2^64 -> rw_cells asegs mm A [].
  Proof.
    intros mm A H0 H1. unfold rw_cells. split.
    - unfold cells_at. cbn. split; [exact I|]. unfold bytes_at. cbn [length Z.of_nat]. split; [exact H0| split; [lia| intros i Hi; exfalso; cbn in Hi; lia]].
    - unfold wr_at. cbn [cells_size Z.of_nat]. split; [exact H0| split; [lia| intros i Hi; exfalso; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L4254243367.300000;S2sp2lo3SLO". (* [comment removed for export] *)
  #[using="ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 EC0"] Lemma pr_ec_pop : ECA R HIA h LB LF m (bv_unsigned sp) lo 0 [] XO MC.
  Proof.
    pose proof (EC0 []) as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    constructor; try assumption; try reflexivity; clear - SLO; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L22566150223.5L23834689196.5L29419287348.1L62134525906.400000@00I00M00YS2sp2lo3LO04LOSPS2sp4SP64S2spS2sp2lo4LOSP". (* [comment removed for export] *)
  #[using="p bs EC0 PAT SLO2"] Lemma pr_pop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R5.R4.R3.R2.R1.)(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,=(1=.$18.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros jk v f hk LBk mk [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    constructor; try assumption.
    - pose proof (stk_release asegs mk lo (bv_unsigned sp - 96) (C8 s10 :: PR_REGS) STk FRk ltac:(clear - LOSP LO0; lia)) as STR.
      unfold PR_REGS in STR. cbn [cells_size csize Nat.add] in STR. replace (bv_unsigned sp - 96 + Z.of_nat 96) with (bv_unsigned sp - 0) in STR by (clear; lia). exact STR.
    - apply rw_cells_nilA; clear - LO0 LOSP SP64; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L20775533352.9L35693534892.2L39595771183.7L52615975131.5L52938123213.3L59314923118.6L60726810988.1L60900445136.3L61063055714.900000J00Q00i01601=01L01P01Y023S1R3HIA1h2bs1N1v2hk2HV3HVkS1G3GMCS1R3DI13DI23MC13MC21e2BIS2sp1G1a2Ha1KS1Q1e1KS1G2lo1a2Ha1S1KS2spS1G1Q3QGsS1R3HIA1h1N1d1f2hk2HF4HFRk". (* [comment removed for export] *)
  #[using="EC0 GAT GCR GSP GMC QG QGL"] Lemma pr_post_of : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PdX,$6.PdY,$6.PdZ,$6.Pr,$2.Pmo9,$53.Py0,(27.&40.)Py1,(27.&40.)Py2,(27.&40.)Pya1,(27.&40.)Pya2,(27.&40.)Pya3,(27.&40.)Pya4,(27.&40.)Pya5,(27.&40.)Pya6,(27.&40.)Pya7,(27.&40.)Py3,(27.&40.)Py4,(27.&40.)Py5,(27.&40.)Py6,(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,=(1=.$18.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R18.R17.R16.R15.R14.)P,(1>.VR,VHIA,VLB,VLF,R17.R16.R15.VQ,R14.(>.VQ,+10.)R13.(>.VQ,+20.)R12.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(14.(20.(3<.(21.+2.+1?.))R13.)(=.R13.=))P,(=.R1<.(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.R1<.(3?.VN,Vd,))P,P,(1.$2.R16.=)(14.(=.(10.R1:.)(40.VN,))(14.(=.(10.R19.)(40.VN,))(=.(10.R18.)(40.VN,))))P,(54.$12.VR,VHIA,R1=.R16.)P,(55.Vmo,R17.)(41.(56.(33.(34.Vra,Vsp,Vgp,Vtp,R17.R16.R15.Vs0,Vs1,(35.&40.R19.)R14.R13.R12.R11.R10.R?.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(57.Vra,)Vfc,(36.(27.&40.))R1=.(37.$12.))R18.))")
(* [comment removed for export] *).
  Proof.
    intros until y6. intros J T GXNZ HR HV HF SZS HK9 MF9.
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose T as ((MXk & EAX & NSX & FRSX & OAX) & (MYk & EAY & NSY & FRSY & OAY) & (MZk & EAZ & NSZ & FRSZ & OAZ) & D12 & D13 & D23 & COV).
    assert (GATk : ecp_group_at asegs MT mk LBk G g).
    { pose proof (EC0 []) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
      assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
      { intros a Ha. destruct (GCR a Ha) as [S|[D|Bk]]; [| right; left; exact D| right; right; exact Bk].
        destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
      pose proof (QG GXNZ) as QGs.
      eapply (ecp_group_at_presx asegs L MT m mk (LB ++ fdata LF) LBk (bv_unsigned sp) XO G g);
        [| exact (presA_presx asegs R _ _ _ _ _ _ _ _ PXk)| exact MIm| exact MIk| exact CRS| cbn [disjoint_from fst snd]; split; [clear - QGs; lia| split; [clear - GMC; lia| exact I]]|].
      - ddestruct GAT as (HD & GAL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & REST).
        assert (RB' : forall e, mpdr_at asegs m LB e -> mpdr_at asegs m (LB ++ fdata LF) e).
        { intros e Hm. apply (mpdr_at_LB_one asegs m LB); [exact Hm|]. intros EO. ddestruct Hm as (_ & _ & _ & _ & _ & OW). rewrite EO in OW. apply in_or_app. left. exact (proj1 (proj2 OW)). }
        split; [exact HD|]. split; [exact GAL|]. split; [exact POS|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EN|].
        split; [exact (RB' _ MP)|]. split; [exact (RB' _ MA)|]. split; [exact (RB' _ MB)|].
        split; [exact (conj EX (conj EY (conj EZ (conj (RB' _ MX) (conj (RB' _ MY) (RB' _ MZ))))))|].
        split; [exact (RB' _ MN)| exact REST].
      - intros e He EO. pose proof (grp_blocks_in asegs MT m LB G g e GAT He EO) as IN. split; [exact (SUBk _ IN)|].
        destruct (hm_apart asegs R HIA h LB LF m HH) as [HF0 _]. rewrite Forall_forall in HF0.
        destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (_ & _ & _ & BI). cbn [fst snd] in BI. ddestruct MCOK as (MC1 & MC2 & _).
        cbn [disjoint_from fst snd]. split; [pose proof (QGL GXNZ e He EO) as K; clear - K; lia| split; [destruct DIMG as [DI1 DI2]; clear - BI MC1 MC2 DI1 DI2; lia| exact I]]. }
    replace (bv_unsigned sp - 0) with (bv_unsigned sp) in STk by (clear; lia).
    unfold PR_POST, ecp_point_read_postA.
    deexists 14. dexists mk, mo9, hk, LBk, (mkPT dX dY dZ), r, ck.
    split; [reflexivity|]. split; [exact MIk|]. split; [exact STk|]. split; [exact MF9|]. split; [exact PXk|].
    split; [exact HTk|]. split; [exact HSk|]. split; [exact HFk|]. split; [exact HK9|]. split; [exact HCSk|].
    split; [clear - HVk HV; lia|]. split; [clear - HFRk HF; lia|]. split; [exact HHk|].
    split; [unfold ecp_point_at; cbn [pt_X pt_Y pt_Z]; exact (conj EAX (conj EAY (conj EAZ (conj (proj1 MXk) (conj (proj1 MYk) (proj1 MZk))))))|].
    split; [unfold pt_freeable, pt_mpds, mpd_freeable; cbn [pt_X pt_Y pt_Z]; repeat (apply Forall_cons; [assumption|]); apply Forall_nil|].
    split; [unfold pt_mpds; cbn [pt_X pt_Y pt_Z]; apply Forall_cons; [exact (proj2 MXk)| apply Forall_cons; [exact (proj2 MYk)| apply Forall_cons; [exact (proj2 MZk)| apply Forall_nil]]]|].
    split; [unfold pt_dis; cbn [pt_X pt_Y pt_Z]; split; [intros O1 O2 E; injection E as E1 _; exact (D12 O1 O2 E1)| split; [intros O1 O2 E; injection E as E1 _; exact (D13 O1 O2 E1)| intros O1 O2 E; injection E as E1 _; exact (D23 O1 O2 E1)]]|].
    split; [intros R0; ddestruct (SZS R0) as (SZX & SZY & SZZ); unfold pt_mpds; cbn [pt_X pt_Y pt_Z]; apply Forall_cons; [exact SZX| apply Forall_cons; [exact SZY| apply Forall_cons; [exact SZZ| apply Forall_nil]]]|].
    split; [exact SUBk|].
    split; [intros b Hb; destruct (COV b Hb) as [K|K]; [left; exact K| right; unfold pt_blocks, pt_mpds; cbn [pt_X pt_Y pt_Z flat_map]; rewrite app_nil_r; exact K]|].
    split.
    { intros b Hb. unfold pt_blocks, pt_mpds in Hb. cbn [pt_X pt_Y pt_Z flat_map] in Hb. rewrite app_nil_r in Hb. rewrite !in_app_iff in Hb.
      destruct Hb as [Hb|[Hb|Hb]]; [exact (FRSX b Hb)| exact (FRSY b Hb)| exact (FRSZ b Hb)]. }
    split; [exact GATk|]. split; [exact MCk|].
    split; [intros C; exfalso; exact (GXNZ C)| exact HR].
    all: match goal with |- ?g => idtac "POSTOF-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11681438613.9 L27883368372.9 L50772133899.11L52618119093.6 L56759386243.10L59309024491.6 00000O00m01O01`02?02PS1R3HIA1h2sp2lo4LOSP3LOS3TOP2HTS1R3HIA1h2sp2lo4LOSP4MCLO1a2HaS1R3HIA1h2sp1Q2lo4LOSP3LOS2Q11a2HaS1R3HIA1h2sp1a2HaS1R3HIA1h2sp2lo3LO04LOSP1a2Ha1KS1R3HIA1h2HT1K2SH". (* [comment removed for export] *)
  #[using="ra s1 s2 s3 s4 s5 s6 s7 s8 s9 p EC0 PAT QUW SLO2 UW"] Lemma pr_uwc : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "PFRk,$2.PFRAMEk,(24.$18.)Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,R7.R6.(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R5.R4.R3.R2.R1.)(58.$12.R2.(23.VR,)(59.$12.VR,VHIA,R4.)(16.&40.Vs0,)(16.&40.Vsp,)Vd,)")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros FRk FRAMEk v f hk LBk mk J. pose proof (EC0 []) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    rewrite (ej_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J).
    destruct QUW as [[Q1 _]|D28]; [| apply uwc_cap; exact D28].
    eapply uwc_transport; [exact UW|]. intros a Ha.
    pose proof (hcs_stack asegs R HIA h) as SCS. pose proof (hm_top asegs R HIA h LB LF m HH) as HT.
    destruct (hcs_app asegs R HIA h _ _ SCS ltac:(clear - HT LOS LOSP TOP; lia)) as [[_ K]|[_ K]]; [pose proof (art_stk_high asegs R HIA) as SH; exfalso; clear - K SH HT; lia|].
    destruct (ej_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as [PX _].
    refine (proj1 (PX a ltac:(clear - Ha LO0 LOSP K; lia) ltac:(left; clear - Ha; lia) _)).
    cbn [outside fst snd]. split; [clear - Ha Q1 LOS LOSP; lia| split; [clear - Ha MCLO LOSP; lia| exact I]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation EJP := (EJ R HIA h LB LF m (bv_unsigned sp) lo 0 [] XO MC).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L14538835516.3 L17245741792.1 L18975063279.5 L22352253106.7 L29558281123.11L3813375827.13 L6714007179.3  00000<00@00P00m01P02702CS2sp2lo4LOSPS2spS1R1Q2A13QA23GU1S1R2sp2lo4SLO25STACK4HSTK3NERS1R3HIA1h1N1d4BUDF3FRC1f2hk2HF4HFRkS1R3HIA1h2bs1N3BUD3PHI1v2hk2d11z2HV3HVkS2sp2lo4LOSP". (* [comment removed for export] *)
  #[using="EC0 TPV RAE GAT GCR GSP GMC PAT QUW QG QGL SLO2 SPA BUD BUDF UW"] Lemma pr_tail_xop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "PENTRY,$2.PSTACK,$2.PPX,P,$2.SpPPHI,P,$6.P,$2.$2.PFRC,P,$2.$2.PRr,P,(24.$25.)P,$6.P,$2.P,$2.P,$6.SpP,(26.$12.VR,VHIA,R6.R5.R4.R3.R2.R1.)Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.Pz,$2.Pcx,P,$6.$6.Pcy,P,$6.$6.Pcz,P,$6.$6.Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxa0,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,=(1=.$18.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R1=.R1<.R1;.R1:.R19.)P,(1>.VR,VHIA,VLB,VLF,R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R1:.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R19.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R18.)P,(<.(=.(>.R1=.+10.)R1;.)(=.(>.R1;.+10.)R1=.))P,(<.(=.(>.R1>.+10.)R1:.)(=.(>.R1:.+10.)R1>.))P,(=.VQ,R1?.)P,(=.(>.R20.+10.)(>.VQ,+30.))P,Ph',(28.$12.VR,VHIA,)PLB',(24.$25.)Pm',P,(27.&40.)(29.(27.&8.))Pd1',$6.P,(1>.VR,VHIA,VLB,VLF,R4.R3.R2.R25.R1.R23.R22.R21.R20.)(1>.VR,VHIA,VLB,VLF,R5.R4.R3.VQ,A1.R1?.R2.(>.VQ,+10.)A1.R1>.R2.(>.VQ,+20.)A1.R1=.R2.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,A1.R2=.R1=.P,(=.R2?.+480.)P,(=.=A2.R2>.R24.R1?.)P,(=.=A1.R2>.Vd,)P,(=.(>.R2<.A2.R30.R26.R21.)(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.(>.R2<.A1.R30.Vd,)(3?.VN,Vd,))P,Pr,$2.Pd1',$6.P,A5.R32.R2=.R2:.R25.R2.R1.(14.(14.(20.(3<.(21.+2.+1?.))R3.)(=.R3.=))P,(1.$2.R3.=)(14.(=.(10.A1.R26.R3.)(40.VN,))(14.(=.(10.A1.R25.R3.)(40.VN,))(=.(10.A1.R24.R3.)(40.VN,)))))P,(1.(27.&40.)R1=.(35.&40.R2:.))(31.$12.(32.$12.VR,VHIA,R2>.Vmo,)$41.(33.(34.Vra,Vsp,Vgp,Vtp,R21.R20.R1?.Vs0,Vs1,R1>.(35.&40.R25.)R1=.R1<.R1;.R1:.R19.R18.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(35.&40.R37.)Vfc,(36.(27.&40.))R2<.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros ENTRY STACK PX PHI FRC Rr HC. intros until xt6. intros J T S1 S2 S3 S12 S13 QA1 QA2 PERM GXNZ HPX HSTK HPHI HFRC HV HF HRR E0. subst xa0.
    pose proof pr_ec_pop as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. pose proof (arl_need_ecp_rt R) as NER.
    pose proof T as (T1 & _). dpose S1 as (CW1 & SL1 & _ & _).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk A1 d1 (bv_unsigned sp) J T1 CW1 SL1 ltac:(clear - LOSP; lia))
      as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (UW1 : uw_obj R A1 16 d) by (destruct QUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1 QA2; lia| exact GU2]| right; exact GU]).
    pose proof (pr_uwc 0 [] v f hk LBk mk J) as UWk.
    unfold point_read_PHIn in BUD. 
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_xop_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (v := z) (lo := lo) (d := d).
      - exact HHk.
      - exact HK1.
      - exact XM.
      - exact XNS.
      - exact HPX.
      - exact XWR.
      - exact XLSq.
      - replace (bv_unsigned sp) with (bv_unsigned sp - 0) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 HSTK NER. lia.
      - rewrite HTk. exact TOP.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - exact RAE.
      - exact XAO.
      - fold (point_read_PHIn N (Z.of_nat (length bs))) in BUD. clear - HV HVk BUD. lia.
      - exact UWk.
      - rewrite XAD. exact UW1.
      - clear - HF HFRk BUDF. lia.
      - rewrite XAD. reflexivity.
      - reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'. rewrite XAD in HP2.
    pose proof ST2 as ST2'. replace (bv_unsigned sp) with (bv_unsigned sp - 0) in ST2' by (clear; lia).
    destruct (etri_call R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk A1 d1 A2 d2 A3 d3 m2 h2 LB2 dX2 (bv_unsigned sp) (PHI d1 z) (FRC d)
                J T S1 S2 S3 S12 S13 ltac:(clear - LOSP; lia) HPHI HFRC MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 FRA2) as [J2 T2].
    destruct (HRR _ _ GR) as [RR RSZ].
    apply aevtS_now.
    eapply (pr_post_of _ _ h2 LB2 m2 (cx dX2) (cy dX2) (cz dX2) r mo2); [exact J2| exact (PERM _ _ _ _ T2)| exact GXNZ| exact RR| exact HV| exact HF| exact RSZ| exact HK2| exact (mo_frame_trans _ _ _ MF1 MF2)].
    all: match goal with |- ?g => idtac "TAILX-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis NP : md_n (g_P g) <= N.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010<L268303490.400000<S1g1N2NP3NPr". (* [comment removed for export] *)
  #[using="MT LB m G g GAT NP"] Lemma pr_N0 : 0 <= N.
  Proof. ddestruct GAT as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & NPr & _) & _). clear - NPr NP. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L25133699025.5L38855362761.4L39938293576.2L4781719053.2 L48303896707.2L60757248128.3L64952157189.300000>00I00O00U00[00d00lS1N1d2D02K12K2S1N1d2D02DFS1N2N0S1d2D0S1N2N0S2bs1N2DPS1N2N01K". (* [comment removed for export] *)
  #[using="MT LB m G g D0 GAT NP"] Lemma pr_budget : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "(14.(=.(?.+3.(5:.+1.))(3=.VN,(3>.(3:.(27.&8.)Vbs,))))(14.(=.+9.(3?.VN,Vd,))(14.(=.=(5;.VN,))(=.=(5<.VN,Vd,)))))")
(* [comment removed for export] *).
  Proof.
    pose proof pr_N0 as N0.
    assert (DP : 0 <= derive_y_PHIn N).
    { unfold derive_y_PHIn, sw_rhs_PHIn, mm_PHIn, red_PHIn, mul_mpi_PHIn, addsub_PHIn, intop_PHIn, exp_mod_PHIn, grow_PHI, ecp_dy_sz, ecp_sz. unfold AVOL_CALL.
      pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N0; lia) N0) as K. clear - K N0. lia. }
    assert (DF : 0 <= derive_y_FRn N d).
    { unfold derive_y_FRn, sw_rhs_FRn, mm_FRn, red_FRn, mul_mpi_FRn, addsub_FRn, intop_FRn.
      pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (ecp_sz N) (ecp_sz N) (ecp_sz N)) N (d + 1) ltac:(unfold mul_mpi_nz, ecp_sz; clear - N0; lia) ltac:(clear - D0; lia)) as K1.
      pose proof (exp_mod_FRn_nonneg (ecp_sz N) (N + 1) N (d + 1) ltac:(unfold ecp_sz; clear - N0; lia) ltac:(clear - D0; lia)) as K2.
      unfold calls_FR, fr_charge. clear - K1 K2 D0. lia. }
    split; [unfold point_read_PHIn, MPI_RB_PHI, grow_PHI; unfold AVOL_CALL; clear - DP; lia|].
    split; [unfold point_read_FRn, calls_FR, fr_charge; clear - DF D0; lia|]. split; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation SGN1 := (fun z : Z => -2^31 <= z < 2^31).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L24016386102.0L38692635477.0L38948636245.0L39280637297.0L64639430938.0L68531391002.0000001002003004005006SSSSSS". (* [comment removed for export] *)
  #[using="QCW QSP QMC"] Lemma pr_slots : SLOT Q /\ SLOT (Q + 16) /\ SLOT (Q + 32).
  Proof.
    split; [pose proof (pr_slot 0 ltac:(clear; lia) ltac:(clear; lia)) as K; rewrite Z.add_0_r in K; exact K|].
    split; apply pr_slot; clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01:0@L12263194313.0  L16075574774.122L16629301330.1  L18399384683.4  L18457785511.0  L19687428440.206L22768689836.1  L22863681670.4  L23305025156.0  L2397676628.0   L24097320787.1  L2506617407.4   L25465666776.206L26470913780.8  L26482986152.1  L27838437606.1  L28125529944.206L29025845208.206L29956516996.0  L31244335457.1  L31686769240.206L35003468832.5  L35663928186.7  L36180290948.1  L3625504082.1   L37778662896.5  L3798784865.9   L38691415991.0  L39188636933.0  L39332637397.0  L41976525601.0  L4237361117.5   L45594513448.8  L50339925160.1  L52253708504.206L53847981231.9  L5581275937.0   L57786795530.8  L57978561187.1  L58724481964.1  L59093286312.1  L59315053158.1  L60098763854.3  L60692334296.206L6123187174.1   L61601561944.206L62501866156.5  L62505661912.206L64270350808.206L65178513496.206L6664711336.1   L6801190015.4   Q15645357707.214Q18359701643.214Q18380922088.214Q21890334440.214Q24383073128.214Q27595621003.214Q27909229928.214Q30400559592.214Q31256904715.214Q32657407371.214Q33911774184.214Q36436296808.214Q3836524392.214 Q39937517160.214Q41141712779.214Q44654940683.214Q4544207243.214 Q51221311243.214Q59242015499.214Q59828521227.214Q66536679656.214Q9837135336.214 00000100K00N00X00Y01001301=01>01?01B01L01c02:02=02@02W02n02o03203I03W03l04004304A04[04\04]04^04_04m05E05H05_06906:06Q06U06X06[06^06h07?07B07Y07g08>08U08l08o09909P09g0:C0:_0;;0;R0;n0<J0<a0=80=T0>00>L0>h0??0?V0?m0@D0@[0A20AN0AjSS2ra2sp1B2bs2B03B632jk3JK8S1QS1N1d1f2HFSS2ra2sp2bs2jk2dX2dY3JK8S1QS1N1d1f2HFSSS1QS1N1d1f2HFS2ra2sp2bs2jk2dX2dY3JK8S1R3HIA1h1N1d4BUDF1f2HFS1QS1QS2ra2sp2bs2jk2dX2dY3JK8S2ra2sp2bs2jk2dX2dY3JK8SS1QS2ra2sp2bs2jk2dX2dY3JK8S2bs1N1v2HV2G1S1R3HIA1h2sp2lo3TOP1HS2spS1QS2bs1N1v2HV2G1S1R3HIA1h2bs1N3BUD1v2HV2G1SSSSS2bs1N1v2HV2G1S1N2N02dX2dY2dZ2NX2NY2NZS1QS2ra2sp2bs2jk2dX2dY3JK8S1R3HIA1h2bs1N3BUD1v2HV2G1SS1R3HIA1h1N1d4BUDF1f2HFS2spS1QS1QS1CS1R2lo3LOSS2ra2sp2bs2jk2dX2dY3JK8S1QS2ra2sp2bs2jk2dX2dY3JK8S2bs1N1v2HV2G1S2ra2sp2bs2jk2dX2dY3JK8S2ra2sp2bs2jk2dX2dY3JK8S2ra2sp2bs2jk2dX2dY3JK8S1QS1N1d1f2HFS2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8S2sp2bs2lo4LOSP2jk2dX2dY3JK8". (* [comment removed for export] *)
  #[using="IMG HLSET B EC0 TPV RAE GAT GCR GSP GMC PAT QCW QSP QMC QUW QG QGL SLO2 SPA BUD BUDF B0 B63 UW NP"] Lemma pr_zero : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PdX,$6.PdY,$6.PdZ,$6.Pxra,(27.&40.)Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxa0,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxs2,(27.&40.)Pxs3,(27.&40.)Pxs4,(27.&40.)Pxs5,(27.&40.)Pxs6,(27.&40.)Pxs7,(27.&40.)Pxs8,(27.&40.)Pxs9,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(1.$39.(3:.(27.&8.)R21.)#8.)P,(3;.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(=.(10.R1>.)+1.)P,(=.(10.R1>.)+1.)P,(=.(10.R1>.)+1.)P,(=.(>.R26.(?.+3.(5:.+1.)))(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.(>.R26.+9.)(3?.VN,Vd,))(31.$12.(32.$12.VR,VHIA,R26.Vmo,)$41.(33.(34.R20.(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R1?.R1>.R1=.(35.&40.VQ,)(35.&40.(3>.(3:.(27.&8.)Vbs,)))R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.Vs10,Vs11,R<.R;.R:.R9.)VF,(35.&40.+<;618.)Vfc,(36.(27.&40.))R24.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48). dpose pr_slots as (SQ0 & SQ1 & SQ2). pose proof pr_N0 as N0. pose proof pr_qal as QAL.
    intros until xt6. intros JK8 [J T] GXNZ NX NY NZ HV HF.
    pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM.
    assert (G1 : grow_PHI 1 = 8) by (unfold grow_PHI; unfold AVOL_CALL; reflexivity).
    assert (LFR : lset_FR d = 3) by apply lset_FR_val.
    pose proof (conj J (conj T I)) as JTbox. clear J T.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KL; zify_cond KL; ddestruct JTbox as (J & T & _).
    - (* [comment removed for export] *)
      zstep. zstep.
      lazymatch goal with |- _ (MS ?RR _ _ _ _ _ _) => let v0 := getx RR 10%positive in replace v0 with (Z_to_bv 64 (-20352)) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (pr_exit jk v f hk LBk mk dX dY dZ (-20352)); [exact JK8| exact (conj J T)| exact GXNZ| clear; lia| clear - HV G1; lia| clear - HF; lia| intros C; discriminate C].
    -
      pose proof (conj J (conj T I)) as JTbox. clear J T.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      ddestruct JTbox as (J & T & _).
      eapply (pr_xop A_MPI_LSET _ _ _ _ _ HLSET jk v f hk LBk mk Q dX (Q + 16) dY (Q + 32) dZ 1 0xcb638);
        [exact J| exact T| exact SQ0| exact SQ1| exact SQ2| clear; lia| clear; lia| clear; lia| clear; lia| cbv beta; clear; lia| clear; lia
        | cbv beta; rewrite G1; clear; lia| rewrite LFR; clear; lia| cbv beta; rewrite G1; clear - HV G1 BUD; lia| rewrite LFR; clear - HF BUDF; lia| clear; lia| reflexivity| | reflexivity].
      cbv beta. intros h2 LB2 m2 dX2 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' J2 T2 GR2. rewrite G1, LFR in J2.
      clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
        pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      ddestruct GR2 as ([(R0 & NX2 & _)|(RF & EQ2)] & _ & _).
      + (* [comment removed for export] *)
        subst r. pose proof (conj J2 (conj T2 I)) as JTbox. clear J2 T2.
        zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        ddestruct JTbox as (J2 & T2 & _).
        eapply (pr_xop A_MPI_LSET _ _ _ _ _ HLSET jk _ _ h2 LB2 m2 (Q + 16) dY Q dX2 (Q + 32) dZ 1 0xcb648);
          [exact J2| exact (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T2)| exact SQ1| exact SQ0| exact SQ2| clear; lia| clear; lia| clear; lia| clear; lia| cbv beta; clear; lia| clear; lia
          | cbv beta; rewrite G1; clear; lia| rewrite LFR; clear; lia| cbv beta; rewrite G1; clear - HV G1 BUD; lia| rewrite LFR; clear - HF BUDF; lia| clear; lia| reflexivity| | reflexivity].
        cbv beta. intros h3 LB3 m3 dY3 r3 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' J3 T3 GR3. rewrite G1, LFR in J3.
        clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo) as KINV;
          pose proof (munch_refl ([] : list ivl) m3) as MU; pose proof (wmono_refl asegs m3) as WM.
        pose proof (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T3) as T3c.
        ddestruct GR3 as ([(R0 & NY3 & _)|(RF & EQ3)] & _ & _).
        * subst r3. basic_factsA h3.
          pose proof J3 as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
          pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
          assert (SCS : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HSk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
          unfold PR_REGS in FRk. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FRk, STk by (clear; lia).
          pose proof (conj J3 (conj T3c I)) as JTbox. clear J3 T3 T3c.
          (* [comment removed for export] *)
          zstep. zstep. zstep. do 11 zstep. zstep.
          replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
          zstep.
          ddestruct JTbox as (J3 & T3c & _).
          eapply (pr_tail_xop A_MPI_LSET _ _ _ _ _ HLSET _ _ h3 LB3 m3 (Q + 32) dZ (Q + 16) dY3 Q dX2 0 (fun _ => dX2) (fun _ => dY3) (fun e => e));
            [exact (pr_pop jk _ _ h3 LB3 m3 J3)| exact (etri_swap13 R HIA LB LF _ _ _ _ _ _ _ _ _ T3c)| exact SQ2| exact SQ1| exact SQ0| clear; lia| clear; lia| clear; lia| clear; lia
            | intros h' LB' m' d1' T'; exact (etri_swap13 R HIA LB LF _ _ _ _ _ _ _ _ _ T')| exact GXNZ| cbv beta; clear; lia| clear; lia
            | cbv beta; rewrite G1; clear; lia| rewrite LFR; clear; lia| cbv beta; rewrite G1; clear - HV G1; lia| rewrite LFR; clear - HF; lia| | reflexivity].
          cbv beta. (intros r4 d1' dd_H; ddestruct dd_H as ([(R0 & NZ4 & _)|(RF & EQ4)] & _ & _)).
          -- subst r4. split; [clear; lia|]. intros _. unfold ecp_dy_sz, ecp_sz. rewrite NX2, NY3, NZ4. clear - NX NY NZ N0. lia.
          -- subst r4. split; [unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia|]. intros C. exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C. clear - C. lia.
        * (* [comment removed for export] *)
          subst r3. zstep.
          eapply (pr_exit jk _ _ h3 LB3 m3 dX2 dY3 dZ MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact JK8| exact (conj J3 T3c)| exact GXNZ| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| clear - HV G1; lia| clear - HF; lia|].
          intros C. exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C. clear - C. lia.
      + (* [comment removed for export] *)
        subst r. zstep.
        eapply (pr_exit jk _ _ h2 LB2 m2 dX2 dY dZ MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact JK8| exact (conj J2 T2)| exact GXNZ| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| clear - HV G1; lia| clear - HF; lia|].
        intros C. exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C. clear - C. lia.
    all: match goal with |- ?g => idtac "ZERO-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0?L14538835516.3 L15756354262.4 L17245741792.1 L17396075838.3 L18975063279.5 L22110851875.4 L2397676628.0  L25373077975.9 L27455238532.2 L29956516996.0 L40741407973.3 L41724633378.6 L42256698918.7 L4923939807.7  L4957641651.5  L50790580594.6 L51159590045.4 L5246360089.2  L52615975131.6 L5281856140.4  L53258413131.12L59278005337.10L59308873939.3 L59314923118.7 L60200447195.9 L61953102669.8 L64491265552.2 L66254310303.10L66558098759.2 L6714007179.3  L977192228.11  00000<00J00N00X00h01701801M01T01U01a02202G02\02n03?03Q03X03h04304Y05905D05V05m06H06N06m07407@07`S2sp2lo4LOSPS1R2lo3LOS3ALOS2spS1B2bs3BMCS1R1Q2A13QA23GU1S1B2B03off4HOFFSS1B2bs2d13off4HOFF2K1S1k3HK0SS1B3off4HOFFS1B2bs3off1k4HLENS1B2bs3B633off1k4HLENS1B2bs3off1k4HLEN3K47S1R2sp2lo4SLO23NERS1R2sp2lo3LOS3SLOS2LB4C24H3LBk4C24kS2d12N1S2sp1B2bs1a2Ha1KS1Q1B2bs2BQS1Q1B2bs2BQ2A13off1k3QA13QA24HOFF4HLENS2sp1B2bs2lo3BSP3off1k4HOFF4HLENS2bs3HLP2Z0S1B2bs2lo1a2Ha1S1KS1B2bs2d13off1k4HLEN2K1S1B2bs3off1k4HOFF4HLEN1a2HaS1d2D0S1R3HIA1h1N1d4BUDF1f2hk2HF4HFRkS1k3HK0S2sp2lo4LOSPS1R3HIA1h2bs1N3BUD1v2hk1k2HV3HVk". (* [comment removed for export] *)
  #[using="HRB EC0 TPV RAE D0 GAT GCR GSP GMC PAT QMC QUW QG QGL SLO2 SPA BUD BUDF BYT B0 B63 BCR BSP BQ BMC BOB B47 C24H"] Lemma pr_tail_rb : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.Poff,$2.Pk,$2.Pcx,P,$6.$6.Pcy,P,$6.$6.Pcz,P,$6.$6.Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxa0,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,=(1=.$18.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R1?.R1>.R1=.R1<.R1;.)P,(1>.VR,VHIA,VLB,VLF,R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R1<.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R1;.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R1:.)P,(<.(=.(>.R1?.+10.)R1=.)(=.(>.R1=.+10.)R1?.))P,(<.(=.(>.R20.+10.)R1<.)(=.(>.R1<.+10.)R20.))P,(=.VQ,R21.)P,(=.(>.R22.+10.)(>.VQ,+30.))P,Ph',(28.$12.VR,VHIA,)PLB',(24.$25.)Pm',P,(27.&40.)(29.(27.&8.))Pd1',$6.P,(1>.VR,VHIA,VLB,VLF,R4.R3.R2.R27.R1.R25.R24.R23.R22.)(1>.VR,VHIA,VLB,VLF,R5.R4.R3.VQ,A1.R20.R2.(>.VQ,+10.)A1.R1?.R2.(>.VQ,+20.)A1.R1>.R2.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(=.=R1?.)P,(=.=R1?.)P,(=.(>.R21.R20.)(3>.(3:.(27.&8.)Vbs,)))P,(20.=(3>.(3:.(27.&8.)Vbs,)))P,(=.(>.R2>.(4>.R22.))(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.(>.R2>.(4?.Vd,))(3?.VN,Vd,))P,Pd1',$6.P,(1.$2.(10.R1.)(52.R25.))(14.(=.(10.A1.R25.R2.)(40.VN,))(14.(=.(10.A1.R24.R2.)(40.VN,))(=.(10.A1.R23.R2.)(40.VN,))))P,(1.(27.&40.)R1>.(35.&40.R2<.))P,(1.(27.&40.)R1>.(35.&40.(>.VB,R27.)))P,(1.(27.&40.)R1>.(35.&40.R27.))(31.$12.(32.$12.VR,VHIA,R32.Vmo,)$41.(33.(34.Vra,Vsp,Vgp,Vtp,R24.R23.R22.Vs0,Vs1,R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R19.R18.R17.R16.)VF,(35.&40.$5=.)Vfc,(36.(27.&40.))R30.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros until xt6. intros J T S1 S2 S3 S12 S13 QA1 QA2 PERM GXNZ HOFF HK0 HLEN HLP HV HF HSZ E0 E1 E2. subst xa0 xa1 xa2.
    pose proof pr_ec_pop as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. pose proof (arl_need_ecp_rt R) as NER.
    pose proof T as (T1 & _). dpose S1 as (CW1 & SL1 & _ & _).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk A1 d1 (bv_unsigned sp) J T1 CW1 SL1 ltac:(clear - LOSP; lia))
      as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) B (Z.of_nat (length bs))).
    { intros a Ha. destruct (BCR a Ha) as [S|[D|Bk]]; [| right; left; exact D| right; right; exact Bk].
      destruct BSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    assert (BYk : bytes_at asegs mk B bs).
    { eapply (presA_bytes_at asegs R); [exact PXk| exact BYT| exact CRS|]. cbn [disjoint_from fst snd]. split; [clear - BQ; lia| split; [clear - BMC; lia| exact I]]. }
    assert (BCRk : client_range L (LBk ++ fdata LF) lo B (Z.of_nat (length bs))).
    { intros a Ha. destruct (BCR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [| exact Hr]].
      apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBk b Hb)| right; exact Hb]. }
    assert (OBk : aobj asegs AL (hcs asegs R HIA hk) mk B (Z.of_nat (length bs))).
    { destruct BOB as [Z0|OB]; [exfalso; clear - Z0 HLP; lia|]. eapply aobj_cs_mono; [exact HCSk|].
      eapply (presA_aobj0 asegs R); [exact (hcs_ok asegs R HIA h)| exact PXk| exact OB| intros x Hx; eapply hcs_below_top; exact Hx|]. right. split; [exact CRS| clear - LOS SLO FR0; lia]. }
    destruct (bytes_at_subA mk B bs off k BYk HOFF HK0 HLEN) as [IBY ILEN].
    set (ibs := firstn (Z.to_nat k) (skipn (Z.to_nat off) bs)) in *.
    assert (ILZ : Z.of_nat (length ibs) = k) by (rewrite ILEN; clear - HK0; lia).
    pose proof (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC v f hk LBk mk A1 d1 J T1) as BLK1.
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    assert (UW1 : uw_obj R A1 16 d) by (destruct QUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1 QA2; lia| exact GU2]| right; exact GU]).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HRB as HC. unfold mpi_read_binary_stmtA_r_c in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (B := B + off) (ibs := ibs) (lo := lo) (d := d); rewrite ?ILZ.
      - exact HHk.
      - exact HK1.
      - exact (proj1 XM).
      - exact XNS.
      - exact XWR.
      - exact IBY.
      - clear - B0 HOFF. lia.
      - clear - B63 HOFF HLEN. lia.
      - intros a Ha. apply BCRk. clear - Ha HOFF HLEN. lia.
      - rewrite XAD. clear - BQ QA1 QA2 HOFF HLEN HK0. lia.
      - intros EO. ddestruct (BLK1 EO) as (_ & N1 & _ & _ & _ & _ & FRA).
        destruct (fresh_apart_client R LB LF lo B (Z.of_nat (length bs)) _ _ FRA BCR HLP ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K1|K1]; [right| left]; clear - K1 HOFF HLEN HK0; lia.
      - clear - BSP HOFF HLEN HK0. lia.
      - right. destruct B47 as [Z0|K47]; [exfalso; clear - Z0 HLP; lia| clear - K47 HOFF HLEN; lia].
      - replace (bv_unsigned sp) with (bv_unsigned sp - 0) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 NER. lia.
      - rewrite HTk. exact TOP.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - exact RAE.
      - rewrite XAD. pose proof (proj1 XAO) as OX. rewrite XAD in OX. exact OX.
      - eapply aobj_sub; [exact OBk| clear - HOFF; lia| clear - HOFF HLEN; lia].
      - clear - HV HVk BUD. lia.
      - rewrite XAD. exact UW1.
      - clear - HF HFRk BUDF. lia.
      - dpose T as (_ & _ & _ & _ & _ & _ & COVc).
        pose proof (ej_cnt24 R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk [d1; d2; d3] J ltac:(intros b Hb; destruct (COVc b Hb) as [Kc|Kc]; [left; exact Kc| right; cbn [flat_map]; rewrite app_nil_r; exact Kc])) as C24k.
        cbn [length] in C24k. unfold C24_RB_c. unfold C24_ECP_POINT_READ in C24H. clear - C24H C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_read_binary_postA_c in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & RC2 & ROK2 & FRA2 & CNT2).
    injection E as E1 E2. subst ms' mo'. rewrite XAD in HP2. rewrite ?ILZ in HV2, ROK2.
    pose proof ST2 as ST2'. replace (bv_unsigned sp) with (bv_unsigned sp - 0) in ST2' by (clear; lia).
    destruct (etri_call R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk A1 d1 A2 d2 A3 d3 m2 h2 LB2 dX2 (bv_unsigned sp) (MPI_RB_PHI k) (MPI_RB_FR d)
                J T S1 S2 S3 S12 S13 ltac:(clear - LOSP; lia) ltac:(unfold MPI_RB_PHI; unfold AVOL_CALL; clear - HK0; lia) ltac:(unfold MPI_RB_FR, fr_charge; clear - D0; lia)
                MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 FRA2) as [J2 T2].
    apply aevtS_now.
    eapply (pr_post_of _ _ h2 LB2 m2 (cx dX2) (cy dX2) (cz dX2) r mo2); [exact J2| exact (PERM _ _ _ _ T2)| exact GXNZ| | exact HV| exact HF| | exact HK2| exact (mo_frame_trans _ _ _ MF1 MF2)].
    - destruct RC2 as [R0|RF]; subst r; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia].
    - intros R0. exact (HSZ dX2 (proj2 (ROK2 R0))).
    all: match goal with |- ?g => idtac "TAILRB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Variable cnt : word.
  Hypothesis MC0 : rw_cells asegs m MC [C8 cnt].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0@L19687428440.147L20721575143.4  L25465666776.147L27763294094.7  L28125529944.147L29025845208.147L31686769240.147L35653441506.7  L4841863511.4   L50360337654.3  L52253708504.147L57978561187.1  L60098763854.3  L60498772352.4  L60692334296.147L61601561944.147L61706971693.6  L62505661912.147L64270350808.147L65178513496.147L68133380584.6  L945579388.1    Q15641292651.155Q18363763051.155Q18376590600.155Q21877614344.155Q24387400328.155Q27582913387.155Q27905168520.155Q30413004808.155Q31269363179.155Q32653337707.155Q33916092936.155Q36423851400.155Q3832458888.155 Q39941586824.155Q41154424427.155Q44650875883.155Q4531486827.155 Q51233765099.155Q59254731499.155Q59840975083.155Q66524229896.155Q9841204232.155 00000=00J00W00m01:01G01T01l02902E02R02V02`02l03903F03X03e04204?04P04T04a04n05@05R05d06106C06U06b06o07A07S07e08708D08Q08^08k09809E09W09iS2ra2sp2bs2jkS2sp1G2lo3GSPS2ra2sp2bs2jkS1R2sp2lo3ALO3LOS1e2B2S2ra2sp2bs2jkS2ra2sp2bs2jkS2ra2sp2bs2jkS1R3HIA1h2sp2lo3TOP4HTOPS2sp1Q2lo3QSPS2sp2lo4MCLOS2ra2sp2bs2jkS2spS1R2lo3LOSS2sp2lo4LOSPS2ra2sp2bs2jkS2ra2sp2bs2jkS1R3HIA1h2bs1N3PB1S2ra2sp2bs2jkS2ra2sp2bs2jkS2ra2sp2bs2jkS1R3HIA1h1N1d3PB2S2spS2sp2bs2lo2jkS2sp2bs2lo2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo2jkS2sp2bs2lo2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo2jkS2sp2bs2lo2jkS2sp2bs2lo2jkS2sp2bs2lo2jkS2sp2bs2lo2jkS2sp2bs2lo2jkS2sp2bs2lo4LOSP2jkS2sp2bs2lo4LOSP2jk". (* [comment removed for export] *)
  #[using="IMG EC0 D0 GAT GSP PAT PNULL PSG QSP SLO2 NP cnt MC0"] Lemma pr_exit0 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pmk,P,(27.&40.)(29.(27.&8.))Pr,$2.Pxra,(27.&40.)Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxs0',(27.&40.)Pxs1,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxs2,(27.&40.)Pxs3,(27.&40.)Pxs4,(27.&40.)Pxs5,(27.&40.)Pxs6,(27.&40.)Pxs7,(27.&40.)Pxs8,(27.&40.)Pxs9,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(5>.(17.(1;.$2.$2.)(1<.$2.$2.Vlo,(16.&40.Vsp,))(1=.(1;.$2.$2.)))Vm,R1;.)P,(5?.$12.Vm,R1<.)P,(60.$12.R1=.)P,(61.$12.VR,VHIA,Vh,VLB,VLF,R1>.)P,(62.$12.R1?.Vlo,(>.(16.&40.Vsp,)-60.))P,(63.$12.R20.(>.(16.&40.Vsp,)-60.)(17.$18.(70.Vs10,)$1:.))P,(14.(20.(3<.(21.+2.+1?.))R20.)(=.R20.=))P,(0.(1.$2.R21.=))P,P,(1.$2.(3.(4.(5.Vg,)))=)P,(1.(27.&40.)(35.&40.R23.)(35.&40.$64.))(=.+1.(3>.(3:.(27.&8.)Vbs,)))(31.$12.(32.$12.VR,VHIA,Vh,Vmo,)$41.(33.(34.R22.(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R21.R20.R1?.R1>.R1=.(35.&40.R23.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.Vs10,Vs11,R=.R<.R;.R:.)VF,(35.&40.+<;6?4.)Vfc,(36.(27.&40.))R24.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros until xt6. intros MU0 WM0 MIk HHk STk FRk HR RNZ RFU. basic_factsA h.
    pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC) as (_ & _ & _ & MCLO & SPHI).
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (PXk : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) XO m mk).
    { apply presA_nil_any. eapply (presA_tail0 asegs R HIA h LB); [exact HH| intros b Hb; exact Hb| exact LOS| exact TOP| exact MU0| exact WM0]. }
    assert (PATk : ecp_point_at asegs mk LB Q p).
    { eapply (ecp_point_at_munch asegs); [exact PAT| exact MU0| exact WM0| exact MIm| exact MIk| cbn [disjoint_from fst snd]; split; [clear - QSP; lia| exact I]|].
      intros e He EO. exfalso. rewrite Forall_forall in PNULL. rewrite (PNULL e He) in EO. discriminate EO. }
    assert (GATk : ecp_group_at asegs MT mk LB G g).
    { eapply (ecp_group_at_munch asegs); [exact GAT| exact MU0| exact WM0| exact MIm| exact MIk| cbn [disjoint_from fst snd]; split; [clear - GSP; lia| exact I]|].
      intros e He EO. pose proof (grp_blocks_in asegs MT m LB G g e GAT He EO) as IN.
      destruct (hm_apart asegs R HIA h LB LF m HH) as [HF0 _]. rewrite Forall_forall in HF0.
      destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (_ & _ & B2 & _). cbn [fst snd] in B2.
      cbn [disjoint_from fst snd]. split; [clear - B2 ALO LOS; lia| exact I]. }
    assert (MCk : rw_cells asegs mk MC [C8 cnt]).
    { eapply rw_cells_transport; [exact MC0| exact MU0| exact WM0|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - MCLO; lia| exact I]. }
    assert (PB0 : pt_blocks p = []).
    { unfold pt_blocks, pt_mpds in *. inversion PNULL as [|e1 l1 E1 F1]; subst. inversion F1 as [|e2 l2 E2 F2]; subst. inversion F2 as [|e3 l3 E3 F3]; subst.
      cbn [flat_map]. unfold mpd_blk. rewrite E1, E2, E3. reflexivity. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (stk_release asegs mk lo (bv_unsigned sp + -96) (C8 s10 :: PR_REGS) STk FRk ltac:(clear - LOSP LO0; lia)) as STR.
    unfold PR_REGS in FRk, STR. cbn [cells_size csize Nat.add] in STR. replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in STR by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    pose proof (conj MCk (conj GATk (conj PATk I))) as BOX. clear MCk GATk PATk MU0 WM0.
    do 11 zstep.
    zstep.
    replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold PR_POST, ecp_point_read_postA.
    ddestruct BOX as (MCk & GATk & PATk & _).
    deexists 14. dexists mk, mo9, h, LB, p, r, cnt.
    split; [reflexivity|]. split; [exact MIk|]. split; [exact STR|]. split; [exact MF9|]. split; [exact PXk|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|]. split; [intros x Hx; exact Hx|].
    dpose pr_budget as (PB1 & PB2 & _).
    split; [clear - PB1; unfold grow_PHI in PB1; unfold AVOL_CALL in PB1; lia|]. split; [clear - PB2; lia|]. split; [exact HHk|].
    split; [exact PATk|].
    split; [unfold pt_freeable, mpd_freeable; rewrite Forall_forall in *; intros e He C; rewrite (PNULL e He) in C; discriminate C|].
    split; [exact PSG|].
    split.
    { unfold pt_dis. rewrite Forall_forall in PNULL. unfold pt_mpds in PNULL.
      split; [intros O1 _; rewrite (PNULL (pt_X p) ltac:(left; reflexivity)) in O1; discriminate O1|].
      split; [intros O1 _; rewrite (PNULL (pt_X p) ltac:(left; reflexivity)) in O1; discriminate O1| intros O1 _; rewrite (PNULL (pt_Y p) ltac:(right; left; reflexivity)) in O1; discriminate O1]. }
    split; [intros C; exfalso; exact (RNZ C)|].
    split; [intros b Hb; exact Hb|]. split; [intros b Hb; left; exact Hb|].
    split; [intros b Hb; rewrite PB0 in Hb; destruct Hb|].
    split; [exact GATk|]. split; [exact MCk|].
    split; [intros GX0; split; [reflexivity| split; [reflexivity| exact (RFU GX0)]]| exact HR].
    all: match goal with |- ?g => idtac "EXIT0-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L15756354262.4 L28704391748.3 L28776808227.3 L29963136370.7 L30558141499.4 L31816887633.2 L3422393608.3  L38948636245.0 L40113525374.1 L43497569673.19L52320020432.3 L52632121253.5 L59657045483.8 L64509295911.2 L65228853028.5 L66033505167.23L7359481436.2  L9689407360.2  00000>00J00U00n01?01E01P01Q01U01V01_02202J02R02d02e02m034S1R2lo3LOS3ALOS2sp2lo4LOSPS2A12A23S12S1R3DI13DI23MC13MC22dZ2BIS2sp2lo4LOSP4MCLOS1x2K2S2A12A33S13SS2spFS2A12dZ1KS2sp2lo4LOSP2A13SL1S1R3HIA1h2sp2lo4LOSP1a1SS2A23MS2S1R2sp2lo4LOSP3LOSFS2A33MS3S2dZ2N1". (* [comment removed for export] *)
  #[using="ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 p EC0 PAT SLO2"] Lemma pr_tri_call_mc : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.Pm',P,(27.&40.)(29.(27.&8.))Ph',(28.$12.VR,VHIA,)PLB',(24.$25.)Pd1',$6.Pdv,$2.Pdf,$2.P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,=(1=.$18.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R11.R10.R?.R>.R=.)P,(1>.VR,VHIA,VLB,VLF,R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R>.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R=.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R<.)P,(<.(=.(>.R11.+10.)R?.)(=.(>.R?.+10.)R11.))P,(<.(=.(>.R12.+10.)R>.)(=.(>.R>.+10.)R12.))P,(=.=R9.)P,(=.=R9.)P,(60.$12.R?.)P,(62.$12.R10.Vlo,(1?.(16.&40.Vsp,)=))P,(65.$12.VR,(66.R19.R16.)VLF,(16.&40.Vsp,)(23.VR,)(59.$12.VR,VHIA,R1:.)(17.(1;.$2.$2.)(1<.$2.$2.R17.(>.R17.+10.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))R18.R11.)P,(1.$2.(67.$12.VR,VHIA,R11.)(67.$12.VR,VHIA,R1;.))P,(1.$2.(59.$12.VR,VHIA,R12.)(59.$12.VR,VHIA,R1<.))P,(1.$2.(68.$12.VR,VHIA,R13.)(68.$12.VR,VHIA,R1=.))P,Px,$2.P,(49.$12.VR,VHIA,R1?.R1.)(49.$12.VR,VHIA,R16.R2.)P,(=.(2<.$12.VR,VHIA,R15.)(>.(2<.$12.VR,VHIA,R1?.)R12.))P,(=.(2>.$12.VR,VHIA,R16.)(>.(2>.$12.VR,VHIA,R20.)R12.))P,(61.$12.VR,VHIA,R17.R16.VLF,R18.)P,(69.$12.R19.R17.R16.)P,(6:.R22.R1?.R18.R17.)P,Pb,$25.P,(7.$25.R1.(6;.R19.))(<.(7.$25.R2.(6;.R22.))(6<.VR,(66.R25.R22.)VLF,(6=.$2.$2.R2.)(6>.$2.$2.R2.)))P,(6?.(27.&40.)Lc,(27.&40.)(63.$12.R1=.$13.(17.$18.(70.R1.)(1=.$18.))))(14.(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,=(1=.$18.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.(>.R28.R19.)(>.R27.R18.)R1<.R1;.R1=.)(1>.VR,VHIA,VLB,VLF,R1<.R1;.R1=.R23.R1:.R21.R20.R1?.R1>.))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    pose proof pr_ec_pop as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros until df. (intros J dd_H; ddestruct dd_H as (T1 & T2 & T3 & D12 & D13 & D23 & COV); intros dd_H; ddestruct dd_H as (CW1 & SL1 & XI1 & MS1); intros dd_H; ddestruct dd_H as (CW2 & SL2 & _ & MS2); intros dd_H; ddestruct dd_H as (CW3 & SL3 & _ & MS3); intros S12 S13 Hdv Hdf MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA' MC').
    assert (HSP2 : arl_stklo R <= bv_unsigned sp <= bv_unsigned sp) by (clear - LOS LOSP; lia).
    assert (CRA : forall A, client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) A 16 -> client_range L (LB ++ fdata LF) lo A 16).
    { intros A CW a Ha. destruct (CW a Ha) as [S|[D|Bk]]; [left; clear - S LOSP; lia| right; left; exact D| right; right; exact Bk]. }
    ddestruct MCOK as (MC1 & MC2 & _).
    assert (LAP : forall A dZ, ejtmp R HIA LB LF hk LBk mk A dZ -> md_own dZ = LHeap -> disjoint_from [(A1, A1 + 16); (MC, MC + 8)] (md_p dZ) (4 * md_n dZ)).
    { intros A dZ TZ EO. destruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC v f hk LBk mk A dZ J TZ EO) as (_ & N1 & _ & _ & BI & _ & FRA).
      destruct (fresh_apart_client R LB LF lo A1 16 _ _ FRA (CRA A1 CW1) ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K];
        cbn [disjoint_from fst snd]; (split; [clear - K; lia| split; [destruct DIMG as [DI1 DI2]; clear - BI MC1 MC2 DI1 DI2; lia| exact I]]). }
    pose proof (ej_aobj_call R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC v f hk LBk mk A1 d1 m' h' (bv_unsigned sp) _ J T1 CW1 HSP2 HP HCS') as OA1'.
    destruct (ej_call R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk A1 d1 m' h' LB' d1' (bv_unsigned sp) dv df [(A1, A1 + 16); (MC, MC + 8)] J T1
                ltac:(clear; lia) Hdv Hdf MI' ST' HP) as [J' T1'];
      first [ assumption | solve [intros x Hx; pose proof (XI1 x Hx) as K1; pose proof (XOMC x Hx) as K2; cbn [outside fst snd] in *; split; [exact (proj1 K1)| split; [clear - K2; lia| exact I]]]
            | solve [cbn [disjoint_from fst snd]; split; [clear - SL1 LOSP; lia| split; [clear - MCLO LOSP; lia| exact I]]] | solve [clear - LOSP; lia] | idtac ].
    destruct (ejtmp_keep R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk A1 d1 A2 d2 m' h' LB' d1' (bv_unsigned sp) _ J T1 T2 D12 CW2 HSP2 HP
                ltac:(cbn [disjoint_from fst snd]; split; [clear - S12; lia| split; [clear - MS2; lia| exact I]]) (LAP A2 d2 T2) MI' HCS' OUT' M1' FRA') as [T2' D12'].
    destruct (ejtmp_keep R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk A1 d1 A3 d3 m' h' LB' d1' (bv_unsigned sp) _ J T1 T3 D13 CW3 HSP2 HP
                ltac:(cbn [disjoint_from fst snd]; split; [clear - S13; lia| split; [clear - MS3; lia| exact I]]) (LAP A3 d3 T3) MI' HCS' OUT' M1' FRA') as [T3' D13'].
    split; [exact J'|]. refine (conj T1' (conj T2' (conj T3' (conj D12' (conj D13' (conj D23 _)))))).
    dpose OUT' as (_ & _ & O3 & _ & O5).
    intros b Hb. destruct (O3 b Hb) as [K1|K1]; [| right; apply in_or_app; left; exact K1].
    destruct (COV b K1) as [K2|K2]; [left; exact K2| right]. rewrite !in_app_iff in *. destruct K2 as [K2|K2]; [left; rewrite (O5 b K2 Hb); exact K2| right; exact K2].
    all: match goal with |- ?g => idtac "TRIMC-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis HDY : ecp_derive_y_stmtA asegs R HIA MT A_ECP_SW_DERIVE_Y A_MUL_COUNT.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO3 : slo <= lo.
  Hypothesis LFB : (length LF + 4 <= 512)%nat.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0?L14538835516.3 L15756354262.4 L17245741792.1 L19715346259.5 L19715409235.11L19725895507.11L23465044660.3 L23984727694.2 L2665442938.4  L26892418956.1 L27641239183.3 L29754076365.4 L29762076929.6 L34227125215.4 L3453108681.2  L35184430972.3 L35693534892.2 L38948636245.0 L42733969043.4 L45826280167.7 L45826406887.13L45828504551.13L45830929681.7 L50339925160.1 L53611932839.3 L5519111400.2  L55325028193.1 L57853566577.10L57856181233.7 L59657045483.8 L60900445136.3 L60905121392.3 L6123187174.1  L65029767540.3 L68016077746.11L68018693682.8 L68030757298.1000000<00J00N00O00P00Q00Z00a00n01201;01M01a01n02502=02D02E02S02T02U02V02W02Z02b02i02l03J03K03c03l04704:04C04D04E04dS2sp2lo4LOSPS1R2lo3LOS3ALOS2spFFFS1R1Q3GU1S2dX2N1S1N2N02dX3NXNS2spS1R1Q3GU1S2LB4C24H3LBk4C24kS1R2lo2dX3LOS3ALO2B2S2sp1Q2lo3SLXS1Q3MSXS1Q2dX1KS1G3GMCSS1R2sp2lo4SLO2FFFFS1QS1Q2dX1KS1Q3MSYS1QS1R3HIA1h2bs1N3BUD1v2hk2HV3HVkFS1R3HIA1h2sp2lo4LOSP1a1SS1G1Q3QGsS1N3dY23SZ2S1QS1G1Q3QGsFFS1R3HIA1h1N1d4BUDF1f2hk2HF4HFRk". (* [comment removed for export] *)
  #[using="slo EC0 TPV RAE D0 GAT GCR GSP GMC PAT QCW QSP QMC QUW QG QGL SLO2 SPA BUD BUDF C24H UW NP HDY SSH SLO1 SLO3 LFB"] Lemma pr_tail_dy : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PdX,$6.PdY,$6.PdZ,$6.Pxa3,(27.&40.)Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,=(1=.$18.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R14.R13.R12.R11.R10.)P,(1>.VR,VHIA,VLB,VLF,R13.R12.R11.VQ,R10.(>.VQ,+10.)R?.(>.VQ,+20.)R>.)P,(71.$12.VR,VHIA,VMT,Vh,VLB,VLF,Vm,VG,Vg,$13.Vlo,(16.&40.Vsp,)Vd,)P,(1.$2.(51.(72.Vg,))+1.)P,(1.$2.(51.(73.Vg,))+1.)P,(=.+1.(74.(75.Vg,)))P,(=.(10.(75.Vg,))+1387.)P,(76.Vg,VN,)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(1.$9.(:.R17.)$77.)P,(=.(10.R19.)VN,)P,(=.(10.R18.)(40.VN,))P,(=.(>.R20.(5;.VN,))(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.(>.R20.(5<.VN,Vd,))(3?.VN,Vd,))(31.$12.(32.$12.VR,VHIA,R20.Vmo,)$41.(33.(34.Vra,Vsp,Vgp,Vtp,R19.R18.R17.Vs0,Vs1,(35.&40.VG,)(35.&40.VQ,)(35.&40.(>.VQ,+10.))R1:.R16.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(35.&40.$78.)Vfc,(36.(27.&40.))R1>.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48). dpose pr_slots as (SQ0 & SQ1 & SQ2). pose proof pr_N0 as N0.
    intros until xt6. intros J T GRP SGA SGB VP P4999 NLE GXNZ YNULL NXN NZS HV HF.
    pose proof pr_ec_pop as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    dpose T as (TX & TY & TZ & D12 & D13 & D23 & COV).
    dpose SQ0 as (CWX & SLX & _ & MSX). dpose SQ1 as (CWY & SLY & _ & MSY).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk Q dX (bv_unsigned sp) J TX CWX SLX ltac:(clear - LOSP; lia))
      as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk (Q + 16) dY (bv_unsigned sp) J TY CWY SLY ltac:(clear - LOSP; lia))
      as (YM & YNS & YAD & YOS & YCR & YCRL & YWR & YLSq & YAO & YIM).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose GRP as (GAT' & GH1 & GPS & GIMG & GCR' & GSP' & GMC' & GOB & GUW).
    pose proof (QG GXNZ) as QGs.
    assert (DXG : disjoint_from XO G 192) by (cbn [disjoint_from fst snd]; split; [clear - QGs; lia| split; [clear - GMC; lia| exact I]]).
    pose proof (ej_grp_pre R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC MT v f hk LBk mk G g (bv_unsigned sp) d J GRP DXG ltac:(clear; lia)) as GRPk.
    pose proof (ej_sshad R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk slo J SSH SLO1) as SSk.
    pose proof (ej_cnt24 R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC EC v f hk LBk mk [dX; dY; dZ] J ltac:(intros b Hb; destruct (COV b Hb) as [K|K]; [left; exact K| right; cbn [flat_map]; rewrite app_nil_r; exact K])) as C24k.
    pose proof (pr_uwc 0 [] v f hk LBk mk J) as UWk.
    pose proof (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 0 _ XO MC v f hk LBk mk Q dX J TX) as BLKX.
    assert (CRY16 : client_range L (LB ++ fdata LF) lo (Q + 16) 16).
    { intros a Ha. destruct (CWY a Ha) as [S|[D|Bk]]; [left; clear - S LOSP; lia| right; left; exact D| right; right; exact Bk]. }
    assert (XOWN : md_own dX <> LNull -> md_own dX = LHeap) by (destruct (md_own dX); [intros C; exfalso; exact (C eq_refl)| reflexivity| intros _; exfalso; exact (XNS eq_refl)]).
    assert (EXT : ext_opndA asegs R HIA hk LBk LF mk dY dX MC (bv_unsigned sp) lo d).
    { unfold ext_opndA. rewrite YAD, XAD.
      split; [exact XM|]. split; [right; clear; lia|].
      split.
      { unfold opnd_sep. rewrite YAD, XAD.
        split; [intros ON; ddestruct (BLKX (XOWN ON)) as (_ & N1 & _ & _ & _ & _ & FRA);
                destruct (fresh_apart_client R LB LF lo (Q + 16) 16 _ _ FRA CRY16 ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K]; [right| left]; clear - K; lia|].
        split; [intros C; rewrite YNULL in C; discriminate C|]. split; [right; left; rewrite YNULL; discriminate|].
        split; [clear - SLX; lia|]. intros ON. left. ddestruct (BLKX (XOWN ON)) as (_ & _ & _ & B2 & _). clear - B2 ALO LOS. lia. }
      split; [exact XCR|]. split; [exact XCRL|]. split; [clear - MSX; lia|]. split; [exact XAO|]. split; [exact XIM|].
      destruct QUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1; lia| exact GU2]| right; exact GU]. }
    assert (OSk : ecp_out_sepA dY G MC).
    { unfold ecp_out_sepA. rewrite YAD. split; [clear - QGs; lia|]. split; [intros C; rewrite YNULL in C; discriminate C| clear - MSY; lia]. }
    assert (UWY : uw_obj R (Q + 16) 16 d) by (destruct QUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1; lia| exact GU2]| right; exact GU]).
    dpose pr_budget as (_ & _ & DP0 & DF0).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HDY as HC. unfold ecp_derive_y_stmtA, ecp_rhs_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := dY) (dA := dX) (G := G) (g := g) (cnt := ck) (N := N) (lo := lo) (d := d) (slo := slo); cbv iota.
      all: first [ exact HHk | exact HK1 | exact LFB | exact GRPk | exact OSk | exact SGA | exact SGB | exact VP | (intros _; exact P4999) | exact NLE | exact NXN
                 | exact YM | exact YNULL | exact YWR | exact EXT | exact MCk | exact MCOK | exact LOS | exact SSk | exact SLO1 | exact SLO3 | exact SPA | exact TPV | exact MIk | exact RAE
                 | exact YAO | exact UWk | (rewrite YAD; exact UWY) | reflexivity
                 | (replace (bv_unsigned sp) with (bv_unsigned sp - 0) by (clear; lia); exact STk)
                 | (rewrite HTk; exact TOP) | (clear - SLO2; lia) | (clear - HV HVk BUD; lia) | (clear - HF HFRk BUDF; lia)
                 | (unfold C24_ECP_DERIVE_Y, C24_ECP_POINT_READ in *; cbn [length] in C24k; clear - C24H C24k; lia)
                 | (rewrite XAD, YAD; split; reflexivity) | idtac ].
      all: match goal with |- ?g => idtac "DY-PRE-LEFT:" g end. }
    cbv iota. (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold ecp_mul_mod_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dY2 & r & cnt2 & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MY2 & OUT2 & FRA2 & GR2 & MCC2 & MR2 & SZ2).
    injection E as E1 E2. subst ms' mo'. rewrite YAD in HP2.
    pose proof ST2 as ST2'. replace (bv_unsigned sp) with (bv_unsigned sp - 0) in ST2' by (clear; lia).
    destruct (pr_tri_call_mc v f hk LBk mk (Q + 16) dY Q dX (Q + 32) dZ m2 h2 LB2 dY2 (derive_y_PHIn N) (derive_y_FRn N d)
                J (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T) SQ1 SQ0 SQ2 ltac:(clear; lia) ltac:(clear; lia) DP0 DF0
                MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MY2 OUT2 FRA2 ltac:(exists cnt2; exact MCC2)) as [J2 T2].
    apply aevtS_now.
    eapply (pr_post_of _ _ h2 LB2 m2 dX dY2 dZ r mo2); [exact J2| exact (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T2)| exact GXNZ| exact (proj1 MR2)| exact HV| exact HF| | exact HK2| exact (mo_frame_trans _ _ _ MF1 MF2)].
    intros _. unfold ecp_dy_sz, ecp_sz in *. split; [clear - NXN N0; lia| split; [clear - SZ2; lia| exact NZS]].
    all: match goal with |- ?g => idtac "TAILDY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis QOB : aobj asegs AL (hcs asegs R HIA h) m Q 48.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L11560304158.1L11821110626.3L19945316590.2L24016386102.0L27824359356.7L35653441506.7L38692635477.0L38948636245.0L39280637297.0L60098763854.3L64639430938.0L65701454385.3L68531391002.000000300=00D00E00\01401501601701A01B01L01MS1QS1Q3off2O1S2sp2loSS2sp1Q2lo3QSP3off2O02O1S1R3HIA1h2sp2lo3TOP4HTOPSSSS1R2lo3LOSSS1Q3off2O0S". (* [comment removed for export] *)
  #[using="EC0 PAT PNULL PSG QSP SLO2 cnt MC0 QOB"] Lemma pr_start : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pm1,P,(27.&40.)(29.(27.&8.))P,(5>.(17.(1;.$2.$2.)(1<.$2.$2.Vlo,(16.&40.Vsp,))(1=.(1;.$2.$2.)))Vm,R1.)P,(5?.$12.Vm,R2.)P,(61.$12.VR,VHIA,Vh,VLB,VLF,R3.)P,(60.$12.R4.)P,(62.$12.R5.Vlo,(1?.(16.&40.Vsp,)+60.))P,(63.$12.R6.(1?.(16.&40.Vsp,)+60.)(17.$18.(70.Vs10,)$1:.))(3;.R8.==Vh,VLB,R7.(4.Vp,)(79.Vp,)(7:.Vp,))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros jk m1 MU WM HH1 MI1 ST1 FR1. pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - TOP HTOP; lia]).
    assert (WC0 : w_client (hcs asegs R HIA h) [(lo, bv_unsigned sp)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    ddestruct PAT as (EX & EY & EZ & MX & MY & MZ).
    assert (NUL : forall e, In e (pt_mpds p) -> md_own e = LNull) by (rewrite Forall_forall in PNULL; exact PNULL).
    assert (SGN : forall e, In e (pt_mpds p) -> md_sg e = 1 \/ md_sg e = -1) by (rewrite Forall_forall in PSG; exact PSG).
    assert (TMP : forall e off, In e (pt_mpds p) -> mpdr_at asegs m LB e -> md_addr e = Q + off -> 0 <= off -> off + 16 <= 48 ->
                  ejtmp R HIA LB LF h LB m1 (Q + off) e).
    { intros e off He Me Ae O0 O1. pose proof (NUL e He) as EO.
      split; [| split; [exact Ae| split; [rewrite EO; discriminate| split; [intros b Hb; unfold mpd_blk in Hb; rewrite EO in Hb; destruct Hb|]]]].
      - eapply mpd_at_munch_any; [exact (conj Me (SGN e He))| exact MU| exact WM| rewrite Ae; cbn [disjoint_from fst snd]; split; [clear - QSP O0 O1; lia| exact I]|].
        intros C. exfalso. exact (C EO).
      - eapply (aobj_munch asegs AL _ CSOK); [exact WC0| exact MU|]. eapply aobj_sub; [exact QOB| clear - O0; lia| clear - O1; lia]. }
    split.
    - exact (ej_start R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC m1 cnt MU WM HH1 MI1 ST1 FR1 MC0).
    - unfold pt_mpds in *.
      pose proof (TMP (pt_X p) 0 ltac:(left; reflexivity) MX ltac:(rewrite EX; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as TX. rewrite Z.add_0_r in TX.
      pose proof (TMP (pt_Y p) 16 ltac:(right; left; reflexivity) MY EY ltac:(clear; lia) ltac:(clear; lia)) as TY.
      pose proof (TMP (pt_Z p) 32 ltac:(right; right; left; reflexivity) MZ EZ ltac:(clear; lia) ltac:(clear; lia)) as TZ.
      refine (conj TX (conj TY (conj TZ _))).
      split; [intros O1 _; rewrite (NUL (pt_X p) ltac:(left; reflexivity)) in O1; discriminate O1|].
      split; [intros O1 _; rewrite (NUL (pt_X p) ltac:(left; reflexivity)) in O1; discriminate O1|].
      split; [intros O1 _; rewrite (NUL (pt_Y p) ltac:(right; left; reflexivity)) in O1; discriminate O1|].
      intros b Hb. left. exact Hb.
    all: match goal with |- ?g => idtac "START-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac pr_a0_lit z :=
    lazymatch goal with |- _ (MS ?RR _ _ _ _ _ _) => let v0 := getx RR 10%positive in replace v0 with (Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity) end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02N0@L10378821749.8  L11544553258.2  L12263194313.0  L14239371309.4  L14485315996.12 L15032450075.157L15045230384.159L15047975938.232L15061589845.8  L15425583723.6  L16075583823.234L16075583950.236L16075584073.162L16629301330.1  L18399384683.6  L18457785511.0  L19628484262.236L19687428440.235L19687428440.236L21870408481.0  L22092987155.8  L22768689836.1  L23305025156.0  L24097320787.1  L25465666776.235L25465666776.236L26482986152.1  L27838437606.1  L27970009891.6  L28125529944.235L28125529944.236L29025845208.235L29025845208.236L29956516996.0  L31244335457.1  L31686769240.235L31686769240.236L35649065510.6  L35663928186.7  L35817963778.6  L36180290948.1  L3625504082.1   L37263264722.3  L37593927265.3  L39188636933.0  L39220637093.0  L39332637397.0  L41554056648.12 L41619615305.4  L42615853770.153L42630520520.156L42630520520.233L48548502905.3  L492447604.233  L50339925160.1  L50850723928.2  L52253708504.235L52253708504.236L53302591708.3  L53854142740.12 L54356895797.162L54356896563.234L57425804311.235L57784697092.10 L57978561187.1  L58724481964.1  L59093286312.1  L59308873939.3  L59315053158.1  L60098763854.3  L60692334296.235L60692334296.236L6123187174.1   L61601561944.235L61601561944.236L62011818785.0  L62501763081.6  L62505661912.235L62505661912.236L62778661174.8  L63179383713.6  L64014195754.157L64270350808.235L64270350808.236L64522770220.6  L64591683288.10 L64784600963.6  L6511551241.6   L65178513496.235L65178513496.236L66555306242.1  L6664711336.1   L7041532117.3   L7561994737.3   Q15645357707.243Q15645357707.244Q15930096381.165Q15930096381.242Q18235521043.169Q18235521043.242Q18359701643.243Q18359701643.244Q18380922088.243Q18380922088.244Q21890334440.243Q21890334440.244Q24383073128.243Q24383073128.244Q27595621003.243Q27595621003.244Q27909229928.243Q27909229928.244Q30400559592.243Q30400559592.244Q31256904715.243Q31256904715.244Q32657407371.243Q32657407371.244Q32677371590.165Q32677371590.242Q33911774184.243Q33911774184.244Q36436296808.243Q36436296808.244Q3836524392.243 Q3836524392.244 Q38407131824.165Q38407131824.242Q39937517160.243Q39937517160.244Q41141712779.243Q41141712779.244Q43614618594.162Q43614618594.239Q44654940683.243Q44654940683.244Q4544207243.243 Q4544207243.244 Q51221311243.243Q51221311243.244Q59242015499.243Q59242015499.244Q59828521227.243Q59828521227.244Q59850850150.165Q59850850150.242Q61914824482.162Q61914824482.239Q61916948695.165Q61916948695.242Q61917310046.169Q61917310046.242Q66536679656.243Q66536679656.244Q8675760286.162 Q8675760286.239 Q9837135336.243 Q9837135336.244 00000F00L00M00Y01301K01c02>02W02k03Z04I05205505G05H05I05g06J06K06f06i06j06m07K07n08108408@08^09A09_0:B0:C0:F0:d0;G0;Y0;n0<?0<C0<F0<R0<`0<a0<b0<c0=J0=\0>E0>n0?Z0?f0?g0?j0@20@P0A30AA0Ah0BU0CP0DK0Di0Dm0E00E30E>0EA0EK0Ei0FL0FO0Fm0GP0GQ0Ge0HC0Hf0IA0IP0Il0JJ0Jm0K90KW0Kl0L=0L[0M>0MB0ME0MS0M_0N:0NX0Nj0O?0OW0P20PM0Pk0QK0Qn0RN0S10SQ0T40TO0Tm0UM0V00VP0W30WN0Wl0XG0Xe0Y90YP0Z00ZS0[30[V0\60\Y0]10]L0]l0^O0^j0_H0_Z0_o0`J0`h0aC0aa0b<0bZ0c50cS0cn0dL0dc0e=0eQ0eh0f<0fS0fg0g>0g^0hA0hY0i40iT0j7S2bs1N1v4plen2HV3RBM1HS2bs1NSS1N2N02dZ2NZS1g1N2NP4plen3PLB1q1r1H2H0S2LF2ra2sp2bs3LFB2jk3JK8S2LF2ra2sp2bs3LFB2jk3JK8S2LF2ra2sp2bs3LFB2jk2dZ3JK8S2bs1N4DYP01v4plen2HV3RBMS2bs1N4DYP01v3HLP2HVS2LF2ra2sp1B2bs2B03B633LFB2jk2dZ3JK83HLP2b03SPRS2LF2ra2sp1B2bs2B03B633LFB2jk2dZ3JK83HLP2b03SPRS2LF2ra2sp1B2bs2B03B633LFB2jk3JK83HLP3SPRS1QS1N1d2D04DYF01f2HFSFS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0SS2bs1N4DYP01v4plen2HV3RBM1HS1QSS1QS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S1QS1QS2bs4plen2K1S2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0SS1QS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S1N1d2D04DYF01f2HFS1R3HIA1h2sp2lo3TOP1HS1N1d4DYF01f2HF1HS2spS1QS1g4plen3PLBS2bs4plen4LENPSSSS1R3HIA1h2bs1N3BUD4DYP01v4plen2HV3RBM1HS1g4plen5P49993PLBS2LF2ra2sp1B2bs2B03B633LFB2jk3JK83HLP3SPRS2LF2ra2sp1B2bs2B03B633LFB2jk3JK83HLP3SPRS2LF2ra2sp1B2bs2B03B633LFB2jk2dZ3JK83HLP3SPRS1g4plen3PLBFS1QS1B4plenS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S2bs4plen4LENPS1R3HIA1h2bs1N3BUD4DYP01v4plen2HV3RBM1HS2LF2ra2sp1g2bs3LFB2jk4plen3JK85P49993PLB3SPRS2LF2ra2sp1B1g2bs2B03B633LFB2jk2dZ4plen3JK83PLB2b04LENP3SPRS2LF2ra2sp1B1g2bs2B03B633LFB2jk2dZ4plen3JK83PLB2b04LENP3SPRS1R3HIA1h1N1d4BUDF4DYF01f2HF1HS2spS1QS1QS2bs3HLP2Z0S1CS1R2lo3LOSS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S1QS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0SS2bs1N4DYP01v3HLP2HVS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S2bs1N4DYP01v4plen2HV3RBM1HS1N1d4DYF01f2HFS2LF2ra2sp2bs3LFB2jk3JK83HLPS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S1N1d1f2HF1HS1R3HIA1h1N1d4BUDF4DYF01f2HF1HS1N2N02dZ4plen2NZ3PLNS1N1d4DYF01f2HF1HS2LF2ra2sp2bs3LFB2jk2dZ3JK82b0S2LF2ra2sp2bs3LFB2jk2dZ4plen3JK82b0S2bsS1QS2bs4plen4LEN2S2bs4plen2K4S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2bs3LFB2jk3JK8S2LF2bs3LFB2jk2dZ3JK8S2LF1B2bs3LFB2jk3JK83HLPS2LF1B2bs3LFB2jk2dZ3JK83HLPS2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF1B2bs3LFB2jk3JK8S2LF1B2bs3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF1B2bs3LFB2jk3JK83HLPS2LF1B2bs3LFB2jk2dZ3JK83HLPS2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2bs3LFB2jk3JK8S2LF2bs3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF2sp2bs2lo3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB2jk2dZ3JK82b0S2LF1B2bs2B03LFB2jk3JK8S2LF1B2bs2B03LFB2jk2dZ3JK8S2LF1B2bs3LFB2jk3JK8S2LF1B2bs3LFB2jk2dZ3JK8S2LF1B2bs3LFB2jk3JK8S2LF1B2bs3LFB2jk2dZ3JK8S2LF1B2bs3LFB2jk3JK8S2LF1B2bs3LFB2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0S2LF1B2bs3LFB2jk3JK83HLPS2LF1B2bs3LFB2jk2dZ3JK83HLPS2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK8S2LF2sp2bs2lo3LFB4LOSP2jk2dZ3JK82b0". (* [comment removed for export] *)
  #[using="IMG HLSET HRB slo EC0 TPV RAE D0 GAT GCR GSP GMC PAT QCW QSP QMC QUW QG QGL SLO2 SPA BUD BUDF BYT B0 B63 BCR BSP BQ BMC BOB B47 C24H UW NP HDY SSH SLO1 SLO3 LFB"] Lemma pr_sw : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PdX,$6.PdY,$6.PdZ,$6.Pplen,$2.Pxra,(27.&40.)Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxa0,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxs4,(27.&40.)Pxs5,(27.&40.)Pxs6,(27.&40.)Pxs7,(27.&40.)Pxs8,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(1.$39.(3:.(27.&8.)R1?.)#8.)P,(3;.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(71.$12.VR,VHIA,VMT,Vh,VLB,VLF,Vm,VG,Vg,$13.Vlo,(16.&40.Vsp,)Vd,)P,(1.$2.(51.(72.Vg,))+1.)P,(1.$2.(51.(73.Vg,))+1.)P,(=.+1.(74.(75.Vg,)))P,(=.(10.(75.Vg,))+1387.)P,(76.Vg,VN,)P,(1.$9.(:.R21.)$77.)P,(=.(10.R23.)+1.)P,(=.(10.R23.)+1.)P,(=.(10.R23.)+1.)P,(14.(=.=R23.)(=.R23.(?.+4.(10.(75.Vg,)))))P,(20.=(3>.(3:.(27.&8.)Vbs,)))P,(=.(>.R2=.(>.(>.(?.+2.(4>.(3>.(3:.(27.&8.)Vbs,))))(?.+3.(5:.+1.)))(5;.VN,)))(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.(>.R2=.(>.(>.(?.+2.(4?.Vd,))+9.)(5<.VN,Vd,)))(3?.VN,Vd,))P,(1.(27.&40.)R18.(35.&40.(7;.(48.VR,))))(31.$12.(32.$12.VR,VHIA,R2>.Vmo,)$41.(33.(34.R27.(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R26.R25.R24.(35.&40.VQ,)(35.&40.(3>.(3:.(27.&8.)Vbs,)))R23.R22.(35.&40.R28.)R20.R1?.R1>.R1=.R1<.(35.&40.VG,)(35.&40.VB,)R1;.R1:.R19.R18.R17.R21.Vs10,Vs11,R16.R15.R14.R13.)VF,(35.&40.+<;4;4.)Vfc,(36.(27.&40.))R2<.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48). dpose pr_slots as (SQ0 & SQ1 & SQ2). pose proof pr_N0 as N0. pose proof pr_qal as QAL.
    dpose pr_budget as (_ & _ & DYP0 & DYF0).
    intros until xt6. intros JK8 [J T] GXNZ GRP SGA SGB VP P4999 NLE YNULL NX NY NZ PLB HLP HV HF E6. subst xs6.
    pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM.
    assert (G1 : grow_PHI 1 = 8) by (unfold grow_PHI; unfold AVOL_CALL; reflexivity).
    assert (LFR : lset_FR d = 3) by apply lset_FR_val.
    ddestruct (pr_bytes jk v f hk LBk mk J) as (BYk & BCRk & [Z0|OBk]); [exfalso; clear - Z0 HLP; lia|].
    basic_factsA hk.
    pose proof (conj J (conj T I)) as JTbox. clear J T.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk OBk B 1.
    assert (PLN : P_mpi_read_binary.chars_to_limbs plen <= N) by (unfold P_mpi_read_binary.chars_to_limbs; clear - PLB NP; Z.div_mod_to_equations; lia).
    assert (BUD' : point_read_PHIn N (Z.of_nat (length bs)) = 3 * MPI_RB_PHI (Z.of_nat (length bs)) + 16 + derive_y_PHIn N)
      by (unfold point_read_PHIn; rewrite G1; unfold AVOL_CALL; clear; lia).
    (* [comment removed for export] *)
    get_byte bs 0 b0 NB. read_at BYk NB 0 RD. rewrite Z.add_0_r in RD.
    zstep. clear RD.
    zstep. if_cases K0; zify_cond K0; ddestruct JTbox as (J & T & _).
    { eapply (pr_zero jk v f hk LBk mk dX dY dZ); [exact JK8| exact (conj J T)| exact GXNZ| exact NX| exact NY| exact NZ| |].
      - rewrite G1 in *. unfold MPI_RB_PHI in HV. unfold AVOL_CALL in HV. clear - HV DYP0 HLP. lia.
      - unfold MPI_RB_FR, fr_charge in HF. clear - HF DYF0 D0. lia. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases K1; zify_cond K1.
    { zstep. zstep. pr_a0_lit (-20352).
      eapply (pr_exit jk v f hk LBk mk dX dY dZ (-20352)); [exact JK8| exact (conj J T)| exact GXNZ| clear; lia| | | intros C; discriminate C].
      - rewrite G1 in *. unfold MPI_RB_PHI in HV. unfold AVOL_CALL in HV. clear - HV DYP0 HLP. lia.
      - unfold MPI_RB_FR, fr_charge in HF. clear - HF DYF0 D0. lia. }
    assert (LENP : plen + 1 <= Z.of_nat (length bs)) by (clear - K1 PLB P4999; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    eapply (pr_rb A_MPI_READ_BINARY HRB jk v f hk LBk mk Q dX (Q + 16) dY (Q + 32) dZ 1 plen 0xcb4fc);
      [exact J| exact T| exact SQ0| exact SQ1| exact SQ2| clear; lia| clear; lia| clear; lia| clear; lia| clear; lia| clear - PLB; lia| clear - LENP; lia| exact HLP
      | | | clear; lia| reflexivity| | reflexivity| reflexivity| reflexivity].
    - pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV BUD DYP0. lia.
    - assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF BUDF DYF0. lia.
    - cbv beta. intros h2 LB2 m2 dX2 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' J2 T2 RC2 ROK2.
      clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
        pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
      destruct RC2 as [R0|RF]; subst r.
      2:{ zstep.
          eapply (pr_exit jk _ _ h2 LB2 m2 dX2 dY dZ MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact JK8| exact (conj J2 T2)| exact GXNZ| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| | |intros C; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C; clear - C; lia].
          - pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV DYP0. lia.
          - assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF DYF0. lia. }
      destruct (ROK2 eq_refl) as [SGX2 NX2].
      pose proof (conj J2 (conj T2 I)) as JTbox. clear J T J2 T2.
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      ddestruct JTbox as (J2 & T2 & _).
      eapply (pr_xop A_MPI_LSET _ _ _ _ _ HLSET jk _ _ h2 LB2 m2 (Q + 32) dZ (Q + 16) dY Q dX2 1 0xcb50c);
        [exact J2| exact (etri_swap13 R HIA LB LF _ _ _ _ _ _ _ _ _ T2)| exact SQ2| exact SQ1| exact SQ0| clear; lia| clear; lia| clear; lia| clear; lia| cbv beta; clear; lia| clear; lia
        | cbv beta; rewrite G1; clear; lia| rewrite LFR; clear; lia| cbv beta | rewrite LFR | clear; lia| reflexivity| | reflexivity].
      + pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in *. clear - RBM H HV BUD DYP0. lia.
      + assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF BUDF DYF0. lia.
      + cbv beta. intros h3 LB3 m3 dZ3 r3 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' J3 T3 GR3. rewrite G1, LFR in J3.
        clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo) as KINV;
          pose proof (munch_refl ([] : list ivl) m3) as MU; pose proof (wmono_refl asegs m3) as WM.
        pose proof (etri_swap13 R HIA LB LF _ _ _ _ _ _ _ _ _ T3) as T3c.
        ddestruct GR3 as ([(R0 & NZ3 & _)|(RF & EQ3)] & _ & _); subst r3.
        2:{ zstep.
            eapply (pr_exit jk _ _ h3 LB3 m3 dX2 dY dZ3 MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact JK8| exact (conj J3 T3c)| exact GXNZ| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| | |intros C; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C; clear - C; lia].
            - pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV DYP0. lia.
            - assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF DYF0. lia. }
        clear CSOK SB64 ALWF' IMG' ALO ACP SCS0 NRA NRM NRF NER NES SPR BYk BCRk OBk. basic_factsA h3.
        destruct (pr_bytes jk _ _ h3 LB3 m3 J3) as (BY3 & BCR3 & [Z0|OB3]); [exfalso; clear - Z0 HLP; lia|].
        pose proof J3 as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
        pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
        assert (SCS : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HSk; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
        unfold PR_REGS in FRk. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FRk, STk by (clear; lia).
        pose proof (conj J3 (conj T3c I)) as JTbox. clear J2 T2 J3 T3 T3c.
        zstep.
        (* [comment removed for export] *)
        shadow_chk OB3 B 1.
        read_at BY3 NB 0 RD. rewrite Z.add_0_r in RD.
        zstep. clear RD.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. pr_a0_lit (-20352).
        zstep. if_cases K2; zify_cond K2.
        * (* [comment removed for export] *)
          zstep. zstep. if_cases K3; zify_cond K3; ddestruct JTbox as (J3 & T3c & _).
          { eapply (pr_exit jk _ _ h3 LB3 m3 dX2 dY dZ3 (-20352)); [exact JK8| exact (conj J3 T3c)| exact GXNZ| clear; lia| | | intros C; discriminate C].
            - pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV DYP0. lia.
            - assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF DYF0. lia. }
          (* [comment removed for export] *)
          zstep. zstep. zstep. if_cases K4; zify_cond K4.
          { zstep. zstep. pr_a0_lit (-20352).
            eapply (pr_exit jk _ _ h3 LB3 m3 dX2 dY dZ3 (-20352)); [exact JK8| exact (conj J3 T3c)| exact GXNZ| clear; lia| | | intros C; discriminate C].
            - pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV DYP0. lia.
            - assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF DYF0. lia. }
          pose proof (conj J3 (conj T3c I)) as JTbox. clear J3 T3c.
          (* [comment removed for export] *)
          zstep. zstep. zstep. do 11 zstep. zstep.
          replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
          zstep.
          ddestruct JTbox as (J3 & T3c & _).
          assert (LEN2 : Z.of_nat (length bs) = 2 * plen + 1).
          { rewrite Z.shiftl_mul_pow2 in K4 by (clear; lia). rewrite Z.mod_small in K4 by (clear - PLB P4999; lia). clear - K4. lia. }
          eapply (pr_tail_rb _ _ h3 LB3 m3 (Q + 16) dY Q dX2 (Q + 32) dZ3 (1 + plen) plen (fun _ => dX2) (fun e => e) (fun _ => dZ3));
            [exact (pr_pop jk _ _ h3 LB3 m3 J3)| exact (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T3c)| exact SQ1| exact SQ0| exact SQ2| clear; lia| clear; lia| clear; lia| clear; lia
            | intros h' LB' m' d1' T'; exact (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T')| exact GXNZ| clear - PLB; lia| clear - PLB; lia| clear - LEN2; lia| exact HLP
            | | | | reflexivity| apply f_equal; clear; lia| reflexivity].
          -- pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV DYP0. lia.
          -- assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF DYF0. lia.
          -- cbv beta. intros d1' ND1. unfold ecp_dy_sz, ecp_sz. rewrite NX2, NZ3, ND1. clear - PLN NZ N0. lia.
        * (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3; ddestruct JTbox as (J3 & T3c & _).
          { eapply (pr_exit jk _ _ h3 LB3 m3 dX2 dY dZ3 (-20352)); [exact JK8| exact (conj J3 T3c)| exact GXNZ| clear; lia| | | intros C; discriminate C].
            - pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV DYP0. lia.
            - assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF DYF0. lia. }
          pose proof (conj J3 (conj T3c I)) as JTbox. clear J3 T3c.
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. do 11 zstep. zstep.
          replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
          zstep.
          ddestruct JTbox as (J3 & T3c & _).
          eapply (pr_tail_dy _ _ h3 LB3 m3 dX2 dY dZ3);
            [exact (pr_pop jk _ _ h3 LB3 m3 J3)| exact T3c| exact GRP| exact SGA| exact SGB| exact VP| exact P4999| exact NLE| exact GXNZ| exact YNULL| rewrite NX2; exact PLN
            | unfold ecp_dy_sz, ecp_sz; rewrite NZ3; clear - NZ N0; lia| | ].
          -- pose proof (MPI_RB_PHI_mono plen (Z.of_nat (length bs)) ltac:(clear - LENP; lia)) as RBM. assert (0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia). rewrite G1 in HV. clear - RBM H HV DYP0. lia.
          -- assert (0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0). clear - H HF DYF0. lia.
    all: match goal with |- ?g => idtac "SW-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis HRBLE : mpi_read_binary_stmtA_r_c asegs R HIA A_MPI_READ_BINARY_LE.
  Hypothesis HFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L16015024961.3 L18142789841.7 L18975063279.5 L27214106967.5 L30741553502.0 L33316717491.5 L39280637297.0 L42254643250.5 L58331465648.1 L66151427842.16L66254310303.8 L6966896546.3  L861591149.2   00000<00Q00a01101201D01E01Z01^02802P02\02bS2sp2lo4LOSPS1R3HIA1h1v2hk2HV3HVkS1R1Q2A13QA23GU1S1R3HIA1h2sp3TOPSS1R2sp2lo4SLO23NERSS2sp2lo3LO04LOSP4SP64S2spS2sp2r03SPA1q1r1H2H02q02H4S1R3HIA1h1d1f2hk2HF4HFRkS2sp2lo4LOSPS1d2D0". (* [comment removed for export] *)
  #[using="p EC0 TPV D0 PAT QUW SLO2 SPA HFREE"] Lemma pr_free : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.PRET,$2.Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pc1,(27.&40.)Pxa0,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pc2,(27.&40.)Pc3,(27.&40.)Pc4,(27.&40.)Pc5,(27.&40.)Pc6,(27.&40.)Pc7,(27.&40.)Pc8,(27.&40.)Pc9,(27.&40.)Pc10,(27.&40.)Pc11,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)PQ',P,$2:.SpP,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R27.R26.R25.R24.R23.)P,(1>.VR,VHIA,VLB,VLF,R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R24.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R23.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R22.)P,(<.(=.(>.R27.+10.)R25.)(=.(>.R25.+10.)R27.))P,(<.(=.(>.R28.+10.)R24.)(=.(>.R24.+10.)R28.))P,(=.VQ,R29.)P,(=.(>.R2:.+10.)(>.VQ,+30.))P,(1.$9.(:.R2:.)$77.)P,(=.(>.(2<.$12.VR,VHIA,Vh,)(>.R31.$7<.))$2=.)P,(=.(>.(2>.$12.VR,VHIA,Vh,)(>.R31.(7=.Vd,)))$2?.)P,(14.(=.=R28.)(20.R28.(21.+2.+40.)))P,(1.$2.(30.R29.+2.)=)P,Ph',(28.$12.VR,VHIA,)Pm',P,(27.&40.)(29.(27.&8.))Pt0',(27.&40.)Pt1',(27.&40.)Pt2',(27.&40.)Pa0',(27.&40.)Pa1',(27.&40.)Pa2',(27.&40.)Pa3',(27.&40.)Pa4',(27.&40.)Pa5',(27.&40.)Pa6',(27.&40.)Pa7',(27.&40.)Pt3',(27.&40.)Pt4',(27.&40.)Pt5',(27.&40.)Pt6',(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.(>.R46.$7<.)(>.R45.(7=.Vd,))R11.R43.R10.)P,(1>.VR,VHIA,VLB,VLF,R12.R44.R11.R42.(7>.R42.+1.==(1=.(27.&40.))(7?.R41.)$77.)R40.R3?.R3>.R3=.)(31.$12.(32.$12.VR,VHIA,R13.Vmo,)R22.(33.(34.(35.&40.R3=.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R11.R10.R?.(35.&40.VQ,)R39.R>.R=.R<.R;.R:.R9.R8.R7.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R6.R5.R4.R3.)VF,(35.&40.R3=.)Vfc,(36.(27.&40.))R12.(37.$12.)))P,(1.(27.&40.)R26.(35.&40.R31.))(31.$12.(32.$12.VR,VHIA,R35.Vmo,)R11.(33.(34.(35.&40.R2<.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R2;.R2:.R29.(35.&40.VQ,)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)VF,(35.&40.$80.)Vfc,(36.(27.&40.))R33.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros until Q'. intros J T S1 S2 S3 S12 S13 QA1 QA2 EO HV HF HRET HRE K E0. subst xa0.
    pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. pose proof (arl_need_ecp_rt R) as NER.
    pose proof T as (T1 & _). dpose S1 as (CW1 & SL1 & _ & _).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk A1 d1 (bv_unsigned sp + -96) J T1 CW1 SL1 ltac:(clear - LOSP; lia))
      as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (UW1 : uw_obj R A1 16 d) by (destruct QUW as [[GU1 GU2]|GU]; [left; split; [clear - GU1 QA2; lia| exact GU2]| right; exact GU]).
    pose proof XM as [MAT SG1]. dpose MAT as (CX1 & AL1 & X01 & LL1 & NR1 & OW1). rewrite EO in OW1. destruct OW1 as [P0 N0'].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof HFREE as HC. unfold mpi_free_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (X := md_addr d1) (sw := Z_to_bv 64 (md_sg d1)) (n := md_n d1) (P := md_p d1) (limbs := md_limbs d1)
                     (pad := md_pad d1) (own := md_own d1) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by (clear - LO0 LOSP SP64; lia).
      - exact HHk.
      - exact HK1.
      - exact MAT.
      - exact XNS.
      - rewrite EO. cbn [P_mpi_free.mpi_free_LB]. exact (proj1 XWR).
      - intros C. rewrite EO in C. discriminate C.
      - replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by (clear; lia). exact STk.
      - exact LOS.
      - clear - SLO2 NER. lia.
      - rewrite HTk. clear - TOP. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact TPV.
      - exact MIk.
      - exact (proj1 XAO).
      - clear - HV HVk. lia.
      - rewrite XAD. exact UW1.
      - clear - HF HFRk. lia.
      - rewrite XAD. reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & CX2).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HP2 by (clear - LO0 LOSP SP64; lia).
    rewrite EO in HP2, HH2. cbn [P_mpi_free.mpi_free_LB P_mpi_free.mpi_free_X] in HP2, HH2. rewrite XAD in HP2, CX2.
    rewrite (ret_pc_even RET HRET HRE).
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in ST2' by (clear; lia).
    set (d1' := mkMPD A1 1 0 0 [] (md_pad d1) LNull).
    assert (MX2 : mpd_at asegs m2 LBk d1').
    { unfold d1', mpd_at, mpi_at. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. rewrite XAD in AL1, X01.
      split; [| left; reflexivity]. split; [exact CX2|]. split; [exact AL1|]. split; [exact X01|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia| split; reflexivity]. }
    assert (OUT2 : mpd_out LBk d1 LBk d1').
    { unfold mpd_out, d1'. cbn [md_addr md_own]. split; [symmetry; exact XAD|]. split; [discriminate|].
      split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b Hb. unfold mpd_blk in Hb. rewrite EO in Hb. destruct Hb. }
    assert (KEEP : mpd_keep LBk d1 = LBk) by (unfold mpd_keep; rewrite EO; reflexivity).
    destruct (etri_call R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk A1 d1 A2 d2 A3 d3 m2 h2 LBk d1' (bv_unsigned sp + -96) AVOL_CALL (fr_charge d)
                J T S1 S2 S3 S12 S13 ltac:(clear - LOSP; lia) ltac:(unfold AVOL_CALL; clear; lia) ltac:(unfold fr_charge; clear - D0; lia)
                MI2 ST2' ltac:(rewrite KEEP; exact HP2) HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 ltac:(intros b Hb; destruct Hb)) as [J2 T2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact J2| exact T2].
    all: match goal with |- ?g => idtac "FREE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0>L10633144206.3L10947173192.2L20317546771.7L2333536794.10L28006323098.1L28639647395.3L35653327737.6L37831063278.7L38948636245.0L44946436004.8L46816783159.5L48132467214.6L50790731766.5L5246360089.2 L52616371395.6L60098763854.3L6064815669.3 L60858800200.1L61896008187.3L66566358642.500000900@00Z01601:01F01Z02202302P02]03303E03L03\03f03o04304;04GS2d11a2HaS2sp2loS1R2d13DI13DI23MC13MC23PI1S1R3HIA1h2sp2lo3LOS3TOP1a2HaS2d1S2sp2lo4MCLOS1R3HIA1h2sp2lo4SPHIS1R2sp2lo3LOS3ALO2dd3PCdSS1R2sp2lo4LOSP2d13LOS3ALO3PC1S2sp2lo1A3SLAS1R2sp2lo4LOSP3LOS3ALOS1R2sp2lo4LOSP3LOSS2d12N1S1R3HIA1h2sp1a1SS1R2lo3LOSS2d12dd1KS2spS2d11A1KS2sp2lo1x2Hx". (* [comment removed for export] *)
  #[using="p EC0 PAT SLO2"] Lemma pr_limbs : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.Pm',P,(27.&40.)(29.(27.&8.))Pxs',(24.(27.&40.))P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R=.R<.R;.R:.R9.)P,(1>.VR,VHIA,VLB,VLF,R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R:.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R9.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R8.)P,(<.(=.(>.R=.+10.)R;.)(=.(>.R;.+10.)R=.))P,(<.(=.(>.R>.+10.)R:.)(=.(>.R:.+10.)R>.))P,(1.$9.(:.R>.)$;.)P,(5>.(17.(1;.$2.$2.)(1<.$2.$2.Vlo,(>.(16.&40.Vsp,)-60.))(17.(1;.$2.$2.)(1<.$2.$2.(3.R?.)(>.(3.R?.)(?.+4.(10.R?.))))(1=.(1;.$2.$2.))))R11.R:.)P,(5?.$12.R12.R;.)P,(60.$12.R<.)P,(62.$12.R=.Vlo,(>.(16.&40.Vsp,)-60.))P,(69.$12.R>.R16.(7>.(81.R13.)(51.R13.)(10.R13.)(3.R13.)R=.(7?.R13.)(:.R13.)))(14.(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R1:.R19.R18.R17.R?.)(1>.VR,VHIA,VLB,VLF,R18.R17.R?.R15.(7>.(81.R14.)(51.R14.)(10.R14.)(3.R14.)R>.(7?.R14.)(:.R14.))R13.R12.R11.R10.))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros until xs'. intros J T S1 S2 S3 S12 S13 EO MU WM MI' ST' MX'.
    pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose T as (T1 & T2 & T3 & D12 & D13 & D23 & COV). dpose T1 as (MY1 & EA1 & NS1 & FRS1 & OA1).
    destruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC v f hk LBk mk A1 d1 J T1 EO) as (IN1 & N1 & P01 & PC1 & PI1 & NIN1 & FRA1).
    pose proof (hcs_ok asegs R HIA hk) as CSOK.
    set (W := [(lo, bv_unsigned sp + -96); (md_p d1, md_p d1 + 4 * md_n d1)]) in *.
    assert (SCS : crange (hcs asegs R HIA hk) lo (bv_unsigned sp - lo)).
    { eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI; lia]. }
    assert (WC : w_client (hcs asegs R HIA hk) W).
    { unfold w_client, W. apply Forall_cons; [cbn [fst snd]; intros x Hx; apply SCS; clear - Hx LOSP; lia|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (md_p d1 + 4 * md_n d1 - md_p d1) with (4 * md_n d1) by (clear; lia).
      eapply aobj_crange. eapply hm_aobj_block; [exact HHk| exact IN1]. }
    assert (HH' : HM asegs R HIA hk LBk LF m').
    { eapply (hm_munch asegs R HIA hk LBk LF W mk m' HHk MU WM). unfold W.
      apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; rewrite HTk; clear - Ha LOS TOP LOSP; lia|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. right. right.
      exists (md_p d1, 4 * md_n d1). split; [apply in_or_app; left; exact IN1| cbn [fst snd]; clear - Ha; lia]. }
    assert (DMCW : disjoint_from W MC 8).
    { unfold W. cbn [disjoint_from fst snd]. ddestruct MCOK as (MC1 & MC2 & _). destruct DIMG as [DI1 DI2].
      split; [clear - MCLO; lia| split; [clear - PI1 MC1 MC2 DI1 DI2; lia| exact I]]. }
    assert (DSLOT : forall A, SLOT A -> disjoint_from W A 16).
    { (intros A dd_H; ddestruct dd_H as (CWA & SLA & _ & _)). unfold W. cbn [disjoint_from fst snd].
      assert (CRA : client_range L (LB ++ fdata LF) (bv_unsigned sp) A 16).
      { intros a Ha. destruct (CWA a Ha) as [S|[D|Bk]]; [left; clear - S; lia| right; left; exact D| right; right; exact Bk]. }
      pose proof (fresh_apart_client R LB LF (bv_unsigned sp) A 16 _ _ FRA1 CRA ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS LOSP; lia)) as K.
      split; [clear - SLA LOSP; lia| split; [clear - K; lia| exact I]]. }
    assert (DTMP : forall A dd, ejtmp R HIA LB LF hk LBk mk A dd -> edis d1 dd -> SLOT A -> ejtmp R HIA LB LF hk LBk m' A dd).
    { intros A dd TT DD SA. dpose TT as (MY & EA & NS & FRS & OA).
      split; [| split; [exact EA| split; [exact NS| split; [exact FRS|]]]].
      - eapply mpd_at_munch_any; [exact MY| exact MU| exact WM| rewrite EA; exact (DSLOT A SA)|].
        intros ON. assert (EOd : md_own dd = LHeap) by (destruct (md_own dd); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (NS eq_refl)]).
        destruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC v f hk LBk mk A dd J TT EOd) as (INd & Nd & P0d & PCd & _).
        destruct (hm_apart asegs R HIA hk LBk LF mk HHk) as [_ BA].
        pose proof (blocks_apart_in2 (LBk ++ LF) _ _ _ _ BA ltac:(apply in_or_app; left; exact IN1) ltac:(apply in_or_app; left; exact INd) (DD EO EOd)) as K.
        unfold W. cbn [disjoint_from fst snd]. split; [clear - PCd ALO LOS; lia| split; [clear - K; lia| exact I]].
      - eapply (aobj_munch asegs AL _ CSOK W mk m'); [exact WC| exact MU| exact OA]. }
    split.
    - constructor; try assumption.
      + eapply presA_trans; [exact PXk|]. apply presA_nil_any.
        eapply (presA_drop_fresh asegs R HIA h LB LF [] (md_p d1) (4 * md_n d1) mk m' (bv_unsigned sp)); [| exact FRA1| clear - LOS LOSP; lia].
        eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp + -96) m mk m' (bv_unsigned sp) HH); [| clear; lia| exact LOS].
        rewrite <- HSk.
        eapply presA_weaken; [| exact SUBk| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x Hx; exact Hx].
        eapply (presA_of_munch asegs R LBk LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA hk) W mk m' (hcs asegs R HIA hk) CSOK); [exact WC| | exact MU| exact WM].
        intros c0 Hc. eapply cshd_hcs; [exact HHk| apply Z.le_refl| exact Hc].
      + exists ck. eapply rw_cells_transport; [exact MCk| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact DMCW.
      + eapply rw_cells_transport; [exact FRk| exact MU| exact WM|]. unfold PR_REGS. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold W. cbn [disjoint_from fst snd].
        split; [clear; lia| split; [clear - PC1 ALO LOS LOSP; lia| exact I]].
    - split.
      + split; [exact MX'|]. cbn [md_addr md_own]. split; [exact EA1|]. split; [exact NS1|]. split.
        * intros b Hb. apply FRS1. unfold mpd_blk in *. cbn [md_own md_p md_n] in Hb. exact Hb.
        * eapply (aobj_munch asegs AL _ CSOK W mk m'); [exact WC| exact MU| exact OA1].
      + split; [exact (DTMP A2 d2 T2 D12 S2)|]. split; [exact (DTMP A3 d3 T3 D13 S3)|].
        split; [intros O1 O2; cbn [md_p]; exact (D12 EO O2)|]. split; [intros O1 O2; cbn [md_p]; exact (D13 EO O2)|]. split; [exact D23|].
        intros b Hb. destruct (COV b Hb) as [K|K]; [left; exact K| right]. unfold mpd_blk in *. cbn [md_own md_p md_n]. exact K.
    all: match goal with |- ?g => idtac "LIMBS-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L13479214727.4 L35653327737.7 L40400849357.6 L42254643250.5 L50190268317.5 L58331465648.1 L60098763854.3 L66151427842.16L6966896546.3  00000>00R00g01<01N01R01\02602BS2sp2lo2A13SL1S1R3HIA1h2sp2lo4SPHIS1R2lo2d13LOS3ALO3PC1S2sp2lo3LO04LOSP4SP64S1R2sp2lo4SLO23NE0S2spS1R2lo3LOSS2sp2r03SPA1q1r1H2H02q02H4S2sp2lo4LOSP". (* [comment removed for export] *)
  #[using="IMG p EC0 PAT SLO2 SPA"] Lemma pr_setbit0 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PA1,$2.Pd1,$6.PA2,$2.Pd2,$6.PA3,$2.Pd3,$6.Ppos,$2.PRET,$2.Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pc1,(27.&40.)Pxa0,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pc2,(27.&40.)Pc3,(27.&40.)Pc4,(27.&40.)Pc5,(27.&40.)Pc6,(27.&40.)Pc7,(27.&40.)Pc8,(27.&40.)Pc9,(27.&40.)Pc10,(27.&40.)Pc11,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)PQ',P,$2:.SpP,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R28.R27.R26.R25.R24.)P,(1>.VR,VHIA,VLB,VLF,R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R25.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R24.)P,(2;.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)Vlo,(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R23.)P,(<.(=.(>.R28.+10.)R26.)(=.(>.R26.+10.)R28.))P,(<.(=.(>.R29.+10.)R25.)(=.(>.R25.+10.)R29.))P,(=.VQ,R2:.)P,(=.(>.R2;.+10.)(>.VQ,+30.))P,(1.$9.(:.R2;.)$;.)P,(14.(=.=R27.)(20.R27.(21.+2.+40.)))P,(14.(=.=R27.)(20.R27.(21.+2.+40.)))P,(1.$2.(30.R28.+2.)=)P,Pm',P,(27.&40.)(29.(27.&8.))Pxs',(24.(27.&40.))Pt0',(27.&40.)Pt1',(27.&40.)Pt2',(27.&40.)Pa1',(27.&40.)Pa2',(27.&40.)Pa3',(27.&40.)Pa4',(27.&40.)Pa5',(27.&40.)Pa6',(27.&40.)Pa7',(27.&40.)Pt3',(27.&40.)Pt4',(27.&40.)Pt5',(27.&40.)Pt6',(27.&40.)P,(15.VR,VHIA,Vh,VLB,VLF,Vm,(16.&40.Vsp,)Vlo,+60.(17.$18.(70.Vs10,)$1:.)(17.(1;.$2.$2.)(1<.$2.$2.VQ,(>.VQ,+30.))(17.(1;.$2.$2.)(1<.$2.$2.$13.(>.$13.+8.))(1=.(1;.$2.$2.))))$13.R45.R44.R43.R42.R10.)P,(1>.VR,VHIA,VLB,VLF,R44.R43.R11.R41.(7>.(81.R40.)(51.R40.)(10.R40.)(3.R40.)R10.(7?.R40.)(:.R40.))R3?.R3>.R3=.R3<.)(31.$12.(32.$12.VR,VHIA,R45.Vmo,)R20.(33.(34.(35.&40.R3;.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R10.R?.R>.(35.&40.VQ,)R37.(35.&40.=)R=.R<.R;.R:.R9.R8.R7.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R6.R5.R4.R3.)VF,(35.&40.R3;.)Vfc,(36.(27.&40.))R12.(37.$12.)))P,(1.(27.&40.)R25.(35.&40.R31.))P,(1.(27.&40.)R25.(35.&40.R2<.))P,(1.(27.&40.)R25.(35.&40.=))(31.$12.(32.$12.VR,VHIA,R37.Vmo,)R12.(33.(34.(35.&40.R2=.)(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R2<.R2;.R2:.(35.&40.VQ,)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)VF,(35.&40.$82.)Vfc,(36.(27.&40.))R35.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48).
    intros until Q'. intros J T S1 S2 S3 S12 S13 QA1 QA2 EO HPOS HRET HRE K E0 E1 E2. subst xa0 xa1 xa2.
    pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. pose proof (arl_need_ecp_rt R) as NER.
    pose proof (ej_facts R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    pose proof T as (T1 & _). dpose S1 as (CW1 & SL1 & _ & _).
    destruct (ej_opY R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC EC v f hk LBk mk A1 d1 (bv_unsigned sp + -96) J T1 CW1 SL1 ltac:(clear - LOSP; lia))
      as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    destruct (ejtmp_blk R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC v f hk LBk mk A1 d1 J T1 EO) as (IN1 & N1 & P01 & PC1 & PI1 & NIN1 & FRA1).
    assert (SCS : crange (hcs asegs R HIA hk) lo (bv_unsigned sp + -96 - lo)).
    { eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI LOSP; lia]. }
    pose proof (A_mpi_set_bit0_spec AL IMG) as SPC. unfold mpi_set_bit0_stmtA in SPC.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { eapply SPC with (LB := LBk) (dX := d1) (pos := pos) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by (clear - LO0 LOSP SP64; lia).
      - exact XM.
      - exact XNS.
      - intros _. split; [exact P01| clear - PC1 ALO LOS; lia].
      - exact MIk.
      - exact HPOS.
      - exact (art_alwf asegs R HIA).
      - exact (hcs_ok asegs R HIA hk).
      - exact (hm_abase asegs R HIA hk LBk LF mk HHk).
      - exact (proj1 XAO).
      - intros _. eapply hm_aobj_block; [exact HHk| exact IN1].
      - replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by (clear; lia). exact STk.
      - exact LO0.
      - clear - SLO2 NE0. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact SCS.
      - rewrite XAD. clear - SL1. lia.
      - exact (proj2 XWR).
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    intros ms' PO. unfold mpi_set_bit0_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & xs2 & E & MU2 & WM2 & MI2 & ST2 & MX2 & LEN2). subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in MU2, ST2 by (clear - LO0 LOSP SP64; lia).
    rewrite (ret_pc_even RET HRET HRE).
    destruct (pr_limbs jk v f hk LBk mk A1 d1 A2 d2 A3 d3 m2 xs2 J T S1 S2 S3 S12 S13 EO MU2 WM2 MI2 ST2 MX2) as [J2 T2].
    eapply K; [exact J2| exact T2].
    all: match goal with |- ?g => idtac "SETBIT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis GOB : aobj asegs AL (hcs asegs R HIA h) m G 192.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L50790580594.6L52615975131.5L59314923118.600000A00N00]S1R2sp2lo3LOS3SLOS2sp1G1a2Ha1KS1G2lo1a2Ha1S1K". (* [comment removed for export] *)
  #[using="EC0 GCR GSP GOB"] Lemma pr_gobj : forall (jk : list byte) v f hk LBk mk, EJ0 v f hk LBk mk -> aobj asegs AL (hcs asegs R HIA hk) mk G 192.
  Proof.
    intros jk v f hk LBk mk J. pose proof (EC0 jk) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
    { intros a Ha. destruct (GCR a Ha) as [S|[D|Bk]]; [| right; left; exact D| right; right; exact Bk].
      destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    eapply aobj_cs_mono; [exact HCSk|].
    eapply (presA_aobj0 asegs R); [exact (hcs_ok asegs R HIA h)| exact PXk| exact GOB| intros x Hx; eapply hcs_below_top; exact Hx|].
    right. split; [exact CRS| clear - LOS SLO FR0; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11007094131.173L12263194313.0  L12860309875.172L17387139489.0  L18457785511.0  L22768689836.1  L2397676628.0   L25952690121.8  L26470913780.8  L27838437606.1  L29956516996.0  L3798936004.8   L39188636933.0  L39332637397.0  L55516431550.1  L59093286312.1  L59315053158.1  L6664711336.1   Q23890796818.181Q33656017904.181Q4155597051.182 Q4155970771.181 Q55391880562.180Q55964990415.182Q59394051867.181Q63579311504.180Q64341970611.180Q64356526075.181Q64619154459.182Q7661097679.181 00000Q00R01301401501801901Q01h01k01l02C02D02E02H02K02N02Q02l03G03b04=04X05305a06<06W07207`08;S2LF2ra2sp1G2bs3LFB2jk2dZ3JK83GHISS2LF2ra2sp1G2bs3LFB2jk2dZ3JK83GHISSS1QSS1N2N02dX2dY2dZ2NX2NY2NZS1R3HIA1h1N1d4BUDF1f2HFS1QSS1R3HIA1h2bs1N3BUD1v2HVSSS1GS1QS1CS1QS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF2ra2sp1G2bs3LFB2jk2dZ3JK83SPR3GAL4GPOS3GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF1G2bs3LFB2jk2dZ3JK83GHIS2LF2ra2sp1G2bs3LFB2jk2dZ3JK83SPR3GAL4GPOS3GHIS2LF1G2bs3LFB2jk2dZ3JK83GHI". (* [comment removed for export] *)
  #[using="IMG HLSET EC0 TPV GAT GCR GSP GMC PAT QCW QSP QMC QUW QG QGL SLO2 SPA BUD BUDF NP LFB GOB"] Lemma pr_mx_tail : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PdX,$6.PdY,$6.PdZ,$6.Pxra,(27.&40.)Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxa0,(27.&40.)Pxa1,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxs6,(27.&40.)Pxs9,(27.&40.)Pxs10,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(1.$39.(3:.(27.&8.)R1<.)#8.)P,(3;.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(1.$2.(3.(79.(5.Vg,)))=)P,(=.(10.R1:.)VN,)P,(=.(10.R1:.)+1.)P,(=.(10.R1:.)+1.)P,(=.(>.R22.(5:.+1.))(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.(>.R22.+3.)(3?.VN,Vd,))(31.$12.(32.$12.VR,VHIA,R22.Vmo,)$41.(33.(34.R1<.(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R1;.R1:.R19.(35.&40.VQ,)(35.&40.(3>.(3:.(27.&8.)Vbs,)))R18.R17.R16.R15.R14.R13.R12.R11.(35.&40.VG,)(35.&40.VB,)(35.&40.(>.VG,+38.))(35.&40.(>.VG,+48.))R10.(35.&40.(>.(83.(>.VG,+38.)+3.)(7;.(48.VR,))))(35.&40.(>.(83.(>.VG,+48.)+3.)(7;.(48.VR,))))R?.R>.Vs11,R=.R<.R;.R:.)VF,(35.&40.+<;5><.)Vfc,(36.(27.&40.))R20.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48). dpose pr_slots as (SQ0 & SQ1 & SQ2). pose proof pr_N0 as N0.
    intros until xt6. intros JK8 [J T] GXNZ GYZ NX NY NZ HV HF.
    pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM.
    assert (G1 : grow_PHI 1 = 8) by (unfold grow_PHI; unfold AVOL_CALL; reflexivity).
    assert (LFR : lset_FR d = 3) by apply lset_FR_val.
    pose proof (conj J (conj T I)) as JTbox. clear J T.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    ddestruct JTbox as (J & T & _).
    eapply (pr_xop A_MPI_LSET _ _ _ _ _ HLSET jk _ _ hk LBk mk (Q + 32) dZ (Q + 16) dY Q dX 1 0xcb5f8);
      [exact J| exact (etri_swap13 R HIA LB LF _ _ _ _ _ _ _ _ _ T)| exact SQ2| exact SQ1| exact SQ0| clear; lia| clear; lia| clear; lia| clear; lia| cbv beta; clear; lia| clear; lia
      | cbv beta; rewrite G1; clear; lia| rewrite LFR; clear; lia| cbv beta; rewrite G1 in *; clear - HV BUD; lia | rewrite LFR; clear - HF BUDF; lia | clear; lia| reflexivity| | reflexivity].
    cbv beta. intros h3 LB3 m3 dZ3 r3 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' J3 T3 GR3. rewrite G1, LFR in J3.
    clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo) as KINV;
      pose proof (munch_refl ([] : list ivl) m3) as MU; pose proof (wmono_refl asegs m3) as WM.
    pose proof (etri_swap13 R HIA LB LF _ _ _ _ _ _ _ _ _ T3) as T3c.
    ddestruct GR3 as ([(R0 & NZ3 & _)|(RF & EQ3)] & _ & _); subst r3.
    2:{ zstep.
        eapply (pr_exit jk _ _ h3 LB3 m3 dX dY dZ3 MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact JK8| exact (conj J3 T3c)| exact GXNZ| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| rewrite G1 in HV; exact HV| exact HF
          |intros C; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C; clear - C; lia]. }
    basic_factsA h3.
    pose proof (pr_gobj jk _ _ h3 LB3 m3 J3) as GOB3.
    pose proof (pr_grp jk _ _ h3 LB3 m3 J3 GXNZ) as GAT3.
    dpose GAT3 as (_ & GAL & GPOS & _ & _ & _ & _ & _ & _ & _ & (EGX & EGY & _ & MGX & MGY & _) & _ & GTL & _).
    pose proof (rw_cells_bound _ _ _ _ GTL) as GHI. unfold grp_tail_cells in GHI. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in GHI. clear GTL.
    pose proof (mpdr_p_range' _ _ _ _ MGX) as GXR. pose proof (mpdr_p_range' _ _ _ _ MGY) as GYR.
    pose proof MGX as (CGX & _). pose proof MGY as (CGY & _). unfold mpi_cells in CGX, CGY. rewrite EGX in CGX. rewrite EGY in CGY.
    replace (G + 56 + 16) with (G + 72) in CGY by (clear; lia). clear MGX MGY GAT3.
    pose proof (conj J3 (conj T3c I)) as JTbox. clear J3 T3 T3c.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KX; zify_cond KX; rewrite ?Z.mod_small in KX by exact GXR; [exfalso; exact (GXNZ KX)|].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KY; zify_cond KY; rewrite ?Z.mod_small in KY by exact GYR; [| exfalso; exact (KY GYZ)].
    ddestruct JTbox as (J3 & T3c & _).
    eapply (pr_exit jk _ _ h3 LB3 m3 dX dY dZ3 0); [exact JK8| exact (conj J3 T3c)| exact GXNZ| clear; lia| rewrite G1 in HV; exact HV| exact HF|].
    intros _. unfold ecp_dy_sz, ecp_sz. rewrite NZ3. clear - NX NY NZ N0. lia.
    all: match goal with |- ?g => idtac "MXT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@L13741127908.192L13755790566.189L14485315996.12 L15089158174.4  L16073394164.193L16075584458.131L16629301330.1  L17379153958.8  L18397517277.6  L18691776455.4  L18753489717.2  L23305025156.0  L24029143540.8  L24097320787.1  L24803304693.4  L26482986152.1  L28717461921.0  L29956516996.0  L31244335457.1  L35813672890.5  L3625504082.1   L39188636933.0  L39220637093.0  L39280637297.0  L40870879649.0  L41551960790.8  L4855685921.0   L50339925160.1  L52067443862.7  L57425804946.131L58724481964.1  L59308579414.10 L59315053158.1  L6123187174.1   L62499566127.5  L64009471222.1  L64587389024.9  L66555306242.1  L66651401969.1  L861591149.2    L9999373409.192 Q22302874620.198Q22308835568.200Q22309129225.201Q24795532011.200Q26295627581.201Q32032123914.198Q46509596121.201Q51959900438.201Q64969063261.201Q8958280274.198 00000S01601P01[02O03403703N03`03j04004104H04K04V04Y04Z04[04^04l04o05005105205305J05K05N05h06O06R06f06i06l07;07?07Z07^07b07h08F08^09609N09f0:>0:V0;30;K0;c0<;S2LF2ra2sp1G2bs3LFB2jk3JK84GPOS3GHIS2LF2ra2sp1G2bs3LFB2jk3JK84GPOS3GHIS1g1N2NP4plen3PLB1q1r1H2H0S2bs1N1v2HVS2LF2ra2sp1G1B2bs2B03B633LFB2jk3JK83HLP3SPR4GPOS3GHIS2LF2ra2sp1B2bs2B03B633LFB2jk3JK83HLPS1QS1R3HIA1h2bs1N3BUD1v2HVS1N1d1f2HF3RF03FC0S1N1d1f2HFS1g2NRSS1R3HIA1h1N1d4BUDF1f2HFS1QS2bs1N1v2HVS1QSSS1QS1N1d1f2HF3FC0S1QSSSSS1R3HIA1h2bs1N3BUD1v2HVSS1QS1g2bs4plen3PLB3HLP3NPR2K0S2LF2ra2sp1g2bs3LFB2jk4plen3JK83PLB3NPRS1QS2bs3HLP1q2E01r1H2H0S1CS1QS2bs1N1v2HV3RB0S2bsS1R3HIA1h1N1d4BUDF1f2HF3FC0S2bsS2bsS1d2D0S2LF2ra2sp1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK84GPOS3GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHI". (* [comment removed for export] *)
  #[using="IMG HLSET EC0 TPV D0 GAT GCR GSP GMC PAT QCW QSP QMC QUW QG QGL SLO2 SPA BUD BUDF BYT B0 B63 BCR BSP BQ BMC BOB B47 C24H NP LFB HRBLE HFREE GOB"] Lemma pr_mx : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pjk,(24.(27.&8.))Pv,$2.Pf,$2.Phk,(28.$12.VR,VHIA,)PLBk,(24.$25.)Pmk,P,(27.&40.)(29.(27.&8.))PdX,$6.PdY,$6.PdZ,$6.Pplen,$2.Pxra,(27.&40.)Pxt0,(27.&40.)Pxt1,(27.&40.)Pxt2,(27.&40.)Pxa2,(27.&40.)Pxa3,(27.&40.)Pxa4,(27.&40.)Pxa5,(27.&40.)Pxa6,(27.&40.)Pxa7,(27.&40.)Pxs9,(27.&40.)Pxt3,(27.&40.)Pxt4,(27.&40.)Pxt5,(27.&40.)Pxt6,(27.&40.)P,(1.$39.(3:.(27.&8.)R19.)#8.)P,(3;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(1.$2.(3.(79.(5.Vg,)))=)P,(1.$9.(:.R16.)$77.)P,(=.(10.R16.)+1.)P,(14.(=.=R16.)(=.R16.(?.+4.(10.(75.Vg,)))))P,(20.=(3>.(3:.(27.&8.)Vbs,)))P,(=.(>.R20.(>.(>.(4>.(3>.(3:.(27.&8.)Vbs,)))$7<.)(5:.+1.)))(3=.VN,(3>.(3:.(27.&8.)Vbs,))))P,(=.(>.R20.(>.(>.(4?.Vd,)(7=.Vd,))+3.))(3?.VN,Vd,))(31.$12.(32.$12.VR,VHIA,R20.Vmo,)$41.(33.(34.R19.(35.&40.(>.(16.&40.Vsp,)-60.))Vgp,Vtp,R18.R17.R16.(35.&40.VQ,)(35.&40.(3>.(3:.(27.&8.)Vbs,)))(35.&40.R1:.)(35.&40.-5000.)R15.R14.R13.R12.R11.R10.(35.&40.VG,)(35.&40.VB,)(35.&40.(>.VG,+38.))(35.&40.(>.VG,+48.))(35.&40.(7;.(48.VR,)))(35.&40.(>.(83.(>.VG,+38.)+3.)(7;.(48.VR,))))(35.&40.(>.(83.(>.VG,+48.)+3.)(7;.(48.VR,))))R?.Vs10,Vs11,R>.R=.R<.R;.)VF,(35.&40.+<;588.)Vfc,(36.(27.&40.))R1>.(37.$12.)))")
(* [comment removed for export] *).
  Proof.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48). dpose pr_slots as (SQ0 & SQ1 & SQ2). pose proof pr_N0 as N0. pose proof pr_qal as QAL.
    intros until xt6. intros JK8 [J T] GXNZ GYZ YNULL NZ PLB HLP HV HF.
    pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU; pose proof (wmono_refl asegs mk) as WM.
    assert (G1 : grow_PHI 1 = 8) by (unfold grow_PHI; unfold AVOL_CALL; reflexivity).
    assert (RB0 : 0 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia).
    assert (RF0 : 0 <= MPI_RB_FR d) by (apply MPI_RB_FR_nonneg; exact D0).
    assert (FC0 : 0 <= fr_charge d) by (unfold fr_charge; clear - D0; lia).
    assert (AV0 : AVOL_CALL = 0) by reflexivity.
    assert (NPR : md_n (g_P g) <= 10000).
    { ddestruct GAT as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & NR & _) & _). unfold MPI_MAX_LIMBS in NR. clear - NR. lia. }
    pose proof (conj J (conj T I)) as JTbox. clear J T.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      ddestruct JTbox as (J & T & _).
      zstep. zstep. pr_a0_lit (-20352).
      eapply (pr_exit jk v f hk LBk mk dX dY dZ (-20352)); [exact JK8| exact (conj J T)| exact GXNZ| clear; lia| rewrite G1, AV0 in HV; clear - HV RB0; lia| clear - HF RF0 FC0; lia| intros C; discriminate C]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    ddestruct JTbox as (J & T & _).
    eapply (pr_rb A_MPI_READ_BINARY_LE HRBLE jk v f hk LBk mk Q dX (Q + 16) dY (Q + 32) dZ 0 (Z.of_nat (length bs)) 0xcb5ac);
      [exact J| exact T| exact SQ0| exact SQ1| exact SQ2| clear; lia| clear; lia| clear; lia| clear; lia| clear; lia| clear; lia| clear; lia| exact HLP
      | rewrite G1, AV0 in HV; clear - HV BUD; lia| clear - HF BUDF FC0; lia| clear; lia| reflexivity| | reflexivity| rewrite Z.add_0_r; reflexivity| reflexivity].
    cbv beta. intros h2 LB2 m2 dX2 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' J2 T2 RC2 ROK2.
    clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo) as KINV;
      pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    destruct RC2 as [R0|RF]; subst r.
    2:{ zstep.
        eapply (pr_exit jk _ _ h2 LB2 m2 dX2 dY dZ MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact JK8| exact (conj J2 T2)| exact GXNZ| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia
          | rewrite G1, AV0 in HV; clear - HV; lia| clear - HF FC0; lia|intros C; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C; clear - C; lia]. }
    destruct (ROK2 eq_refl) as [SGX2 NX2].
    pose proof (conj J2 (conj T2 I)) as JTbox. clear J T J2 T2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    ddestruct JTbox as (J2 & T2 & _).
    eapply (pr_free jk _ _ h2 LB2 m2 (Q + 16) dY Q dX2 (Q + 32) dZ 0xcb5b8);
      [exact J2| exact (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T2)| exact SQ1| exact SQ0| exact SQ2| clear; lia| clear; lia| clear; lia| clear; lia| exact YNULL
      | rewrite G1, AV0 in HV; rewrite AV0; clear - HV BUD; lia| clear - HF BUDF; lia| clear; lia| reflexivity| | reflexivity].
    intros h3 m3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' J3 T3.
    clear LAWS KINV MU WM; pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo) as KINV;
      pose proof (munch_refl ([] : list ivl) m3) as MU; pose proof (wmono_refl asegs m3) as WM.
    pose proof (etri_swap12 R HIA LB LF _ _ _ _ _ _ _ _ _ T3) as T3c.
    set (dY3 := mkMPD (Q + 16) 1 0 0 [] (md_pad dY) LNull) in *.
    basic_factsA h3.
    pose proof (pr_gobj jk _ _ h3 LB2 m3 J3) as GOB3.
    pose proof (pr_grp jk _ _ h3 LB2 m3 J3 GXNZ) as GAT3.
    dpose GAT3 as (HD3 & GAL & GPOS & _ & _ & _ & _ & _ & _ & _ & _ & _ & GTL & GIDR & _).
    pose proof (rw_cells_bound _ _ _ _ GTL) as GHI. unfold grp_tail_cells in GHI. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in GHI. clear GTL.
    unfold grp_head_cells in HD3. clear GAT3.
    pose proof (conj J3 (conj T3c I)) as JTbox. clear J2 T2 J3 T3 T3c.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. zstep.
    zstep. zstep.
    zstep. if_cases K9; zify_cond K9.
    all: assert (NXN : md_n dX2 <= N) by (rewrite NX2; unfold P_mpi_read_binary.chars_to_limbs; rewrite <- K0; clear - PLB NP; Z.div_mod_to_equations; lia).
    { ddestruct JTbox as (J3 & T3c & _).
      eapply (pr_mx_tail jk _ _ h3 LB2 m3 dX2 dY3 dZ); [exact JK8| exact (conj J3 T3c)| exact GXNZ| exact GYZ| exact NXN| unfold dY3; cbn [md_n]; clear; lia| exact NZ
        | rewrite AV0 in *; clear - HV; lia| clear - HF; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    ddestruct JTbox as (J3 & T3c & _).
    assert (XHEAP : md_own dX2 = LHeap).
    { dpose T3c as ((MX3 & _ & NS3 & _) & _). pose proof MX3 as [(_ & _ & _ & _ & _ & OW) _].
      destruct (md_own dX2); [exfalso; destruct OW as [_ E0]; rewrite NX2 in E0; unfold P_mpi_read_binary.chars_to_limbs in E0; clear - E0 HLP; Z.div_mod_to_equations; lia| reflexivity| exfalso; exact (NS3 eq_refl)]. }
    assert (POSR : 0 <= Z.of_nat (length bs) ≪ 3 + -1 < 2^64).
    { rewrite Z.shiftl_mul_pow2 by (clear; lia). clear - HLP K0 PLB NPR. lia. }
    eapply (pr_setbit0 jk _ _ h3 LB2 m3 Q dX2 (Q + 16) dY3 (Q + 32) dZ (Z.of_nat (length bs) ≪ 3 + -1) 0xcb5e8);
      [exact J3| exact T3c| exact SQ0| exact SQ1| exact SQ2| clear; lia| clear; lia| clear; lia| clear; lia| exact XHEAP| exact POSR| clear; lia| reflexivity| | reflexivity| reflexivity| reflexivity].
    intros m4 xs4 t0''' t1''' t2''' a1''' a2''' a3''' a4''' a5''' a6''' a7''' t3''' t4''' t5''' t6''' J4 T4.
    clear MU WM; pose proof (munch_refl ([] : list ivl) m4) as MU; pose proof (wmono_refl asegs m4) as WM.
    pose proof (conj J4 (conj T4 I)) as JTbox. clear J3 T3c J4 T4.
    (* [comment removed for export] *)
    zstep.
    ddestruct JTbox as (J4 & T4 & _).
    eapply (pr_mx_tail jk _ _ h3 LB2 m4 _ dY3 dZ); [exact JK8| exact (conj J4 T4)| exact GXNZ| exact GYZ| cbn [md_n]; exact NXN| unfold dY3; cbn [md_n]; clear; lia| exact NZ
        | rewrite AV0 in *; clear - HV; lia| clear - HF; lia].
    all: match goal with |- ?g => idtac "MX-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis GPS : md_sg (g_P g) = 1 \/ md_sg (g_P g) = -1.
  Hypothesis GIMG : grp_imgA g.
  Hypothesis GUW : uw_obj R G 192 d.
  Hypothesis LOADED : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "P,(0.(1.$2.(3.(4.(5.Vg,)))=))P,(0.(1.$2.(3.(79.(5.Vg,)))=))(14.(1.$2.(84.Vg,)+1.)(14.(1.$2.(51.(75.Vg,))+1.)(14.(1.$2.(51.(72.Vg,))+1.)(14.(1.$2.(51.(73.Vg,))+1.)(14.(=.+1.(74.(75.Vg,)))(14.(=.(10.(75.Vg,))+1387.)(76.Vg,VN,)))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02A0@D35881667587.150D35881667587.151D61949433775.150D61949433775.151L11007094131.177L11007094131.190L11075936116.138L11544553258.2  L1235317690.4   L12860309875.176L12860309875.189L13447073583.2  L14235606902.1  L16075574774.139L17097338356.138L17598514845.5  L19687428440.138L19786019076.5  L20721575143.4  L22214195881.4  L2256670072.7   L23124392564.138L23305025156.0  L2333536794.10  L23802140329.0  L2411933138.176 L25465666776.138L26368079009.0  L27763278905.7  L27966909654.1  L28125529944.138L28142564996.0  L28376105651.4  L29025845208.138L29135309044.138L30626473435.9  L31686769240.138L33530860120.4  L35161367924.138L35653441506.7  L36180290948.1  L36180999398.146L37344650921.0  L38093592940.5  L38235734261.1  L39220637093.0  L40834179097.143L41172169716.138L42254643250.5  L42333743922.4  L43059266230.144L43374881915.2  L43679985268.137L43880096328.3  L4442768650.7   L4444750724.6   L5065130740.138 L52253708504.138L52314013762.1  L55516431550.1  L55720577396.138L59308660947.3  L60098763854.3  L60692334296.138L61601561944.138L61747685364.138L62065999094.1  L62505661912.137L64009885711.2  L64270350808.138L65178513496.138L65337465138.175L66151427842.16 L67758486644.138Q15643324129.146Q18365925601.147Q18378753154.147Q18694146040.152Q21798041355.152Q21879645826.147Q23890796818.186Q23892894008.199Q24389563138.147Q25157988860.152Q25513505925.149Q25513505925.150Q25662358575.152Q27584944865.147Q27907200258.147Q28083394343.152Q30415036802.147Q31228709292.152Q31271525473.147Q31394594844.152Q32655500769.147Q33465969709.152Q33656017904.186Q33658115034.199Q33918256002.147Q35014437530.152Q35717497884.152Q36425882626.147Q3830427394.147 Q39939554818.147Q41152393185.147Q4153873657.199 Q4155597051.187 Q4155597051.200 Q4155970771.186 Q44648843873.147Q4533518817.147 Q49698585326.148Q49698585326.149Q51235796833.147Q53969758199.152Q54314566387.152Q55387559218.198Q55393864946.185Q55780705378.149Q55780705378.150Q55964990415.187Q55964990415.200Q59256763233.147Q59394051867.186Q59394051867.199Q59843137889.147Q60567083677.152Q63574728144.198Q63580996624.185Q63856323923.147Q63856323923.148Q6416456232.152 Q64255486968.152Q64343951155.185Q64354426611.198Q64356526075.186Q64356526075.199Q64619154459.187Q64619154459.200Q66522067074.147Q67528989526.150Q67528989526.151Q7661097679.186 Q7661097679.199 Q9843367298.146 00000\01f02X03h04F04d05505;05E05c06A06G06K07007A07S07d08108>08K08a09209309O09P0:30:D0:E0:[0:_0;00;10;90;J0;[0;j0<;0<J0<[0=30=70=H0=I0=V0=Z0=[0>50>F0>[0>g0?@0?G0?X0?_0@70@J0@[0@l0@o0A20AC0AL0AV0Ag0B80BI0BL0B]0Bd0C50CF0Ci0DC0DT0De0E60EL0Ee0Ef0F<0FT0Fl0GB0G[0H>0I<0I=0IN0Id0Ie0J;0JU0Jf0K80KI0KJ0Kb0L:0LP0Lj0Lk0MA0MW0Mm0N>0NV0Nn0OF0O^0Oo0P@0P\0Q80QI0Qc0Qd0R<0RT0S<0T?0TW0To0U@0Um0VZ0Vk0Vl0WD0W\0Wm0X>0XW0XX0Y00YH0Y`0Z80Ze0[R0[h0\P0]S0]k0^C0^YS1R3HIA1h2LF2ra2sp2bs3LFB3TOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s02bs3LFB3TOP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S1R2LF2ra2sp2bs2lo3LFB4LOSP3LOS3SPR2HB5Ha_st5Hl_stS1R2LF2ra2sp2s02bs2lo3LFB4LOSP3LOS3SPR2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S2LF2ra2sp1G2bs3LFB2jk3JK83GHIS2LF2ra2sp1G2bs3LFB2jk3JK83GHIS2LF2ra2sp2bs3LFBS2bs1NS2bs1N3RB8S2LF2ra2sp1G2bs3LFB2jk3JK83GHIS2LF2ra2sp1G2bs3LFB2jk3JK83GHIS1g2NRS2bsS2LF2ra2sp1B2bs2B03B633LFB3SPR2jk3JK8S2LF2ra2sp2bs3LFBS1R2sp2lo4SLO23NE0S2LF2ra2sp2bs3LFBS2sp1G2lo3GSPS2sp1G2lo3GSPS1N1d2D04DYF0S1R2sp2lo3LOS3ALO1e2BCS2LF2ra2sp2bs3LFBSS1R3HIA1h2sp2lo3LOS3TOP1a2HaSS2LF2ra2sp1G2bs3LFB2jk3JK84GPOS3GHIS2LF2ra2sp2bs3LFBSS1R2sp2lo3LOS3ALO1e2BCS2spS2LF2ra2sp2bs3LFBSS1N1d2D0S2LF2ra2sp2bs3LFBS2LF2ra2sp2bs3LFBS1g2CB1q1r1H2H0S2LF2ra2sp2bs3LFBS2bs1N4DYP03RB8S2LF2ra2sp2bs3LFBS1R3HIA1h2sp2lo3TOP4HTOPS2spS2LF2ra2sp2bs3LFBSS2sp1G2lo3GSPS2loSS1R2LF2ra2sp2bs3LFB2jk3JK8S2LF2ra2sp2bs3LFBS2sp2lo3LO04LOSP4SP64S2sp2lo1x2HxS2LF2ra2sp2bs2lo3LFB4LOSPS2bs2KLS2LF2ra2sp2bs3LFBS2sp2loS1R1g2lo3LOS3ALO3ACL3IHIS1R1g2lo3LOS3ALO2BCS2LF2ra2sp2bs3LFBS2LF2ra2sp2bs3LFBS1GS1GS2LF2ra2sp2bs3LFBS1g2N12E0S1R2lo3LOSS2LF2ra2sp2bs3LFBS2LF2ra2sp2bs3LFBS2LF2ra2sp2bs3LFBS1GS2LF2ra2sp2bs3LFBS2bs2KLS2LF2ra2sp2bs3LFBS2LF2ra2sp2bs3LFBS2LF2ra2sp1G2bs3LFB2jk3JK84GPOS3GHIS2sp2r03SPA1q1r1H2H02q02H4S2LF2ra2sp2bs3LFBS2LF2sp2bs2lo3LFBS2LF2sp2bs2lo3LFBS2LF2sp2bs2lo3LFB4LOSPS1R2LF2bs3LFB4IMG'2jk3JK8FS2LF2sp2bs2lo3LFB4LOSPS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2sp2bs2lo3LFB4LOSPS1R2LF2bs3LFB4IMG'2jk3JK8S2LF2ra2sp2bs2lo3LFB2HB5Ha_st5Hl_stS2LF2sp2s02bs2lo3LFB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9FS2LF2sp2bs2lo3LFBS2LF2sp2bs2lo3LFB4LOSPFS2LF2sp2bs2lo3LFB4LOSPS1R2LF2bs3LFB5ALWF'2jk3JK8S2LF2sp2bs2lo3LFBS2LF2bs3LFB2jk3JK8S2LF2sp2bs2lo3LFBFS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2sp2bs2lo3LFB4LOSPS1R2LF2bs3LFB5ALWF'2jk3JK8FS2LF2sp2bs2lo3LFB4LOSPS2LF2sp2bs2lo3LFB4LOSPS2LF2sp2bs2lo3LFB4LOSPS2LF2sp2bs2lo3LFBS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2sp2bs2lo3LFBS2LF2sp2bs2lo3LFBS2LF2sp2bs3LFB4SP642HB5Ha_stS2LF2sp2bs3LFB4SP642HB5Ha_stS2LF2sp2bs2lo3LFBS1R2LF2bs3LFB5ALWF'2jk3JK8FS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2ra2sp2bs2lo3LFB4LOSP2HB5Ha_st5Hl_stS2LF2sp2s02bs2lo3LFB4LOSP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2sp2bs2lo3LFBS2LF2ra2sp1G1g2bs3LFB3SPR2jk3JK83GAL4GPOS3GHIS2LF2ra2sp1G1g2bs3LFB3SPR2jk3JK83GAL4GPOS3GHIS2LF2sp2bs2lo3LFBFS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2sp2bs3LFB2HBS2LF2sp2bs3LFB2HBS1R2LF2bs3LFB4IMG'2jk3JK8FS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2ra2sp1G1g2bs3LFB3SPR2jk3JK83GAL4GPOS3GHIS2LF2ra2sp1G1g2bs3LFB3SPR2jk3JK83GAL4GPOS3GHIS2LF2sp2bs2lo3LFB4LOSPS2LF2ra2sp2bs2lo3LFB4LOSP2HB5Ha_st5Hl_stS2LF2sp2s02bs2lo3LFB4LOSP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s9S2LF1G2bs3LFB2jk3JK83GHIS2LF1G2bs3LFB2jk3JK83GHIS2LF2sp2bs2lo3LFB4LOSP". (* [comment removed for export] *)
  #[using="IMG HLSET HRB slo EC0 TPV RAE D0 GAT GCR GSP GMC PAT PNULL PSG QCW QSP QMC QUW QG QGL SLO2 SPA BUD BUDF BYT B0 B63 BCR BSP BQ BMC BOB B47 C24H UW NP cnt MC0 HDY SSH SLO1 SLO3 LFB QOB HRBLE HFREE GOB GPS GIMG GUW LOADED"] Lemma pr_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "Pt0,(27.&40.)Pt1,(27.&40.)Pt2,(27.&40.)Pa4,(27.&40.)Pa5,(27.&40.)Pa6,(27.&40.)Pa7,(27.&40.)Pt3,(27.&40.)Pt4,(27.&40.)Pt5,(27.&40.)Pt6,(27.&40.)Pm0,P,(27.&40.)(29.(27.&8.))P,(1.P,(27.&40.)(29.(27.&8.))R1.Vm,)P,(54.$12.VR,VHIA,Vh,Vmo,)P,(62.$12.Vm,Vlo,(16.&40.Vsp,))(85.$12.$41.(56.(33.(34.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(35.&40.VG,)(35.&40.VQ,)(35.&40.VB,)(35.&40.(3>.(3:.(27.&8.)Vbs,)))R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(35.&40.$86.)Vfc,(36.(27.&40.))R4.(37.$12.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until m0; intros EM HK ST. unfold A_ECP_POINT_READ_BINARY.
    dpose pr_base as (LO0 & LOSP & SP64 & NE0 & LOS' & Q0 & Q48). pose proof pr_N0 as N0.
    pose proof (EC0 []) as EC. pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC]. clear EC.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    (* [comment removed for export] *)
    pose proof MIm as MI0. pose proof GOB as GOB0. rewrite <- EM in HH, ST, MI0, GOB0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    carve_frame 96%nat ST.
    do 12 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    subst m0.
    pose (jk := repeat (Z_to_bv 8 0) 8 : list byte).
    assert (JK8 : length jk = 8%nat) by reflexivity.
    pose proof (pr_start jk mP MU WM HH MI0 ltac:(replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by (clear; lia); exact ST)
                  ltac:(replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by (clear; lia); exact FR)) as S0.
    assert (GAT1 : ecp_group_at asegs MT mP LB G g).
    { eapply (ecp_group_at_munch asegs); [exact GAT| exact MU| exact WM| exact MIm| exact MI0| cbn [disjoint_from fst snd]; split; [clear - GSP; lia| exact I]|].
      intros e He EO. pose proof (grp_blocks_in asegs MT m LB G g e GAT He EO) as IN.
      destruct (hm_apart asegs R HIA h LB LF mP HH) as [HF0 _]. rewrite Forall_forall in HF0.
      destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (_ & _ & BC & _). cbn [fst snd] in BC.
      cbn [disjoint_from fst snd]. split; [clear - BC ALO LOS; lia| exact I]. }
    pose proof (conj S0 (conj GAT1 I)) as Sbox. clear S0 GAT1.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    { zstep. zstep. pr_a0_lit (-20352).
      ddestruct Sbox as (_ & _ & _).
      eapply (pr_exit0 jk mP (-20352)); [exact MU| exact WM| exact MI0| exact HH| exact ST| exact FR| clear; lia| clear; lia|].
      intros _ C. exfalso. apply (f_equal bv_unsigned) in C. vm_compute in C. discriminate C. }
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF mP HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    dpose GAT as (GHD0 & GAL0 & GPOS0 & _). pose proof (rw_cells_bound _ _ _ _ GHD0) as GHB0. unfold grp_head_cells in GHB0.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in GHB0. clear GHD0.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. clear GOT GSB AB. zstep. zstep.
    ddestruct Sbox as (S0 & GAT1 & _). destruct S0 as [J0 T0].
    dpose GAT1 as (_ & _ & _ & EPA & _ & _ & _ & MP1 & _).
    assert (MPD1 : mpd_at asegs mP LB (g_P g)) by exact (conj MP1 GPS).
    assert (PIM : mpd_imgA (g_P g)) by (unfold grp_imgA in GIMG; rewrite Forall_forall in GIMG; apply GIMG; unfold grp_mpds; left; reflexivity).
    assert (PLO : md_own (g_P g) <> LNull -> 0 < md_p (g_P g) /\ md_p (g_P g) + 4 * md_n (g_P g) <= lo).
    { intros NN. dpose MP1 as (_ & _ & _ & _ & _ & DHO). unfold mpd_imgA in PIM. pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
      destruct (md_own (g_P g)) eqn:OD; [exfalso; apply NN; reflexivity| |].
      - ddestruct DHO as (_ & IN & _). destruct (hm_apart asegs R HIA h LB LF mP HH) as [HF0 _]. rewrite Forall_forall in HF0.
        destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (B0' & _ & BC & _). cbn [fst snd] in B0', BC. split; [exact B0'| clear - BC ALO LOS; lia].
      - ddestruct DHO as (_ & _ & P0 & _). destruct (AImgGlobals.img_norz_sound _ _ (PIM eq_refl)) as (_ & _ & IHI & _). unfold AImgGlobals.IMG_HI in IHI.
        split; [exact P0| clear - IHI ACL ALO LOS; lia]. }
    assert (PN1 : 1 <= md_n (g_P g) -> md_own (g_P g) <> LNull).
    { intros N1 C. dpose MP1 as (_ & _ & _ & _ & _ & OW). rewrite C in OW. destruct OW as [_ E0]. clear - E0 N1. lia. }
    assert (PAO : mpd_aobjA asegs AL (hcs asegs R HIA h) mP (g_P g)).
    { split; [rewrite EPA; eapply aobj_sub; [exact GOB0| clear; lia| clear; lia]|].
      intros ES. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH| exact (PIM ES)]. }
    pose proof (A_mpi_size_spec AL IMG) as SPC. unfold mpi_size_stmtA, mpi_query_stmtA in SPC.
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply SPC with (LB := LB) (dX := g_P g) (v := Q) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by (clear - LO0 LOSP SP64; lia).
      - exact MPD1.
      - intros EO. apply PLO. rewrite EO. discriminate.
      - exact MI0.
      - exact I.
      - exact (art_alwf asegs R HIA).
      - exact CSOK.
      - exact (hm_abase asegs R HIA h LB LF mP HH).
      - exact (proj1 PAO).
      - intros N1. exact (mpd_aobjA_limbs asegs R HIA h LB LF mP (g_P g) HH MPD1 PAO (PN1 N1)).
      - exact ST.
      - exact LO0.
      - clear - SLO2 NE0. lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - eapply crange_sub; [exact SCS| clear; lia| clear - LOSP; lia].
      - rewrite EPA. clear - GSP LOSP. lia.
      - intros N1. left. exact (proj2 (PLO (PN1 N1))).
      - rewrite EPA. reflexivity.
      - reflexivity. }
    intros ms' PO. unfold mpi_query_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & plen & E & MU2 & WM2 & MI2 & ST2 & PLV). subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in MU2, ST2 by (clear - LO0 LOSP SP64; lia).
    (* [comment removed for export] *)
    assert (HH2 : HM asegs R HIA h LB LF m2).
    { eapply (hm_munch asegs R HIA h LB LF [(lo, bv_unsigned sp + -96)] mP m2 HH MU2 WM2).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. clear - Ha LOS TOP LOSP. lia. }
    dpose pr_slots as (SQ0 & SQ1 & SQ2).
    destruct (etri_scratch R HIA h LB LF m (bv_unsigned sp) lo 96 _ XO MC (EC0 jk) 0 0 h LB mP Q (pt_X p) (Q + 16) (pt_Y p) (Q + 32) (pt_Z p) lo (bv_unsigned sp + -96) m2
                J0 T0 SQ0 SQ1 SQ2 MU2 WM2 MI2 ltac:(replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by (clear; lia); exact ST2) HH2 ltac:(clear; lia) ltac:(clear; lia)) as [J2 T2].
    assert (GAT2 : ecp_group_at asegs MT m2 LB G g).
    { eapply (ecp_group_at_munch asegs); [exact GAT1| exact MU2| exact WM2| exact MI0| exact MI2| cbn [disjoint_from fst snd]; split; [clear - GSP LOSP; lia| exact I]|].
      intros e He EO. pose proof (grp_blocks_in asegs MT m LB G g e GAT He EO) as IN.
      destruct (hm_apart asegs R HIA h LB LF mP HH) as [HF0 _]. rewrite Forall_forall in HF0.
      destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (_ & _ & BC & _). cbn [fst snd] in BC.
      cbn [disjoint_from fst snd]. split; [clear - BC ALO LOS; lia| exact I]. }
    assert (GOB2 : aobj asegs AL (hcs asegs R HIA h) m2 G 192).
    { eapply (aobj_munch asegs AL _ CSOK [(lo, bv_unsigned sp + -96)] mP m2); [| exact MU2| exact GOB0].
      unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. eapply crange_sub; [exact SCS| clear; lia| clear - LOSP; lia]. }
    assert (MU02 : munch [(lo, bv_unsigned sp)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside fst snd] in *. split; [clear - Hx; lia| exact I]. }
    pose proof (wmono_trans _ _ _ _ WM WM2) as WM02.
    pose proof J2 as [_ _ _ _ _ _ _ _ _ _ _ STk FRk]. unfold PR_REGS in FRk. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FRk, STk by (clear; lia).
    assert (PLB : 0 <= plen <= 4 * md_n (g_P g)).
    { dpose MP1 as (_ & _ & _ & _ & NR & _). pose proof (core_bitlen_range (md_limbs (g_P g)) (md_n (g_P g)) ltac:(clear - NR; lia)) as CB. subst plen. clear - CB. Z.div_mod_to_equations. lia. }
    dpose GAT2 as (_ & GAL & GPOS & _ & _ & _ & _ & _ & _ & _ & (EGX & EGY & _ & MGX & MGY & _) & _ & GTL & _).
    pose proof (rw_cells_bound _ _ _ _ GTL) as GHI. unfold grp_tail_cells in GHI. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in GHI. clear GTL.
    pose proof (mpdr_p_range' _ _ _ _ MGX) as GXR. pose proof (mpdr_p_range' _ _ _ _ MGY) as GYR.
    dpose MGX as (CGX & _ & _ & _ & _ & OWX). dpose MGY as (CGY & _ & _ & _ & _ & OWY). unfold mpi_cells in CGX, CGY. rewrite EGX in CGX. rewrite EGY in CGY.
    replace (G + 56 + 16) with (G + 72) in CGY by (clear; lia).
    clear MU WM MU2 WM2 ST FR HH MI0 GOB0 MPD1 PAO MP1 SPC. clear PLV.
    pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    pose proof (conj J2 (conj T2 (conj GAT2 (conj MU02 (conj WM02 (conj HH2 I)))))) as Sbox. clear J0 T0 J2 T2 GAT1 GAT2 MU02 WM02 MGX MGY.
    rewrite (ret_pc_even 0xcb44c ltac:(clear; lia) ltac:(reflexivity)).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KX; zify_cond KX; rewrite ?Z.mod_small in KX by exact GXR.
    { (* [comment removed for export] *)
      zstep. zstep. zstep. pr_a0_lit ECP_FEATURE_UNAVAILABLE.
      ddestruct Sbox as (_ & _ & _ & MU02 & WM02 & _).
      eapply (pr_exit0 jk m2 ECP_FEATURE_UNAVAILABLE); [exact MU02| exact WM02| exact MI2| exact HH2| exact STk| exact FRk| unfold ECP_FEATURE_UNAVAILABLE; clear; lia| unfold ECP_FEATURE_UNAVAILABLE; clear; lia|].
      intros _ _. clear - KL. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KY; zify_cond KY; rewrite ?Z.mod_small in KY by exact GYR.
    all: assert (PN0 : md_own (pt_Y p) = LNull /\ md_n (pt_X p) = 0 /\ md_n (pt_Y p) = 0 /\ md_n (pt_Z p) = 0).
    all: try (rewrite Forall_forall in PNULL; ddestruct PAT as (_ & _ & _ & MX & MY & MZ); unfold pt_mpds in PNULL;
         dpose MX as (_ & _ & _ & _ & _ & OWX'); rewrite (PNULL (pt_X p) ltac:(left; reflexivity)) in OWX';
         dpose MY as (_ & _ & _ & _ & _ & OWY'); rewrite (PNULL (pt_Y p) ltac:(right; left; reflexivity)) in OWY';
         dpose MZ as (_ & _ & _ & _ & _ & OWZ'); rewrite (PNULL (pt_Z p) ltac:(right; right; left; reflexivity)) in OWZ';
         exact (conj (PNULL (pt_Y p) ltac:(right; left; reflexivity)) (conj (proj2 OWX') (conj (proj2 OWY') (proj2 OWZ'))))).
    all: ddestruct PN0 as (YNULL & NX0 & NY0 & NZ0).
    all: assert (HLP : 0 < Z.of_nat (length bs)) by (clear - KL; lia).
    all: dpose pr_budget as (_ & _ & DYP0 & DYF0).
    all: assert (G1 : grow_PHI 1 = 8) by (unfold grow_PHI; unfold AVOL_CALL; reflexivity).
    all: assert (BUD' : point_read_PHIn N (Z.of_nat (length bs)) = 3 * MPI_RB_PHI (Z.of_nat (length bs)) + 16 + derive_y_PHIn N)
      by (unfold point_read_PHIn; rewrite G1; unfold AVOL_CALL; clear; lia).
    all: assert (RB8 : 8 <= MPI_RB_PHI (Z.of_nat (length bs))) by (unfold MPI_RB_PHI; unfold AVOL_CALL; clear; lia).
    all: ddestruct Sbox as (J2 & T2 & _).
    { eapply (pr_mx jk 0 0 h LB m2 (pt_X p) (pt_Y p) (pt_Z p) plen); [exact JK8| exact (conj J2 T2)| exact KX| exact KY| exact YNULL| rewrite NZ0; clear; lia| exact PLB| exact HLP| |].
      - rewrite BUD', G1. unfold AVOL_CALL. clear - RB8 DYP0. lia.
      - unfold point_read_FRn, calls_FR, MPI_RB_FR, fr_charge. clear - DYF0 D0. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KX2; zify_cond KX2; rewrite ?Z.mod_small in KX2 by exact GXR; [exfalso; exact (KX KX2)|].
    zstep. zstep. zstep.
    zstep. if_cases KY2; zify_cond KY2; rewrite ?Z.mod_small in KY2 by exact GYR; [exfalso; exact (KY KY2)|].
    ddestruct (LOADED KX KY) as (GH1 & GPS1 & SGA & SGB & VP & P4999 & NLE). zpre.
    eapply (pr_sw jk 0 0 h LB m2 (pt_X p) (pt_Y p) (pt_Z p) plen);
      [exact JK8| exact (conj J2 T2)| exact KX| exact (conj GAT (conj GH1 (conj GPS1 (conj GIMG (conj GCR (conj GSP (conj GMC (conj GOB GUW))))))))
      | exact SGA| exact SGB| exact VP| exact P4999| exact NLE| exact YNULL| rewrite NX0; clear; lia| rewrite NY0; clear; lia| rewrite NZ0; clear; lia| exact PLB| exact HLP| | | reflexivity].
    - rewrite BUD', G1. clear - RB8 DYP0. lia.
    - unfold point_read_FRn, calls_FR, MPI_RB_FR, fr_charge. clear - DYF0 D0. lia.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End PRB.

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L27883368372.3L39716638549.0L62132393680.600000800900PS1Q1a2HaSS1R5NEEDR2sp2lo3SLO3NER". (* [comment removed for export] *)
Theorem A_ecp_point_read_binary_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_ecp_point_read_binary_c24 ()) "PR,$87.PHIA,(88.$12.R1.)PMT,(24.$89.)P,(8:.(48.R3.))P,(8;.$12.R4.R3.$8<.)P,(4=.$12.R5.R4.$5=.)P,(4=.$12.R6.R5.$8=.)P,(8>.$12.R7.R6.$80.)P,(8?.$12.R8.R7.R6.$78.$13.)P,(=.=(90.R9.))P,Ph,(28.$12.R:.R9.)PLB,(24.$25.)PLF,(24.$25.)Pm,P,(27.&40.)(29.(27.&8.))P,(61.$12.R>.R=.R4.R3.R2.R1.)(91.$2.(92.(1;.$2.$2.)$2.(6=.$2.$2.)R4.))P,(14.(=.(93.(44.R;.))(94.(44.R;.)))(=.(95.(44.R;.))(96.(44.R;.))))P,Pa,$2.P,(1.$97.(98.$12.(99.R1.))$9:.)P,(14.(=.=R2.)(20.R2.(21.+2.+40.)))(14.(=.(93.(44.R?.))R3.)(20.R3.(96.(44.R?.))))(9;.$12.R=.R<.R;.$86.$13.)")
(* [comment removed for export] *).
Proof.
  intros R HIA MT IMG HLSET HRB HRBLE HFREE HDY NEEDR HND DIMG ROIMG. unfold ecp_point_read_binary_stmtA.
  intros until slo.
  intros HH HK LFB GAT GPS GIMG NP LOADED GCR GSP GMC GOB GUW PAT PNULL PSG QCW QSP QMC QOB QUW QG QGL BYT B0 B63 BCR BSP BQ BMC BOB B47 MC0 MCOK ST LOS SLO
         SSH SLO1 SLO3 TOP SPA TPV MI RAE BUD UW BUDF C24H -> -> -> ->.
  pose proof (arl_need_ecp_rt R) as NER.
  assert (EC : forall jk : list byte, ECA R HIA h LB LF m (bv_unsigned sp) lo 96 (C8 s10 :: PR_REGS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) [(Q, Q + 48); (A_MUL_COUNT, A_MUL_COUNT + 8)] A_MUL_COUNT).
  { intros jk. constructor; try assumption; try reflexivity; [clear; lia| clear - SLO NEEDR NER; lia|].
    intros a Ha. cbn [outside fst snd] in Ha. clear - Ha. lia. }
  eapply (pr_main R HIA IMG MT HLSET HRB h LB LF m mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc G Q B g p bs N lo d slo EC)
    with (m0 := m) (cnt := cnt);
    first [ eassumption | reflexivity | eapply uwc_nonneg; exact UW | clear - SLO; lia | idtac ].
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
