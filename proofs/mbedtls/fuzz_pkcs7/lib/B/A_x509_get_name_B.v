(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_x509_get_name_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_name_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001f0668053fe42d 1 1 64 2 1 1 75 1 3 0 1 76 1 77 64P015c985c091292fa 0 3 0 1 37 1 76 1P04f4244930b63ee8 0 3 0 1 37 1 76 1P062744fe2781ac3c 0 10 0 1 51 1 53 1 55 1 59 1 66 1 67 1 68 1 76 1 77 1P06e6d0c58c94bb94 0 4 0 1 23 1 87 1 88 1P08a8b921aeacde8b 0 3 0 1 37 1 76 1P093b5c51af2b4f03 0 6 0 1 62 1 64 1 77 1 78 1 79 1P0d366b1c97bc4861 1 2 32 3 0 1 76 1 79 1 32 10 25 1 51 1 53 1 55 1 59 1 66 1 67 1 68 1 77 1 78 1 2 80 2 81 2P0f0a2abaa9cb4ce9 0 6 0 1 23 1 37 1 64 1 75 1 76 1P117382120666d025 0 6 0 1 62 1 64 1 77 1 78 1 79 1P14a75f4e31c075cc 0 3 0 1 37 1 64 1P15b81cafc2ef1801 0 4 0 1 23 1 87 1 88 1P18813c22b54fa4c8 0 6 0 1 62 1 64 1 77 1 78 1 79 1P1d54e0867095cf18 1 1 64 2 0 1 75 1 3 2 1 76 1 77 64P1dfd519eb03a724c 0 3 0 1 37 1 76 1P1e60e61b0a6fbdb6 0 6 0 1 62 1 64 1 77 1 78 1 79 1P1e9d7bfe980ba828 0 3 0 1 37 1 76 1P1f5df09184548efd 0 6 0 1 62 1 64 1 77 1 78 1 79 1P20752a591d9bb04f 0 9 0 1 24 1 50 1 52 1 65 1 66 1 67 1 75 1 76 1P210724ebf42d2031 0 7 0 1 24 1 62 1 64 1 77 1 87 1 88 1P214fe8573e00d840 0 6 0 1 62 1 64 1 77 1 78 1 79 1P24f769d3bb049bed 0 6 0 1 23 1 37 1 64 1 75 1 76 1P258acb85cfd2d754 0 3 0 1 37 1 76 1P292a0734cf87a7e6 0 6 0 1 62 1 64 1 77 1 78 1 79 1P2b7a9428ea6e3d79 0 6 0 1 23 1 37 1 64 1 75 1 76 1P2c0d2098d70b65c9 0 6 0 1 62 1 64 1 77 1 78 1 79 1P2cfbcf7415516dba 0 6 0 1 62 1 64 1 77 1 78 1 79 1P2d340297034314be 0 3 0 1 37 1 76 1P2db83c748bd5f690 1 1 64 2 55 1 76 1 3 0 1 75 1 77 64P2e3ced7e72128286 0 3 0 1 37 1 76 1P2ec23bdffb70ebf2 0 6 0 1 62 1 64 1 77 1 78 1 79 1P33b923eba7bc595e 0 3 0 1 37 1 76 1P37e920376d3dded9 0 9 0 1 24 1 50 1 52 1 65 1 66 1 67 1 75 1 76 1P385dfb4ecfe1273c 0 3 0 1 37 1 76 1P39e274a706397ed9 0 3 0 1 37 1 76 1P3a69c2f638e93362 0 6 0 1 62 1 64 1 77 1 78 1 79 1P3b60b68912aca2a5 0 9 0 1 24 1 50 1 52 1 65 1 66 1 67 1 75 1 76 1P3bb2016e766887c2 0 6 0 1 50 1 52 1 65 1 66 1 67 1P3bf2d7451a758450 0 6 0 1 62 1 64 1 77 1 78 1 79 1P3c1932bfff2799d0 0 6 0 1 62 1 64 1 77 1 78 1 79 1P3c63e72087d7125f 0 3 0 1 37 1 76 1P3deabaa098868f22 0 7 0 1 24 1 62 1 64 1 77 1 87 1 88 1P3fda033b14a4e5a3 0 3 0 1 37 1 76 1N02acb8373cdc1b71N030d62341cef0a09N07db1997eeed9079N0b3f9782b7b9d3b8N18bd21d3da72596cN1c1190faa9d88fcaN1c569683f8827e62N1eebcf4ceac216aaN2073bdd3e28d10a6N23c51a0427821affN24a9bc7251d976daN2575a071ccd01a1eN2baaa756b2de4c6aN2e4ef90e6bc0949fN2e75ff8ae904f16cN2f33a3ab99db55b3N3071f5bf3f2cf7cfN326423b8c323e7baN32f788f8e80a1b22N33bea479cbbb8accN340991553a0d1a5dN3739cef6fa3d927cN3adbd416f2540a3fN3ae788d1f095437dN3c0bf49a5404d6fdN3c6317ab4936c372N3fe10e426711d837"%lxh.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_x509_get_name_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.rsl"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.rslr"].



Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55855578687.12000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation STKn := (A_x509_get_name_A.STKn R).
  Local Notation CNTn := A_x509_get_name_A.CNTn.
  Local Notation PHIn := A_x509_get_name_A.PHIn.
  Local Notation FFRn := A_x509_get_name_A.FFRn.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF CUR lo slo d : Z) (bs : list byte) (j48 : list byte) (mg : byte) (pad7 : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 7)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HCUR : rw_cells asegs m CUR (name_blob j48 0 mg pad7).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 64.
  Hypothesis CURLO : CUR + 64 <= lo.
  Hypothesis DCB : CUR + 64 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 64 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKn.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_1 in SM1; unfold A_x509_get_name_A.STKn in SLO; unfold NAME_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBn : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.$5.VR,VHIA,)Lh4,(4.$5.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(6.(7.$0.R11.(8.(9.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(:.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(;.Vra,)Vfc,(<.(2.&40.))R10.(=.$5.)))(6.(>.$5.R10.)(6.(?.$5.R10.Vlo,(10.&40.Vsp,))(6.(11.$5.(12.VR,)R10.Vslo,(10.&40.Vsp,))(6.(13.$5.VR,VHIA,O7.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)O3.O5.R10.)(6.(13.$5.VR,VHIA,O7.(14.$15.O6.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)O2.O4.R10.)(6.(7.P,$16.Sp(17.$5.VR,VHIA,R?.)(17.$5.VR,VHIA,O7.))(6.(7.$16.(18.$5.VR,VHIA,R?.)(18.$5.VR,VHIA,O7.))(6.(7.$16.(19.$5.VR,VHIA,R?.)(19.$5.VR,VHIA,O7.))(6.(7.$16.(1:.$5.VR,VHIA,R?.)(1:.$5.VR,VHIA,O7.))(6.(7.$16.(1;.$5.VR,VHIA,R?.)(1;.$5.VR,VHIA,O7.))(6.(7.$16.(1<.$5.VR,VHIA,R?.)(1<.$5.VR,VHIA,O7.))(6.Pmo,$1=.(1>.(1?.$5.VR,VHIA,R10.R1.)(1?.$5.VR,VHIA,O7.R1.))(20.$5.VR,VHIA,R?.(14.$15.O6.VLB,)VLF,R10.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 CURLO; try lx_pin1 CWC; try lx_pin1 ALC; try lx_pin1 HCUR; try lx_pin1 B30; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 BIN; try lx_pin1 HBY; try lx_pin1 PPLO; try lx_pin1 CWP; try lx_pin1 ALP; try lx_pin1 HPP; try lx_pin1 pad7; try lx_pin1 mg; try lx_pin1 j48; try lx_pin1 d; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 NRT; try lx_pin1 FREEL; try lx_pin1 GETTAG; try lx_pin1 FREE; try lx_pin1 CALLOC; try lx_pin1 HMND; try lx_pin1 DIMG; try lx_pin1 NS1; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01F0@D10777814275.143D2459793318.143 D32452690557.143D3374278032.142 D43016287773.144D45715803169.142D62011770188.144D68405837779.142D6909504982.142 L10116198412.192L13312155929.179L13424450162.125L13424450175.129L19546883927.125L19546883930.129L19658438279.193L2275137097.0   L24131365012.126L24131365017.122L27188209011.147L30443668812.8  L35655538631.8  L38077847203.1  L39540652971.1  L39588638165.0  L39844638933.0  L42411609006.0  L48117620902.126L48117620903.127L48117620904.123L48117620907.122L50790731766.8  L51609971902.131L5162232212.2   L60098763854.6  L61954813926.191L62018535662.1  L67028235242.10 L6912107235.126 L6912107246.122 L9356559676.13  P5152549648.187 Q10592386204.148Q10592386207.152Q21721340005.149Q21721340008.153Q22358563588.151Q23925414036.157Q24131365012.153Q24131365017.149Q24131365917.155Q24137657765.147Q24137657789.151Q30147450662.149Q30223088057.148Q30223088058.152Q30871588746.185Q31314676345.147Q34796740410.152Q38248895679.156Q4125667684.184 Q42439443119.186Q42441479401.159Q4279611329.186 Q43880146019.156Q48117620905.152Q48117620906.148Q48132302223.151Q48132302231.147Q52741535643.185Q5935758158.186 Q59668625896.153Q60382659730.153Q60382659743.149Q62009673036.157Q64133651577.185Q64681502656.159Q64683667846.186Q67397950268.148Q6897428426.151 Q6897428434.147 Q6912107235.153 Q6912107246.149 Q6912108138.155 Q7917062807.153 Q7917062810.149 00000D00E00Y00Z01501I01]01^02202a03?03^04=04W05106D06E06U06e07>07O07h07l08008108208308\09E09n0:W0:h0;K0;L0;V0<A0<D0<]0<m0==0=b0=c0>30>C0>D0>E0>F0>Y0>i0?90?I0?Y0?i0?j0@:0@J0@d0@e0@f0A60AM0Am0BC0BZ0Bm0CV0D?0Dh0EQ0Ek0FB0FC0FD0FE0FR0Fi0GM0H;0H<0HL0H\0Hl0I<0IL0Ic0J:S1R2LF2bs3LFB2FB3sp1FS1R2LF2bs3LFB2FB3sp1FS1R3HIA2LF2bs3LFB2h32FB3sp1S1R2LF2bs3LFB2FB3sp1S1R2LF2bs3LFB2FB3sp1FS1R2LF2bs3LFB2FB3sp1S1R2LF2sp2lo2bs3LFB3SLO2FB3sp13SP14SP1R2F04lxHnS1R2LF2bs3LFB2FB3sp14lxHn1p2PBS1R2LF2bs3LFB2FB3sp14SP1R2F82F0S1R2LF2bs3LFB2FB3sp14SP1R2F82F0S1R2LF2bs3LFB2FB3sp12F82F0S1R2LF2bs3LFB2FB3sp12F82F0S1R2LF2sp2PP1P3END3BUF3CUR2lo2bs3LFB2B12B22B33DPB3DCB2D13SLO2FB3sp13SP12F04lxHn3H13SS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FB3sp11c2HcS1R2sp2lo3SLO3LOSS1R3HIA1h2sp2lo3TOP5HTOP3S2spS2FBSSSS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2sp2lo3SLO3LOSS1R2LF2sp3slo2bs3LFB4SLOS2FB3ALO2F1FS1R2lo3LOSS1R2LF2sp2lo2bs3LFB3SLO2FB3sp14SP1R2F04lxHnS1RS1R2sp2lo3SLO3LOS3sp13SP1S1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBFFFS1R3HIA1h2LF2bs3LFBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBFS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FB4lxHn1p2PBFFS1R2LF2lo2bs3LFBS1R2LF2bs3LFB4lxHn1p2PBS1R2LF3slo2bs3LFB4SLOS4lxHn1p2PBS1R2LF3slo2bs3LFB4SLOSS1R2LF2bs3LFB4lxHn1p2PBS1R2LF2sp2lo2bs3LFBS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3ALOS1R2LF2bs3LFB2FB4lxHn1p2PBS1R2LF2bs3LFB4lxHn1p2PBFFFS1R2LF2bs3LFBS1R2LF2bs3LFB4lxHn1p2PBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP5HTOP3S1R3HIA1h2LF2sp3slo2bs3LFB3TOP5HTOP34lxHn1p2PBFS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FBS1R2LF2bs3LFB2FB3ALO2F1S1R2LF2bs3LFB2FB3ALO2F1". (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS D1 DCB CUR0 DPB B3 B2 B1 PP0 LFB bs BUF P PP IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_B ()) "Ph3,(4.$5.VR,VHIA,)PLBn,(21.$15.)Pm0,P,(2.&40.)(3.(2.&8.))Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(21.$22.)PWB,(21.$22.)PFB,$16.Psp1,$16.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps10v,(2.&40.)Pr64,$16.Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps2v,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps8v,(2.&40.)Ps9v,(2.&40.)Ps11v,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pb4,(2.&8.)Pb8,(2.&8.)Pj0,(21.(2.&8.))Pj96,(21.(2.&8.))Pr,$16.P,(20.$5.VR,VHIA,R28.(14.$15.R27.VLB,)(23.(24.$16.$16.)(25.$16.$16.R21.+80.)VLF,)R24.)P,Px,$16.P,(17.$5.VR,VHIA,Vh,R1.)(17.$5.VR,VHIA,R2;.R2.)P,(7.$16.(18.$5.VR,VHIA,R2:.)(18.$5.VR,VHIA,Vh,))P,(7.$16.(19.$5.VR,VHIA,R2;.)(19.$5.VR,VHIA,Vh,))P,(6.(26.(27.(10.&40.Vsp,)+?0.)R24.)(26.R24.(27.(10.&40.Vsp,)+>0.)))P,(7.$16.(28.R25.+20.)=)P,(7.$16.(28.R27.+40.)=)P,(29.VR,VLB,VLF,R28.+80.)P,(29.VR,(14.$15.R2?.VLB,)VLF,R29.+80.)P,(2:.(17.$5.VR,VHIA,Vh,)R2:.+80.)P,PB,$16.Pj,$16.P,(2;.(24.$16.$16.)(25.$16.$16.R2.R1.)VLF,)(2<.(26.(2=.R2>.+80.)R3.)(26.(2=.R3.R2.)R2>.))P,(2>.$5.R2?.R2<.(23.$2?.(30.R13.)(23.$2?.(30.R12.)(23.$2?.(30.R11.)(31.$2?.)))))P,(2>.$5.R30.(2=.(32.R2=.+3.)(33.(12.VR,)))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.R11.)(23.$2?.(34.(:.&8.+?2.))(23.$2?.(34.(:.&8.+?2.))(23.$2?.(34.(:.&8.+?2.))(23.$2?.(34.R10.)(23.$2?.(34.(:.&8.+?3.))(23.$2?.(34.(:.&8.+?3.))(23.$2?.(34.(:.&8.+?3.))(23.$2?.(34.(:.&8.=))(23.$2?.(34.(:.&8.=))(23.$2?.(34.(:.&8.=))(23.$2?.(34.(:.&8.=))(31.$2?.))))))))))))))))))P,(2>.$5.R31.(2=.(10.&40.Vsp,)-68.)(23.$2?.(30.Vs11,)(23.$2?.(30.Vs10,)(23.$2?.(30.Vs9,)(23.$2?.(30.Vs8,)(23.$2?.(30.Vs7,)(23.$2?.(30.Vs6,)(23.$2?.(30.Vs5,)(23.$2?.(30.Vs4,)(23.$2?.(30.Vs3,)(23.$2?.(30.Vs2,)(23.$2?.(30.Vs1,)(23.$2?.(30.Vs0,)(23.$2?.(30.Vra,)(31.$2?.)))))))))))))))P,(2>.$5.R32.R2>.(3;.VEND,VCUR,R2?.R11.R10.R28.))P,(?.$5.R33.(2=.R2?.+78.)(2=.(10.&40.Vsp,)-68.))P,(?.$5.R34.Vlo,R30.)P,(>.$5.R35.)P,(13.$5.VR,VHIA,R3:.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)R35.R38.R36.)P,(13.$5.VR,VHIA,R3;.(14.$15.R3:.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)R35.R38.R37.)P,(11.$5.(12.VR,)R38.Vslo,(10.&40.Vsp,))P,(6.(36.(37.(38.+2.+1?.))R16.)(36.R16.(38.+2.+1?.)))(39.$5.(12.VR,)(17.$5.VR,VHIA,R3>.)(3:.R3>.R3=.R3<.R3;.R39.R38.R17.)(8.(9.R35.(:.&40.R36.)Vgp,Vtp,R34.R33.R32.Vsp,(:.&40.R36.)(:.&40.R17.)(:.&40.R37.)(:.&40.R37.)R2?.R2>.R2=.R2<.R2;.R26.R25.R24.(:.&40.(2=.(32.R37.+3.)(33.(12.VR,))))R23.R22.R21.R20.R31.R1?.R2:.R29.R28.R27.)VF,(:.&40.+:=1=0.)Vfc,(<.(2.&40.))R3:.(=.$5.)))")
(* [comment removed for export] *).
  Proof.
  intros until r.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP FHD FSH SAVE RSL SThi STlo MI PRES PRES2 SS Hr.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBn ++ LB) LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (128 / 8) with 16 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  unfold rslr in RSL.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xad22c] [] 408%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBn ++ LB) ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBn ++ LB) ++ fdata ((FB, 128) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBn ++ LB) ++ fdata LF) -> In b ((LBn ++ LB) ++ fdata ((FB, 128) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 120 <= p \/ p + 1 <= sp1).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBn ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  lazymatch goal with RS : rw_cells _ mf sp1 _ |- _ => chunk_to_stk RS; chunk_to_stk SAVE;
        lazymatch goal with ST0 : stk _ mf lo sp1, STB : stk _ mf (sp1 + 120) _ |- _ =>
          stk_merge_into ST0 RS; stk_merge_into ST0 STB; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end end.
  }
  split; [assumption|].
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  exact HM4.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
