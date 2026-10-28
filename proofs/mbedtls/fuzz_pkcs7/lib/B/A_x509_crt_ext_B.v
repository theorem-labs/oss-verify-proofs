(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_crt_ext_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_san_A A_x509_crt_ext_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P050b14af12d0d0a7 0 6 0 1 67 1 68 1 69 1 72 1 73 1P06d2bb9a6339813e 0 3 0 1 35 1 66 1P088664727f9b4574 0 3 0 1 35 1 66 1P08b13efe56156988 1 1 64 2 0 1 64 1 3 2 1 65 1 66 64P0cb2de4e6647c897 0 3 0 1 35 1 66 1P0e3b9e0d5f9ee809 0 3 0 1 35 1 66 1P0ee9bdfd15759a9f 0 6 0 1 67 1 68 1 69 1 72 1 73 1P118af2af25f8198a 0 3 0 1 35 1 66 1P12446c02f19f66c0 0 7 0 1 47 1 56 1 61 1 62 1 65 1 66 1P143dd74520a886ab 0 6 0 1 67 1 68 1 69 1 72 1 73 1P15ace70ae5569d31 0 3 0 1 35 1 66 1P17509bd9e3debbc4 0 3 0 1 35 1 66 1P176236c3d4723511 0 6 0 1 67 1 68 1 69 1 72 1 73 1P17fc61ff62e05f87 0 6 0 1 67 1 68 1 69 1 72 1 73 1P1a4fcf290c440398 0 9 0 1 24 1 55 1 56 1 57 1 60 1 61 1 64 1 65 1P1d60dc1bda8fad29 0 7 0 1 24 1 67 1 72 1 73 1 76 1 77 1P1eb506b747f0116e 0 3 0 1 35 1 54 1P1eb9d55f29fbe124 0 6 0 1 23 1 35 1 54 1 64 1 65 1P209bf085c0bce671 0 3 0 1 35 1 66 1P213253a0e847b691 0 3 0 1 35 1 66 1P2390047aa929a015 0 6 0 1 55 1 56 1 57 1 60 1 61 1P24ab50e596fd922b 0 6 0 1 67 1 68 1 69 1 72 1 73 1P267ebd8ccfeb1437 0 6 0 1 67 1 68 1 69 1 72 1 73 1P270a5ea3d8a11fac 0 7 0 1 24 1 67 1 72 1 73 1 76 1 77 1P272101370dc8aded 1 1 64 2 45 1 65 1 3 0 1 64 1 66 64P2787618e5b57a5a7 0 6 0 1 67 1 68 1 69 1 72 1 73 1P286f00606b8649d5 0 6 0 1 67 1 68 1 69 1 72 1 73 1P2dfe3706ec20b5f5 0 4 0 1 23 1 76 1 77 1P2e8a6781cd5c6288 0 3 0 1 35 1 66 1P2ebace064c3af81f 0 6 0 1 67 1 68 1 69 1 72 1 73 1P30c8baf8d55d8dd9 0 4 0 1 23 1 76 1 77 1P310a62578225b87e 0 3 0 1 35 1 66 1P316d0ec511bb43d1 1 2 32 3 0 1 65 1 68 1 32 10 25 1 45 1 49 1 56 1 57 1 58 1 61 1 62 1 66 1 67 1 2 69 2 70 2P31ac6c26eb6ecfc4 0 6 0 1 67 1 68 1 69 1 72 1 73 1P32f346734111cb28 0 3 0 1 35 1 66 1P3620d5d7470bec65 0 3 0 1 35 1 66 1P37b02b965c4dc63b 0 6 0 1 67 1 68 1 69 1 72 1 73 1P3d295bf62c76cdd6 0 6 0 1 67 1 68 1 69 1 72 1 73 1P3ffe10b69319cf17 1 1 64 2 1 1 64 1 3 0 1 65 1 66 64N02b2864bbd74dd81N03f22245dc3f01a6N052cc4ef56b7cd4cN0a09fa31b9d4fb72N0bf9f88b03818077N0ec1dde2141fb4b8N1114d2f81ba75548N1197b262d63d2a01N12e8f61b0607f6dcN147f2c800e306278N14a084e1619f000cN14b53485dfbffc4fN16ff5aa1114561bdN16ff9642ace56ba7N1a0393a871b21a3bN1a3ff49773c43416N1a42c6aff1613f33N1adfba771b8c8e41N1b830748001a559cN1d6b19af858966a0N1f710e1604d15a08N22cdd64780690250N22fd68797c4a2f6fN233901f346d30ea4N29e01da4a67df831N2c8ca738ab28c18cN2fa3c9b009f02a2aN30e19f1a711c03f1N30f7ed22d508d764N3211f421aa244843N32580ec0f0c0d872N3519fe27d07d1b85N351adab4e7173e8fN3694299ca3fedab0N3714a78e0680f2abN38938b430de51c5fN3c3b5534a97a989aN3e6d2ecf0597f9b6N3ed2f77601d8b6e9"%lxh.
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
Ltac2 gd_tbl_A_x509_crt_ext_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_own"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_junk"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_cells"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_ok"; "Stdlib.Sorting.Permutation.Permutation"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_blocks"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_ext_stmt.x509_crt_ext_postA"].



Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = 0x531fc.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.

  Local Notation STKx := (A_x509_crt_ext_A.STKx R STKc).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP CRT P END BUF lo slo : Z) (bs : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CRT mod 8 = 0.
  Hypothesis CRT0 : 0 < CRT.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (CRT + 424) EXT_SIZE.
  Hypothesis CRTLO : CRT + 424 + EXT_SIZE <= lo.
  Hypothesis DXB : CRT + 424 + EXT_SIZE <= BUF \/ BUF + n <= CRT + 424.
  Hypothesis D1 : PP + 8 <= CRT + 424 \/ CRT + 424 + EXT_SIZE <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_x509_crt_ext_A.STKx, EXT_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CRT + 424, CRT + 424 + 272)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHX := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Local Notation RSLX FB k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k128 k136 k144 k152 k160 k168 k176 k184 ja jb :=
    [CB 16 ja; C8 k16; C8 k24; C8 k32; C8 k40; C8 k48; C8 k56; C8 k64; C8 k72; C8 k80; C8 k88; C8 k96; C8 k104; C8 k112; C8 k120; C8 k128; C8 k136;
     C8 k144; C8 k152; C8 k160; C8 k168; C8 k176; C8 k184; CB 16 jb; C8 (Z_to_bv 64 FB)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBc : list blk) (m2x : mem) (WA WB : list ivl) (r : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.$5.VR,VHIA,)Lh4,(4.$5.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(6.(7.$0.R11.(8.(9.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(:.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(;.Vra,)Vfc,(<.(2.&40.))R10.(=.$5.)))(6.(>.$5.R10.)(6.(?.$5.R10.Vlo,(10.&40.Vsp,))(6.(11.$5.(12.VR,)R10.Vslo,(10.&40.Vsp,))(6.(13.$5.VR,VHIA,O6.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)O3.Vm,R10.)(6.(13.$5.VR,VHIA,O6.(14.$15.O5.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)O2.O4.R10.)(6.(7.P,$16.Sp(17.$5.VR,VHIA,R?.)(17.$5.VR,VHIA,O6.))(6.(7.$16.(18.$5.VR,VHIA,R?.)(18.$5.VR,VHIA,O6.))(6.(7.$16.(19.$5.VR,VHIA,R?.)(19.$5.VR,VHIA,O6.))(6.(7.$16.(1:.$5.VR,VHIA,R?.)(1:.$5.VR,VHIA,O6.))(6.(7.$16.(1;.$5.VR,VHIA,R?.)(1;.$5.VR,VHIA,O6.))(6.(7.$16.(1<.$5.VR,VHIA,R?.)(1<.$5.VR,VHIA,O6.))(6.Pmo,$1=.(1>.(1?.$5.VR,VHIA,R10.R1.)(1?.$5.VR,VHIA,O6.R1.))(20.$5.VR,VHIA,R?.(14.$15.O5.VLB,)VLF,R10.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 D1; try lx_pin1 DXB; try lx_pin1 CRTLO; try lx_pin1 CWX; try lx_pin1 ALC; try lx_pin1 DPB; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 BIN; try lx_pin1 PPLO; try lx_pin1 CWP; try lx_pin1 ALP; try lx_pin1 BUF; try lx_pin1 END; try lx_pin1 P; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS CRT0 PP0 LFB bs CRT PP STKc0 STKc NS1 IMG"]
  Lemma epi_walk : (forall (h3 : (HST asegs R HIA)),
 (forall (LBc : (list blk)),
 (forall (m2x : ((bv 64%N) ->
 (option (bv 8%N)))),
 (forall (mm : ((bv 64%N) ->
 (option (bv 8%N)))),
 (forall (WA : (list ivl)),
 (forall (WB : (list ivl)),
 (forall (FB : Z),
 (forall (sp1 : Z),
 (forall (xra : (bv 64%N)),
 (forall (x5 : (bv 64%N)),
 (forall (x6 : (bv 64%N)),
 (forall (x7 : (bv 64%N)),
 (forall (x10 : (bv 64%N)),
 (forall (x11 : (bv 64%N)),
 (forall (x12 : (bv 64%N)),
 (forall (x13 : (bv 64%N)),
 (forall (x14 : (bv 64%N)),
 (forall (x15 : (bv 64%N)),
 (forall (x16 : (bv 64%N)),
 (forall (x17 : (bv 64%N)),
 (forall (s3v : (bv 64%N)),
 (forall (s6v : (bv 64%N)),
 (forall (s8v : (bv 64%N)),
 (forall (s9v : (bv 64%N)),
 (forall (s10v : (bv 64%N)),
 (forall (s7v : (bv 64%N)),
 (forall (x28 : (bv 64%N)),
 (forall (x29 : (bv 64%N)),
 (forall (x30 : (bv 64%N)),
 (forall (x31 : (bv 64%N)),
 (forall (w0 : (bv 64%N)),
 (forall (w1 : (bv 64%N)),
 (forall (w2 : (bv 64%N)),
 (forall (r : Z),
 (forall (ja : (list (bv 8%N))),
 (forall (k16 : (bv 64%N)),
 (forall (k24 : (bv 64%N)),
 (forall (k32 : (bv 64%N)),
 (forall (k40 : (bv 64%N)),
 (forall (k48 : (bv 64%N)),
 (forall (k56 : (bv 64%N)),
 (forall (k64 : (bv 64%N)),
 (forall (k72 : (bv 64%N)),
 (forall (k80 : (bv 64%N)),
 (forall (k88 : (bv 64%N)),
 (forall (k96 : (bv 64%N)),
 (forall (k104 : (bv 64%N)),
 (forall (k112 : (bv 64%N)),
 (forall (k120 : (bv 64%N)),
 (forall (k128 : (bv 64%N)),
 (forall (k136 : (bv 64%N)),
 (forall (k144 : (bv 64%N)),
 (forall (k152 : (bv 64%N)),
 (forall (k160 : (bv 64%N)),
 (forall (k168 : (bv 64%N)),
 ((HM asegs R HIA h3 (@app blk LBc LB) ((@pair Z Z FB 256) :: LF) mm) ->
 ((forall (x : Z),
 ((hcs asegs R HIA h x) ->
 (hcs asegs R HIA h3 x))) ->
 (((htop asegs R HIA h3) = (htop asegs R HIA h)) ->
 (((hstkhi asegs R HIA h3) = (hstkhi asegs R HIA h)) ->
(((((bv_unsigned sp) - 304) <= sp1) /\ (sp1 <= ((bv_unsigned sp) - 288))) ->
 (((sp1 mod 32) = 0) ->
 (((FB mod 64) = 0) ->
 ((fresh_apart R LB LF FB 256) ->
 ((fresh_apart R (@app blk LBc LB) LF FB 256) ->
 ((crange (hcs asegs R HIA h) FB 256) ->
 ((rw_cells asegs mm FB [(C8 w0); (C8 w1); (C8 w2)]) ->
 ((rw_cells asegs mm ((Z.shiftr FB 3) + (al_sb (arl_AL R))) [(C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 243)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0))]) ->
((rw_cells asegs mm ((bv_unsigned sp) + (-104)) [(C8 s11); (C8 s10); (C8 s9); (C8 s8); (C8 s7); (C8 s6); (C8 s5); (C8 s4); (C8 s3); (C8 s2); (C8 s1); (C8 s0); (C8 ra)]) ->
 ((rw_cells asegs mm sp1 [(C8 k16); (C8 k24); (C8 k32); (C8 k40); (C8 k48); (C8 k56); (C8 k64); (C8 k72); (C8 k80); (C8 k88); (C8 k96); (C8 k104); (C8 k112); (C8 k120); (C8 k128); (C8 k136); (C8 k144); (C8 k152); (C8 k160); (C8 k168); (CB 16%nat ja); (C8 (Z_to_bv 64%N FB))]) ->
((stk asegs mm (sp1 + 184) ((bv_unsigned sp) + (-104))) ->
 ((stk asegs mm lo sp1) ->
 ((mem_inv asegs mm) ->
((presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m mm) ->
((presW asegs R HIA h3 (@app blk LBc LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x mm) ->
((sshad asegs (arl_AL R) mm slo (bv_unsigned sp)) ->
 (evtA asegs (arl_AL R) (hcs asegs R HIA h3) (EPOST h3 LBc m2x WA WB r) (MS (mkR xra (Z_to_bv 64%N sp1) gp tp x5 x6 x7 sp (Z_to_bv 64%N sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64%N FB) s3v (Z_to_bv 64%N r) (Z_to_bv 64%N FB) s6v s7v s8v s9v s10v (Z_to_bv 64%N ((Z.shiftr FB 3) + (al_sb (arl_AL R)))) x28 x29 x30 x31) F (Z_to_bv 64%N 0xaad18) fc (@None (bv 64%N)) mm (seg_rom asegs))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
  Proof.
  intros until k168.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE RSL SThi STlo MI PRES PRES2 SS.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKc0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 256) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKc0 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF mm FB 256 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & AP3 & _ & F8 & FBLO & SBND & APS).
  change (256 / 8) with 32 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaadb4] [] 543%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  idtac "T-EPI-2".
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBc ++ LB) ((FB, 256) :: LF) me FB 256 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 256 - 8) with (FB + 248) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 256) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBc ++ LB) ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 256) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1 STKc0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 184 <= p \/ p + 1 <= sp1).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SP1 SLO LOS NS1 STKc0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1 STKc0; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1 STKc0; lia | lx_side_lia ]]).
  clear HHe NCp NSp.
  repeat match goal with H : rw_cells _ me FB _ |- _ => clear H end.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  idtac "EPI-DONE".
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  try (lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf (sp1 + 184) (bv_unsigned sp + -104), SV : rw_cells _ mf (bv_unsigned sp + -104) _, RS : rw_cells _ mf sp1 _ |- _ =>
          chunk_to_stk RS;
          lazymatch type of RS with stk _ _ _ ?hi => replace hi with (sp1 + 184) in RS by (clear; lia) end;
          pose proof (stk_merge asegs mf lo sp1 _ ST0 RS ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as ST2;
          pose proof (stk_merge asegs mf lo (sp1 + 184) _ ST2 STA ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as ST3;
          release_frame SV ST3 (bv_unsigned sp); exact ST3 end).
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

  Variable mo0 : Model.
  Variable d : Z.
  Variables (PHIx : Z -> Z) (FFRx : Z -> Z -> Z) (CNTx : Z -> Z).

  Local Notation POST := (x509_crt_ext_postA asegs R HIA PHIx FFRx CNTx h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END CRT (END - P) lo slo d m mo0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma x_fin : (forall (hq : (HST asegs R HIA)),
 (forall (Lx : (list blk)),
 (forall (FB : Z),
 (forall (sp1 : Z),
 (forall (mm : ((bv 64%N) ->
 (option (bv 8%N)))),
 (forall (r : Z),
 (forall (p' : Z),
 (forall (eo : ext_own),
 (forall (ej : ext_junk),
 (forall (w0 : (bv 64%N)),
 (forall (w1 : (bv 64%N)),
 (forall (w2 : (bv 64%N)),
 (forall (ja : (list (bv 8%N))),
 (forall (k16 : (bv 64%N)),
 (forall (k24 : (bv 64%N)),
 (forall (k32 : (bv 64%N)),
 (forall (k40 : (bv 64%N)),
 (forall (k48 : (bv 64%N)),
 (forall (k56 : (bv 64%N)),
 (forall (k64 : (bv 64%N)),
 (forall (k72 : (bv 64%N)),
 (forall (k80 : (bv 64%N)),
 (forall (k88 : (bv 64%N)),
 (forall (k96 : (bv 64%N)),
 (forall (k104 : (bv 64%N)),
 (forall (k112 : (bv 64%N)),
 (forall (k120 : (bv 64%N)),
 (forall (k128 : (bv 64%N)),
 (forall (k136 : (bv 64%N)),
 (forall (k144 : (bv 64%N)),
 (forall (k152 : (bv 64%N)),
 (forall (k160 : (bv 64%N)),
 (forall (k168 : (bv 64%N)),
 (forall (xra : (bv 64%N)),
 (forall (x5 : (bv 64%N)),
 (forall (x6 : (bv 64%N)),
 (forall (x7 : (bv 64%N)),
 (forall (x10 : (bv 64%N)),
 (forall (x11 : (bv 64%N)),
 (forall (x12 : (bv 64%N)),
 (forall (x13 : (bv 64%N)),
 (forall (x14 : (bv 64%N)),
 (forall (x15 : (bv 64%N)),
 (forall (x16 : (bv 64%N)),
 (forall (x17 : (bv 64%N)),
 (forall (s3v : (bv 64%N)),
 (forall (s6v : (bv 64%N)),
 (forall (s8v : (bv 64%N)),
 (forall (s9v : (bv 64%N)),
 (forall (s10v : (bv 64%N)),
 (forall (s7v : (bv 64%N)),
 (forall (x28 : (bv 64%N)),
 (forall (x29 : (bv 64%N)),
 (forall (x30 : (bv 64%N)),
 (forall (x31 : (bv 64%N)),
 ((HM asegs R HIA hq (@app blk Lx LB) ((@pair Z Z FB 256) :: LF) mm) ->
 ((forall (x : Z),
 ((hcs asegs R HIA h x) ->
 (hcs asegs R HIA hq x))) ->
 (((htop asegs R HIA hq) = (htop asegs R HIA h)) ->
 (((hstkhi asegs R HIA hq) = (hstkhi asegs R HIA h)) ->
 (((hflag asegs R HIA hq) = (hflag asegs R HIA h)) ->
 (((havol asegs R HIA hq) <= ((havol asegs R HIA h) + (PHIx (END - P)))) ->
 (((hfr asegs R HIA hq) <= ((hfr asegs R HIA h) + (FFRx (END - P) d))) ->
 (((Z.of_nat (@length blk Lx)) <= (CNTx (END - P))) ->
(((((bv_unsigned sp) - 304) <= sp1) /\ (sp1 <= ((bv_unsigned sp) - 288))) ->
 (((sp1 mod 32) = 0) ->
 (((FB mod 64) = 0) ->
 ((fresh_apart R LB LF FB 256) ->
 ((crange (hcs asegs R HIA h) FB 256) ->
 ((rw_cells asegs mm FB [(C8 w0); (C8 w1); (C8 w2)]) ->
 ((rw_cells asegs mm ((Z.shiftr FB 3) + (al_sb (arl_AL R))) [(C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 243)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0))]) ->
((rw_cells asegs mm ((bv_unsigned sp) + (-104)) [(C8 s11); (C8 s10); (C8 s9); (C8 s8); (C8 s7); (C8 s6); (C8 s5); (C8 s4); (C8 s3); (C8 s2); (C8 s1); (C8 s0); (C8 ra)]) ->
 ((rw_cells asegs mm sp1 [(C8 k16); (C8 k24); (C8 k32); (C8 k40); (C8 k48); (C8 k56); (C8 k64); (C8 k72); (C8 k80); (C8 k88); (C8 k96); (C8 k104); (C8 k112); (C8 k120); (C8 k128); (C8 k136); (C8 k144); (C8 k152); (C8 k160); (C8 k168); (CB 16%nat ja); (C8 (Z_to_bv 64%N FB))]) ->
((stk asegs mm (sp1 + 184) ((bv_unsigned sp) + (-104))) ->
 ((stk asegs mm lo sp1) ->
 ((mem_inv asegs mm) ->
((presW asegs R HIA hq LB LF (bv_unsigned sp) (bv_unsigned sp) [(@pair Z Z PP (PP + 8)); (@pair Z Z (CRT + 424) ((CRT + 424) + 272))] m mm) ->
 ((sshad asegs (arl_AL R) mm slo sp1) ->
((sshad asegs (arl_AL R) mm sp1 (bv_unsigned sp)) ->
 ((rw_cells asegs mm PP [(C8 (Z_to_bv 64%N p'))]) ->
 (((P <= p') /\ (p' <= END)) ->
 ((rw_cells asegs mm (CRT + 424) (ext_cells eo ej)) ->
 ((ext_ok asegs mm (@app blk Lx LB) eo) ->
 ((@Permutation blk Lx (ext_blocks eo)) ->
 ((((Z.opp (2 ^ 31)) < r) /\ (r <= 0)) ->
 (aevtA asegs (KF asegs R HIA hq mo0) (x509_crt_ext_postA asegs R HIA PHIx FFRx CNTx h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP P END CRT (END - P) lo slo d m mo0) (MS (mkR xra (Z_to_bv 64%N sp1) gp tp x5 x6 x7 sp (Z_to_bv 64%N sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64%N FB) s3v (Z_to_bv 64%N r) (Z_to_bv 64%N FB) s6v s7v s8v s9v s10v (Z_to_bv 64%N ((Z.shiftr FB 3) + (al_sb (arl_AL R)))) x28 x29 x30 x31) F (Z_to_bv 64%N 0xaad18) fc (@None (bv 64%N)) mm (seg_rom asegs)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HHq HCSq ETq ESq EFq EVq EFRq ECNT SP1 SP1M F64 FRSH CFB FHD FSH SAVE RSL SThi STlo MI PRESq SS1 SS2 HPPx Hp' HEXT HOK HPERM RR.
    rt_facts.
    pose proof (fresh_apart_grow R HIA hq Lx LB LF mm FB 256 FRSH HHq) as FRSHq.
    pose proof (presW_init_at R HIA hq _ _ (Lx ++ LB) LF mm (bv_unsigned sp) (bv_unsigned sp) [] hq HHq
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 STKc0; lia)) as PRES2.
    pose proof (sshad_merge asegs AL mm slo sp1 (bv_unsigned sp) SS1 SS2 ltac:(clear - SP1 SLOL SLO NS1 STKc0; lia)) as SSm.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBc := Lx) (WA := W) (WB := @nil ivl) (m2x := mm);
        first [ exact HHq | exact HCSq | exact ETq | exact ESq | exact PRESq | exact PRES2 | exact FRSH | exact FRSHq | exact CFB | exact SSm | exact RSL
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29) as HP29.
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' ((Lx ++ LB) ++ fdata LF)).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((Lx ++ LB) ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    assert (CHN : forall a nodes, (forall x, In x nodes -> In (x, SEQ_SIZE) Lx) -> seq_chain asegs (fun _ => True) mm (Lx ++ LB) a nodes ->
                                  seq_chain asegs (fun _ => True) m9 (Lx ++ LB) a nodes).
    { intros a nodes HIN NC. eapply chain_presx with (L2 := Lx ++ LB) (X := @nil ivl) (SP := bv_unsigned sp);
        [exact NC| | | unfold SEQ_SIZE; clear; lia| intros x Hx; exact I].
      - intros x Hx. apply in_app_iff. left. apply HIN. exact Hx.
      - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP29)| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx]. }
    assert (INX : forall x, In (x, SEQ_SIZE) (ext_blocks eo) -> In (x, SEQ_SIZE) Lx).
    { intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPERM| exact Hx]. }
    assert (INS : forall l x, In x l -> In (x, SEQ_SIZE) (SSEQ l)) by (intros l x Hx; unfold SSEQ; apply (in_map (fun a => (a, SEQ_SIZE))); exact Hx).
    unfold x509_crt_ext_postA.
    do 15 eexists. exists m9, mo9, h4, r, p', eo, ej, Lx.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES9) as HPF; rewrite ESq in HPF; unfold EXT_SIZE; exact HPF|].
    split; [rewrite E4top; exact ETq|]. split; [rewrite E4stk; exact ESq|]. split; [rewrite E4flag; exact EFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; exact EVq|]. split; [rewrite E4fr; exact EFRq|].
    split; [exact ECNT|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HPPx| cbn [cells_size csize Nat.add length]; apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hp'|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HEXT| unfold ext_cells; cbn [cells_size csize Nat.add length]; apply CRo; [exact CRTLO| exact (client_range_of_w L _ _ _ _ _ CWX)]| exact I]|].
    split.
    { destruct HOK as (K1 & K2 & K3 & K4). unfold ext_ok. unfold ext_blocks in INX.
      split; [apply CHN; [intros x Hx; apply INX; apply in_or_app; right; apply in_or_app; left; apply INS; exact Hx| exact K1]|].
      split; [apply CHN; [intros x Hx; apply INX; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply INS; exact Hx| exact K2]|].
      split; [apply CHN; [intros x Hx; apply INX; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply INS; exact Hx| exact K3]|].
      apply CHN; [intros x Hx; apply INX; apply in_or_app; left; apply INS; exact Hx| exact K4]. }
    split; [exact HPERM|]. exact HH4.
  Qed.
  End Call.
End Walk.
