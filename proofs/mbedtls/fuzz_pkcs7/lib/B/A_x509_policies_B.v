(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_asn1_trav.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_san_A A_x509_policies_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P008f522a20e7710c 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P01783a7683db70d1 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P03b250a95b5ec0f2 1 2 32 3 0 1 66 1 69 1 32 11 25 1 45 1 49 1 56 1 57 1 58 1 61 1 62 1 63 1 67 1 68 1 2 70 1 71 1P059d941128f38c69 0 10 0 1 24 1 55 1 56 1 57 1 60 1 61 1 62 1 65 1 66 1P08cc4c9e4af3f462 0 8 0 1 47 1 56 1 61 1 62 1 63 1 66 1 67 1P0a450ff390eff1aa 0 3 0 1 35 1 66 1P0a4ef9607d430533 0 3 0 1 35 1 66 1P0a81365eefe23208 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P0c6438f6e27141b2 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P0d67abec096806ed 1 1 64 2 0 1 65 1 3 2 1 66 1 67 64P0e149c14ef959777 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P111a071497e62409 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P131bbc94ed9d95d7 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P149a9491188f0342 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P14c7caf0c523085e 0 3 0 1 35 1 66 1P1649846819f2fb65 0 6 0 1 23 1 35 1 54 1 65 1 66 1P184c66a0b6b243f2 0 10 0 1 24 1 55 1 56 1 57 1 60 1 61 1 62 1 65 1 66 1P197bcb83d517fe53 0 6 0 1 23 1 35 1 54 1 65 1 66 1P1ba41f42852a1455 0 3 0 1 35 1 66 1P1cb6071e216ade0e 0 3 0 1 35 1 66 1P1f4b4edaa85a49d6 0 3 0 1 35 1 66 1P1fcd8e21f9a01324 0 10 0 1 24 1 55 1 56 1 57 1 60 1 61 1 62 1 65 1 66 1P21706e31a52c22c0 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P22444b36a32c100d 1 1 64 2 1 1 65 1 3 0 1 66 1 67 64P24c46c9e9fcee62a 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P256ce24c0a6a8c3a 0 4 0 1 23 1 77 1 78 1P25a3ca1dbd264084 0 3 0 1 35 1 66 1P2727f70bc6c71e23 0 6 0 1 23 1 35 1 54 1 65 1 66 1P2a647e0ae32b77e1 0 4 0 1 23 1 77 1 78 1P2adf688671a14ac9 0 8 0 1 24 1 67 1 72 1 73 1 74 1 77 1 78 1P2cd3f95b08ecba92 0 3 0 1 35 1 66 1P2e0e081c7f7e8234 0 3 0 1 35 1 66 1P2ebf5a9c7811a80b 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P30f20b04c026a210 0 3 0 1 35 1 66 1P311a0bff1dcce545 0 3 0 1 35 1 54 1P320c7056c01c1940 0 3 0 1 35 1 66 1P34c016e40aca8b35 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P39323f677cd9a623 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P3b01e185d501272f 0 7 0 1 55 1 56 1 57 1 60 1 61 1 62 1P3bec76456c7b9515 1 1 64 2 45 1 66 1 3 0 1 65 1 67 64P3c10941c713f3b7c 0 3 0 1 35 1 66 1P3e9052769bc120e9 0 3 0 1 35 1 66 1P3f54945b0269b95f 0 8 0 1 24 1 67 1 72 1 73 1 74 1 77 1 78 1N00f7935432526b0fN0d10658a0299e6faN0e9f8e2363ca9722N0f511ec4e9cc972fN115695766cf495d4N12cbf0ad83090786N13fbff9d8f90424bN140e0a257fa7aa7aN18bc4355d78e89f8N1bf235b2bff35a2cN1cfdd7fef0758316N1cfe017fbe1b973fN260ee7516208febaN2630810183258ac1N2f8867808fca773cN30473d4bc6d05d47N3231521e69e16341N326c68dfff7794a9N3f51150be3f4b282"%lxh.
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
Ltac2 gd_tbl_A_x509_policies_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.SSEQ"; "Stdlib.Lists.List.rev"; "Walk.Call.FFRpol"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Walk.Call.CNTpol"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Stdlib.Lists.List.hd"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.SEQ_SIZE"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmtsE.seq_parser_postE"; "Walk.Call.PHIpol"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0G.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.
  Hypothesis CALLOC : arl_calloc R = 0x69484.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis OIDH : oid_rt_hyps R HIA.

  Local Notation STKpol := (A_x509_policies_A.STKpol R).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP CUR P END BUF lo slo : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKpol.
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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_0G in SM0; unfold A_x509_policies_A.STKpol in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHG := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].


  Variable mo0 : Model.
  Variable d : Z.
  Hypothesis NDL : List.NoDup (map fst LB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBc : list blk) (m2x : mem) (WA WB : list ivl) (r : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_policies_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.$5.VR,VHIA,)Lh4,(4.$5.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(6.(7.$0.R11.(8.(9.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(:.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(;.Vra,)Vfc,(<.(2.&40.))R10.(=.$5.)))(6.(>.$5.R10.)(6.(?.$5.R10.Vlo,(10.&40.Vsp,))(6.(11.$5.(12.VR,)R10.Vslo,(10.&40.Vsp,))(6.(13.$5.VR,VHIA,O6.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)O3.Vm,R10.)(6.(13.$5.VR,VHIA,O6.(14.$15.O5.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)O2.O4.R10.)(6.(7.P,$16.Sp(17.$5.VR,VHIA,R?.)(17.$5.VR,VHIA,O6.))(6.(7.$16.(18.$5.VR,VHIA,R?.)(18.$5.VR,VHIA,O6.))(6.(7.$16.(19.$5.VR,VHIA,R?.)(19.$5.VR,VHIA,O6.))(6.(7.$16.(1:.$5.VR,VHIA,R?.)(1:.$5.VR,VHIA,O6.))(6.(7.$16.(1;.$5.VR,VHIA,R?.)(1;.$5.VR,VHIA,O6.))(6.(7.$16.(1<.$5.VR,VHIA,R?.)(1<.$5.VR,VHIA,O6.))(6.Pmo,$1=.(1>.(1?.$5.VR,VHIA,R10.R1.)(1?.$5.VR,VHIA,O6.R1.))(20.$5.VR,VHIA,R?.(14.$15.O5.VLB,)VLF,R10.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 d; try lx_pin1 mo0; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 D1; try lx_pin1 DCB; try lx_pin1 CURLO; try lx_pin1 CWC; try lx_pin1 ALC; try lx_pin1 DPB; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 BIN; try lx_pin1 PPLO; try lx_pin1 CWP; try lx_pin1 ALP; try lx_pin1 cpad; try lx_pin1 ct; try lx_pin1 BUF; try lx_pin1 END; try lx_pin1 P; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 OIDH; try lx_pin1 GT; try lx_pin1 CALLOC; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS CUR0 PP0 LFB bs CUR PP NEED0 NB1 NS1 IMG"]
  Lemma epi_walk : 
    (forall h3 : (@HST asegs R HIA),
    forall LBc : (@list blk),
    forall m2x : ((bv 64) -> (@option (bv 8))),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall WA : (@list ivl),
    forall WB : (@list ivl),
    forall FB : Z,
    forall sp1 : Z,
    forall xra : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s3v : (bv 64),
    forall s4v : (bv 64),
    forall s5v : (bv 64),
    forall s6v : (bv 64),
    forall s8v : (bv 64),
    forall s9v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall r : Z,
    forall rs : list cell,
    (@HM asegs R HIA h3 (LBc ++ LB) ((FB, 64) :: LF) mm) ->
    (forall x : Z,
    (@hcs asegs R HIA h x) ->
    (@hcs asegs R HIA h3 x)) ->
    ((@htop asegs R HIA h3) = (@htop asegs R HIA h)) ->
    ((@hstkhi asegs R HIA h3) = (@hstkhi asegs R HIA h)) ->
    ((((bv_unsigned sp) - 208) <= sp1) /\
    (sp1 <= ((bv_unsigned sp) - 192))) ->
    ((sp1 mod 32) = 0) ->
    ((FB mod 64) = 0) ->
    (@fresh_apart R LB LF FB 64) ->
    (@fresh_apart R (LBc ++ LB) LF FB 64) ->
    (@crange (@hcs asegs R HIA h) FB 64) ->
    (@rw_cells asegs mm FB [(@C8 w0); (@C8 w1); (@C8 w2)]) ->
    (@rw_cells asegs mm ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R))) [(@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 0)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243))]) ->
    (@rw_cells asegs mm ((bv_unsigned sp) + (-104)) [(@C8 s11); (@C8 s10); (@C8 s9); (@C8 s8); (@C8 s7); (@C8 s6); (@C8 s5); (@C8 s4); (@C8 s3); (@C8 s2); (@C8 s1); (@C8 s0); (@C8 ra)]) ->
    (@rw_cells asegs mm sp1 rs) ->
    (cells_size rs = 88%nat) ->
    (@stk asegs mm (sp1 + 88) ((bv_unsigned sp) + (-104))) ->
    (@stk asegs mm lo sp1) ->
    (@mem_inv asegs mm) ->
    (@presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m mm) ->
    (@presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x mm) ->
    (@sshad asegs (@arl_AL R) mm slo (bv_unsigned sp)) ->
    (@evtA asegs (@arl_AL R) (@hcs asegs R HIA h3) (@EPOST h3 LBc m2x WA WB r) (@MS (@mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 (Z_to_bv 64 FB) s3v s4v s5v s6v (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) s8v s9v s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabdb4) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
  intros until rs.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE RSL RSZ SThi STlo MI PRES PRES2 SS.
  pose proof (stk_of_rw_cells asegs mm sp1 rs RSL) as RSK. rewrite RSZ in RSK. change (Z.of_nat 88) with 88 in RSK. clear RSL RSZ.
  pose proof (stk_merge asegs mm sp1 (sp1 + 88) (bv_unsigned sp + -104) RSK SThi ltac:(clear - SP1; lia)) as SThi'. clear RSK SThi. rename SThi' into SThi.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 NB1 NEED0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 64) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 NB1 NEED0 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF mm FB 64 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & AP3 & _ & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xabdf0] [] 311%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBc ++ LB) ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 64) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBc ++ LB) ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 64) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1 NB1 NEED0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 88 <= p \/ p + 1 <= sp1).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SP1 SLO LOS NS1 NB1 NEED0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1 NB1 NEED0; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1 NB1 NEED0; lia | lx_side_lia ]]).
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
  first [ assumption
        | lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (bv_unsigned sp + -104), SV : rw_cells _ mf (bv_unsigned sp + -104) _ |- _ =>
            pose proof (stk_merge asegs mf lo sp1 _ ST0 STA ltac:(first [ clear - SP1 SLO NS1 NB1 NEED0; lia | lx_side_lia ])) as ST3;
            release_frame SV ST3 (bv_unsigned sp); exact ST3 end
        | lazymatch goal with ST3 : stk _ mf lo (bv_unsigned sp + -104), SV : rw_cells _ mf (bv_unsigned sp + -104) _ |- _ =>
            release_frame SV ST3 (bv_unsigned sp); exact ST3 end ].
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

  Definition PHIpol (n : Z) : Z := 0.
  (* [comment removed for export] *)
  Definition FFRpol (n d : Z) : Z := (n / 4) * Z.max 0 (fr_charge (d + 1)).
  Definition CNTpol (n : Z) : Z := n / 4.
  Local Notation POST := (seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r => r = 0 \/ r = -8320) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF (END - P) lo slo d m mo0).
  Local Notation nLB nodes := (SSEQ (rev nodes) ++ LB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pol_fin : 
    (forall hq : (@HST asegs R HIA),
    forall nodes : (@list Z),
    forall FB : Z,
    forall sp1 : Z,
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall r : Z,
    forall p' : Z,
    forall hct : (bv 64),
    forall hcpad : (bv 64),
    forall hcl : Z,
    forall hcp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall rs : list cell,
    forall xra : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s3v : (bv 64),
    forall s4v : (bv 64),
    forall s5v : (bv 64),
    forall s6v : (bv 64),
    forall s8v : (bv 64),
    forall s9v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@HM asegs R HIA hq ((@SSEQ (rev nodes)) ++ LB) ((FB, 64) :: LF) mm) ->
    (forall x : Z,
    (@hcs asegs R HIA h x) ->
    (@hcs asegs R HIA hq x)) ->
    ((@htop asegs R HIA hq) = (@htop asegs R HIA h)) ->
    ((@hstkhi asegs R HIA hq) = (@hstkhi asegs R HIA h)) ->
    ((@hflag asegs R HIA hq) = (@hflag asegs R HIA h)) ->
    ((@havol asegs R HIA hq) <= (@havol asegs R HIA h)) ->
    ((@hfr asegs R HIA hq) <= ((@hfr asegs R HIA h) + (@FFRpol (END - P) d))) ->
    ((@Z.of_nat (length nodes)) <= (@CNTpol (END - P))) ->
    ((((bv_unsigned sp) - 208) <= sp1) /\
    (sp1 <= ((bv_unsigned sp) - 192))) ->
    ((sp1 mod 32) = 0) ->
    ((FB mod 64) = 0) ->
    (@fresh_apart R LB LF FB 64) ->
    (@crange (@hcs asegs R HIA h) FB 64) ->
    (@rw_cells asegs mm FB [(@C8 w0); (@C8 w1); (@C8 w2)]) ->
    (@rw_cells asegs mm ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R))) [(@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 0)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243))]) ->
    (@rw_cells asegs mm ((bv_unsigned sp) + (-104)) [(@C8 s11); (@C8 s10); (@C8 s9); (@C8 s8); (@C8 s7); (@C8 s6); (@C8 s5); (@C8 s4); (@C8 s3); (@C8 s2); (@C8 s1); (@C8 s0); (@C8 ra)]) ->
    (@rw_cells asegs mm sp1 rs) ->
    (cells_size rs = 88%nat) ->
    (@stk asegs mm (sp1 + 88) ((bv_unsigned sp) + (-104))) ->
    (@stk asegs mm lo sp1) ->
    (@mem_inv asegs mm) ->
    (@presW asegs R HIA hq LB LF (bv_unsigned sp) (bv_unsigned sp) [(PP, (PP + 8)); (CUR, (CUR + 32))] m mm) ->
    (@sshad asegs (@arl_AL R) mm slo sp1) ->
    (@sshad asegs (@arl_AL R) mm sp1 (bv_unsigned sp)) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 p'))]) ->
    ((P <= p') /\
    (p' <= END)) ->
    (@rw_cells asegs mm CUR (@seq_cells hct hcpad hcl hcp (@List.hd Z 0 nodes))) ->
    (((hcp = 0) /\ ((hcl = 0) /\ (nodes = []))) \/ ((BUF <= hcp) /\ ((0 <= hcl) /\ ((hcp + hcl) <= END)))) ->
    (@seq_chain asegs (fun _ : (@list cell) => True) mm ((@SSEQ (rev nodes)) ++ LB) (@List.hd Z 0 nodes) nodes) ->
    (List.NoDup nodes) ->
    (forall x : Z,
    (In x nodes) ->
    forall B : Z,
    forall k : Z,
    (In (B, k) LB) ->
    (((x + SEQ_SIZE) <= B) \/ ((B + k) <= x))) ->
    (((-12288) < r) /\
    (r <= 0)) ->
    (((r = 0) \/ (r = (-8320))) ->
    (p' = END)) ->
    (@aevtA asegs (@KF asegs R HIA hq mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 (Z_to_bv 64 FB) s3v s4v s5v s6v (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) s8v s9v s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabdb4) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HHq HCSq ETq ESq EFq EVq EFRq ECNT SP1 SP1M F64 FRSH CFB FHD FSH SAVE RSL RSZ SThi STlo MI PRESq SS1 SS2 HPPx Hp' HCURx HCB NC ND APN RR HENDq.
    rt_facts.
    pose proof (fresh_apart_grow R HIA hq (SSEQ (rev nodes)) LB LF mm FB 64 FRSH HHq) as FRSHq.
    pose proof (presW_init_at R HIA hq _ _ (nLB nodes) LF mm (bv_unsigned sp) (bv_unsigned sp) [] hq HHq
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 NB1 NEED0; lia)) as PRES2.
    pose proof (sshad_merge asegs AL mm slo sp1 (bv_unsigned sp) SS1 SS2 ltac:(clear - SP1 SLOL SLO NS1 NB1 NEED0; lia)) as SSm.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBc := SSEQ (rev nodes)) (WA := W) (WB := @nil ivl) (m2x := mm);
        first [ exact HHq | exact HCSq | exact ETq | exact ESq | exact PRESq | exact PRES2 | exact FRSH | exact FRSHq | exact CFB | exact SSm | exact RSL
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29) as HP29.
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (nLB nodes ++ fdata LF)).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (nLB nodes ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    unfold seq_parser_postE.
    do 15 eexists. exists m9, mo9, h4, r, p', hct, hcpad, hcl, hcp, (hd 0 nodes), nodes.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES9) as HPF; rewrite ESq in HPF; exact HPF|].
    split; [rewrite E4top; exact ETq|]. split; [rewrite E4stk; exact ESq|]. split; [rewrite E4flag; exact EFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; unfold PHIpol; clear - EVq; lia|]. split; [rewrite E4fr; exact EFRq|].
    split; [exact ECNT|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HPPx| cbn [cells_size csize Nat.add length]; apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hp'|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HCURx| cbn [cells_size csize Nat.add length seq_cells]; apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| exact I]|].
    split; [exact HCB|]. split; [reflexivity|].
    split.
    { eapply chain_presx with (L2 := nLB nodes) (X := @nil ivl) (SP := bv_unsigned sp);
        [exact NC| | | unfold SEQ_SIZE; clear; lia| intros x Hx; exact I].
      - intros x Hx. apply in_app_iff. left. unfold SSEQ. apply (in_map (fun a => (a, SEQ_SIZE))). apply -> in_rev. exact Hx.
      - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP29)| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx]. }
    split; [exact ND|]. split; [exact APN|]. split; [exact HH4|]. exact HENDq.
  Qed.
  End Call.
End Walk.
