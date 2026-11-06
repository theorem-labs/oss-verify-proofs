(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_asn1_trav.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_x509_get_san_A A_x509_policies_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P008f522a20e7710c 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P01783a7683db70d1 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P03b250a95b5ec0f2 1 2 32 3 0 1 66 1 69 1 32 11 25 1 45 1 49 1 56 1 57 1 58 1 61 1 62 1 63 1 67 1 68 1 2 70 1 71 1P059d941128f38c69 0 10 0 1 24 1 55 1 56 1 57 1 60 1 61 1 62 1 65 1 66 1P08cc4c9e4af3f462 0 8 0 1 47 1 56 1 61 1 62 1 63 1 66 1 67 1P0a450ff390eff1aa 0 3 0 1 35 1 66 1P0a4ef9607d430533 0 3 0 1 35 1 66 1P0a81365eefe23208 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P0c6438f6e27141b2 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P0d67abec096806ed 1 1 64 2 0 1 65 1 3 2 1 66 1 67 64P0e149c14ef959777 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P111a071497e62409 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P131bbc94ed9d95d7 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P149a9491188f0342 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P14c7caf0c523085e 0 3 0 1 35 1 66 1P1649846819f2fb65 0 6 0 1 23 1 35 1 54 1 65 1 66 1P184c66a0b6b243f2 0 10 0 1 24 1 55 1 56 1 57 1 60 1 61 1 62 1 65 1 66 1P197bcb83d517fe53 0 6 0 1 23 1 35 1 54 1 65 1 66 1P1ba41f42852a1455 0 3 0 1 35 1 66 1P1cb6071e216ade0e 0 3 0 1 35 1 66 1P1f4b4edaa85a49d6 0 3 0 1 35 1 66 1P1fcd8e21f9a01324 0 10 0 1 24 1 55 1 56 1 57 1 60 1 61 1 62 1 65 1 66 1P21706e31a52c22c0 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P22444b36a32c100d 1 1 64 2 1 1 65 1 3 0 1 66 1 67 64P24c46c9e9fcee62a 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P256ce24c0a6a8c3a 0 4 0 1 23 1 77 1 78 1P25a3ca1dbd264084 0 3 0 1 35 1 66 1P2727f70bc6c71e23 0 6 0 1 23 1 35 1 54 1 65 1 66 1P2a647e0ae32b77e1 0 4 0 1 23 1 77 1 78 1P2adf688671a14ac9 0 8 0 1 24 1 67 1 72 1 73 1 74 1 77 1 78 1P2cd3f95b08ecba92 0 3 0 1 35 1 66 1P2e0e081c7f7e8234 0 3 0 1 35 1 66 1P2ebf5a9c7811a80b 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P30f20b04c026a210 0 3 0 1 35 1 66 1P311a0bff1dcce545 0 3 0 1 35 1 54 1P320c7056c01c1940 0 3 0 1 35 1 66 1P34c016e40aca8b35 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P39323f677cd9a623 0 7 0 1 67 1 68 1 69 1 72 1 73 1 74 1P3b01e185d501272f 0 7 0 1 55 1 56 1 57 1 60 1 61 1 62 1P3bec76456c7b9515 1 1 64 2 45 1 66 1 3 0 1 65 1 67 64P3c10941c713f3b7c 0 3 0 1 35 1 66 1P3e9052769bc120e9 0 3 0 1 35 1 66 1P3f54945b0269b95f 0 8 0 1 24 1 67 1 72 1 73 1 74 1 77 1 78 1N00f7935432526b0fN0d10658a0299e6faN0e9f8e2363ca9722N0f511ec4e9cc972fN115695766cf495d4N12cbf0ad83090786N13fbff9d8f90424bN140e0a257fa7aa7aN18bc4355d78e89f8N1bf235b2bff35a2cN1cfdd7fef0758316N1cfe017fbe1b973fN260ee7516208febaN2630810183258ac1N2f8867808fca773cN30473d4bc6d05d47N3231521e69e16341N326c68dfff7794a9N3f51150be3f4b282"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_x509_policies_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.LibA.ARt.sshad"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.presW"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.HM"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Frame.ivl"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.Lib.Cells.C1"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "Walk.Call.EPOST"; "OSSVerify.KrLib.Spec.CrtParseStmts.SSEQ"; "Stdlib.Lists.List.rev"; "Walk.Call.FFRpol"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Walk.Call.CNTpol"; "OSSVerify.KrLib.Spec.RepFacts.seq_cells"; "Stdlib.Lists.List.hd"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Spec.Rep.SEQ_SIZE"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "OSSVerify.KrLib.A.A_x509_seq_stmtsE.seq_parser_postE"; "Walk.Call.PHIpol"].


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
  Hypothesis CALLOC : arl_calloc R = 0x68f10.
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
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies_B ()) "Ph3,(4.$5.VR,VHIA,)PLBc,(21.$15.)Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(21.$22.)PWB,(21.$22.)PFB,$16.Psp1,$16.Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps2v,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps8v,(2.&40.)Ps9v,(2.&40.)Ps10v,(2.&40.)Ps11v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pr,$16.Pja,(21.(2.&8.))Pjb,(21.(2.&8.))Pk24,(2.&40.)Pk32,(2.&40.)Pk40,(2.&40.)Pk48,(2.&40.)Pk56,(2.&40.)Pk64,(2.&40.)Pk88,(2.&40.)P,(20.$5.VR,VHIA,R2=.(14.$15.R2<.VLB,)(23.(24.$16.$16.)(25.$16.$16.R27.+40.)VLF,)R2:.)P,Px,$16.P,(17.$5.VR,VHIA,Vh,R1.)(17.$5.VR,VHIA,R30.R2.)P,(7.$16.(18.$5.VR,VHIA,R2?.)(18.$5.VR,VHIA,Vh,))P,(7.$16.(19.$5.VR,VHIA,R30.)(19.$5.VR,VHIA,Vh,))P,(6.(26.(27.(10.&40.Vsp,)+?0.)R2:.)(26.R2:.(27.(10.&40.Vsp,)+>0.)))P,(7.$16.(28.R2;.+20.)=)P,(7.$16.(28.R2=.+40.)=)P,(29.VR,VLB,VLF,R2>.+40.)P,(29.VR,(14.$15.R34.VLB,)VLF,R2?.+40.)P,(2:.(17.$5.VR,VHIA,Vh,)R30.+40.)P,(2;.$5.R34.R31.(23.$2<.(2=.R17.)(23.$2<.(2=.R16.)(23.$2<.(2=.R15.)(2>.$2<.)))))P,(2;.$5.R35.(2?.(30.R32.+3.)(31.(12.VR,)))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(2>.$2<.))))))))))P,(2;.$5.R36.(2?.(10.&40.Vsp,)-68.)(23.$2<.(2=.Vs11,)(23.$2<.(2=.Vs10,)(23.$2<.(2=.Vs9,)(23.$2<.(2=.Vs8,)(23.$2<.(2=.Vs7,)(23.$2<.(2=.Vs6,)(23.$2<.(2=.Vs5,)(23.$2<.(2=.Vs4,)(23.$2<.(2=.Vs3,)(23.$2<.(2=.Vs2,)(23.$2<.(2=.Vs1,)(23.$2<.(2=.Vs0,)(23.$2<.(2=.Vra,)(2>.$2<.)))))))))))))))P,(2;.$5.R37.R33.(23.$2<.(33.#18.R16.)(23.$2<.(2=.R14.)(23.$2<.(2=.R13.)(23.$2<.(2=.R12.)(23.$2<.(2=.R11.)(23.$2<.(2=.R10.)(23.$2<.(2=.R?.)(23.$2<.(2=.(:.&40.R34.))(23.$2<.(2=.(:.&40.R34.))(23.$2<.(2=.R>.)(23.$2<.(33.#10.R15.)(23.$2<.(2=.(:.&40.R34.))(2>.$2<.))))))))))))))P,(?.$5.R38.(2?.R34.+78.)(2?.(10.&40.Vsp,)-68.))P,(?.$5.R39.Vlo,R35.)P,(>.$5.R3:.)P,(13.$5.VR,VHIA,R3>.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)R3:.Vm,R3;.)P,(13.$5.VR,VHIA,R3?.(14.$15.R3>.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)R3:.R3=.R3<.)P,(11.$5.(12.VR,)R3=.Vslo,(10.&40.Vsp,))(34.$5.(12.VR,)(17.$5.VR,VHIA,R41.)(35.R41.R40.R3?.R3=.R3<.R1>.)(8.(9.R39.(:.&40.R3:.)Vgp,Vtp,R38.R37.R36.Vsp,(:.&40.R3:.)(:.&40.R1>.)R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.(:.&40.(2?.(30.R3;.+3.)(31.(12.VR,))))R29.R28.R27.R26.R25.R24.R23.R22.)VF,(:.&40.+:;158.)Vfc,(<.(2.&40.))R3>.(=.$5.)))")
(* [comment removed for export] *).
  Proof.
  intros until k88.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE RSL SThi STlo MI PRES PRES2 SS.
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
  lx_pre. lx_run_tac (PLAN [0xab19c] [] 311%N). lx_tree.
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
  assert (NP6 : sp1 + 120 <= p \/ p + 1 <= sp1).
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
  try (lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf (sp1 + 120) (bv_unsigned sp + -104), SV : rw_cells _ mf (bv_unsigned sp + -104) _, RS : rw_cells _ mf sp1 _ |- _ =>
          chunk_to_stk RS;
          lazymatch type of RS with stk _ _ _ ?hi => replace hi with (sp1 + 120) in RS by (clear; lia) end;
          pose proof (stk_merge asegs mf lo sp1 _ ST0 RS ltac:(first [ clear - SP1 SLO NS1 NB1 NEED0; lia | lx_side_lia ])) as ST2;
          pose proof (stk_merge asegs mf lo (sp1 + 120) _ ST2 STA ltac:(first [ clear - SP1 SLO NS1 NB1 NEED0; lia | lx_side_lia ])) as ST3;
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
  Lemma pol_fin : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies_B ()) "Phq,(4.$5.VR,VHIA,)Pnodes,(21.$16.)PFB,$16.Psp1,$16.Pmm,P,(2.&40.)(3.(2.&8.))Pr,$16.Pp',$16.Phct,(2.&40.)Phcpad,(2.&40.)Phcl,$16.Phcp,$16.Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pja,(21.(2.&8.))Pjb,(21.(2.&8.))Pk24,(2.&40.)Pk32,(2.&40.)Pk40,(2.&40.)Pk48,(2.&40.)Pk56,(2.&40.)Pk64,(2.&40.)Pk88,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps2v,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps8v,(2.&40.)Ps9v,(2.&40.)Ps10v,(2.&40.)Ps11v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(20.$5.VR,VHIA,R2?.(14.$15.(36.(37.$16.R2>.))VLB,)(23.(24.$16.$16.)(25.$16.$16.R2=.+40.)VLF,)R2;.)P,Px,$16.P,(17.$5.VR,VHIA,Vh,R1.)(17.$5.VR,VHIA,R32.R2.)P,(7.$16.(18.$5.VR,VHIA,R31.)(18.$5.VR,VHIA,Vh,))P,(7.$16.(19.$5.VR,VHIA,R32.)(19.$5.VR,VHIA,Vh,))P,(7.$16.(1:.$5.VR,VHIA,R33.)(1:.$5.VR,VHIA,Vh,))P,(26.(1;.$5.VR,VHIA,R34.)(1;.$5.VR,VHIA,Vh,))P,(26.(1<.$5.VR,VHIA,R35.)(2?.(1<.$5.VR,VHIA,Vh,)(38.(27.VEND,VP,)Vd,)))P,(26.(39.(3:.$16.R35.))(3;.(27.VEND,VP,)))P,(6.(26.(27.(10.&40.Vsp,)+?0.)R34.)(26.R34.(27.(10.&40.Vsp,)+>0.)))P,(7.$16.(28.R35.+20.)=)P,(7.$16.(28.R37.+40.)=)P,(29.VR,VLB,VLF,R38.+40.)P,(2:.(17.$5.VR,VHIA,Vh,)R39.+40.)P,(2;.$5.R38.R3:.(23.$2<.(2=.R31.)(23.$2<.(2=.R30.)(23.$2<.(2=.R2?.)(2>.$2<.)))))P,(2;.$5.R39.(2?.(30.R3;.+3.)(31.(12.VR,)))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(2>.$2<.))))))))))P,(2;.$5.R3:.(2?.(10.&40.Vsp,)-68.)(23.$2<.(2=.Vs11,)(23.$2<.(2=.Vs10,)(23.$2<.(2=.Vs9,)(23.$2<.(2=.Vs8,)(23.$2<.(2=.Vs7,)(23.$2<.(2=.Vs6,)(23.$2<.(2=.Vs5,)(23.$2<.(2=.Vs4,)(23.$2<.(2=.Vs3,)(23.$2<.(2=.Vs2,)(23.$2<.(2=.Vs1,)(23.$2<.(2=.Vs0,)(23.$2<.(2=.Vra,)(2>.$2<.)))))))))))))))P,(2;.$5.R3;.R3<.(23.$2<.(33.#18.R31.)(23.$2<.(2=.R2?.)(23.$2<.(2=.R2>.)(23.$2<.(2=.R2=.)(23.$2<.(2=.R2<.)(23.$2<.(2=.R2;.)(23.$2<.(2=.R2:.)(23.$2<.(2=.(:.&40.R3=.))(23.$2<.(2=.(:.&40.R3=.))(23.$2<.(2=.R29.)(23.$2<.(33.#10.R30.)(23.$2<.(2=.(:.&40.R3=.))(2>.$2<.))))))))))))))P,(?.$5.R3<.(2?.R3=.+78.)(2?.(10.&40.Vsp,)-68.))P,(?.$5.R3=.Vlo,R3>.)P,(>.$5.R3>.)P,(13.$5.VR,VHIA,R43.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)(23.(24.$16.$16.)(25.$16.$16.VPP,(2?.VPP,+8.))(23.(24.$16.$16.)(25.$16.$16.VCUR,(2?.VCUR,+20.))(2>.(24.$16.$16.))))Vm,R3?.)P,(11.$5.(12.VR,)R40.Vslo,R41.)P,(11.$5.(12.VR,)R41.R42.(10.&40.Vsp,))P,(2;.$5.R42.VPP,(23.$2<.(2=.(:.&40.R40.))(2>.$2<.)))P,(6.(26.VP,R41.)(26.R41.VEND,))P,(2;.$5.R44.VCUR,(3<.R41.R40.R3?.R3>.(3=.$16.=R47.)))P,(3>.(6.(7.$16.R3?.=)(6.(7.$16.R40.=)(7.(21.$16.)R48.(2>.$16.))))(6.(26.VBUF,R3?.)(6.(26.=R40.)(26.(2?.R3?.R40.)VEND,))))P,(3?.$5.L,(21.$2<.)$40.R46.(14.$15.(36.(37.$16.R49.))VLB,)(3=.$16.=R49.)R49.)P,(41.$16.R4:.)P,Px,$16.P,(42.$16.R1.R4<.)PB,$16.Pk,$16.P,(42.(24.$16.$16.)(25.$16.$16.R2.R1.)VLB,)(3>.(26.(2?.R5.$43.)R3.)(26.(2?.R3.R2.)R5.))P,(6.(44.-3000.R48.)(26.R48.=))P,P,(3>.(7.$16.R49.=)(7.$16.R49.-2080.))(7.$16.R49.VEND,)(45.$5.(46.$5.VR,VHIA,R4?.Vmo0,)(47.$5.VR,VHIA,$48.$38.$3;.Lr,$16.(3>.(7.$16.R1.=)(7.$16.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(27.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(8.(9.R38.(:.&40.R4<.)Vgp,Vtp,R37.R36.R35.Vsp,(:.&40.R4<.)(:.&40.R4:.)R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(:.&40.(2?.(30.R4=.+3.)(31.(12.VR,))))R28.R27.R26.R25.R24.R23.R22.R21.)VF,(:.&40.+:;158.)Vfc,(<.(2.&40.))R4;.(=.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HHq HCSq ETq ESq EFq EVq EFRq ECNT SP1 SP1M F64 FRSH CFB FHD FSH SAVE RSL SThi STlo MI PRESq SS1 SS2 HPPx Hp' HCURx HCB NC ND APN RR HENDq.
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
