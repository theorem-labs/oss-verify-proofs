(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len
     A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_name_A A_x509_get_name_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_x509_get_name_C () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Walk.Call.FSHb"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.rsl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "Stdlib.Lists.List.NoDup"; "Walk.Call.nfreshA"; "Walk.Call.curFA"; "Walk.Call.headrep"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_lseg"; "Stdlib.Lists.List.removelast"; "Stdlib.Lists.List.last"; "Corelib.Init.Datatypes.list"; "Walk.Call.nodeF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Walk.Call.Wc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.hd"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Walk.Call.nvA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_A.rslr"].



Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
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
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
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

  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 64)].
  Local Notation NB := (END - P).
  Local Notation POST := (x509_get_name_postE asegs R HIA PHIn FFRn CNTn h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END NB lo slo d m mo0).

  (* [comment removed for export] *)
  Definition nLB (nodes : list Z) : list blk := map (fun a => (a, 64)) (rev nodes) ++ LB.
  (* [comment removed for export] *)
  Definition Wc (cur : Z) : list ivl := [(PP, PP + 8); (cur, cur + 64)].
  (* [comment removed for export] *)
  Definition nodeF (FB x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "(0.(1.=O1.)(0.(2.$3.(4.O1.+10.)=)(0.(5.(6.O1.+40.)(7.(8.VR,)))(0.(9.(5.(6.O1.+40.)(:.(8.VR,)))(5.(;.(8.VR,))O1.))(0.PB,$3.Pk,$3.P,(<.(=.$3.$3.)(>.$3.$3.R2.R1.)(?.$10.VLB,(11.VLF,)))(9.(5.(6.O1.+40.)R3.)(5.(6.R3.R2.)O1.))(0.(9.(5.(6.VPP,+8.)O1.)(5.(6.O1.+40.)VPP,))(0.(9.(5.(6.O1.+40.)VCUR,)(5.(6.VCUR,+40.)O1.))(9.(5.(6.O2.+80.)O1.)(5.(6.O1.+40.)O2.)))))))))")
(* [comment removed for export] *).
  #[using="Type"] Lemma nodeF_fresh : forall FB x, nodeF FB x -> fresh_apart R LB LF x 64.
  Proof. (intros FB x dd_H; ddestruct dd_H as (N0 & _ & NC & ND & NAP & _)). exact (conj N0 (conj NC (conj ND NAP))). Qed.
  Definition nfreshA (FB : Z) (nodes : list Z) : Prop := forall x, In x nodes -> nodeF FB x.
  (* [comment removed for export] *)
  Definition curFA (nodes : list Z) (cur : Z) : Prop := (nodes = [] /\ cur = CUR) \/ (nodes <> [] /\ cur = last nodes 0).
  (* [comment removed for export] *)
  Definition headrep (mc : mem) (nodes : list Z) : Prop :=
    nodes = [] \/ exists j48' mg' p7', rw_cells asegs mc CUR (name_blob j48' (hd 0 nodes) mg' p7').
  (* [comment removed for export] *)
  Definition FSHb (b4 : byte) : list cell := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "(12.$13.(14.(15.&8.+?1.))(12.$13.(14.(15.&8.+?1.))(12.$13.(14.(15.&8.+?1.))(12.$13.(14.(15.&8.+?1.))(12.$13.(14.O1.)(12.$13.(14.(15.&8.+?2.))(12.$13.(14.(15.&8.+?2.))(12.$13.(14.(15.&8.+?2.))(12.$13.(14.(15.&8.=))(12.$13.(14.(15.&8.+?3.))(12.$13.(14.(15.&8.+?3.))(12.$13.(14.(15.&8.+?3.))(12.$13.(14.(15.&8.=))(12.$13.(14.(15.&8.=))(12.$13.(14.(15.&8.=))(12.$13.(14.(15.&8.=))(16.$13.)))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition nvA (FB sp1 : Z) (w0 w1 w2 ga gb : word) (b4 : byte) (j0 j96 : list byte)
      (Lh : list blk) (nodes : list Z) (cur : Z) (PHIx FFRx : Z) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "(0.(17.$18.VR,VHIA,O1.O8.(12.(=.$3.$3.)(>.$3.$3.O12.+80.)VLF,)O3.)(0.(19.$18.VR,VHIA,O1.O2.)(0.(1:.Vmo0,O2.)(0.(2.$3.(1;.$18.VR,VHIA,O1.)(1;.$18.VR,VHIA,Vh,))(0.(2.$3.(1<.$18.VR,VHIA,O1.)(1<.$18.VR,VHIA,Vh,))(0.(2.$3.(1=.$18.VR,VHIA,O1.)(1=.$18.VR,VHIA,Vh,))(0.Px,$3.P,(1>.$18.VR,VHIA,Vh,R1.)(1>.$18.VR,VHIA,O1.R2.)(0.(5.(1?.$18.VR,VHIA,O1.)(6.(1?.$18.VR,VHIA,Vh,)O5.))(0.(5.(20.$18.VR,VHIA,O1.)(6.(20.$18.VR,VHIA,Vh,)O4.))(0.(21.$18.VR,VHIA,O1.VLB,VLF,(22.&40.Vsp,)(22.&40.Vsp,)(12.(=.$3.$3.)(>.$3.$3.VPP,(6.VPP,+8.))(12.(=.$3.$3.)(>.$3.$3.VCUR,(6.VCUR,+40.))(16.(=.$3.$3.))))Vm,O3.)(0.(0.(5.(23.(22.&40.Vsp,)+?0.)O11.)(5.O11.(23.(22.&40.Vsp,)+>0.)))(0.(2.$3.(4.O11.+20.)=)(0.(2.$3.(4.O12.+40.)=)(0.(24.VR,VLB,VLF,O12.+80.)(0.(25.(1>.$18.VR,VHIA,Vh,)O12.+80.)(0.(26.$18.O3.O12.(12.$13.(27.O10.)(12.$13.(27.O?.)(12.$13.(27.O>.)(16.$13.)))))(0.(26.$18.O3.(6.O12.+20.)(12.$13.(27.O=.)(16.$13.)))(0.(26.$18.O3.(6.O12.+40.)(12.$13.(27.O<.)(16.$13.)))(0.(26.$18.O3.(6.(28.O12.+3.)(29.(2:.VR,)))(2;.O;.))(0.(26.$18.O3.(6.(22.&40.Vsp,)-68.)(12.$13.(27.Vs11,)(12.$13.(27.Vs10,)(12.$13.(27.Vs9,)(12.$13.(27.Vs8,)(12.$13.(27.Vs7,)(12.$13.(27.Vs6,)(12.$13.(27.Vs5,)(12.$13.(27.Vs4,)(12.$13.(27.Vs3,)(12.$13.(27.Vs2,)(12.$13.(27.Vs1,)(12.$13.(27.Vs0,)(12.$13.(27.Vra,)(16.$13.)))))))))))))))(0.(26.$18.O3.O11.(2<.VEND,VCUR,O12.O:.O9.))(0.(2=.$18.O3.(6.O11.+78.)(6.(22.&40.Vsp,)-68.))(0.(2=.$18.O3.Vlo,O11.)(0.(2>.$18.O3.VBUF,Vbs,)(0.(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.VPP,+8.)(0.(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.VCUR,+40.)(0.(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.VBUF,(30.(31.(32.&8.)Vbs,)))(0.(33.$18.O3.)(0.(34.$18.(2:.VR,)O3.Vslo,(22.&40.Vsp,))(0.Pb,$10.P,(<.$10.R1.VLB,)(<.$10.R2.O8.)(0.Px,$3.P,(<.$3.R1.O7.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)O8.)(0.(35.$3.O7.)(0.(36.O12.O7.)(0.(37.O7.O6.)(0.(38.O3.O7.)(0.(39.$18.O3.O8.(3:.$3.O7.)(3;.$3.O7.=))(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.O6.+40.)))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
  Definition nvAr (r64 : Z) (FB sp1 : Z) (w0 w1 w2 ga gb : word) (b4 : byte) (j0 j96 : list byte)
      (Lh : list blk) (nodes : list Z) (cur : Z) (PHIx FFRx : Z) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "(0.(17.$18.VR,VHIA,O1.O8.(12.(=.$3.$3.)(>.$3.$3.O12.+80.)VLF,)O3.)(0.(19.$18.VR,VHIA,O1.O2.)(0.(1:.Vmo0,O2.)(0.(2.$3.(1;.$18.VR,VHIA,O1.)(1;.$18.VR,VHIA,Vh,))(0.(2.$3.(1<.$18.VR,VHIA,O1.)(1<.$18.VR,VHIA,Vh,))(0.(2.$3.(1=.$18.VR,VHIA,O1.)(1=.$18.VR,VHIA,Vh,))(0.Px,$3.P,(1>.$18.VR,VHIA,Vh,R1.)(1>.$18.VR,VHIA,O1.R2.)(0.(5.(1?.$18.VR,VHIA,O1.)(6.(1?.$18.VR,VHIA,Vh,)O5.))(0.(5.(20.$18.VR,VHIA,O1.)(6.(20.$18.VR,VHIA,Vh,)O4.))(0.(21.$18.VR,VHIA,O1.VLB,VLF,(22.&40.Vsp,)(22.&40.Vsp,)(12.(=.$3.$3.)(>.$3.$3.VPP,(6.VPP,+8.))(12.(=.$3.$3.)(>.$3.$3.VCUR,(6.VCUR,+40.))(16.(=.$3.$3.))))Vm,O3.)(0.(0.(5.(23.(22.&40.Vsp,)+?0.)O11.)(5.O11.(23.(22.&40.Vsp,)+>0.)))(0.(2.$3.(4.O11.+20.)=)(0.(2.$3.(4.O12.+40.)=)(0.(24.VR,VLB,VLF,O12.+80.)(0.(25.(1>.$18.VR,VHIA,Vh,)O12.+80.)(0.(26.$18.O3.O12.(12.$13.(27.O10.)(12.$13.(27.O?.)(12.$13.(27.O>.)(16.$13.)))))(0.(26.$18.O3.(6.O12.+20.)(12.$13.(27.O=.)(16.$13.)))(0.(26.$18.O3.(6.O12.+40.)(12.$13.(27.O<.)(16.$13.)))(0.(26.$18.O3.(6.(28.O12.+3.)(29.(2:.VR,)))(2;.O;.))(0.(26.$18.O3.(6.(22.&40.Vsp,)-68.)(12.$13.(27.Vs11,)(12.$13.(27.Vs10,)(12.$13.(27.Vs9,)(12.$13.(27.Vs8,)(12.$13.(27.Vs7,)(12.$13.(27.Vs6,)(12.$13.(27.Vs5,)(12.$13.(27.Vs4,)(12.$13.(27.Vs3,)(12.$13.(27.Vs2,)(12.$13.(27.Vs1,)(12.$13.(27.Vs0,)(12.$13.(27.Vra,)(16.$13.)))))))))))))))(0.(26.$18.O3.O11.(4;.VEND,VCUR,O12.O:.O9.O13.))(0.(2=.$18.O3.(6.O11.+78.)(6.(22.&40.Vsp,)-68.))(0.(2=.$18.O3.Vlo,O11.)(0.(2>.$18.O3.VBUF,Vbs,)(0.(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.VPP,+8.)(0.(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.VCUR,+40.)(0.(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.VBUF,(30.(31.(32.&8.)Vbs,)))(0.(33.$18.O3.)(0.(34.$18.(2:.VR,)O3.Vslo,(22.&40.Vsp,))(0.Pb,$10.P,(<.$10.R1.VLB,)(<.$10.R2.O8.)(0.Px,$3.P,(<.$3.R1.O7.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)O8.)(0.(35.$3.O7.)(0.(36.O12.O7.)(0.(37.O7.O6.)(0.(38.O3.O7.)(0.(39.$18.O3.O8.(3:.$3.O7.)(3;.$3.O7.=))(2?.$18.(2:.VR,)(1>.$18.VR,VHIA,O1.)O3.O6.+40.)))))))))))))))))))))))))))))))))))))").

  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Ltac nvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & GA & GB & FSH & SAVE & RSL & STb & STlo & BYc & OPP & OCUR & OBUF & MIc & SSc
                   & SUBL & SUBN & HND & HFR & HCF & HHD & HLS & OCc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma nLB_snoc : forall nodes N, nLB (nodes ++ [N]) = (N, 64) :: nLB nodes.
  Proof. intros. unfold nLB. rewrite rev_app_distr. reflexivity. Qed.
  #[using="Type"] Lemma nLB_sub : forall nodes b, In b LB -> In b (nLB nodes).
  Proof. intros. unfold nLB. apply in_or_app. right. assumption. Qed.
  #[using="Type"] Lemma nLB_in : forall nodes x, In x nodes -> In (x, 64) (nLB nodes).
  Proof. intros. unfold nLB. apply in_or_app. left. apply in_map_iff. exists x. split; [reflexivity|]. rewrite <- in_rev. exact H. Qed.
    #[using="Type"] Lemma last_in : forall (nodes : list Z), nodes <> [] -> In (last nodes 0) nodes.
  Proof. intros nodes Hne. rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="HIA h slo BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL LOS"] Lemma cur_facts : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.Pnodes,(3<.$3.)Pcur,$3.P,(24.VR,VLB,VLF,R3.+80.)P,(36.R4.R3.)P,(37.R4.R3.)(0.(2.$3.(4.R4.+8.)=)(0.(1.=R4.)(0.(5.(6.R4.+40.)Vlo,)(0.(9.(5.(6.VPP,+8.)R4.)(5.(6.R4.+40.)VPP,))(0.(9.(5.(6.R4.+40.)VBUF,)(5.(6.VBUF,(30.(31.(32.&8.)Vbs,)))R4.))(0.(9.(5.(6.R6.+80.)R4.)(5.(6.R4.+40.)R6.))(9.(2.$3.R4.VCUR,)(0.(<.$3.R4.R5.)(3=.R6.R4.)))))))))")
(* [comment removed for export] *).
  Proof.
    clear - ALC CUR0 CURLO D1 DCB CWC BIN SLOS SLOL LOS HIA. intros FB nodes cur FRSH HFR HCF.
    pose proof (art_lo asegs R HIA) as ALO.
    destruct HCF as [[-> ->]|[Hne ->]].
    - pose proof (frame_apart_obj R HIA LB LF lo _ CUR 64 FB 128 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
      repeat split; try assumption; try lia; try (left; reflexivity).
    - pose proof (last_in nodes Hne) as HIN. pose proof (HFR _ HIN) as NF. dpose NF as (N0 & N16 & NC & ND & NLB & NPP & NCU & NFB).
      split; [clear - N16; Z.div_mod_to_equations; lia|]. split; [exact N0|]. split; [clear - NC ALO LOS; lia|].
      split; [exact NPP|]. split; [apply NLB; apply in_or_app; left; exact BIN|]. split; [exact NFB|]. right. split; [exact HIN| exact NF].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma others_apart : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.PLh,(3<.$10.)Pnodes,(3<.$3.)Pcur,$3.Phc,(3>.$18.VR,VHIA,)PLF',(3<.$10.)Pmq,P,(32.&40.)(3?.(32.&8.))Py,$3.P,(17.$18.VR,VHIA,R4.R7.R3.R2.)P,Px,$3.P,(<.$3.R1.R8.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)R:.)P,(35.$3.R8.)P,(36.R;.R9.)P,(37.R:.R9.)P,(<.$3.R6.(3:.$3.R;.))(0.(3=.R>.R7.)(9.(5.(6.R7.+40.)R;.)(5.(6.R;.+40.)R7.)))")
(* [comment removed for export] *).
  Proof.
    clear. intros FB Lh nodes cur hc LF' mq y HH SUBN HND HFR HCF Hy.
    pose proof (in_removelast _ _ Hy) as HyN. split; [exact (HFR y HyN)|].
    destruct HCF as [[-> ->]|[Hne ->]]; [destruct Hy|].
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [_ HAP].
    assert (NE : y <> last nodes 0).
    { intros E. rewrite <- (removelast_last_app nodes 0) in HND by exact Hne.
      apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
    eapply (blocks_apart_in2 _ y 64 (last nodes 0) 64); [exact HAP| apply in_or_app; left; apply SUBN; exact HyN| apply in_or_app; left; apply SUBN; apply last_in; exact Hne| exact NE].
  Qed.

  #[using="Type"] Lemma lseg_W : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.PLh,(3<.$10.)Pnodes,(3<.$3.)Pcur,$3.Phc,(3>.$18.VR,VHIA,)PLF',(3<.$10.)Pmq,P,(32.&40.)(3?.(32.&8.))PLBn,(3<.$10.)Pmm,P,(32.&40.)(3?.(32.&8.))Pm1,P,(32.&40.)(3?.(32.&8.))Pfin,$3.P,(17.$18.VR,VHIA,R7.R:.R6.R5.)P,Px,$3.P,(<.$3.R1.R;.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)R=.)P,(35.$3.R;.)P,(36.R>.R<.)P,(37.R=.R<.)P,(39.$18.R8.R9.(3:.$3.R>.)R6.)P,(40.(41.R>.)R9.R8.)P,(42.$18.R:.R9.)(39.$18.R:.R<.(3:.$3.R11.)R9.)")
(* [comment removed for export] *).
  Proof.
    clear. intros FB Lh nodes cur hc LF' mq LBn mm m1 fin HH SUBN HND HFR HCF HL MU WM.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
    ddestruct (others_apart FB Lh nodes cur hc LF' mq y HH SUBN HND HFR HCF Hy) as ((_ & _ & _ & _ & _ & YP & _ & _) & YC).
    cbn [disjoint_from Wc]. lia.
  Qed.

  #[using="D1"] Lemma headrep_W : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.Pnodes,(3<.$3.)Pcur,$3.Pmm,P,(32.&40.)(3?.(32.&8.))Pm1,P,(32.&40.)(3?.(32.&8.))P,(36.R5.R4.)P,(37.R5.R4.)P,(38.R4.R6.)P,(40.(41.R6.)R5.R4.)P,(42.$18.R6.R5.)(38.R6.R9.)")
(* [comment removed for export] *).
  Proof.
    clear - D1. intros FB nodes cur mm m1 HFR HCF [->|(j & g & p7 & HR)] MU WM; [left; reflexivity|].
    destruct HCF as [[-> _]|(Hne & ->)]; [left; reflexivity| right].
    pose proof (HFR _ (last_in nodes Hne)) as (_ & _ & _ & _ & _ & _ & NCU & _).
    dexists j, g, p7. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. cbn. lia.
  Qed.


  #[using="Type"] Lemma lseg_presA : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PLq,(3<.$10.)PLFq,(3<.$10.)PSPq,$3.PSSPq,$3.PTOPq,$3.Pl,(3<.$3.)Pfin,$3.Pmm,P,(32.&40.)(3?.(32.&8.))Pm2,P,(32.&40.)(3?.(32.&8.))P,(43.$18.VR,R9.R8.R7.R6.R5.(16.$44.)R2.R1.)P,Px,$3.P,(<.$3.R1.R6.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)R<.)P,(5.(7.(8.VR,))R9.)P,(39.$18.R5.R<.R7.R6.)(39.$18.R5.R=.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    clear. intros Lq LFq SPq SSPq TOPq l fin mm m2 HP SUB HSP HL.
    eapply name_lseg_mem; [exact HL| intros y Hy; eapply name_lseg_in; [exact HL| exact Hy] |].
    intros y cs Hy HR Hsz. eapply (presA_rw_cells asegs R); [exact HP| exact HR| | exact I]. rewrite Hsz.
    eapply client_range_block; [apply in_or_app; left; eapply name_lseg_in; [exact HL| exact Hy] | lia | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma close_nodes : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.PLh,(3<.(=.$3.$3.))Pnodes,(3<.$3.)Pcur,$3.Pmm,P,(32.&40.)(3?.(32.&8.))PJ,(3<.(32.&8.))PMG,(32.&8.)PP7,(3<.(32.&8.))P,(36.R8.R6.)P,(37.R7.R6.)P,(38.R6.R8.)P,Px,$3.P,(<.$3.R1.R:.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)R<.)P,(39.$18.R8.R;.(3:.$3.R:.)(3;.$3.R:.=))P,(26.$18.R9.R:.(45.R8.=R7.R6.))(0.(46.(3<.(32.&8.))Lj,(3<.(32.&8.))(46.(32.&8.)Lg,(32.&8.)(46.(3<.(32.&8.))Lp7,(3<.(32.&8.))(26.$18.R=.VCUR,(45.R3.(47.$3.=R?.)R2.R1.)))))(39.$18.R:.R=.R<.=))")
(* [comment removed for export] *).
  Proof.
    clear. intros FB Lh nodes cur mm J MG P7 HFR HCF HHD SUBN HL HR.
    destruct HCF as [[-> ->]|(Hne & ->)].
    - split; [dexists J, MG, P7; exact HR| exact I].
    - destruct HHD as [E|HHD]; [exfalso; exact (Hne E)|]. split; [exact HHD|].
      pose proof (HFR _ (last_in nodes Hne)) as (N0 & N16 & _).
      rewrite <- (removelast_last_app nodes 0) at 1 by exact Hne. apply name_lseg_app. split; [exact HL|].
      cbn [name_lseg hd]. split; [apply SUBN; apply last_in; exact Hne|].
      split; [exact N16|]. split; [exact N0|]. split; [| exact I]. dexists J, MG, P7. exact HR.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma close_fin : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.PLh,(3<.(=.$3.$3.))Pnodes,(3<.$3.)Pcur,$3.Pmm,P,(32.&40.)(3?.(32.&8.))PJ,(3<.(32.&8.))PMG,(32.&8.)PP7,(3<.(32.&8.))Pfin,$3.P,(36.R9.R7.)P,(37.R8.R7.)P,Px,$3.P,(<.$3.R1.R:.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)R<.)P,(39.$18.R8.R;.(3:.$3.R:.)(3;.$3.R:.=))P,(26.$18.R9.R:.(45.R8.R5.R7.R6.))(39.$18.R:.R=.R<.R6.)")
(* [comment removed for export] *).
  Proof.
    clear. intros FB Lh nodes cur mm J MG P7 fin HFR HCF SUBN HL HR.
    destruct nodes as [|n0 rest0]; [exact I|]. assert (Hne : n0 :: rest0 <> []) by discriminate.
    revert Hne HFR HCF SUBN HL HR. generalize (n0 :: rest0). clear n0 rest0. intros nodes Hne HFR HCF SUBN HL HR.
    destruct HCF as [[E _]|(_ & ->)]; [exfalso; exact (Hne E)|].
    pose proof (HFR _ (last_in nodes Hne)) as (N0 & N16 & _).
    rewrite <- (removelast_last_app nodes 0) at 1 by exact Hne. apply name_lseg_app. split; [exact HL|].
    cbn [name_lseg hd]. split; [apply SUBN; apply last_in; exact Hne|].
    split; [exact N16|]. split; [exact N0|]. split; [| exact I]. dexists J, MG, P7. exact HR.
  Qed.

  #[using="Type"] Lemma headrep_snoc : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "Pnodes,(3<.$3.)Pcur,$3.Pmm,P,(32.&40.)(3?.(32.&8.))PJ,(3<.(32.&8.))PMG,(32.&8.)PP7,(3<.(32.&8.))PN,$3.P,(37.R7.R6.)P,(38.R6.R8.)P,(26.$18.R7.R8.(45.R6.R3.R5.R4.))(38.R8.(?.$3.R:.(12.$3.R4.(16.$3.))))")
(* [comment removed for export] *).
  Proof.
    clear. intros nodes cur mm J MG P7 N HCF HHD HR. right.
    destruct HCF as [[-> ->]|(Hne & _)].
    - dexists J, MG, P7. exact HR.
    - destruct HHD as [E|(j & g & p7 & HH)]; [exfalso; exact (Hne E)|]. dexists j, g, p7. rewrite hd_app_ne by exact Hne. exact HH.
  Qed.

  (* [comment removed for export] *)
  #[using="h lo slo CWP CWC SLOS SLOL LOS"] Lemma snoc_facts : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.PLh,(3<.(=.$3.$3.))Pnodes,(3<.$3.)Pcur,$3.PN,$3.Phc,(3>.$18.VR,VHIA,)Pmq,P,(32.&40.)(3?.(32.&8.))P,(17.$18.VR,VHIA,R2.(12.(=.$3.$3.)(>.$3.$3.R3.+40.)R6.)(12.(=.$3.$3.)(>.$3.$3.R7.+80.)VLF,)R1.)P,Pb,$10.P,(<.$10.R1.VLB,)(<.$10.R2.R9.)P,Px,$3.P,(<.$3.R1.R8.)(<.(=.$3.$3.)(>.$3.$3.R2.+40.)R:.)P,(35.$3.R8.)P,(36.R;.R9.)P,(37.R:.R9.)P,(24.VR,R<.(12.(=.$3.$3.)(>.$3.$3.R=.+80.)VLF,)R9.+40.)P,(2.$3.(4.R:.+10.)=)(0.(35.$3.(?.$3.R=.(12.$3.R;.(16.$3.))))(0.(36.R?.(?.$3.R=.(12.$3.R;.(16.$3.))))(0.(37.(?.$3.R=.(12.$3.R;.(16.$3.)))R;.)(0.(9.(5.(6.R;.+40.)R<.)(5.(6.R<.+40.)R;.))Px,$3.P,(<.$3.R1.(?.$3.R>.(12.$3.R<.(16.$3.))))(<.(=.$3.$3.)(>.$3.$3.R2.+40.)(12.(=.$3.$3.)(>.$3.$3.R=.+40.)R10.))))))")
(* [comment removed for export] *).
  Proof.
    clear - CWP CWC PPLO CURLO SLOS SLOL LOS. intros FB Lh nodes cur N hc mq HH SUBL SUBN HND HFR HCF NFR N16.
    pose proof (art_lo asegs R HIA) as ALO.
    dpose NFR as (N0 & NC & ND & NAP).
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [_ HAP]. cbn [blocks_apart app] in HAP. destruct HAP as [HAPN _].
    assert (NLB : forall B k, In (B, k) (LB ++ fdata LF) -> N + 64 <= B \/ B + k <= N).
    { intros B k Hb. apply NAP. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL _ Hb)| right; apply (fdata_cons_sub (B, k) [] FB 128 LF); exact Hb]. }
    assert (NPP : PP + 8 <= N \/ N + 64 <= PP).
    { destruct (fresh_apart_client R Lh ((FB, 128) :: LF) lo PP 8 N 64 NFR) as [X|X]; [| clear; lia| clear; lia| clear - ALO LOS; lia| right; exact X| left; exact X].
      eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL _ Hb)| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
    assert (NCU : N + 64 <= CUR \/ CUR + 64 <= N).
    { eapply (fresh_apart_client R Lh ((FB, 128) :: LF) lo CUR 64 N 64 NFR); [| clear; lia| clear; lia| clear - ALO LOS; lia].
      eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWC)|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL _ Hb)| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
    assert (NFB : FB + 128 <= N \/ N + 64 <= FB).
    { destruct (HAPN FB 128 ltac:(apply in_or_app; right; left; reflexivity)) as [X|X]; [right; exact X| left; exact X]. }
    assert (NF : nodeF FB N).
    { split; [exact N0|]. split; [exact N16|]. split; [exact NC|]. split; [exact ND|]. split; [exact NLB|]. split; [exact NPP|]. split; [exact NCU| exact NFB]. }
    assert (APcur : N + 64 <= cur \/ cur + 64 <= N).
    { destruct HCF as [[_ ->]|(Hne & ->)]; [exact NCU|]. apply HAPN. apply in_or_app. left. apply SUBN. apply last_in. exact Hne. }
    split; [| split; [| split; [| split; [exact APcur|]]]].
    - apply List.NoDup_app; [exact HND| constructor; [intros HIn; destruct HIn| constructor] |].
      intros y Hy [E|[]]. pose proof (HAPN y 64 ltac:(apply in_or_app; left; apply SUBN; exact Hy)). pose proof (HFR y Hy) as (Y0 & _). subst y. lia.
    - intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|[]]]; [exact (HFR y Hy)| exact NF].
    - right. split; [destruct nodes; discriminate| symmetry; apply last_last].
    - intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]]; [right; exact (SUBN _ Hx)| left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma nvA_mo : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.Psp1,$3.Pw0,(32.&40.)Pw1,(32.&40.)Pw2,(32.&40.)Pga,(32.&40.)Pgb,(32.&40.)Pb4,(32.&8.)Pj0,(3<.(32.&8.))Pj96,(3<.(32.&8.))PLh,(3<.$10.)Pnodes,(3<.$3.)Pcur,$3.PPHIx,$3.PFFRx,$3.Pmc,P,(32.&40.)(3?.(32.&8.))Pmoc,$48.Phc,(3>.$18.VR,VHIA,)Pmo',$48.P,(49.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(19.$18.VR,VHIA,R3.R2.)P,(1:.R5.R3.)(49.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R4.R5.)")
(* [comment removed for export] *).
  Proof.
    intros until mo'. intros D HK' MF'. nvA_open D.
    split; [exact HHc|]. split; [exact HK'|]. split; [eapply mo_frame_trans; [exact MFc| exact MF']|].
    spine; assumption.
  Qed.
  #[using="Type"] Lemma nvAr_mo : forall r64 FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mc moc hc mo',
    nvAr r64 FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mc moc hc -> HK asegs R HIA hc mo' -> mo_frame moc mo' ->
    nvAr r64 FB sp1 w0 w1 w2 ga gb b4 j0 j96 Lh nodes cur PHIx FFRx mc mo' hc.
  Proof.
    intros until mo'. intros D HK' MF'. nvA_open D.
    split; [exact HHc|]. split; [exact HK'|]. split; [eapply mo_frame_trans; [exact MFc| exact MF']|].
    spine; assumption.
  Qed.

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="IMG CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP LOS"] Lemma nvA_call0 : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_C ()) "PFB,$3.Psp1,$3.Pw0,(32.&40.)Pw1,(32.&40.)Pw2,(32.&40.)Pga,(32.&40.)Pgb,(32.&40.)Pb4,(32.&8.)Pj0,(3<.(32.&8.))Pj96,(3<.(32.&8.))PLh,(3<.$10.)Pnodes,(3<.$3.)Pcur,$3.PPHIx,$3.PFFRx,$3.Pmc,P,(32.&40.)(3?.(32.&8.))Pmoc,$48.Phc,(3>.$18.VR,VHIA,)PLh',(3<.$10.)PdV,$3.PdF,$3.Pm1,P,(32.&40.)(3?.(32.&8.))Pmo1,$48.Ph1,(3>.$18.VR,VHIA,)P,(49.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,Pb,$10.P,(<.$10.R1.R10.)(<.$10.R2.R9.)P,(33.$18.R5.)P,(2=.$18.R6.Vlo,R1:.)P,(1:.R<.R6.)P,(43.$18.VR,R13.(12.(=.$3.$3.)(>.$3.$3.R1=.+80.)VLF,)R1<.(4:.VR,)(1<.$18.VR,VHIA,R<.)(16.$44.)R>.R8.)P,(2.$3.(1;.$18.VR,VHIA,R7.)(1;.$18.VR,VHIA,R=.))P,(2.$3.(1<.$18.VR,VHIA,R8.)(1<.$18.VR,VHIA,R>.))P,(2.$3.(1=.$18.VR,VHIA,R9.)(1=.$18.VR,VHIA,R?.))P,(19.$18.VR,VHIA,R:.R;.)P,Py,$3.P,(1>.$18.VR,VHIA,R12.R1.)(1>.$18.VR,VHIA,R=.R2.)P,(5.(1?.$18.VR,VHIA,R<.)(6.(1?.$18.VR,VHIA,R12.)R10.))P,(5.(20.$18.VR,VHIA,R=.)(6.(20.$18.VR,VHIA,R13.)R10.))P,(17.$18.VR,VHIA,R>.R13.(12.(=.$3.$3.)(>.$3.$3.R25.+80.)VLF,)R10.)(49.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R14.R1;.R1:.(6.R19.R13.)(6.R18.R12.)R11.R10.R?.)")
(* [comment removed for export] *).
  Proof.
    intros until h1. intros D SUBq MI1 ST1 MF1 HP1 HT1 HS1 HF1 HK1 HCS1 HV1 HFR1 HH1. nvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    pose proof FRSH as FRSH'. ddestruct FRSH' as (F0 & F1 & F2 & F3).
    ddestruct (cur_facts FB nodes cur FRSH HFR HCF) as (CAL & CPOS & CLO & CPP & CBF & CFBa & CCASE).
    assert (SUBq' : forall b, In b (LB ++ fdata LF) -> In b (Lh ++ fdata ((FB, 128) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL b Hb)| right; apply (fdata_cons_sub b [] FB 128 LF); exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (Lh ++ fdata ((FB, 128) :: LF)) sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq']. }
    assert (INHq : In (FB, 24) (Lh ++ fdata ((FB, 128) :: LF))) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDq : In (FB + 32, 128 - 40) (Lh ++ fdata ((FB, 128) :: LF))) by (apply in_or_app; right; cbn; right; left; reflexivity).
    assert (CSHD : forall c, FB <= c < FB + 128 -> cshd R Lh ((FB, 128) :: LF) (arl_stklo R) (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn; exact Hc]. }
    assert (CRcur : client_range L (Lh ++ fdata ((FB, 128) :: LF)) sp1 cur 64).
    { destruct CCASE as [->|(HIN & _)]; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]|].
      eapply client_range_block; [apply in_or_app; left; exact (SUBN _ HIN)| clear; lia| clear; lia]. }
    split; [exact HH1|]. split; [exact HK1|]. split; [eapply mo_frame_trans; [exact MFc| exact MF1]|].
    split; [rewrite HT1; exact HTc|]. split; [rewrite HS1; exact HSc|]. split; [rewrite HF1; exact HFc|].
    split; [intros y Hy; exact (HCS1 y (HCSc y Hy))|].
    split; [clear - HVc HV1; lia|]. split; [clear - HFRc HFR1; lia|].
    split.
    { eapply (presW_hmono R HIA hc h1); [| exact HCS1| exact HS1].
      eapply (presW_call asegs R HIA hc LB LF _ _ X0 m mc m1); [exact PRES| exact HP1| exact SUBL| intros b Hb; right; exact Hb
        | clear - SP1; lia| clear - LOS SLO NS1 NRT; lia| clear; lia| intros y Hy; exact I]. }
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact FHD| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INHq| clear; lia| clear; lia]| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact GA| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear; lia| clear; lia]| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact GB| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear; lia| clear; lia]| exact I]|].
    split.
    { eapply (presA_shadow_cells_sh asegs R CS); [exact CSOK| cbn [cells_size csize Nat.add length FSHb]; exact CFB| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP1| exact FSH|].
      cbn [cells_size csize Nat.add length FSHb]. intros c Hc. apply CSHD. clear - Hc. lia. }
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact SAVE| apply client_range_stack; clear - SP1; lia| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP1| exact RSL| apply client_range_stack; clear; lia| exact I]|].
    split; [eapply (presA_stk asegs R); [exact HP1| exact STb| clear; lia| exact I]|].
    split; [exact ST1|].
    split.
    { eapply (presA_bytes_at0 asegs R); [exact HP1| exact BYc|]. destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right].
      split; [| exact I]. eapply client_range_block; [apply in_or_app; left; exact (SUBL _ BIN)| clear; lia| clear; lia]. }
    split; [eapply aobj_cs_mono; [exact HCS1|]; eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OPP| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear - LOS SLO SP1 NS1 NRT; lia]]|].
    split; [eapply aobj_cs_mono; [exact HCS1|]; eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OCUR| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| clear - LOS SLO SP1 NS1 NRT; lia]]|].
    split.
    { eapply aobj_cs_mono; [exact HCS1|]. eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OBUF| intros y Hy; eapply hcs_below_top; exact Hy|].
      destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right]. split; [| clear - LOS SLO SP1 NS1 NRT; lia].
      eapply client_range_block; [apply in_or_app; left; exact (SUBL _ BIN)| clear; lia| clear; lia]. }
    split; [exact MI1|].
    split; [eapply (presA_sshad asegs R); [exact HP1| exact SSc| exact SLOS| rewrite HSc; clear - HT TOP; lia]|].
    split; [intros b Hb; exact (SUBq _ (SUBL _ Hb))|]. split; [intros x Hx; exact (SUBq _ (SUBN _ Hx))|].
    split; [exact HND|]. split; [exact HFR|]. split; [exact HCF|].
    split.
    { destruct HHD as [E|(j & g & p7 & HR)]; [left; exact E| right]. dexists j, g, p7.
      eapply (presA_rw_cells asegs R); [exact HP1| exact HR| cbn [cells_size csize Nat.add length name_blob]; apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| exact I]. }
    split.
    { eapply name_lseg_mem; [exact HLS| intros y Hy; apply SUBq; eapply name_lseg_in; [exact HLS| exact Hy] |].
      intros y cs Hy HR Hsz. eapply (presA_rw_cells asegs R); [exact HP1| exact HR| | exact I]. rewrite Hsz.
      eapply client_range_block; [apply in_or_app; left; eapply name_lseg_in; [exact HLS| exact Hy] | clear; lia | cbn; clear; lia]. }
    eapply aobj_cs_mono; [exact HCS1|].
    eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OCc| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [exact CRcur| clear - LOS SLO SP1 NS1 NRT; lia]].
  Qed.
  End Call.
End Walk.
