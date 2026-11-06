(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo
     A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_x509_seq_stmtsE_w A_x509_get_san_A A_asn1_trav A_x509_policies_A A_x509_policies_B.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_x509_policies () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.Rep.SEQ_SIZE"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.CrtParseStmts.SSEQ"; "Stdlib.Lists.List.rev"; "OSSVerify.KrLib.LibA.ARt.fdata"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Walk.Call.Body.nodeF"; "OSSVerify.KrLib.A.A_asn1_trav.seqrep"; "Walk.Call.Body.curP"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "Stdlib.Lists.List.NoDup"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.RepFacts.seq_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.Lib.Cells.C1"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.LibA.ARt.sshad"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.removelast"; "Stdlib.Lists.List.last"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Walk.Call.Body.pinvx"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.LibA.ARt.fr_charge"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "OSSVerify.KrLib.A.A_x509_seq_stmtsE.seq_parser_postE"; "OSSVerify.KrLib.A.A_x509_policies_B.PHIpol"; "OSSVerify.KrLib.A.A_x509_policies_B.FFRpol"; "OSSVerify.KrLib.A.A_x509_policies_B.CNTpol"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Walk.Call.Body.LoopOblig"; "OSSVerify.KrLib.LibA.ARt.presA"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.Lib.Frame.ivl"; "Corelib.Lists.ListDef.repeat"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.A.A_x509_policies_A.A_X509_POLICIES"; "OSSVerify.KrLib.A.A_x509_seq_stmtsE.seq_parser_stmtE"; "OSSVerify.KrLib.A.A_x509_policies_A.STKpol"; "Corelib.Init.Nat.add"; "OSSVerify.KrLib.A.A_crt_parse_stmts.LFMAX_CRT"; "Corelib.Init.Logic.True"; "OSSVerify.KrLib.A.A_x509_seq_stmts.seq_parser_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
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

  Local Notation PHIpol := A_x509_policies_B.PHIpol.
  Local Notation FFRpol := A_x509_policies_B.FFRpol.
  Local Notation CNTpol := A_x509_policies_B.CNTpol.
  Local Notation POST := (seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r => r = 0 \/ r = -8320) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF (END - P) lo slo d m mo0).
  Local Notation nLB nodes := (SSEQ (rev nodes) ++ LB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis BUDF : hfr asegs R HIA h + FFRpol (END - P) d <= FR_MAX.
  Hypothesis BUDV : havol asegs R HIA h <= AVOL_MAX.

  Section Body.
  Variables (FB sp1 : Z).
  Hypothesis SP1 : bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 64.
  Hypothesis CFB : crange CS FB 64.
  Hypothesis APP : FB + 64 <= PP \/ PP + 8 <= FB.
  Hypothesis APC : FB + 64 <= CUR \/ CUR + 32 <= FB.
  Local Notation LF' := ((FB, 64) :: LF).
  Local Notation WMU cur := [(PP, PP + 8); (cur%Z, (cur + 32)%Z); (FB, FB + 64); (lo, bv_unsigned sp)].
  Local Notation K24 := (Z_to_bv 64 18446744073709542038).
  Local Notation K32 := (Z_to_bv 64 18446744073709542144).
  Local Notation K40 := (Z_to_bv 64 18446744073709542042).
  Local Notation K48 := (Z_to_bv 64 156512).
  Local Notation K56 := (Z_to_bv 64 18446744073709543296).

  #[using="Type"] Lemma nLB_in : forall nodes x, In x nodes -> In (x, 32) (nLB nodes).
  Proof. intros nodes x Hx. apply in_or_app. left. unfold SSEQ. apply (in_map (fun a => (a, SEQ_SIZE))). apply -> in_rev. exact Hx. Qed.
  #[using="Type"] Lemma nLB_snoc : forall nodes N, nLB (nodes ++ [N]) = (N, 32) :: nLB nodes.
  Proof. intros nodes N. unfold SSEQ. rewrite rev_app_distr. reflexivity. Qed.

  Definition nodeF (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(0.(1.=O1.)(0.(2.$3.(4.O1.+10.)=)(0.(5.(6.O1.+20.)Vlo,)(0.(7.(5.(6.VPP,+8.)O1.)(5.(6.O1.+20.)VPP,))(0.(7.(5.(6.VCUR,+20.)O1.)(5.(6.O1.+20.)VCUR,))(0.(7.(5.(6.VFB,+40.)O1.)(5.(6.O1.+20.)VFB,))(0.PB,$3.Pk,$3.P,(8.(9.$3.$3.)(:.$3.$3.R2.R1.)VLB,)(7.(5.(6.O1.$;.)R3.)(5.(6.R3.R2.)O1.))(<.VR,VLB,VLF,O1.+20.))))))))")
(* [comment removed for export] *).
  Definition curP (nodes : list Z) (cur : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(0.(1.=O1.)(0.(2.$3.(4.O1.+8.)=)(0.(5.(6.O1.+20.)Vlo,)(0.(7.(5.(6.VPP,+8.)O1.)(5.(6.O1.+20.)VPP,))(0.(7.(5.(6.O1.+20.)VBUF,)(5.(6.VBUF,(=.(>.(?.&8.)Vbs,)))O1.))(0.(7.(5.(6.VFB,+40.)O1.)(5.(6.O1.+20.)VFB,))(0.(10.(11.VR,)(12.$13.(12.$13.(14.(15.$3.O2.))VLB,)(16.(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)))Vlo,(18.$19.VR,VHIA,Vh,)O1.+20.)(7.(2.$3.O1.VCUR,)(8.$3.O1.O2.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L38383890888.1 L44052539574.1 L64638104799.4 L66151427842.1600000500:00J00eS3curS3curS3BUF2bs3cur3NLBS3cur2r03N161q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="BIN ALC CUR0 CWC CURLO DCB D1 APC"] Lemma curP_of : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Pm',P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.P,Px,$3.P,(8.$3.R1.R3.)(1<.R2.)P,(1=.$19.R4.(12.$13.(14.(15.$3.R3.))VLB,)VBUF,VEND,VCUR,R3.R2.)(1>.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m' nodes cur HF HS. destruct nodes as [|a r].
    - cbn in HS. subst cur. unfold curP. spine; first [assumption | left; reflexivity | idtac].
      eapply client_wrange_mono; [exact CWC|]. intros b Hb. apply fdata_cons_sub. exact Hb.
    - ddestruct HS as (E & HI & H16 & H0 & _).
      assert (Hne : a :: r <> []) by discriminate.
      pose proof (last_in (a :: r) Hne) as HIN. rewrite <- E in HIN.
      ddestruct (HF cur HIN) as (N0 & N16 & NLO & NPP & NCUR & NFB & NLB & _).
      unfold curP. spine; try assumption.
      + clear - N16. Z.div_mod_to_equations. lia.
      + specialize (NLB _ _ BIN). unfold SEQ_SIZE in NLB. clear - NLB. lia.
      + eapply client_wrange_block; [apply in_or_app; left; exact HI| clear; lia| clear; lia].
      + right. exact HIN.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pinvx (Lx : list blk) (mm : mem) (hc : HST asegs R HIA) (nodes : list Z) (cur : Z) (nt npad : word) (cl cp : Z)
                  (w0 w1 w2 lenw k64 k88 : word) (ja jb : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(0.(1?.$19.VR,VHIA,O?.(12.$13.O11.(12.$13.(14.(15.$3.O>.))VLB,))(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)O10.)(0.Px,$3.P,(20.$19.VR,VHIA,Vh,R1.)(20.$19.VR,VHIA,O?.R2.)(0.(2.$3.(18.$19.VR,VHIA,O?.)(18.$19.VR,VHIA,Vh,))(0.(2.$3.(21.$19.VR,VHIA,O?.)(21.$19.VR,VHIA,Vh,))(0.(2.$3.(22.$19.VR,VHIA,O?.)(22.$19.VR,VHIA,Vh,))(0.(5.(23.$19.VR,VHIA,O?.)(23.$19.VR,VHIA,Vh,))(0.(24.$3.O>.)(0.Px,$3.P,(8.$3.R1.O>.)(1<.R2.)(0.(1=.$19.O10.(12.$13.(14.(15.$3.O>.))VLB,)VBUF,VEND,VCUR,O>.O=.)(0.(25.$19.O10.O=.(26.O<.O;.O:.O9.=))(0.(7.(0.(2.$3.O9.=)(2.$3.O:.=))(0.(5.VBUF,O9.)(0.(5.=O:.)(5.(6.O9.O:.)VEND,))))(0.(7.(2.(?.&40.)O4.(27.&40.=))(2.(?.&40.)O4.(27.&40.+????????????=?80.)))(0.(25.$19.O10.VFB,(17.$28.(29.O8.)(17.$28.(29.O7.)(17.$28.(29.O6.)(2:.$28.)))))(0.(25.$19.O10.(6.VFB,+20.)(17.$28.(29.O5.)(2:.$28.)))(0.(25.$19.O10.(6.(2;.VFB,+3.)(2<.(2=.VR,)))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.=))(17.$28.(2>.(27.&8.+?3.))(17.$28.(2>.(27.&8.+?3.))(17.$28.(2>.(27.&8.+?3.))(2:.$28.))))))))))(0.(25.$19.O10.(6.(2?.&40.Vsp,)-68.)(17.$28.(29.Vs11,)(17.$28.(29.Vs10,)(17.$28.(29.Vs9,)(17.$28.(29.Vs8,)(17.$28.(29.Vs7,)(17.$28.(29.Vs6,)(17.$28.(29.Vs5,)(17.$28.(29.Vs4,)(17.$28.(29.Vs3,)(17.$28.(29.Vs2,)(17.$28.(29.Vs1,)(17.$28.(29.Vs0,)(17.$28.(29.Vra,)(2:.$28.)))))))))))))))(0.(25.$19.O10.Vsp1,(17.$28.(30.#18.O2.)(17.$28.(29.(27.&40.+????????????=:96.))(17.$28.(29.(27.&40.+????????????=;00.))(17.$28.(29.(27.&40.+????????????=:9:.))(17.$28.(29.(27.&40.+26360.))(17.$28.(29.(27.&40.+????????????=?80.))(17.$28.(29.O4.)(17.$28.(29.(27.&40.VFB,))(17.$28.(29.(27.&40.VFB,))(17.$28.(29.O3.)(17.$28.(30.#10.O1.)(17.$28.(29.(27.&40.VFB,))(2:.$28.))))))))))))))(0.(31.$19.O10.(6.Vsp1,+78.)(6.(2?.&40.Vsp,)-68.))(0.(31.$19.O10.Vlo,Vsp1,)(0.(32.$19.O10.)(0.(33.$19.O10.VBUF,Vbs,)(0.(34.$19.(2=.VR,)(20.$19.VR,VHIA,O?.)O10.VPP,+8.)(0.(34.$19.(2=.VR,)(20.$19.VR,VHIA,O?.)O10.VBUF,(=.(>.(?.&8.)Vbs,)))(0.(34.$19.(2=.VR,)(20.$19.VR,VHIA,O?.)O10.VCUR,+20.)(0.(35.$19.VR,VHIA,O?.VLB,VLF,(2?.&40.Vsp,)(2?.&40.Vsp,)(17.(9.$3.$3.)(:.$3.$3.VPP,(6.VPP,+8.))(17.(9.$3.$3.)(:.$3.$3.VCUR,(6.VCUR,+20.))(2:.(9.$3.$3.))))Vm,O10.)(0.(36.$19.(2=.VR,)O10.Vslo,Vsp1,)(36.$19.(2=.VR,)O10.Vsp1,(2?.&40.Vsp,))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Notation pinv := (pinvx []).

  #[using="Type"] Lemma others_apart : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "PLx,(1;.$13.)Phc,(37.$19.VR,VHIA,)Pmq,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Py,$3.P,(1?.$19.VR,VHIA,R4.(12.$13.R5.(12.$13.(14.(15.$3.R2.))VLB,))(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)R3.)P,(24.$3.R3.)P,(38.(2.(1;.$3.)R4.(2:.$3.)))P,(8.$3.R4.(39.$3.R5.))(7.(5.(6.R5.+20.)(3:.$3.R6.=))(5.(6.(3:.$3.R6.=)+20.)R5.))")
(* [comment removed for export] *).
  Proof.
    intros Lx hc mq nodes y HH HND Hne Hy.
    pose proof (in_rl _ _ Hy) as HyN.
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [_ HAP].
    assert (NE : y <> last nodes 0).
    { intros E. rewrite <- (rl_last_app nodes 0) in HND by exact Hne.
      apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
    eapply (blocks_apart_in2 _ y 32 (last nodes 0) 32); [exact HAP| apply in_or_app; left; apply in_or_app; right; apply nLB_in; exact HyN| apply in_or_app; left; apply in_or_app; right; apply nLB_in; apply last_in; exact Hne| exact NE].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L2389586940.10 L36149741099.1000000R019S2sp2PP2lo2FB3cur1A2OA3NLO3NPP3NFBS2sp2PP3CUR2lo5CURLO2D12FB3APC3cur4NCUR". (* [comment removed for export] *)
  #[using="CURLO D1 APC"] Lemma seqrep_mu : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "PLx,(1;.$13.)Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pmm',P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.P,(1=.$19.R4.(12.$13.(14.(15.$3.R2.))VLB,)VBUF,VEND,VCUR,R2.R1.)P,Px,$3.P,(8.$3.R1.R4.)(1<.R2.)P,(1?.$19.VR,VHIA,R7.(12.$13.R8.(12.$13.(14.(15.$3.R4.))VLB,))(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)R6.)P,(24.$3.R5.)P,(3;.(17.(9.$3.$3.)(:.$3.$3.VPP,(6.VPP,+8.))(17.(9.$3.$3.)(:.$3.$3.R5.(6.R5.+20.))(17.(9.$3.$3.)(:.$3.$3.VFB,(6.VFB,+40.))(17.(9.$3.$3.)(:.$3.$3.Vlo,(2?.&40.Vsp,))(2:.(9.$3.$3.))))))R8.R7.)P,(3<.$19.R9.R8.)(1=.$19.R9.(12.$13.(14.(15.$3.R8.))VLB,)VBUF,VEND,VCUR,R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros Lx hc mm mm' nodes cur HS HF HH HND MU WM. eapply seqrep_mem; [exact HS| intros b Hb; exact Hb|].
    intros A cs HA HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz. cbn [disjoint_from].
    assert (CURE : nodes <> [] -> cur = last nodes 0 /\ In cur nodes).
    { intros Hne. destruct nodes as [|a0 r0]; [exfalso; exact (Hne eq_refl)|]. destruct HS as (E & _). split; [exact E| rewrite E; apply last_in; exact Hne]. }
    destruct HA as [[-> Hne]|HA].
    - destruct (CURE Hne) as [_ CINn]. ddestruct (HF cur CINn) as (_ & _ & _ & _ & NCUR & _).
      clear - D1 APC CURLO NCUR. lia.
    - assert (Hne : nodes <> []) by (intros E; rewrite E in HA; exact HA).
      destruct (CURE Hne) as [CE _]. pose proof (others_apart Lx hc mm nodes A HH HND Hne HA) as OA. rewrite <- CE in OA.
      destruct (HF A (in_rl _ _ HA)) as (_ & _ & NLO & NPP & _ & NFB & _). clear - OA NLO NPP NFB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac open_pinv INV hc :=
    destruct INV as (HHc & HCSc & HTc & HSc & HFc & HVc & HND & HNF & HSR & HCURC & HCB & HK64 & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI & HBUF
                     & OPP & OBUF & OCUR & PRES & SS1 & SS2);
    pose proof (curP_of _ _ _ HNF HSR) as (CU0 & CUA8 & CLO & CPPa & CBUFa & CFBa & CWcur & CIN);
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_x509_policies_A.STKpol in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (cs_ok_sb _ _ CSOKc) as SB64;
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo0) as KINV;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOPc; rewrite HTc, HSc in HTOPc;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NB1 NEED0; lia);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo))
      by (eapply crange_mono; [exact HCSc| eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NB1 NEED0 TOP HTOPc; lia]]);
    assert (SCS1c : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS0c : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 64) by (eapply crange_mono; [exact HCSc| exact CFB]);
    pose proof FRSH as (F0 & F1 & F2 & F3);
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia);
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia);
    assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN);
    assert (BUFLO : BUF + n <= lo)
      by (destruct (blocks_below_hm R HIA hc _ _ _ LB HHc ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb) _ BIN) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    assert (WCC : wcover R LB LF (bv_unsigned sp) W CUR 32) by (apply wcover_inside; cbn [inside]; right; left; clear; lia);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ _ =>
      assert (CWPn : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA hc) PP 8)
        by (rewrite HTc; eapply client_wrange_mono; [exact CWP| intros b' Hb'; apply in_app_iff in Hb'; apply in_app_iff; destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; right; apply in_or_app; right; exact Hb'| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb']]) end;
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ _ =>
      assert (INHc : In (FB, 24) (Lh ++ fdata LF')) by (apply in_or_app; right; cbn; left; reflexivity);
      assert (INDc : In (FB + 32, 64 - 40) (Lh ++ fdata LF')) by (apply in_or_app; right; cbn; right; left; reflexivity) end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    unfold seq_cells in HCURC.

  Ltac open_pinv_mu INV hc cur :=
    open_pinv INV hc;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (WMU cur) mx) as MU; pose proof (wmono_refl asegs mx) as WM;
      lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HHx) as AB; pose proof (conj HHx I) as HH0 end end.
  (* [comment removed for export] *)
  Ltac fold_pinv INVn hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb :=
    lazymatch goal with MU : munch _ ?m0 ?mx, WM : wmono _ ?m0 ?mx, SRx : seqrep _ ?m0 _ _ _ _ _ _, NFx : (forall x, In x _ -> nodeF x), HHz : HM _ _ _ hc _ _ ?m0 /\ True, NDx : List.NoDup _ |- _ =>
      let HSR2 := fresh "HSR2" in
      pose proof (seqrep_mu _ hc _ _ _ _ SRx NFx (proj1 HHz) NDx MU WM) as HSR2;
      assert (INVn : pinv mx hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb) by (unfold pinvx; spine; first [eassumption | match goal with |- ?g => idtac "FOLD-LEFT:" g end])
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L10719636406.2L34429891072.4L38310959932.6L39268637205.000000600B00X00YS1d2D0S1P3END1e2HES1P3END5nodes1e3HLN2E4S". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO CUR0 CWC CURLO SLOS SLOL SLO TOP SPH UW SP1 SP1M F64 FRSH CFB"] Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pr,$3.Pp',$3.Pxra,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps3v,(?.&40.)Ps4v,(?.&40.)Ps5v,(?.&40.)Ps6v,(?.&40.)Ps8v,(?.&40.)Ps9v,(?.&40.)Ps10v,(?.&40.)Ps11v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R2:.R2;.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,P,(2.$3.R25.=)(2.(1;.$3.)R2;.(2:.$3.))P,(25.$19.R2<.VPP,(17.$28.(29.(27.&40.R1;.))(2:.$28.)))P,(0.(5.VP,R1<.)(5.R1<.VEND,))P,(0.(1.-3000.R1>.)(5.R1>.=))P,P,(7.(2.$3.R1?.=)(2.$3.R1?.-2080.))(2.$3.R1?.VEND,)P,(5.=R21.)P,(5.(3>.+4.R22.)(3?.VEND,VP,))P,(5.(40.$19.VR,VHIA,R33.)(6.(40.$19.VR,VHIA,Vh,)(3>.R23.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R32.))R24.)(42.$19.(43.$19.VR,VHIA,R35.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R22.(27.&40.Vsp1,)Vgp,Vtp,R21.R20.R1?.Vsp,(27.&40.Vsp1,)(27.&40.R24.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))R12.R11.R10.R?.R>.R=.R<.R;.)VF,(27.&40.+:;158.)Vfc,(4:.(?.&40.))R34.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hp' RR HENDx HE0 HE BUDFa HLN.
    assert (E4 : e <= (END - P) / 4) by (apply Z.div_le_lower_bound; [clear; lia| clear - HE; lia]).
    ddestruct INV as (HHc & HCSc & HTc & HSc & HFc & HVc & HND & HNF & HSR & HCURC & HCB & HK64 & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI & HBUF
                     & OPP & OBUF & OCUR & PRES & SS1 & SS2).
    assert (HCBs : (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END)) by (destruct HCB as [(E1 & E2)|K]; [left; exact (conj E1 (conj E2 (HNE E1)))| right; exact K]).
    destruct (seqrep_close asegs _ _ _ _ _ _ _ _ _ _ _ HSR HCURC HCBs) as (t & pd & l & p & HHEAD & HCB' & HCH).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    eapply A_x509_policies_B.pol_fin with (hq := hc) (nodes := nodes) (p' := p') (hct := t) (hcpad := pd) (hcl := l) (hcp := p);
      first [ exact HHc | exact HCSc | exact HTc | exact HSc | exact HFc | exact HVc | exact PRES | exact HPP | exact Hp' | exact HHEAD | exact HCB' | exact HCH | exact HND | exact RR | exact HENDx | exact CFB
            | eassumption
            | lazymatch goal with
              | |- hfr _ _ _ _ <= _ => unfold A_x509_policies_B.FFRpol; unfold fr_charge in *; rewrite Z.max_r by (clear - D0; lia); clear - BUDFa HE0 E4 D0; nia
              | |- Z.of_nat (length _) <= _ => unfold A_x509_policies_B.CNTpol; clear - HLN E4; lia
              | |- forall x, In x nodes -> _ => intros x Hx; ddestruct (HNF x Hx) as (_ & _ & _ & _ & _ & _ & NLBx & _); exact NLBx
              end
            | match goal with |- ?g => idtac "EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L14406737544.133L19246787633.2  L28629085765.2  L36682633318.4  L40228640085.0  L51907746211.2  00000100200900G00H00OFSS2rg2RRS3END2rg2p'2RRSS2rg2RR". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO CUR0 CWC CURLO SLOS SLOL SLO TOP SPH UW SP1 SP1M F64 FRSH CFB"] Lemma err_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Prg,$3.Pp',$3.Pxra,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps3v,(?.&40.)Ps4v,(?.&40.)Ps5v,(?.&40.)Ps6v,(?.&40.)Ps8v,(?.&40.)Ps9v,(?.&40.)Ps10v,(?.&40.)Ps11v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R2:.R2;.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,P,(2.$3.R25.=)(2.(1;.$3.)R2;.(2:.$3.))P,(25.$19.R2<.VPP,(17.$28.(29.(27.&40.R1;.))(2:.$28.)))P,(0.(5.VP,R1<.)(5.R1<.VEND,))P,(0.(1.-7?.R1>.)(1.R1>.=))P,(5.=R20.)P,(5.(3>.+4.R21.)(3?.VEND,VP,))P,(5.(40.$19.VR,VHIA,R32.)(6.(40.$19.VR,VHIA,Vh,)(3>.R22.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R31.))R23.)(42.$19.(43.$19.VR,VHIA,R34.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R21.(27.&40.Vsp1,)Vgp,Vtp,R20.R1?.R1>.Vsp,(27.&40.Vsp1,)(27.&40.R23.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))R11.R10.R?.R>.R=.R<.R;.R:.)VF,(27.&40.+:;14<.)Vfc,(4:.(?.&40.))R33.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hp' RR HE0 HE BUDFa HLN.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    (* [comment removed for export] *)
    do 3 zstep.
    first [ rewrite A_x509_get_san_A.swrap32_errsum'' by (clear - RR; lia)
          | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - RR; lia))
          | match goal with |- ?g => idtac "ERRSUM-LEFT" end ].
    eapply exit_walk with (e := e) (p' := p'); first [ exact INV | exact HPP | eassumption | clear - RR; lia | match goal with |- ?g => idtac "ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac open_pinv_cur INV hc cur :=
    open_pinv_mu INV hc cur;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with CINx : cur = CUR \/ In cur _, OCx : aobj _ _ _ mx CUR 32, HHx : HM _ _ _ hc _ _ mx |- _ =>
        assert (OCN : aobj asegs AL (hcs asegs R HIA hc) mx cur 32)
          by (destruct CINx as [CE|CINn]; [rewrite CE; exact OCx| exact (hm_aobj_block asegs R HIA hc _ _ mx cur 32 HHx (in_or_app _ _ _ (or_intror (nLB_in _ _ CINn))))]) end;
      lazymatch goal with CINx : cur = CUR \/ In cur _, NFx : (forall x, In x _ -> nodeF x) |- _ =>
        assert (WCcur : wcover R LB LF (bv_unsigned sp) W cur 32)
          by (destruct CINx as [CE|CINn];
              [ rewrite CE; apply wcover_inside; cbn [inside]; right; left; clear; lia
              | destruct (NFx cur CINn) as (_ & _ & _ & _ & _ & _ & _ & NFRx);
                eapply (wcover_fresh R LB LF _ W cur 32 cur 32 NFRx); [clear; lia| clear; lia| let ALOx := fresh "ALOx" in pose proof (art_lo asegs R HIA) as ALOx; pose proof SLO as SLOx; unfold A_x509_policies_A.STKpol in SLOx; clear - ALOx SLOx LOS NS1 NB1 NEED0; lia] ]) end end.

  (* [comment removed for export] *)
  Definition LoopOblig (p : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps9v,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R23.R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,P,(2.$3.R1>.=)(2.(1;.$3.)R24.(2:.$3.))P,(25.$19.R25.VPP,(17.$28.(29.(27.&40.O1.))(2:.$28.)))P,(5.=R17.)P,(5.(3>.+4.R18.)(3?.O1.VP,))P,(5.(40.$19.VR,VHIA,R29.)(6.(40.$19.VR,VHIA,Vh,)(3>.R19.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R28.))R1:.)(42.$19.(43.$19.VR,VHIA,R2;.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R1:.(27.&40.Vsp1,)Vgp,Vtp,R19.R18.R17.Vsp,(27.&40.Vsp1,)R16.R15.R14.R13.R12.R11.R10.R?.R>.(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.R28.)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))R=.R<.(27.&40.VEND,)R;.R:.R9.R8.)VF,(27.&40.+:;208.)Vfc,(4:.(?.&40.))R2:.(4;.$19.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00l0@D11532395422.204D15964341902.204D29401369980.204D31242237967.204D32827785284.204D57329886304.204D60109196847.204K14662993782.204K44164039966.204K48593550302.204K59713869701.204L10946870795.9  L14647789168.2  L1685717371.0   L26071006300.0  L27111942217.1  L31165784101.191L34603895532.0  L35655538583.11 L38235734261.1  L38383890888.1  L44052539574.1  L44166661144.3  L48118080743.12 L48596171480.2  L51578300575.1  L56380991837.10 L56488151316.187L57130527895.2  L59251680703.12 L59723830915.2  L60098763854.6  L61971934371.2  L62586168108.2  L62619108508.0  L66151427842.16 L9080220944.4   L9356559676.16  L9817099845.191 P57140489617.204P62587740714.204Q1101800120.201 Q11530185118.203Q11532395422.204Q12921224503.201Q24579862679.201Q29399418748.203Q29401369980.204Q35038668202.200Q42439443119.204Q43414146086.201Q43622973458.202Q49746415830.204Q62457807837.201Q66314508158.200Q67038978349.204Q68013150533.204Q8699115497.204 Q9077729369.201 Q9092350619.200 00000e00f01[01\01]01^02\03H04604b05N05b05c05d05e05i07a07b08;08?08D08I08J08o09009509N0:l0:m0;?0;@0;J0;Q0;R0;S0;m0<<0<o0>e0?g0A10AM0B10BU0CC0D:0D^0EB0EW0FF0GJ0Gh0He0I:0IO0JY0KI0LN0Lc0M8S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur5CBUFa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur4CPPa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1FSSS2PPS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur1p2Hp3CU03SPR4SP1R2F05BUFLOSS1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curS3curFS1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS3CURS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0FS1P3END2bs1p2Hp2KeFS1R2lo3LOSS3END1pFSS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B22B32B54CUR03SLO3SPH2FB3sp15nodes3cur3CU03SPR4SP1R2F05BUFLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLO2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS1R2LF3slo2bs3LFB4SLOS5nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3cur2HB5Ha_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO BIN B1 B2 B3 B5 ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APC"] Lemma fin_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pp,$3.Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps9v,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R23.R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,P,(2.$3.R1>.=)(2.(1;.$3.)R24.(2:.$3.))P,(25.$19.R25.VPP,(17.$28.(29.(27.&40.R15.))(2:.$28.)))P,(0.(5.VP,R16.)(5.R16.VEND,))P,(5.=R18.)P,(5.(3>.+4.R19.)(3?.VEND,VP,))P,(5.(40.$19.VR,VHIA,R2:.)(6.(40.$19.VR,VHIA,Vh,)(3>.R1:.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R29.))R1;.)(42.$19.(43.$19.VR,VHIA,R2<.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R1:.(27.&40.Vsp1,)Vgp,Vtp,R19.R18.R17.Vsp,(27.&40.Vsp1,)R16.(27.&40.R1;.)R15.R14.R13.R12.R11.R10.R?.(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.R29.)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))R>.R=.(27.&40.VEND,)R<.R;.R:.R9.)VF,(27.&40.+:;414.)Vfc,(4:.(?.&40.))R2;.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hp HE0 HE BUDFa HLN.
    open_pinv_cur INV hc cur.
    (* [comment removed for export] *)
    do 7 zstep.
    idtac "FIN-STORED".
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Ke; zify_cond Ke.
    - idtac "FIN-OK".
      assert (PE : p = END) by (clear - Ke Hp B1 B2 B3 B5 B47; try kland Ke; rewrite ?Z.mod_small in Ke by lia; lia).
      destruct HK64 as [-> | ->].
      + eapply exit_walk with (e := e) (r := 0) (p' := p); first [ exact INV2 | eassumption | clear; lia | (intros _; exact PE) | match goal with |- ?g => idtac "FIN-LEFT:" g end ].
      + replace (Z_to_bv 64 18446744073709543296) with (Z_to_bv 64 (-8320)) by (apply bv_eq; vm_compute; reflexivity).
        eapply exit_walk with (e := e) (r := -8320) (p' := p); first [ exact INV2 | eassumption | clear; lia | (intros _; exact PE) | match goal with |- ?g => idtac "FIN2-LEFT:" g end ].
    - idtac "FIN-MISMATCH".
      (* [comment removed for export] *)
      do 3 zstep.
      eapply exit_walk with (e := e) (r := -9574) (p' := p); first [ exact INV2 | eassumption | clear; lia | match goal with |- ?g => idtac "FIN3-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L10946870795.9  L24341865253.10 L27111942217.1  L34427793940.10 L35655538583.11 L36792362049.193L38235734261.1  L41202929119.193L47571963878.10 L49334199172.10 L51578300575.1  L56380991837.10 L56775170761.193L60098763854.6  L66151427842.16 L9080220944.4   L9356559676.16  Q10649498890.206Q10651748618.205Q13733106231.205Q17701933584.206Q33842005717.206Q34390149656.206Q39600066516.206Q42641839989.206Q45353769141.205Q61847600945.20600000D00K00O00b01;03503903_03`04804=04V06Z06d07>07M08@08T08h09<09P0:>0:?0:@0;70;K0<ES1R2lo3LOS2FB3ALO2F1S3END1qS2PPS1P3END1e1q3HQE3HEQS1R3HIA1h2sp2lo3TOP5HTOPcS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur2pe3HPE3CU03SPR4SP1R2F05BUFLOS2loS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curSS1P3END1q2p03HP03HQ03HQES3CURS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur1q2p03HP03HQ03HQE3CU03SPR4SP1R2F05BUFLOS1R2lo3LOSS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcFFS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2PP2bs3LFB5nodesS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB ALP PP0 CWP PPLO BIN B1 B3 B5 ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APC"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pq,$3.Ppe,$3.Pp0,$3.Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R25.R26.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)P,P,(2.$3.R20.=)(2.(1;.$3.)R26.(2:.$3.))P,(25.$19.R27.VPP,(17.$28.(29.(27.&40.R17.))(2:.$28.)))P,(5.VP,R16.)P,(1.R17.R19.)P,(5.R1:.VEND,)P,(0.(5.VP,R1:.)(5.R1:.VEND,))P,(5.=R1=.)P,(5.(3>.+4.R1>.)(3?.R1=.VP,))P,(5.(40.$19.VR,VHIA,R2?.)(6.(40.$19.VR,VHIA,Vh,)(3>.R1?.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R2>.))R20.)P,Pp',$3.P,(1.R1?.R1.)P,(5.R2.VEND,)(4<.R3.)(42.$19.(43.$19.VR,VHIA,R32.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R1>.(27.&40.Vsp1,)Vgp,Vtp,R1=.R1<.R1;.Vsp,(27.&40.Vsp1,)R1:.R19.R18.R17.R16.R15.R14.R13.R12.(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.R2?.)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))(27.&40.R20.)R11.(27.&40.VEND,)R10.R?.R>.R=.)VF,(27.&40.+:;38<.)Vfc,(4:.(?.&40.))R31.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQE HPE HE0 HEQ BUDFa HLN KLOOP.
    pose proof INV as INV0.
    open_pinv_mu INV hc cur.
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    - idtac "TAIL-LOOP".
      eapply (KLOOP q HQ0 HQE) with (e := e); first [ exact INV0 | exact HPP | eassumption | match goal with |- ?g => idtac "TAIL-LOOP-LEFT:" g end ].
    - idtac "TAIL-MISMATCH".
      (* [comment removed for export] *)
      do 3 zstep.
      replace (Z_to_bv 64 18446744073709542042) with (Z_to_bv 64 (-9574)) by (apply bv_eq; vm_compute; reflexivity).
      eapply exit_walk with (e := e) (r := -9574) (p' := q); first [ exact INV0 | exact HPP | eassumption | clear - HP0 HQ0 HQE HE0 HEQ; lia | match goal with |- ?g => idtac "TAIL-EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03S0@C40858145355.234C60410007123.233D10636937134.234D16071854214.234D16901939902.234D2457516971.234 D28498761192.209D28498761192.236D32458870384.234D4451634193.209 D4451634193.236 D46794843979.234D60109196847.209D60109196847.236D60109446735.234D65008160014.234K20981739667.232K2431698795.209 K2431698795.236 K29378133114.234K30993319891.234K3337916572.209 K3337916572.236 K44164039966.209K44164039966.236K49541715106.232K65858155712.233K67298046963.232K9840090748.209 K9840090748.236 L10946870795.9  L11176926315.42 L12865196093.19 L14402536676.221L14402536676.3  L1685717371.0   L18489062900.25 L19664123645.18 L19666039969.0  L19698232010.42 L19914454641.3  L20977711877.2  L21654730866.2  L23182876091.2  L2419170461.2   L2621559066.1   L26505715237.20 L27111942217.1  L27830600341.209L27938279177.42 L29391009772.3  L29902247181.14 L30507144274.2  L3055355236.3   L30997223346.3  L3323761050.2   L34429531785.19 L3484917920.42  L35236225328.25 L35655538583.11 L35903316071.25 L36792364629.196L38235734261.1  L40228640085.0  L41110154015.25 L41202929119.193L41202929119.220L41251426164.1  L42488948659.2  L43305107741.25 L44168742175.3  L45703618005.20 L47870616696.2  L49233373885.2  L49478371288.2  L49526752708.2  L5021251703.1   L50678314462.3  L51578300575.1  L53271535775.193L53271535775.220L53779026635.14 L54261998223.2  L55195235631.25 L56380991837.10 L57387363123.42 L57427258186.20 L576250137.193  L576250137.220  L58033769229.14 L58046298131.20 L58541431983.14 L58972524609.3  L59308586248.2  L6008604205.3   L60098763854.6  L62275882349.3  L62417043471.19 L63039845559.196L64179129035.1  L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67304579733.2  L881835912.0    L9080220944.4   L9356559676.16  L9717202392.42  L9748633241.2   L9835808138.2   N26872553873.233N48204456022.233N49450819242.233N60733400192.233O10871149737.231O1254725598.231 O14912726833.233O18988691132.233O20866770946.234O22525005962.233O30010457231.233O33449646875.232O3493317847.232 O37559489567.234O3821773283.234 O424351700.232  O44938202843.232O49701823576.233O50011839873.232O54119978487.232O55209884805.232O57031441090.232O64474006218.233P19899262166.231P21647862485.232P23170010975.209P23170010975.236P30511339222.233P3069564867.231 P42484919333.233P47876372191.232P49230739482.233P50671478649.232P54268551240.209P54268551240.236P62260666314.232P66292560634.233P66818508295.234P67064334489.233P9764112383.232 Q10592389669.232Q10592533181.234Q10596742693.209Q10598691865.205Q10636937134.234Q10637080374.232Q10649498890.206Q10649498890.233Q10651748618.205Q11133374175.234Q11657053839.234Q13731015691.232Q13733106231.205Q14695702359.209Q14695702359.236Q16071854214.234Q17027695041.234Q17681074618.234Q17701933584.206Q17701933584.233Q19559239151.209Q21767670690.234Q23219026840.234Q27573751300.234Q2803826605.234 Q28496781288.208Q28496781288.235Q28498761192.209Q28498761192.236Q29775981542.234Q32681607669.234Q34377611452.234Q34390149656.206Q34390149656.233Q37216054521.206Q37216054521.233Q39600066516.206Q39600066516.233Q40251356518.209Q42439168719.234Q42439443119.209Q42439443119.236Q43479930840.234Q4451634193.209 Q4451634193.236 Q4453582353.208 Q4453582353.235 Q45317270253.234Q45353769141.205Q45360064137.232Q46794843979.234Q48118064779.234Q49746198710.234Q49746415830.209Q49746415830.236Q50283589684.232Q50294066696.205Q52711570354.234Q56530976407.234Q57828105177.234Q61556549392.207Q61556549392.234Q61847600945.206Q61847600945.233Q67038703949.234Q67038978349.209Q67038978349.236Q68013150533.209Q68013150533.236Q8699115497.209 Q8699115497.236 Q8699324297.234 Q9356559674.211 Q9632015376.209 Q9644583048.234 00000400800^02<03R03S04O05K06106m07i08O09T0:Y0;H0;n0<I0=:0=k0?30?O0@B0A50Ag0BY0Cb0D=0EF0F70Fh0G<0HY0IC0ID0IO0IP0JF0JW0JX0K_0K`0Ka0Kb0Kc0Kd0Ki0LA0LE0Lk0N40N50NH0NI0NJ0NK0NL0Nn0P20Q20QK0QZ0Sm0T10T20TA0Tg0UM0UQ0UR0U`0Ua0VC0VD0VE0VM0VN0VO0VP0VU0W;0Wa0X80X90Xg0Y@0YQ0Z40ZZ0[@0[g0\_0]10]=0]C0]N0]X0]Y0]d0`70`80`90`S0`T0`U0`V0`W0`X0`g0aZ0bk0bl0bm0cG0ci0dC0e<0e=0e>0e?0e@0eA0eB0eC0eD0eE0eF0eG0eH0eI0eJ0eK0eL0eM0eN0eO0fJ0fK0gT0h]0iP0jK0k>0l?0m@0m`0o110B10b11>12;13614114E14Y14m15A15U15i16=16Q16e17917:17N17b17c17d18[18o19j1:>1:R1;B1<=1<Q1<R1<g1=Q1>;1>e1?O1?k1?l1?m1?n1?o1@J1@e1@f1@g1A;1AW1BL1CA1D>1Dh1ER1F<1Ff1Fg1G;1GO1Gc1HV1I@1JC1KF1KZ1Kn1Ko1L01L^1M;1MX1NR1OL1PC1QS1Rc1SZ1TQ1U\1Vg1WY1X31XJ1XaS2PPS2FBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F0FS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4lenw1q2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2q43Lw42HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4lenw1q2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2q43Lw42HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur4lenw1q2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2q43Lw42HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2bs3LFB2FB3APP5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB3APP5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP3BUF2lo2bs3LFB2FB3sp15nodes4lenw1q2pe3x263APB2x33x273x323x334POSTS2LF2PP3BUF2bs3LFB3DPB5nodesS2LF2PP2bs3LFB5nodes3cur4lenw1q4CPPa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur2q43Lw44CPPa2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur4lenw1q2pe3x264CFBa2x33x273x323x334POSTS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur4lenw1q2pe3x264CPPa2x33x273x323x334POSTS2LF2PP2bs3LFB2FB3APP5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB3APP5nodes2q43Lw42HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1S1R3NS13NB15NEED02sp2PP1P3BUF2lo2bs3PP02B13SLO3LOS2FB3sp13SP14lenw1q2p03HP03HQ02LR3ALO3ACP2F0S1P3END4lenw1q2pe2p03HP03HQ03HPE2LR2q43Hq4FS2rg3RRg2KzSS1R3NS13NB15NEED02sp2PP2lo2bs4PPLO3SLO2FB3sp13SP14FBLOS2bs4lenw1q2pe2KqSS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8FFFFFS3sp1S3END2pe2q43Lw43HPE4Hq4LS2PPS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0FS1P4lenw1e1q3HEQ2LRFFFFS1P3END4lenw1e1q2pe3HQL3HPE3HEQ2LRS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS13NB15NEED02sp2PP3BUF2lo2bs4PPLO3SLO2FB3sp13SP14FBLO5BUFLOS1R3HIA1h2sp2lo3TOP5HTOPcS3BUF2bs2FB3APBS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOS2loSS2PP3BUF2bs3DPBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2FBFS2PP2bs2FB3APPFS4lenw1q2p02q43Lw43HQ02LR3LR44Hq4aFFS2sp3sp1FFFS3CURS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS3END4lenw1q2pe3HQL3HPEFS1R3NS13NB15NEED02sp2lo2bs3SLO2FB3sp13SP14FBLOS1R3BUF2lo2bs3LOS3ALO3BCES2PP2bs2FB3sp12F0S1P4lenw1e1q2q43Lw43HEQ2LR3LR44Hq4aS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1P3END4lenw1q2pe2p03HP03HQ03HQL3HPE2LRS1P3END4lenw1q2pe2p02q43Lw43HP03HQ03HPE2LR3LR44Hq4a4Hq4LS4lenw1q2p03HQ02LRS3BUF2bs3B47S1i2HiS2rg3RRg2KzS1R2lo3LOSFS2rg3RRg2RNS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOFFS2FB2r03F641q1r1H2H02q02H4FFFFSS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02sp2PP3END3BUF2lo2bs3PP02B33SLO3LOS2FB3sp13SP12pe3HPE3ALO3ACP2F0FFS2LF2bs3LFB2FB5nodes3x341CS2LF2sp2bs3LFB3sp13SP15nodes3x341CS2LF2bs3LFB2FB5nodes3x341CS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3x341CFFFFFFFFFFFFFFFFFFFS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB3sp13SP15nodes4FBLOFS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodes4lenw1q2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodes2q43Lw42HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB5nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S2LF2PP2lo2bs3LFB4PPLO3sp15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes4lenw1q2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes2q43Lw42HB5Ha_st5Hl_stS2LF2lo2bs3LFB2FB3sp15nodes4FBLOS2LF2sp2bs3LFB3sp13SP15nodesS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes5BUFLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLOS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2bs3LFB2FB5nodesFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesFFS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur3SPR2F02F8S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3ALOS2LF2bs3LFB2FB5nodesFS2LF2bs3LFB3sp15nodesS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2sp2bs3LFB3sp13SP15nodesFFFFS2LF2PP2bs3LFB3PP05nodes2HBS2LF2PP2bs3LFB3PP05nodes2HBFFS2LF2bs3LFB2FB5nodesS1R2LF3slo2bs3LFB4SLOS5nodesS1R2LF2PP3slo2bs3LFB4SLOS5nodes4lenw1q2HB5Ha_st5Hl_stS1R2LF2PP3slo2bs3LFB4SLOS5nodes2q43Lw42HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodesS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS5nodes3ALOS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPcS1R3HIA1h2LF2sp2PP2bs3LFB3TOP3sp15nodes4lenw1q5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP2bs3LFB3TOP3sp15nodes2q43Lw45HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2PP2bs3LFB5nodes2HB5Ha_stS2LF2PP2bs3LFB5nodes2HB5Ha_stS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB3SLO3LOS3sp13SP15nodes4lenw1q2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB3SLO3LOS3sp13SP15nodes2q43Lw42HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur4lenw1q2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2q43Lw42HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs3LFB3TOP3sp13SP15nodes4lenw1q5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs3LFB3TOP3sp13SP15nodes2q43Lw45HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB3sp15nodes4SP1RS2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APP APC"] Lemma qual_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pq,$3.Ppe,$3.Pp0,$3.Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R25.R26.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)P,P,(2.$3.R20.=)(2.(1;.$3.)R26.(2:.$3.))P,(25.$19.R27.VPP,(17.$28.(29.(27.&40.R17.))(2:.$28.)))P,(5.VP,R16.)P,(1.R17.R19.)P,(5.(6.R1:.(2?.&40.R20.))R19.)P,(5.R1:.VEND,)P,(5.=R1=.)P,(5.(3>.+4.R1>.)(3?.R1=.VP,))P,(5.(40.$19.VR,VHIA,R2?.)(6.(40.$19.VR,VHIA,Vh,)(3>.R1?.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R2>.))R20.)P,Pp',$3.P,(1.R1?.R1.)P,(5.R2.VEND,)(4<.R3.)(42.$19.(43.$19.VR,VHIA,R32.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R1>.(27.&40.Vsp1,)Vgp,Vtp,R1=.R1<.R1;.Vsp,(27.&40.Vsp1,)R1:.R19.R18.R17.R16.R15.R14.R13.R12.(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.R2?.)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))(27.&40.R20.)R11.(27.&40.VEND,)R10.R?.R>.R=.)VF,(27.&40.+:;340.)Vfc,(4:.(?.&40.))R31.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQL HPE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 lenw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    open_pinv_mu INV hc cur.
    (* [comment removed for export] *)
    do 6 zstep.
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kq; zify_cond Kq.
    { idtac "QUAL-NONE".
      eapply tail_walk with (e := e) (q := q + bv_unsigned lenw) (pe := pe) (p0 := p0);
        first [ exact INV2 | exact KLOOP | eassumption | clear - HP0 HQ0 HQL HPE HE0 HEQ LR; lia | match goal with |- ?g => idtac "QUAL-TAIL-LEFT:" g end ]. }
    assert (QL : q + bv_unsigned lenw < pe) by (clear - Kq HP0 HQ0 HQL HPE LR B1 B3 B5 B47; try kland Kq; rewrite ?Z.mod_small in Kq by lia; lia).
    clear Kq.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "QUAL-GT".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := q + bv_unsigned lenw) (END := pe) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3 HP0 HQ0 HQL HPE LR QL; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "QGT-LEFT:" g end ]).
    clear SPT OLEN.
    idtac "QUAL-GT-BACK".
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw4 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q4 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q4 <= pe |- _ => rename H into Hq4 end.
    pose proof (bv_unsigned_in_range 64 Lw4) as LR4. unfold bv_modulus in LR4. cbn [Z.pow Z.of_N Pos.pow] in LR4.
    fold_pinv INV3 hc nodes cur nt npad cl cp w0 w1 w2 Lw4 k64 k88 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "QUAL-GT-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (e := e) (rg := rg) (p' := q4);
        first [ exact INV3 | eassumption | clear - HP0 HQ0 HQL HPE HE0 HEQ LR Hq4 RRg RN; lia | match goal with |- ?g => idtac "QUAL-ERR-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq4a Hq4L]. clear HLg Kz RRg.
    (* [comment removed for export] *)
    do 6 zstep.
    fold_pinv INV4 hc nodes cur nt npad cl cp w0 w1 w2 Lw4 k64 k88 ja jb.
    idtac "QUAL-SKIPPED".
    eapply tail_walk with (e := e) (q := q4 + bv_unsigned Lw4) (pe := pe) (p0 := p0);
      first [ exact INV4 | exact KLOOP | eassumption | clear - HP0 HQ0 HQL HPE HE0 HEQ LR Hq4 Hq4a Hq4L LR4; lia | match goal with |- ?g => idtac "QUAL-TAIL2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01T0@D10916531869.214D11532395422.215D15964341902.215D17452743891.214D19889830902.214D23155707565.214D29401369980.214D29401369980.215D31242237967.215D32827785284.215D48729998015.214D57329886304.215D60109196847.214D60109196847.215K14662993782.214K14662993782.215K44164039966.214K44164039966.215K48593550302.214K48593550302.215K59713869701.214K59713869701.215L10946870795.9  L14647789168.2  L1685717371.0   L22925878376.198L22927780832.195L27111942217.1  L35655538583.11 L38235734261.1  L38383890888.1  L44052539574.1  L44166661144.3  L44903346094.7  L45581944931.198L46512611463.198L48118080743.12 L48596171480.2  L4951167123.198 L51578300575.1  L56380991837.10 L57130527895.2  L59308660947.5  L59456438371.198L59723830915.2  L60098763854.6  L62586168108.2  L66151427842.16 L9080220944.4   L9356559676.16  P57140489617.214P57140489617.215P62587740714.214P62587740714.215Q10914612381.213Q10916531869.214Q1101800120.212 Q11530185118.214Q11532395422.215Q12773147547.211Q13351507773.210Q25803421623.211Q26295627581.211Q27554188553.211Q29399418748.213Q29399418748.214Q29401369980.214Q29401369980.215Q30263103398.212Q3056822380.211 Q30615626263.211Q3067468761.212 Q38370982088.208Q38385314999.211Q38386200654.210Q41564835977.211Q42377995046.212Q42439443119.214Q42439443119.215Q43622973458.212Q43622973458.213Q46411729629.212Q49746415830.214Q49746415830.215Q52480275446.208Q53541741149.211Q59023939651.211Q60795410781.212Q65750499052.211Q65765526873.212Q67038978349.214Q67038978349.215Q68013150533.214Q68013150533.215Q7174379670.211 Q8172711389.211 Q8699115497.214 Q8699115497.215 Q8958231000.208 Q9916536454.211 00000e01c01d01e01f01g02\03Z03[03\03]03^04\05c06O07D08208i09U0:J0;60;k0<?0<@0<A0=_0?=0?A0?Z0?^0?c0?h0?i0@F0Ad0BJ0Bo0C00CV0C[0D40D50DI0Eg0Eh0F20F30FM0F\0GO0HQ0I\0Jf0L90L]0MA0M]0NJ0O70OL0Oa0PO0P`0Q50QY0RF0Rj0SW0T[0U00Ug0V<0VQ0Vf0W;0WP0XT0YC0Z;0ZY0[70[L0\I0]O0]d0^90^U0^j0_?0_T0`^0b10ba0cZ0d30dH0eM0f[0fl0gAS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4oidp2HB5Ha_st5Hl_st3k88FFFFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4oidp2HB5Ha_st5Hl_st3k88FFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4oidp4CFBa2HB5Ha_st5Hl_st3k88S2LF3BUF2bs3LFB5nodes3cur5CBUFa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur4oidp5CBUFa2HB5Ha_st5Hl_st3k88S2LF2PP2bs3LFB5nodes3cur4CPPa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur4oidp4CPPa2HB5Ha_st5Hl_st3k88S2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4oidp4CFBa2HB5Ha_st5Hl_st3k88S1R2lo3LOS2FB3ALO2F1FSS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S2PPS1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curS3curFS3END3BUF3k884oidp3HOB3HOE2KRS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS3CURS1R3BUF2lo2bs3LOS3ALO3BCEFS3BUF2B54oidp3HOB2E0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0FS1R2lo3LOSFS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur4oidp3CLO2HB5Ha_st5Hl_st3k88S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur4oidp3CLO2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB5nodesS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S1R2LF3slo2bs3LFB4SLOS5nodes3cur2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur2HB5Ha_stS2LF2bs3LFB5nodes3cur2HB5Ha_stS2LF2bs3LFB5nodes3curS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur4oidp5HTOPc2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur3CU0S2LF2bs3LFB5nodes3curS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur4oidp5HTOPc2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodesS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APP APC"] Lemma fill_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pq,$3.Ppe,$3.Pp0,$3.Poidp,$3.Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R25.R26.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)P,(25.$19.R26.VPP,(17.$28.(29.(27.&40.R16.))(2:.$28.)))P,(5.VP,R15.)P,(1.R16.R18.)P,(5.(6.R19.(2?.&40.R1?.))R18.)P,(5.R19.VEND,)P,(5.VBUF,R18.)P,(5.(6.R19.(2?.&40.R20.))VEND,)P,(5.=R1>.)P,(5.(3>.+4.R1?.)(3?.R1>.VP,))P,(5.(40.$19.VR,VHIA,R30.)(6.(40.$19.VR,VHIA,Vh,)(3>.R20.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R2?.))R21.)P,Pp',$3.P,(1.R20.R1.)P,(5.R2.VEND,)(4<.R3.)(42.$19.(43.$19.VR,VHIA,R33.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R1>.(27.&40.Vsp1,)Vgp,Vtp,R1=.R1<.R1;.Vsp,(27.&40.Vsp1,)R1:.R19.R18.R17.R16.R15.R14.R13.(27.&40.R1?.)(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.R30.)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))(27.&40.R21.)R12.(27.&40.VEND,)R11.R10.R?.R>.)VF,(27.&40.+:;2?4.)Vfc,(4:.(?.&40.))R32.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQL HPE HOB HOE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 k88) as KR. unfold bv_modulus in KR. cbn [Z.pow Z.of_N Pos.pow] in KR.
    open_pinv_cur INV hc cur.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk OCN cur 4.
    idtac "FILL-CHK".
    (* [comment removed for export] *)
    do 15 zstep.
    idtac "FILL-STORED".
    rewrite <- (Z_to_bv_bv_unsigned k88) in HCURC at 1.
    clear HCB.
    assert (HCB : (oidp = 0 /\ bv_unsigned k88 = 0) \/ (BUF <= oidp /\ 0 <= bv_unsigned k88 /\ oidp + bv_unsigned k88 <= END)) by (right; clear - HOB HOE KR; lia).
    fold_pinv INV2 hc nodes cur (Z_to_bv 64 6) npad (bv_unsigned k88) oidp w0 w1 w2 lenw k64 k88 ja jb.
    eapply qual_walk with (e := e) (q := q) (pe := pe) (p0 := p0);
      first [ exact INV2 | exact KLOOP | eassumption | (intros E0; exfalso; clear - E0 HOB B5; lia) | match goal with |- ?g => idtac "FILL-QUAL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10837002389.2 L10946870795.9 L12654381620.1 L1540877545.3  L1912329416.1  L19966991388.8 L21367331087.1 L23615739305.3 L24128180555.1 L31023889862.6 L32454903270.1 L37714553091.1 L38383890888.1 L44052539574.1 L45363093875.3 L50796875722.11L52045659405.3 L52442115986.7 L52992257876.1 L55628717916.1 L6203936179.1  L66151427842.16L67038720880.13L6899380056.1  L9631767084.2  00000800L00Q00]00b01@01D01N01R01h01l01o02402902B02b02n03E03I03L03Q03k04]04a04hS3BUF2bsS1R2lo3LOS2FB3ALO2F1S3BUFS2sp3sp13SP1S3sp1S1R3HIA1h2sp3TOP3sp13SP15HTOPcS2FBS1R3HIA2hcS2FBS1R3HIA1h2sp3TOP5HTOPcS2FBS1AS3curS3curS2FB1c2HcS1R3NS13NB15NEED02sp2lo3LOS4SLO'S2sp3sp13SP1S1R3HIA1h2hc2h23HVc3HV2S2FBS1AS3sp1S2FB2r03F641q1r1H2H02q02H4S1R3NS13NB15NEED02sp2lo3slo4SLOS4SLOL3sp13SP14SLO'S2FBS2FB2F0". (* [comment removed for export] *)
  #[using="NS1 NB1 NEED0 CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP LOS SP1 F64 FRSH CFB APC"] Lemma pinv_call : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "PLx',(1;.$13.)Phc,(37.$19.VR,VHIA,)Ph2,(37.$19.VR,VHIA,)Pmc,P,(?.&40.)(1:.(?.&8.))Pm2,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))P,(3=.(2:.$13.)R10.R12.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(4=.$19.VR,(12.$13.(14.(15.$3.R?.))VLB,)(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)Vsp1,(4>.VR,)(21.$19.VR,VHIA,R13.)(2:.$4?.)R11.R10.)P,(32.$19.R11.)P,(31.$19.R12.Vlo,Vsp1,)P,(2.$3.(18.$19.VR,VHIA,R15.)(18.$19.VR,VHIA,R16.))P,(2.$3.(21.$19.VR,VHIA,R16.)(21.$19.VR,VHIA,R17.))P,(2.$3.(22.$19.VR,VHIA,R17.)(22.$19.VR,VHIA,R18.))P,Px,$3.P,(20.$19.VR,VHIA,R1:.R1.)(20.$19.VR,VHIA,R1:.R2.)P,(5.(23.$19.VR,VHIA,R19.)(23.$19.VR,VHIA,R1:.))P,(1?.$19.VR,VHIA,R1:.(12.$13.R1<.(12.$13.(14.(15.$3.R17.))VLB,))(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)R18.)(3=.R1=.R19.R1;.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)")
(* [comment removed for export] *).
  Proof.
    intros until jb. intros INV HP2 MI2 ST2 HT2 HS2 HF2 HCS2 HV2 HH2.
    ddestruct INV as (HHc & HCSc & HTc & HSc & HFc & HVc & HND & HNF & HSR & HCURC & HCB & HK64 & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI & HBUF
                     & OPP & OBUF & OCUR & PRES & SS1 & SS2).
    pose proof (curP_of _ _ _ HNF HSR) as (CU0 & CUA8 & CLO & CPPa & CBUFa & CFBa & CWcur & CIN).
    pose proof (hcs_ok asegs R HIA hc) as CSOKc.
    pose proof (art_lo asegs R HIA) as ALO. pose proof SLO as SLO'. unfold A_x509_policies_A.STKpol in SLO'.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOPc. rewrite HTc, HSc in HTOPc.
    dpose FRSH as (F0 & F1 & F2 & F3).
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (TOPCS : forall x, hcs asegs R HIA hc x -> x < hstkhi asegs R HIA hc) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (nLB nodes ++ fdata LF')).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (nLB nodes ++ fdata LF') sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    assert (INHc : In (FB, 24) (nLB nodes ++ fdata LF')) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDc : In (FB + 32, 64 - 40) (nLB nodes ++ fdata LF')) by (apply in_or_app; right; cbn; right; left; reflexivity).
    assert (CSHD : forall c, FB <= c < FB + 64 -> cshd R (nLB nodes) LF' (arl_stklo R) (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    assert (CRcur : client_range L (nLB nodes ++ fdata LF') sp1 cur 32).
    { destruct CIN as [->|CINn]; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]|].
      eapply client_range_block; [apply in_or_app; left; apply nLB_in; exact CINn| clear; lia| clear; lia]. }
    unfold pinvx. spine.
    - exact HH2.
    - intros x Hx. apply HCS2. apply HCSc. exact Hx.
    - rewrite HT2. exact HTc.
    - rewrite HS2. exact HSc.
    - rewrite HF2. exact HFc.
    - clear - HV2 HVc. lia.
    - exact HND.
    - exact HNF.
    - eapply seqrep_mem; [exact HSR| intros b Hb; exact Hb|].
      intros A cs HA HR Hsz. eapply (presA_rw_cells asegs R); [exact HP2| exact HR| | exact I]. rewrite Hsz.
      destruct HA as [[-> _]|HA]; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]|].
      eapply client_range_block; [apply in_or_app; left; apply nLB_in; exact (in_rl _ _ HA)| clear; lia| clear; lia].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact HCURC| exact CRcur| exact I].
    - exact HCB.
    - exact HK64.
    - eapply (presA_rw_cells asegs R); [exact HP2| exact FHD| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INHc| clear; lia| clear; lia]| exact I].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact HLEN| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INDc| clear; lia| clear; lia]| exact I].
    - eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) (nLB nodes) LF' sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2 FB _ CSOKc);
        [ cbn [cells_size csize Nat.add]; eapply crange_sub; [eapply crange_mono; [exact HCSc| exact CFB]| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP2
        | exact FSH | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact SAVE| apply client_range_stack; clear - SP1; lia| exact I].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact RSL| apply client_range_stack; clear; lia| exact I].
    - eapply (presA_stk asegs R); [exact HP2| exact SThi| clear; lia| exact I].
    - exact ST2.
    - exact MI2.
    - eapply (presA_bytes_at asegs R); [exact HP2| exact HBUF| eapply client_range_block; [apply in_app_iff; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]| exact I].
    - eapply aobj_cs_mono; [exact HCS2|]. eapply (presA_aobj asegs R); [exact CSOKc| exact HP2| exact OPP| apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear - LOS SLO' SP1 NS1 NB1 NEED0; lia| exact TOPCS].
    - exact (hm_aobj_block asegs R HIA h2 _ _ m2 BUF n HH2 (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror BIN))))).
    - eapply aobj_cs_mono; [exact HCS2|]. eapply (presA_aobj asegs R); [exact CSOKc| exact HP2| exact OCUR| apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| clear - LOS SLO' SP1 NS1 NB1 NEED0; lia| exact TOPCS].
    - eapply (presW_hmono R HIA hc h2); [| exact HCS2| exact HS2].
      eapply (presW_call asegs R HIA hc LB LF _ _ W m mc m2 (nLB nodes) LF'); [exact PRES| exact HP2| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear - SP1; lia| clear - LOS SLO' NS1 NB1 NEED0; lia| clear; lia| intros x Hx; exact I].
    - eapply (presA_sshad asegs R); [exact HP2| exact SS1| exact SLOS| rewrite HSc; clear - HTOPc TOP SP1; lia].
    - eapply (presA_sshad asegs R); [exact HP2| exact SS2| clear - LOS SLO' SP1 NS1 NB1 NEED0; lia| rewrite HSc; clear - HTOPc TOP; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00f0@D11532395422.203D15964341902.203D29401369980.203D31242237967.203D32827785284.203D57329886304.203D60109196847.203K14662993782.203K44164039966.203K48593550302.203K59713869701.203L10946870795.9  L13059311132.0  L14647789168.2  L1685717371.0   L24338315589.2  L27111942217.1  L35655538583.11 L38235734261.1  L38383890888.1  L44052539574.1  L44166661144.3  L48118080743.12 L48596171480.2  L51578300575.1  L56380991837.10 L57130527895.2  L59723830915.2  L60098763854.6  L62586168108.2  L66151427842.16 L9080220944.4   L9356559676.16  P57140489617.203P62587740714.203Q10035437079.200Q1101800120.200 Q11530185118.202Q11532395422.203Q29399418748.202Q29401369980.203Q35038668202.199Q42439443119.203Q43414146086.200Q43622973458.201Q47383858103.200Q49746415830.203Q62457807837.200Q66314508158.199Q67038978349.203Q68013150533.203Q8699115497.203 Q9077729369.200 Q9092350619.199 00000e00f01[01\01]01^02\03H04604b05N05b05c05d05e05l06006I06M06R06W06X07=07>07C07\07]07^07h07i08C08R09E0:G0;Q0<H0<d0=H0=l0>P0?40?I0@80A<0AZ0BH0CE0CZ0Co0E90Ei0Fn0GC0GXS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur5CBUFa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur4CPPa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1SFSS3END1qS2PPS1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curS3curFS1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS3CURS1R3BUF2lo2bs3LOS3ALO3BCEFFS1R2lo3LOSFS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS1R2LF3slo2bs3LFB4SLOS5nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3cur2HB5Ha_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APC"] Lemma null_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pq,$3.Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps9v,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R22.R23.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)P,P,(2.$3.R1=.=)(2.(1;.$3.)R23.(2:.$3.))P,(25.$19.R24.VPP,(17.$28.(29.(27.&40.R14.))(2:.$28.)))P,(0.(5.VP,R15.)(5.R15.VEND,))P,(5.=R17.)P,(5.(3>.+4.R18.)(3?.VEND,VP,))P,(5.(40.$19.VR,VHIA,R29.)(6.(40.$19.VR,VHIA,Vh,)(3>.R19.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R28.))R1:.)(42.$19.(43.$19.VR,VHIA,R2;.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.(27.&40.+:;2=<.)(27.&40.Vsp1,)Vgp,Vtp,R19.R18.R17.Vsp,(27.&40.Vsp1,)(27.&40.=)R16.R15.R14.R13.R12.R11.R10.R?.(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.(6.(2;.(6.R28.+18.)+3.)(2<.(2=.VR,))))(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))R>.R=.(27.&40.(6.R28.+18.))R<.R;.R:.R9.)VF,(27.&40.+:;2=<.)Vfc,(4:.(?.&40.))R2:.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hq HE0 HE BUDFa HLN.
    open_pinv_cur INV hc cur.
    (* [comment removed for export] *)
    do 8 zstep.
    idtac "NULL-EXIT".
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb.
    replace (Z_to_bv 64 18446744073709542038) with (Z_to_bv 64 (-9578)) by (apply bv_eq; vm_compute; reflexivity).
    eapply exit_walk with (e := e) (r := -9578) (p' := q); first [ exact INV2 | eassumption | clear; lia | match goal with |- ?g => idtac "NULL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0150@D11532395422.228D15964341902.228D29401369980.228D31242237967.228D32827785284.228D57329886304.228D60109196847.228K14662993782.228K44164039966.228K48593550302.228K59713869701.228K64521742742.228L10946870795.9  L13747222400.3  L14647789168.2  L15756354262.7  L1685717371.0   L19609460064.3  L20838820200.3  L2676165540.3   L27111942217.1  L29765677068.208L34384972077.8  L35655538583.11 L38235734261.1  L38383890888.1  L38692635477.0  L39332637397.0  L40362990079.3  L41991340432.8  L44052539574.1  L44166661144.3  L47348856443.5  L48118080743.12 L48596171480.2  L51578300575.1  L5294437637.3   L56380991837.10 L57130527895.2  L5721395798.8   L59308636045.12 L59314923118.2  L59723830915.2  L60098763854.6  L62586168108.2  L64461871424.3  L64515273836.2  L66151427842.16 L9080220944.4   L9356559676.16  P57140489617.228P62587740714.228Q1101800120.225 Q11530185118.227Q11532395422.228Q29399418748.227Q29401369980.228Q35042489430.224Q42439443119.228Q43414146086.225Q43622973458.226Q49746415830.228Q62457807837.225Q66309932674.224Q67038978349.228Q68013150533.228Q8699115497.228 Q9077729369.225 Q9079886695.224 00000g00h01_01`01a01b02b03P04@04n05\06H06\06e06f07407507>07F07S07W08f08m09F09J09O09P09Q09]09o0:40:50:D0:i0:j0:o0;70;P0;Q0;[0;e0;j0;k0<50<60<>0<?0<Y0<h0=[0>_0?k0@G0@m0AS0B90B_0C40Ce0Do0EM0FL0Fa0G60HL0I>0JE0JZ0JoS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur1N2HB5Ha_st5Hl_stFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur1N2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur1N4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur1N5CBUFa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur1N4CPPa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur1N4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur1N5NCURW2HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1S3CUR1N1KFS1R2lo3LOS3ALOSS3cur1N1KS2PP1N1KS5nodes1e3HLNS2PPS1R2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur1N3CU03ACV3SPR4SP1R2F03NF03NF1S1e3HE0S1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curSSS3CUR1N4NCURS1P1e1q2p03HQ03HEQS3curFS1R2lo1N3NF12CES1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS3CURS2FB1N1KS1R3BUF2lo2bs3LOS3ALO3BCEFS1q2p03HQ0S1N3NF02KnS1N1KFS1R2lo3LOSFS2FB1N1KFS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur1N3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur1N3CLO2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS1R2LF3slo2bs3LFB4SLOS5nodes3cur1N2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur1N3CU04CUA83SPR4SP1R2F03NF0S2LF2bs3LFB5nodes3cur2HB5Ha_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur1N5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3sp13SP15nodes3cur1N2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur1N2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur1N5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APP APC"] Lemma link_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))PN,$3.Pe,$3.Pq,$3.Ppe,$3.Pp0,$3.Poidp,$3.Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(17.(9.$3.$3.)(:.$3.$3.R14.+20.)(2:.(9.$3.$3.)))R23.R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,(38.(2.$3.R1>.=))P,(25.$19.R25.VPP,(17.$28.(29.(27.&40.R14.))(2:.$28.)))P,(2.$3.(4.R17.+10.)=)P,(<.VR,(12.$13.(14.(15.$3.R26.))VLB,)(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)R18.+20.)P,(25.$19.R28.R19.(17.$28.(30.#20.(50.(?.&8.)(27.&8.=)#20.))(2:.$28.)))P,(5.VP,R16.)P,(5.(6.R17.+4.)R19.)P,(5.(6.R1:.(2?.&40.R21.))R19.)P,(5.R1:.VEND,)P,(5.VBUF,R19.)P,(5.(6.R1:.(2?.&40.R22.))VEND,)P,(5.=R1?.)P,(5.(3>.+4.R20.)(3?.R1=.VP,))P,(5.(40.$19.VR,VHIA,R32.)(6.(40.$19.VR,VHIA,Vh,)(3>.(6.R21.+1.)(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R31.))R22.)P,Pp',$3.P,(1.R21.R1.)P,(5.R2.VEND,)(4<.R3.)(42.$19.(43.$19.VR,VHIA,R35.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.(27.&40.+:;2=<.)(27.&40.Vsp1,)Vgp,Vtp,R1?.R1>.R1=.Vsp,(27.&40.Vsp1,)(27.&40.R25.)R1<.R1;.R1:.R19.R18.R17.R16.(27.&40.R20.)(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.(6.(2;.(6.R32.+18.)+3.)(2<.(2=.VR,))))(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))(27.&40.R22.)(27.&40.VEND,)(27.&40.(6.R32.+18.))R15.R14.R13.R12.)VF,(27.&40.+:;2=<.)Vfc,(4:.(?.&40.))R34.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV CPN HPP N16 NFR NZ HP0 HQ0 HQL HPE HOB HOE HE0 HEQ BUDFa HLN KLOOP.
    open_pinv_cur INV hc cur.
    dpose NFR as (NF0 & NF1 & NF2 & NF3).
    assert (HCB2 : BUF <= cp /\ 0 <= cl /\ cp + cl <= END) by (clear - HCB CPN; destruct HCB as [(E & _)|K]; [exfalso; exact (CPN E)| exact K]).
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (nLB nodes ++ fdata LF')).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
    assert (NFR0 : fresh_apart R LB LF N 32).
    { split; [exact NF0|]. split; [exact NF1|]. split; [exact NF2|]. intros B j Hb. apply NF3. apply SUBq. exact Hb. }
    assert (CE : alloc_ceiling <= lo) by (clear - ALO LOS; lia).
    assert (NPP : PP + 8 <= N \/ N + 32 <= PP).
    { destruct (fresh_apart_client R LB LF lo PP 8 N 32 NFR0 (client_range_of_w L _ _ _ _ _ CWP) ltac:(clear; lia) ltac:(clear; lia) CE) as [K|K]; clear - K; lia. }
    assert (NCUR : CUR + 32 <= N \/ N + 32 <= CUR).
    { destruct (fresh_apart_client R LB LF lo CUR 32 N 32 NFR0 (client_range_of_w L _ _ _ _ _ CWC) ltac:(clear; lia) ltac:(clear; lia) CE) as [K|K]; clear - K; lia. }
    assert (NFB : FB + 64 <= N \/ N + 32 <= FB).
    { destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [_ HAP].
      assert (NE : N <> FB) by (destruct (NF3 FB 24 ltac:(apply in_or_app; right; cbn; left; reflexivity)) as [K|K]; clear - K; lia).
      destruct (blocks_apart_in2 _ N 32 FB 64 HAP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity) NE) as [K|K]; clear - K; lia. }
    assert (NCURW : N + 32 <= cur \/ cur + 32 <= N).
    { destruct CIN as [->|CINn]; [clear - NCUR; lia|]. destruct (NF3 cur 32 ltac:(apply in_or_app; left; apply nLB_in; exact CINn)) as [K|K]; clear - K; lia. }
    assert (NNI : ~ In N nodes).
    { intros HI. destruct (NF3 N 32 ltac:(apply in_or_app; left; apply nLB_in; exact HI)) as [K|K]; clear - K; lia. }
    assert (NLO : N + 32 <= lo) by (clear - NF1 CE; lia).
    assert (NFN : nodeF N).
    { unfold nodeF. spine; try assumption. intros B k Hb. unfold SEQ_SIZE. apply NF3. apply in_or_app. left. apply in_or_app. right. exact Hb. }
    (* [comment removed for export] *)
    do 5 zstep.
    idtac "LINK-STORED".
    (* [comment removed for export] *)
    zstep. if_cases Kn; zify_cond Kn.
    { exfalso. clear - Kn NF0 NLO SLO SPH NS1 NB1 NEED0. try kland Kn. rewrite ?Z.mod_small in Kn by lia. lia. }
    clear Kn.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch _ ?m0 m3, WM : wmono _ ?m0 m3, HHz : HM _ _ _ hc _ _ ?m0 /\ True |- _ =>
      pose proof (seqrep_mu _ hc _ _ _ _ HSR HNF (proj1 HHz) HND MU WM) as SR3 end.
    lazymatch goal with H : rw_cells _ m3 N ?cs |- _ =>
      pose proof (rw_cells_reshape asegs m3 N cs
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H
                    ltac:(cbn; repeat split; reflexivity) ltac:(first [exact eq_refl | vm_compute; reflexivity])) as HNZ end.
    assert (INV3 : pinv m3 hc (nodes ++ [N]) N (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 w0 w1 w2 lenw k64 k88 ja jb).
    { unfold pinvx. rewrite nLB_snoc. spine; first [ eassumption | exact HNZ
        | lazymatch goal with
          | |- _ \/ _ => left; split; reflexivity
          | |- List.NoDup _ => apply NoDup_app; [exact HND| repeat constructor; intros []| intros x Hx [<-|[]]; exact (NNI Hx)]
          | |- forall x, In x (nodes ++ [N]) -> nodeF x => intros x Hx; apply in_app_iff in Hx; destruct Hx as [Hx|[<-|[]]]; [exact (HNF x Hx)| exact NFN]
          | |- seqrep _ _ _ _ _ _ _ _ =>
              eapply seqrep_snoc with (cur := cur) (ct := nt) (cpad := npad) (cl := cl) (cp := cp);
                [ eapply seqrep_mem; [exact SR3| intros b Hb; right; exact Hb| intros A cs _ HR _; exact HR]
                | exact HCURC | exact (proj1 HCB2) | exact (proj1 (proj2 HCB2)) | exact (proj2 (proj2 HCB2)) | left; reflexivity | exact N16 | exact NF0 ]
          end
        | match goal with |- ?g => idtac "LINK-INV-LEFT:" g end ]. }
    idtac "LINK-INV".
    eapply fill_walk with (e := e + 1) (q := q) (pe := pe) (p0 := p0) (oidp := oidp);
      first [ exact INV3 | exact KLOOP | exact HPP | eassumption | rewrite length_app; cbn [length]; clear - HLN; lia | clear - HP0 HQ0 HE0 HEQ; lia | match goal with |- ?g => idtac "LINK-FILL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00e0@L10719636406.2  L10946870795.9  L1609905979.6   L16500284193.0  L19980016842.7  L26892418956.1  L27111942217.1  L34387002284.15 L34810683834.0  L35655538583.11 L36048514837.5  L38087549238.15 L38235734261.1  L38383890888.1  L38692635477.0  L39220637093.0  L39268637205.0  L44052539574.1  L45569510388.198L46646466118.12 L46646617831.4  L48118080743.12 L49336363269.15 L49603979340.15 L49799904432.3  L51578300575.1  L56380991837.10 L56485944020.200L56658999053.1  L5721395798.8   L58790154276.9  L60042172946.15 L60098763854.6  L62037211595.12 L62908263739.8  L64700576064.12 L66151427842.16 L66617044166.9  L696052593.2    L9080220944.4   L9356559676.16  Q30263103398.212Q3067468761.212 Q3069291515.211 Q35036100202.213Q41569211166.211Q43414146086.214Q53545853386.211Q60795410781.212Q62457807837.214Q66311996606.213Q9077729369.214 Q9090470235.213 00000600J00_00`01801<01@01M01N01g02802g02k03003103203303804V05?05K06006]07N07Z07_08809V09Z09d0:A0:N0:X0;E0;W0<70<a0=?0=G0=V0>I0?M0?b0@70@L0@a0Ae0B:0BO0Bd0C90CN0CcS1d2D0S1R2lo3LOS2FB3ALO2F1S1R3HIA1h4BUDV2hc3HVcSS1R3HIA1h2sp3TOP3sp13SP1S2spS2PPS5nodes1e3HE0SS1R3HIA1h2sp2lo3TOP5HTOPcS1R3HIA2hc2h23HV2S1R3HIA3NS13NB15NEED02sp2PP2lo4PPLO3SLO2hc1a2HaS2loS3curSSSS3curS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S1P3END4lenw1e1q2pe2p03HQ03HQL3HPE3HEQ2LRS1P3END1e2E1S1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxS1P3END5nodes4lenw1q2pe2p03HP03HQ03HQL3HPE2LRS1R3HIA3NS13NB15NEED02sp3CUR2lo5CURLO3SLO2hc1a2HaS2sp3sp13SP1S3CURS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S2spS1q2p03HQ0S1R3NS13NB12sp2lo3SLO3sp13SP1S5nodes1e3HLNS1R2lo3LOSS1R3NS13NB15NEED02sp2lo3slo4SLOS4SLOL3SLO3SPRS1P1e1q2p03HQ03HEQS3END3BUF2bs2B33B472B52cl2cp3HCBS2FB2r03F641q1r1H2H02q02H42sp3SPA3sp14SP1MS1R3HIA1h1d2hc1e5BUDFa2h24HFR2S2sp3SPRS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma append_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pq,$3.Ppe,$3.Pp0,$3.Poidp,$3.Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R25.R26.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)P,P,(2.$3.R20.=)(2.(1;.$3.)R26.(2:.$3.))P,(25.$19.R27.VPP,(17.$28.(29.(27.&40.R17.))(2:.$28.)))P,(5.VP,R16.)P,(5.(6.R17.+4.)R19.)P,(5.(6.R1:.(2?.&40.R20.))R19.)P,(5.R1:.VEND,)P,(5.VBUF,R19.)P,(5.(6.R1:.(2?.&40.R21.))VEND,)P,(5.=R1?.)P,(5.(3>.+4.R20.)(3?.R1=.VP,))P,(5.(40.$19.VR,VHIA,R31.)(6.(40.$19.VR,VHIA,Vh,)(3>.R21.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R30.))R22.)P,Pp',$3.P,(1.R21.R1.)P,(5.R2.VEND,)(4<.R3.)(42.$19.(43.$19.VR,VHIA,R34.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R1?.(27.&40.Vsp1,)Vgp,Vtp,R1>.R1=.R1<.Vsp,(27.&40.Vsp1,)R1;.R1:.R19.R18.R17.R16.R15.R14.(27.&40.R20.)(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.R31.)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))(27.&40.R22.)R13.(27.&40.VEND,)R12.R11.R10.R?.)VF,(27.&40.+:;294.)Vfc,(4:.(?.&40.))R33.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQL HPE HOB HOE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 lenw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof INV as INV0.
    open_pinv_cur INV hc cur.
    assert (CPR : 0 <= cp < 2^64) by (clear - HCB B1 B2 B3 B47 B5; lia).
    (* [comment removed for export] *)
    do 6 zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kp; zify_cond Kp.
    { idtac "APP-INPLACE".
      eapply fill_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := oidp);
        first [ exact INV0 | exact KLOOP | eassumption | clear - HP0 HQ0 HE0 HEQ; lia | match goal with |- ?g => idtac "APP-FILL0-LEFT:" g end ]. }
    assert (CPN : cp <> 0) by (clear - Kp CPR; intros E; apply Kp; rewrite E; reflexivity).
    assert (HCB2 : BUF <= cp /\ 0 <= cl /\ cp + cl <= END) by (clear - HCB CPN; destruct HCB as [(E & _)|K]; [exfalso; exact (CPN E)| exact K]).
    clear Kp.
    (* [comment removed for export] *)
    do 10 zstep.
    idtac "APP-CALLOC".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    fold_pinv INVc hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES)| rewrite HSc; exact UW| clear; lia| | clear - SPR; lia| rewrite HSc; apply hstkhi_le64; clear - LOS SLO SPR NS1 NB1 NEED0; lia].
        intros a Ha. cbn [outside]. split; [| split; [| exact I]]; clear - Ha PPLO CURLO SLO NS1 NB1 NEED0; lia. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    assert (E1 : 4 * (e + 1) <= END - P) by (clear - HEQ HQ0 HQL HPE LR; lia).
    assert (E4 : e + 1 <= (END - P) / 4) by (apply Z.div_le_lower_bound; [clear; lia| clear - E1; lia]).
    (* [comment removed for export] *)
    zstep.
    replace (Z_to_bv 64 429840 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc_t asegs R HIA) with (h := hc) (LB := nLB nodes) (LF := LF') (cnt := 1) (sz := 32) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact LOS | exact TPV | exact UW1 | exact STlo | exact MI | reflexivity
              | lazymatch goal with
                | |- lo <= sp1 - arl_need_malloc R => clear - SLO SP1 NS1 NB1 NEED0; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 <= 1 => clear; lia
                | |- 0 <= 32 => clear; lia
                | |- 1 * 32 < AMAX => unfold AMAX; clear; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => rewrite (vchg_small (1 * 32)) by (unfold AMAX_SEC; clear; lia); clear - BUDV HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold A_x509_policies_B.FFRpol in BUDF; unfold fr_charge in *; rewrite Z.max_r in BUDF by (clear - D0; lia); clear - BUDF BUDFa HE0 E4 D0; nia
                end
              | c24_lit   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2' & mo2 & E2 & PO). injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & r & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0x0ab2dc)) with (Z_to_bv 64 0x0ab2dc : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (vchg_small (1 * 32)) in HV2 by (unfold AMAX_SEC; clear; lia). rewrite ?Z.mul_1_l in CASES.
    idtac "CALLOC-POST".
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    assert (BUD2 : hfr asegs R HIA h2 <= hfr asegs R HIA h + (e + 1) * fr_charge (d + 1)) by (clear - HFR2 BUDFa; lia).
    assert (HV2' : havol asegs R HIA h2 <= havol asegs R HIA hc) by (clear - HV2; lia).
    destruct CASES as [[Er HH2] | (N & Er & NAL & NFR & NSTK & HH2 & NZ)]; subst r.
    - idtac "APP-NULL".
      pose proof (pinv_call [] hc h2 mc m2 nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb INVc HP2 MI2 ST2 HT2 HS2 HF2 HCS2 HV2' HH2) as INV2.
      assert (HPP2 : rw_cells asegs m2 PP [C8 (Z_to_bv 64 q)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HPP| | exact I]. cbn [cells_size csize Nat.add].
        eapply client_range_lower; [| exact PPLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
      eapply null_walk with (e := e + 1) (q := q);
        first [ exact INV2 | exact HPP2 | exact HNE | exact BUD2 | exact E1 | clear - HP0 HQ0 HQL HPE LR HE0 HLN; lia | match goal with |- ?g => idtac "APP-NULL-LEFT:" g end ].
    - idtac "APP-NODE".
      pose proof (pinv_call [(N, 32)] hc h2 mc m2 nodes cur nt npad cl cp w0 w1 w2 lenw k64 k88 ja jb INVc HP2 MI2 ST2 HT2 HS2 HF2 HCS2 HV2' HH2) as INV2.
      assert (HPP2 : rw_cells asegs m2 PP [C8 (Z_to_bv 64 q)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HPP| | exact I]. cbn [cells_size csize Nat.add].
        eapply client_range_lower; [| exact PPLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
      change (Z.to_nat 32) with 32%nat in NZ.
      eapply link_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := oidp) (N := N);
        first [ exact INV2 | exact HPP2 | exact CPN | exact NAL | exact NFR | exact NZ | exact KLOOP | exact BUD2 | eassumption | match goal with |- ?g => idtac "APP-LINK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L16526487874.96L19616048289.99L2192452093.95 L22676661558.96L24188363034.96L32883993289.99L38339916114.9900001T03804U06207S09:09oS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz3HB12H22H32HLS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H12HL1i2Hi1HS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H12H3S2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H22HLS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz3HB02H12HLS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H12H32HL1i2Hi1HS2LF2sp2PP3CUR2bs3LFB2FB3sp12mX1B3bsx2P02Lz2HL1i2Hi1H". (* [comment removed for export] *)
  #[using="LF sp PP CUR P END BUF bs LFB PP0 B1 B2 B3 DPB CUR0 DCB D1 FB sp1 APP APC"] Lemma bytes_at_slice : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "PmX,P,(?.&40.)(1:.(?.&8.))PB,$3.Pbsx,(1;.(?.&8.))PP0,$3.PLz,$3.P,(33.$19.R5.R4.R3.)P,(5.R5.R3.)P,(5.=R3.)P,(5.(6.R5.R4.)(6.R7.(=.(>.(?.&8.)R6.))))(0.(33.$19.R9.R6.(51.(?.&8.)(52.R5.)(53.(?.&8.)(52.(3?.R6.R8.))R7.)))(2.$3.(=.(>.(?.&8.)(51.(?.&8.)(52.R5.)(53.(?.&8.)(52.(3?.R6.R8.))R7.))))R5.))")
(* [comment removed for export] *).
  Proof.
    (intros mX B bsx P0 Lz dd_H; ddestruct dd_H as (HB0 & HB1 & HB); intros H1 H2 H3).
    assert (HL : length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx)) = Z.to_nat Lz).
    { rewrite firstn_length, skipn_length. lia. }
    split; [| rewrite HL; lia]. split; [lia|]. split; [rewrite HL; lia|].
    intros i Hi. rewrite HL in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat Lz)); [| lia].
    rewrite nth_error_skipn. rewrite <- (HB (Z.to_nat (P0 - B) + i)%nat) by lia. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02i0@C17025492443.242D27847976046.242D3953997537.216 D3953997537.220 D3953997537.245 D60109446735.242D60189065437.216D60189065437.220D60189065437.245L10122348893.19 L10946870795.9  L12126572370.2  L12252132089.3  L12478726249.10 L13176305223.2  L16507621472.3  L1685717371.0   L17696347041.15 L17698509571.7  L19980016842.7  L20478160884.19 L21218866939.2  L21472756189.3  L22204407068.1  L26532001206.3  L27111942217.1  L28632618922.2  L30994845580.4  L33594514891.2  L35655538583.11 L36463206329.4  L38235734261.1  L38259954321.2  L38736745103.19 L39268637205.0  L41202929119.200L41409160545.3  L44166924249.3  L46710299783.5  L46982844833.0  L51578300575.1  L52002333302.19 L52941874306.3  L53047225244.220L53779026635.15 L55085943702.3  L55230983175.220L56380991837.10 L576250137.200  L57698627611.2  L58790369554.10 L59133665049.2  L60098763854.6  L62107348008.19 L66151427842.16 L881835912.0    L9080220944.4   L9356559676.16  N26738689353.243N42129917801.243O1478916974.242 O17025492443.242O24745514321.242O35027264241.242O36520195031.242O43849271089.242O50689527441.242O56414299794.242O59625529265.242P12115299733.216P12115299733.220P12115299733.245P12257878110.242P16492167430.242P21212095580.242P22205718491.245P28627113325.216P28627113325.220P28627113325.245P31000317067.245P33597136077.216P33597136077.220P33597136077.245P36465839390.242P38261788758.216P38261788758.220P38261788758.245P41419110342.242P44164039966.216P44164039966.220P44164039966.245P46717128672.242P52940256805.242P55088519473.242P57713046236.216P57713046236.220P57713046236.245P59127942590.242Q10598707900.212Q10649498890.213Q10651733935.212Q12931746950.216Q12931752285.241Q13733123218.212Q15766564435.242Q17426747697.242Q17701933584.213Q19243646445.216Q19243646445.220Q19243646445.245Q24594481446.216Q24594492669.241Q24854118877.241Q24854129670.216Q25815989927.212Q25952160488.215Q25952160488.219Q25952160488.244Q26481634750.219Q28465177121.213Q28465177121.217Q28465177121.242Q30603029255.212Q31124869336.242Q32681824661.216Q32681824661.220Q32681824661.245Q34363165844.242Q34390149656.213Q34964382778.242Q37149073081.216Q37149073081.220Q37149073081.245Q39180574961.216Q39180574961.220Q39180574961.245Q39600066516.213Q42439168719.242Q42439443119.216Q42439443119.220Q42439443119.245Q45257319447.216Q45257319447.220Q45257319447.245Q45353786896.212Q45741809296.216Q45741809296.220Q45741809296.245Q48360113622.242Q49746198710.242Q49746415830.216Q49746415830.220Q49746415830.245Q50294081709.212Q52124784706.242Q5265442331.214 Q5265442331.218 Q5265442331.243 Q54690711677.241Q54690719142.216Q55415036769.216Q55415036769.220Q55415036769.245Q56854244147.216Q56854244147.220Q56854244147.245Q60191312605.215Q60191312605.219Q60191312605.244Q60703457310.219Q61847600945.213Q62380812747.242Q67038703949.242Q67038978349.216Q67038978349.220Q67038978349.245Q68013150533.216Q68013150533.220Q68013150533.245Q8699115497.216 Q8699115497.220 Q8699115497.245 Q8699324297.242 Q9356887103.222 Q9644583048.242 00000101P03:04_06J07?0910:^0<Q0<U0<i0<j0<k0=O0=W0=X0=Y0>30>J0>b0>c0>d0>o0?00?90?=0?>0??0?@0?Y0?Z0?^0?_0@L0@M0A30A40A50A60A70A<0A[0A\0BH0Bb0Bc0CO0Ch0DN0DO0Dn0Do0E90FA0F[0F\0Fk0G^0HI0Hm0Hn0Ho0I00I10I20I30I40I50I60JE0KO0L_0ME0Mk0Ml0O@0PU0Qe0S;0Tg0V60W@0XP0Y40ZI0[Y0\o0]U0^f0`20a@0bB0bh0cM0d=0dh0eY0fE0fY0fm0gA0go0hc0i70i[0j?0jS0jT0jU0jV0kM0lJ0m>0ml0nZ0o\10Y11\12P12m13J13m14d14e14f14g14h14i14j15c17218<19L1:[1;e1=51=61=X1>L1?;1@01AA1BM1C_1D31D41D51D61D[1EK1FI1GB1HA1HU1HV1I41IR1J61K31Kj1LZ1ME1N61N71N81N91OD1PJ1QV1RS1SM1So1Tl1V71W=1XI1Z31[X1]C1^I1_J1`Q1aI1ai1bFFS1R3HIA1h2LF2sp2PP3CUR3BUF2lo2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur1q3HTc3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur4lenw3HTc3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CUR3BUF2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur1q3HTc3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR3BUF2lo2bs3LFB3LOS2FB3sp15nodes3cur1qS1R3NS15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur4lenw3NBC3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3NBC3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3CUR3BUF2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur1q3NBC3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS2bsS1R2lo3LOS2FB3ALO2F1FFS3END3BUF2bs2B34lenw1q2pe3HQL3HPE2L4S2lo3sp1FSS1P3BUF2bs2B11q2p03HP03HQ0S1P3BUF2B11q2p03HP03HQ0S1R3HIA1h2sp3TOP3sp13SP1FFS2sp2lo3sp1FS4lenw2K4S2PPFFFS1R3HIA1h2sp2lo3TOP5HTOPcFS2loFS3END3BUF2lo2bs2B34lenw1q2pe3HQL3HPE5BUFLO2L4SS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curFFFSS3CURS1R2lo3slo2bs4SLOS4SLOL3ALO3ACVFS2LF2sp2PP3CUR3BUF2bs3LFB2FB3sp15nodes3cur1qS3END2bs4lenw1q2pe3HQL3HPEFS2LF2sp2PP3CUR3BUF2bs3LFB2FB3sp15nodes3cur1qS1R3BUF2lo2bs3LOS3ALO3BCES2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curFS1R3NS15NEED02sp2lo3SLO3sp13SP1FS1R2lo3LOSS1R3NS13NB15NEED02sp3END3BUF2lo2bs2B33SLO3SPH4lenw1q2pe3HQL3HPE5BUFLO2L4S2FB2r03F641q1r1H2H02q02H4SS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2LF2sp3BUF2lo2bs3LFB3sp13SP15nodes1q3x271CS2LF3BUF2lo2bs3LFB3sp15nodes1q3x271CFFFFFFFFFS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes4lenw3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3BUF2lo2bs3LFB4PPLO3SLO3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS2LF2PP3BUF2lo2bs3LFB4PPLO3sp15nodes1qS2LF3BUF2lo2bs3LFB3sp15nodes3cur1q3CLOFS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC3ALO3ACV2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes4lenw3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes1q3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3END3BUF2lo2bs3LFB2B33SLO3sp13SP15nodes4lenw1q2pe3HQL3HPE3NBC5BUFLO2L43HXL2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur4lenw3NBC3CLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3NBC3CLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes3cur1q3NBC3CLO2HB5Ha_st5Hl_stS2LF3BUF2lo2bs3LFB3sp15nodes1q5BUFLOS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes4lenw3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes1q3NBC3ALO2F12HB5Ha_st5Hl_stS2LF3BUF2lo2bs3LFB2FB3sp15nodes1q4FBLOS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes4lenw3NBC5BUFLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes3NBC5BUFLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes1q3NBC5BUFLO2HB5Ha_st5Hl_stS2LF3END3BUF2lo2bs3LFB2B33sp15nodes4lenw1q2pe3HQL3HPE5BUFLO2L43HXLS2LF3BUF2lo2bs3LFB2FB3sp15nodes1q4FBLOS2LF2sp3BUF2lo2bs3LFB3sp13SP15nodes1qS2LF2sp2bs3LFB3sp13SP15nodes4lenw2HB5Ha_st5Hl_stS2LF2sp2bs3LFB3sp13SP15nodes2HB5Ha_st5Hl_stS2LF2sp3BUF2bs3LFB3sp13SP15nodes1q2HB5Ha_st5Hl_stS1R2LF3BUF2lo2bs3LFB3LOS3sp15nodes1q3ALO3ACVS2LF2bs3LFB2FB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp13SP15nodes1q5HTOPcS2LF2PP2bs3LFB5nodesS1R2LF3BUF2lo2bs3LFB3LOS5nodes1q3ALOS2LF3CUR3BUF2lo2bs3LFB5CURLO5nodes1qS2LF2PP2bs3LFB5nodesFFFS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBCS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBCS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp13SP15nodes1q5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes4lenw5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp13SP15nodes1q5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp13SP15nodes1q5HTOPcS2LF2bs3LFB3sp15nodes4SP1R2HBS2LF2bs3LFB3sp15nodes4SP1R2HBS2LF3BUF2bs3LFB3sp15nodes1q4SP1R2HBS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBCFFFFFFS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes1q3NBCS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes4lenw3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3BUF2lo2bs3LFB4PPLO3SLO3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes4lenw3NBC3ALO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBC3ALO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC3ALO2HB5Ha_st5Hl_stFS1R2LF3BUF3slo2bs3LFB4SLOS5nodes1qS1R2LF3slo2bs3LFB4SLOS3sp15nodes4lenw2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS3sp15nodes2HB5Ha_st5Hl_stS1R2LF3BUF3slo2bs3LFB4SLOS3sp15nodes1q2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodes4lenw3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3CUR3BUF2lo2bs3LFB5CURLO3SLO3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodesFFFS2LF2sp3BUF2lo2bs3LFB3sp13SP15nodes1qS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp15nodes1q5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes4lenw5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp15nodes1q5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodesFS2LF2bs3LFB3sp15nodes2HB5Ha_stS2LF2bs3LFB3sp15nodes2HB5Ha_stS2LF3BUF2bs3LFB3sp15nodes1q2HB5Ha_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBCS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBCS2LF2sp2bs3LFB3sp13SP15nodes4lenw2HB5Ha_st5Hl_stS2LF2sp2bs3LFB3sp13SP15nodes2HB5Ha_st5Hl_stS2LF2sp3BUF2bs3LFB3sp13SP15nodes1q2HB5Ha_st5Hl_stFFFS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes4lenw3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBCS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S2LF2PP3BUF2lo2bs3LFB4PPLO5nodes1qS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBCS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes4lenw3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3LOS2FB3sp13SP15nodes3cur4lenw3NBC3CLO3ALO2F14FBLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3LOS2FB3sp13SP15nodes3cur3NBC3CLO3ALO2F14FBLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3BUF2lo2bs3LFB4PPLO3SLO3LOS2FB3sp13SP15nodes3cur1q3NBC3CLO3ALO2F14FBLO2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes4lenw5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF3slo2bs3LFB3TOP3sp13SP15nodes1q5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF3slo2bs3LFB3TOP3sp13SP15nodes1q5HTOPcS2LF3BUF2bs3LFB3sp15nodes1q4SP1RS2LF3BUF2bs3LFB2FB5nodes1q2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma oid_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.Pnt,(?.&40.)Pnpad,(?.&40.)Pcl,$3.Pcp,$3.Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenw,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pe,$3.Pq,$3.Ppe,$3.Pp0,$3.Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Ps2v,(?.&40.)Ps10v,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(3=.(2:.$13.)R25.R26.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)P,P,(2.$3.R20.=)(2.(1;.$3.)R26.(2:.$3.))P,(25.$19.R27.VPP,(17.$28.(29.(27.&40.R17.))(2:.$28.)))P,(5.VP,R16.)P,(5.(6.R17.+4.)R19.)P,(5.(6.R1:.(2?.&40.R20.))R19.)P,(5.R1:.VEND,)P,(5.=R1=.)P,(5.(3>.+4.R1>.)(3?.R1;.VP,))P,(5.(40.$19.VR,VHIA,R2?.)(6.(40.$19.VR,VHIA,Vh,)(3>.R1?.(41.(6.Vd,+1.)))))P,(5.(=.(>.$3.R2>.))R20.)P,Pp',$3.P,(1.R1?.R1.)P,(5.R2.VEND,)(4<.R3.)(42.$19.(43.$19.VR,VHIA,R32.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.R1>.(27.&40.Vsp1,)Vgp,Vtp,R1=.R1<.R1;.Vsp,(27.&40.Vsp1,)R1:.R19.R18.R17.R16.R15.R14.R13.R12.(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.R2?.)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))(27.&40.(6.(2;.VPP,+3.)(2<.(2=.VR,))))(27.&40.R20.)R11.(27.&40.VEND,)R10.R?.R>.R=.)VF,(27.&40.+:;25<.)Vfc,(4:.(?.&40.))R31.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQL HPE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 lenw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    ddestruct OIDH as (IMGo & GSBo & MCI & RTC & NBC & ISH).
    open_pinv_mu INV hc cur.
    pose proof (hcs_img_cs R HIA hc IMGo GSBo) as ICS.
    (* [comment removed for export] *)
    do 6 zstep.
    fold_pinv INV1 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 lenw ja jb.
    (* [comment removed for export] *)
    zstep. if_cases K4; zify_cond K4.
    2:{ idtac "OID-LEN4".
        assert (L4 : bv_unsigned lenw = 4) by (clear - K4 LR; try kland K4; rewrite ?Z.mod_small in K4 by lia; lia).
        destruct (bytes_at_slice _ BUF bs q 4 HBUF ltac:(clear - HP0 HQ0 B1; lia) ltac:(clear; lia) ltac:(clear - HQL HPE L4 B3; lia)) as [HXS HXL].
        (* [comment removed for export] *)
        do 3 zstep.
        pose proof (artA_bcmp asegs R HIA) as SPB. rewrite MCI in SPB. unfold A_WRAP_BCMP in SPB.
        (* [comment removed for export] *)
        zstep.
        ro_str 156512 4%nat as RO. img_aobj 156512 4 as ORO.
        lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc ?lbx _ mx |- _ =>
          acallxA_sp sp1
            (eapply SPB with (h := hc) (LB := lbx) (LF := LF') (P := 156512) (Q := q) (n := 4) (lo := lo) (qs := firstn (Z.to_nat 4) (skipn (Z.to_nat (q - BUF)) bs));
             rewrite ?(unsigned_lit sp1) by exact SP1R;
             first [ exact RO | exact HXS | exact ORO | exact HXL | exact HHx | eassumption | reflexivity
                   | (eapply aobj_sub; [exact OBUF | clear - HP0 HQ0 B1; lia | clear - HQL HPE L4 B3; lia])
                   | lazymatch goal with
                     | |- _ \/ _ => first [ left; clear - ACV ALO LOS HQL HPE L4 B3 BUFLO; lia | right; clear - HQL HPE L4 B3 BUFLO SLO SPH NS1 NB1 NEED0; lia ]
                     | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                     | |- _ => clear - SLO SP1 NS1 NB1 NEED0 NBC; lia
                     end
                   | match goal with |- ?g => idtac "BCMP-SIDE:" g end ]) end end.
        idtac "OID-BCMP-BACK".
        (* [comment removed for export] *)
        zstep. if_cases Km; zify_cond Km.
        { idtac "OID-ANY".
          fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 lenw ja jb.
          eapply append_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := q);
            first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - HP0 HQ0 HQL HPE B1 B3 LR; lia | match goal with |- ?g => idtac "OID-APP1-LEFT:" g end ]. }
        idtac "OID-OTHER4".
        (* [comment removed for export] *)
        do 2 zstep.
        clear HK64. assert (HK64 : K56 = Z_to_bv 64 0 \/ K56 = K56) by (right; reflexivity).
        fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw (Z_to_bv 64 18446744073709543296) lenw ja jb.
        eapply append_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := q);
          first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - HP0 HQ0 HQL HPE B1 B3 LR; lia | match goal with |- ?g => idtac "OID-APP2-LEFT:" g end ]. }
    idtac "OID-OTHER".
    (* [comment removed for export] *)
    do 2 zstep.
    clear HK64. assert (HK64 : K56 = Z_to_bv 64 0 \/ K56 = K56) by (right; reflexivity).
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw (Z_to_bv 64 18446744073709543296) lenw ja jb.
    eapply append_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := q);
      first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - HP0 HQ0 HQL HPE B1 B3 LR; lia | match goal with |- ?g => idtac "OID-APP3-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0490@C40858145355.227C40860242543.249C60407910007.250C60410007123.226D10636937134.227D10639034250.250D16069757090.250D16071854214.227D16899842714.250D16901939902.227D2455419791.250 D2457516971.227 D32456773204.250D32458870384.227D46792746863.250D46794843979.227D60109446735.227D60111543915.250D65008160014.227D65010257194.250K20981739667.225K20983836855.248K29378133114.227K29380230238.250K30993319891.227K30995417079.250K49539617926.248K49541715106.225K65856058596.250K65858155712.226K67298046963.225K67300144087.248L10660966143.41 L10946870795.9  L11641955660.41 L14402536676.214L14402536676.237L14402536676.3  L18489062900.25 L19698248394.35 L19710956874.41 L19914454641.3  L20944479544.11 L20944629842.35 L20977711877.2  L21654730866.2  L23315923745.0  L25583009864.35 L2621559066.1   L27111942217.1  L27817884949.225L27830583957.202L27938262793.35 L27942858889.41 L29391009772.3  L29844563604.41 L30507144274.2  L3055355236.3   L30997223346.3  L31165784228.189L34427793940.7  L34429531785.12 L34429531785.17 L3480346400.41  L3484934304.35  L35236225328.25 L35655538583.11 L35903316071.25 L38235734261.1  L40228640085.0  L41110154015.25 L41202929119.189L41202929119.213L41251426164.1  L42488948659.2  L43305107741.25 L45176358614.19 L47369315770.19 L47870616696.2  L49233373885.2  L49478371288.2  L49526752708.2  L5021251703.1   L50678314462.3  L51578300575.1  L52836486813.17 L55195235631.25 L5603384057.19  L56380991837.10 L57383048371.41 L57387379507.35 L576250137.213  L58972524609.3  L59308586248.2  L6008604205.3   L60098763854.6  L61139194273.0  L61643025177.12 L62275882349.3  L62417043471.12 L62417043471.17 L64179129035.1  L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67304579733.2  L7063233879.19  L881835912.0    L9080220944.4   L9356559676.16  L9748633241.2   L9817099972.189 N16222602423.249N21382570003.249N26872553873.226N42205538131.249N48204456022.226N49450819242.226N60733400192.226N66852175570.249O10869052557.247O10871149737.224O1254725598.224 O1256822778.247 O14912726833.226O14914823957.248O18988691132.226O18990788248.248O20866770946.227O20868868134.250O22525005962.226O22527103150.250O30010457231.226O30012554411.248O33449646875.225O33451744063.248O3491220723.248 O3493317847.225 O37557392443.250O37559489567.227O3821773283.227 O3823870407.250 O424351700.225  O426448880.248  O44938202843.225O44940300031.248O49699726460.248O49701823576.226O50009742757.248O50011839873.225O54119978487.225O54122075603.248O55209884805.225O55211981985.248O57031441090.225O57033538278.248O64471909102.248O64474006218.226P19899262166.224P19901359346.247P21647862485.225P21649959665.248P30511339222.226P30513436402.248P3067467751.247 P3069564867.224 P42484919333.226P42487016449.248P47874275067.248P47876372191.225P49228642366.248P49230739482.226P50671478649.225P50673575773.248P62260666314.225P62262763502.248P66292560634.226P66294657758.248P66816411171.250P66818508295.227P67064334489.226P67066431677.248P9762015195.248 P9764112383.225 Q10592389541.225Q10592533181.227Q10594630297.250Q10596726309.202Q10636937134.227Q10637079734.225Q10639034250.250Q10649498890.202Q10649498890.226Q10651748618.201Q11133374175.227Q11135471355.250Q11657053839.227Q11659151019.250Q13731016587.225Q13733106231.201Q16069757090.250Q16071854214.227Q17025597925.250Q17027695041.227Q17681074618.227Q17683171742.250Q17701933584.202Q17701933584.226Q19546780271.225Q19559222767.202Q21765573510.250Q21767670690.227Q23216929724.250Q23219026840.227Q27573751300.227Q27575848480.250Q2803826605.227 Q2805923721.250 Q29775981542.227Q29778078658.250Q32679510481.250Q32681607669.227Q34377611452.227Q34379708568.250Q34390149656.202Q34390149656.226Q39600066516.202Q39600066516.226Q40251340134.202Q40264043238.225Q42439168719.227Q42441265899.250Q43479930840.227Q43482028028.250Q45317270253.227Q45319367369.250Q45353769141.201Q45360063753.225Q46792746863.250Q46794843979.227Q48118064779.227Q48120161967.250Q49746198710.227Q49748295826.250Q50283590580.225Q52711570354.227Q52713667478.250Q56530976407.227Q56533073587.250Q57828105177.227Q57830202365.250Q61847600945.202Q61847600945.226Q67038703949.227Q67040801129.250Q8699324297.227 Q8701421485.250 Q9356559674.204 Q9356559674.227 Q9631998992.202 Q9644448656.225 Q9644583048.227 Q9646680236.250 00000400800<00@00f01L02j04H05^07407507607\08B08h09N0:=0:l0;R0<80<S0<n0>20?90?U0@10A90B>0BY0C40D90EA0FZ0Fn0GG0GH0GI0GT0HJ0IQ0JX0JY0Jf0K?0K@0KA0KB0LS0LX0L\0MB0Mh0O10P:0P;0QQ0QR0QS0QT0SL0S^0T00TK0UO0VS0WS0Wl0X;0X?0X@0XO0Y50Y[0Y_0Y`0Yn0Z:0ZN0ZO0ZP0ZX0ZY0ZZ0Z[0Z`0[D0\20\E0\^0\o0]@0]f0^20^80^C0^M0^N0^a0^b0^m0_80_90_:0_T0_U0_V0_W0_X0_i0_j0`90`l0`m0bc0cE0c_0d90e20eT0en0fg0gA0gB0gC0gD0gE0gF0gG0gH0gI0gJ0gK0gL0gM0gN0gO0gP0gQ0gR0gS0gT0gU0gV0gW0gX0gY0gZ0g[0g\0g]0g^0g_0g`0ga0gb0gc0gd0ge0gf0gg0hb0i]0i^0i_0jR0kE0l@0m;0mn0na0ob10c11d12e13E13e14E14e15A15]16Z17W18R19M1:H1;C1;W1;k1<?1<S1<g1=;1=O1=c1>71>K1>_1?31?41?51?I1?]1@T1AK1A_1B31Bn1Ci1D=1DQ1EA1F11Fl1Gg1H;1HO1HP1HQ1Hf1I;1IW1J31J41J51J61J71J81J91J:1J;1JO1Jc1K?1K[1LX1MU1MV1MW1Mk1N?1NS1Ng1OZ1PM1Q71Qa1R51R61R71R81R91Rg1SU1TO1UI1V@1W71Wi1X[1Y51YO1Yf1Z=1ZT1ZkS2PPS2PPS2FBS2FBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3CU03SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F0FFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3curS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP3END3BUF2lo2bs3LFB2FB3sp11p5nodes3x263APB2x33x273x323x334POSTS2LF2PP3BUF2lo2bs3LFB2FB3sp15nodes3x453APB2q13Lw13x333x463x473x485POST0S2LF2PP3BUF2bs3LFB3DPB5nodesS2LF2PP3BUF2bs3LFB3DPB5nodesS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur3x454CFBa2q13Lw13x333x463x473x485POST0S2LF2PP3END2lo2bs3LFB2FB3sp11p5nodes3cur3x264CFBa2x33x273x323x334POSTS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP3END2lo2bs3LFB2FB3sp11p5nodes3cur3x264CPPa2x33x273x323x334POSTS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur3x454CPPa2q13Lw13x333x463x473x485POST0S1R3NS13NB15NEED02sp2PP1P3END3BUF2lo2bs3PP02B13SLO3LOS2FB3sp13SP11p2Hp3ALO3ACP2F02q14Hq1aS1R2lo3LOS2FB3ALO2F1S2PP2bs2FB3sp12q13Lw13LR1FFS2rg3RRg2KzS1R3NS13NB15NEED02sp2PP2lo2bs4PPLO3SLO2FB3sp13SP14FBLOS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8FS3END2bs1p2KfS2PP1P3END2bs2FB3sp11p2HpFFSS1R3NS13NB15NEED02sp2PP1P3END3BUF2lo2bs3PP02B13SLO3LOS2FB3sp13SP11p2Hp3ALO3ACP2F0S3sp1S2PPS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0S1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0FS1R3NS13NB15NEED02sp2PP3END3BUF2lo2bs3PP02B33SLO3LOS2FB3sp13SP13ALO3ACP2F02q13Lw14Hq1LFFFS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F05BUFLOS1P3END1p2Hp1e3HEQS1P3END1p2Hp1e3HEQS1P3END1p1e3HEQ2q13Hq14Hq1aS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS13NB15NEED02sp2PP3BUF2lo2bs4PPLO3SLO2FB3sp13SP14FBLO5BUFLOS1R3HIA1h2sp2lo3TOP5HTOPcS3BUF2bs2FB3APBS2loSS2PP3BUF2bs3DPBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2FBFS2PP2bs2FB3APPS1P3END1p2HpS2q13Lw12q23Lw24Hq2LFFS2sp3sp1FFFS3CURS1P3END1p2Hp2q13Lw14Hq1a4Hq1L2q23Hq2S1R3NS13NB15NEED02sp2lo2bs3SLO2FB3sp13SP14FBLOS1p2q14Hq1a2q24Hq2aS1R3BUF2lo2bs3LOS3ALO3BCES2PP2bs2FB3sp12F0S2PP2bs2FB3sp12F0S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS3BUF2bs3B47S1i2HiS2rg3RRg2KzS1R2lo3LOSSS1P3END1p2Hp2q13Hq1FS2rg3RRg2RNS2rg3RRg2RNFFS2FB2r03F641q1r1H2H02q02H4FFFFS3END2q13Lw14Hq1LSS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B22B32B54CUR03SLO3SPH2FB3sp15nodes3cur3CU03SPR4SP1R2F05BUFLOS2LF2sp2bs3LFB3sp13SP15nodes3x491CS2LF2bs3LFB2FB5nodes3x491CS2LF2bs3LFB2FB5nodes3x341CS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3x491CS2LF2sp2bs3LFB3sp13SP15nodes3x341CS2LF2bs3LFB2FB5nodes3x341CS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3x341CS2LF2bs3LFB2FB5nodes3x491CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB3sp13SP15nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB3sp13SP15nodes4FBLOFFS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB5nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB5nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S2LF2PP2lo2bs3LFB4PPLO3sp15nodesS2LF2PP2lo2bs3LFB4PPLO3sp15nodesS2LF2lo2bs3LFB2FB3sp15nodes4FBLOS2LF2lo2bs3LFB2FB3sp15nodes4FBLOS2LF2sp2bs3LFB3sp13SP15nodesS2LF2sp2bs3LFB3sp13SP15nodesS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes5BUFLOS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes5BUFLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLOS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesFFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur3SPR2F02F8S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur3SPR2F02F8S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3ALOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3ALOS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesFFS2LF2bs3LFB3sp15nodesS2LF2bs3LFB3sp15nodesS2LF2sp2bs3LFB3sp13SP15nodesS2LF2sp2bs3LFB3sp13SP15nodesFFFFFFFFS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS1R2LF3slo2bs3LFB4SLOS5nodesS1R2LF3slo2bs3LFB4SLOS5nodesS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodesFFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS5nodes3ALOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS5nodes3ALOS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPcS2LF2bs3LFB2FB5nodesFFFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB3sp15nodes4SP1RS2LF2bs3LFB3sp15nodes4SP1RS2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma body_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Pp,$3.P,(0.(5.VP,R1.)(5.R1.VEND,))P,Pp',$3.P,(1.R3.R1.)P,(5.R2.VEND,)(4<.R3.)(4<.R3.)")
(* [comment removed for export] *).
  Proof.
    intros p Hp KLOOP. unfold LoopOblig. intros until x31. intros INV HNE HPP HE0 HEQ BUDFa HLN.
    pose proof INV as INV0.
    open_pinv_mu INV hc cur.
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Kf; zify_cond Kf.
    { idtac "BODY-FIN".
      eapply fin_walk with (e := e) (p := p); first [ exact INV0 | exact HPP | eassumption | clear - Hp HE0 HEQ; lia | match goal with |- ?g => idtac "BODY-FIN-LEFT:" g end ]. }
    assert (PL : p < END) by (clear - Kf Hp B1 B3 B5 B47; try kland Kf; rewrite ?Z.mod_small in Kf by lia; lia).
    clear Kf.
    (* [comment removed for export] *)
    do 5 zstep.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "BODY-GT1".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := p) (END := END) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3 Hp PL; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "GT1-LEFT:" g end ]).
    clear SPT OLEN.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw1 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q1 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q1 <= END |- _ => rename H into Hq1 end.
    pose proof (bv_unsigned_in_range 64 Lw1) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    fold_pinv INV1 hc nodes cur nt npad cl cp w0 w1 w2 Lw1 k64 k88 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "BODY-GT1-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (e := e) (rg := rg) (p' := q1);
        first [ exact INV1 | eassumption | clear - Hp Hq1 HE0 HEQ RRg RN; lia | match goal with |- ?g => idtac "BODY-ERR1-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq1a Hq1L]. clear HLg Kz RRg.
    (* [comment removed for export] *)
    do 5 zstep.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => frame_aobj FSHx (FB + 32) 1%nat as OLEN2 end.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "BODY-GT2".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := q1) (END := q1 + bv_unsigned Lw1) (BUF := BUF) (bs := bs) (tag := 6) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3 Hp PL Hq1 Hq1a Hq1L LR1; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "GT2-LEFT:" g end ]).
    clear SPT OLEN2.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw2 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : q1 <= q2 <= _ |- _ => rename H into Hq2 end.
    pose proof (bv_unsigned_in_range 64 Lw2) as LR2. unfold bv_modulus in LR2. cbn [Z.pow Z.of_N Pos.pow] in LR2.
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 Lw2 k64 k88 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "BODY-GT2-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (e := e) (rg := rg) (p' := q2);
        first [ exact INV2 | eassumption | clear - Hp Hq1 Hq1a Hq1L Hq2 HE0 HEQ RRg RN; lia | match goal with |- ?g => idtac "BODY-ERR2-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq2a Hq2L]. clear HLg Kz RRg.
    idtac "BODY-OID".
    eapply oid_walk with (e := e) (q := q2) (pe := q1 + bv_unsigned Lw1) (p0 := p);
      first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - Hp Hq1 Hq1a Hq1L Hq2 Hq2a Hq2L HE0 HEQ LR1 LR2; lia | match goal with |- ?g => idtac "BODY-OID-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26726586762.6L34758806549.7L59308579281.600000B00W00jS3END1k1p2Hk2p'2H1S1P3END1p2Hp2p'2H12H2S3END1p2Hk2p'2H12H2". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma tloop : forall (k : nat) (p : Z), END - p <= Z.of_nat k -> P <= p <= END -> LoopOblig p.
  Proof.
    induction k as [|k IH]; intros p Hk Hp.
    - apply body_walk; [exact Hp|]. intros p' H1 H2. exfalso. clear - Hk H1 H2. lia.
    - apply body_walk; [exact Hp|]. intros p' H1 H2. apply IH; [clear - Hk H1; lia| clear - Hp H1 H2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0370@C40858145355.196C60410007123.195D10636937134.196D16071854214.196D2457516971.196 D32458870384.196D39565106411.198D46794843979.196D60109446735.196D60189065437.198D65008160014.196D68221095944.196K20981739667.194K29378133114.196K30993319891.196K32053909171.196K36557281826.196K65858155712.195L10946870795.9  L12126572370.2  L14402538871.186L14402538871.3  L1685717371.0   L18489062900.25 L19244690506.2  L19698471166.32 L19914454641.3  L2033615896.2   L20977711877.2  L21654730866.2  L24338315589.2  L24342030815.4  L26144142753.2  L2621559066.1   L27111942217.1  L27818050065.170L27938633021.32 L28626988606.2  L28632618922.2  L29391009772.3  L30507144274.2  L3055355236.3   L30997223346.3  L32051500981.2  L34452444106.2  L3484572308.32  L35236225328.25 L35903316071.25 L36544860596.2  L38259954321.2  L39263166881.0  L39268637205.0  L39280637297.0  L40228640085.0  L40281191306.3  L40825480686.8  L41110154015.25 L41202929119.187L41251426164.1  L42488948659.2  L43305107741.25 L43491718995.0  L44166924249.3  L46861157104.185L47870616696.2  L49233373885.2  L49478371288.2  L5021251703.1   L50678314462.3  L51905649112.2  L54316457420.5  L54323387852.2  L55195235631.25 L56380991837.10 L57387012359.32 L576250137.186  L57698627611.2  L58972524609.3  L59308586248.2  L6008606654.3   L60098763854.6  L62275882349.3  L62619108508.0  L63039848099.187L64179129035.1  L65110679799.3  L65110778357.8  L65862516566.2  L66099424948.4  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67242908301.13 L881835912.0    L9356559676.16  L9817099845.187 O10871149737.193O1254725598.193 O14912726833.195O18988691132.195O20866770946.196O22525005962.195O25735317723.196O30010457231.195O33542776439.196O3493317847.194 O37559489567.196O3821773283.196 O424351700.194  O44938202843.194O49701823576.195O50011839873.194O53687452546.196O55209884805.194O64474006218.195P12115299733.198P19899262166.193P2044614335.196 P21647862485.194P28627113325.198P30511339222.195P3069564867.193 P34450608397.198P38261788758.198P42484919333.195P44164039966.198P47876372191.194P49230739482.195P50671478649.194P57713046236.198P62260666314.194P66292560634.195P66818508295.196P67064334489.195Q10048380702.194Q10592533181.196Q10592581281.170Q10598576411.192Q10636937134.196Q10649498890.193Q10649604160.193Q10651864072.192Q11133374175.196Q11657053839.196Q12931753301.194Q13193308734.194Q13732992821.192Q16071854214.196Q17027695041.196Q17681074618.196Q17701933584.193Q19546688875.170Q21767670690.196Q23219026840.196Q24594491637.194Q24852143294.194Q25952160488.197Q26481470270.194Q27573751300.196Q2803826605.196 Q28465177121.195Q29775981542.196Q32681607669.196Q32681824661.198Q33839800254.194Q34390149656.193Q37149073081.198Q39180574961.198Q39600066516.193Q40263906786.170Q42439168719.196Q42439443119.198Q42639330846.194Q45355844095.193Q45741809296.198Q46794843979.196Q47387953854.194Q48118064779.196Q48667442078.194Q49746198710.196Q49746415830.198Q50293951242.192Q5265442331.196 Q54692959518.194Q55415036769.198Q56530976407.196Q56854244147.198Q57828105177.196Q60191312605.197Q60703360670.194Q61847600945.193Q67038703949.196Q67038978349.198Q8699115497.198 Q8699324297.196 Q9356559674.173 Q9644565652.170 Q9644583048.196 00000400800T01e01f02B03[04704\06<06X07b08709509K09`0:60:K0:_0:`0:a0:l0:m0;d0;e0<m0<n0<o0=00=10=80=F0=M0=R0=V0>20?<0?D0?E0?F0?G0?H0?I0?J0?K0@P0AQ0A`0Aa0Ab0Ac0Ad0Ae0Af0Ao0B00B?0B[0B_0B`0Bn0Bo0C00DB0DC0DD0DL0DM0DN0DV0Dc0Dd0ES0El0F=0FY0FZ0Ff0Fl0G70GA0GB0GC0I80I90IC0IM0IN0IY0J30J40J50J60JV0JW0KK0MD0ME0MF0MG0MH0MI0MJ0MK0ML0MM0MN0MO0MP0MQ0MR0MS0MT0MU0MV0MW0N\0OR0PJ0PK0QV0RD0S:0TA0UL0V:0WA0X=0Y90YS0Z80ZR0Zh0[`0\V0]H0]V0]d0^20^@0^N0^\0^j0_80_90_`0`G0`U0aG0aU0bK0bY0c?0d50dC0e50e\0fR0g90g:0gI0g`0h60h70h80h_0h`0ie0jj0jk0k90kO0l80lj0m80m90mG0mn0n\0oN10110c11111I12;12`12a12b13I14J15<15l16^17_18Y19D19X19i1::S2PPS2FBS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03LOS2FB3sp13SP14SLO'3SPR4SP1R2F0FS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12h15Ehtop3SPR4SP1R2F02HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp1S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03LOS2FB3sp13SP14SLO'3SPR4SP1R2F02HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12h15Ehtop3SPR4SP1R2F0S2LF2PP2bs3LFB2FB3APPS2LF2PP1P3END3BUF2lo2bs3LFB2FB3sp13x253APB2x23x263x273x324POSTS2LF2PP3BUF2bs3LFB3DPBS2LF2PP3CUR2bs3LFB2D1S2LF3CUR2bs3LFB2FB3APCS2LF2PP2bs3LFB2FB3APPS1R2lo3LOS2FB3ALO2F1FFS2rg3RRg2KgSS1R3NS13NB15NEED02sp2PP2lo2bs4PPLO2FB3sp13SP14SLO'4FBLOSS1R3NS13NB15NEED02sp2PP2lo2bs3PP03LOS2FB3sp13SP14SP1M3ALO3ACP4SLO'2F02F8FFFFS3END1qS3END2rg1q3RRgS3END1qS3sp1S2PPS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL2FB3sp13SP13ALO3ACP4SLO'2F0S2rg3RRgFFFFFFFS1R3NS13NB15NEED02sp2PP2lo2bs3PP03LOS2FB3sp13SP14SP1M3ALO3ACP4SLO'2F0S1R3NS13NB15NEED02sp2PP3BUF2lo2bs4PPLO2FB3sp13SP14SLO'4FBLO5BUFLOS3BUF2bs2FB3APBFFSSSSS1R3HIA1hSS2PP3BUF2bs3DPBS2LF2sp2PP3CUR2bs3LFB2FB3sp1S2FBFS2PP2bs2FB3APPSFS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04PPLO4CUR03SPH2FB3sp14SLO'3SPR4SP1R2F0FFS2sp3sp1FFS2rg3RRgS1P3END1q3HqrFS1R3NS13NB15NEED02sp2lo2bs2FB3sp13SP14SLO'4FBLOS1R3BUF2lo2bs3LOS3ALO3BCES2PP2bs2FB3sp12F0S2LF2sp2PP3CUR2bs3LFB2FB3sp1FS3BUF2bs3B47S1i2HiS2rg3RRg2KgS1R2lo3LOSFSS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q2Lw2LR2Hq3HqLFS1P3END2B2S1P3END2B2FS1R3HIA1h1dS2FB2r03F641q1r1H2H02q02H4FFFS1R3HIA1h2sp2lo3TOP3sp13SP14HTOPSS1R3NS13NB15NEED02sp2lo3LOS3sp13SP13ALO3ACV4SLO'3SPRS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q2Lw3Hqr2LR2Hq3HqLFFFFFFFFFFFFFFFFFFFS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB2FB3sp13SP14SLO'4FBLOS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3sp13SP14SLO'FS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO4SLO'S1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB2FB4SLO'4FBLOS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3sp13SP14SLO'5BUFLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F1S2LF2PP2lo2bs3LFB4PPLO3sp1S2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_stS2LF2lo2bs3LFB2FB3sp14FBLOS2LF2sp2bs3LFB3sp13SP1S1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3sp13SP14SLO'5BUFLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2bs3LFB2FBFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS2LF2PP2bs3LFBS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2PP2bs3LFBS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'S2LF2PP2bs3LFBS2LF2sp2PP3CUR2bs3LFB2FB3sp13SPR2F02F8S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP13ALO4SLO'S2LF2bs3LFB2FBS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPFS2LF2bs3LFB3sp1S2LF2bs3LFB3sp14SP1R2HBS2LF2sp2bs3LFB3sp13SP1FFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPFS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP13ALO4SLO'2HB5Ha_st5Hl_stFS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOS3sp12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2PP2bs3LFBFS2LF2PP2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3ALO4SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3HIA1h2LF2sp2bs3LFB3TOP3sp14HTOPS1R3HIA1h2LF2sp2bs3LFB3TOP3sp14HTOP2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF2bs3LFB3sp12HB5Ha_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_stFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp13SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB2FB2F0S2LF2bs3LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma hdr_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Ph1,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)Pw0,(?.&40.)Pw1,(?.&40.)Pw2,(?.&40.)Plenj,(?.&40.)Pja,(1;.(?.&8.))Pjb,(1;.(?.&8.))Pk24,(?.&40.)Pk32,(?.&40.)Pk40,(?.&40.)Pk48,(?.&40.)Pk56,(?.&40.)Pk64,(?.&40.)Pk88,(?.&40.)P,(1?.$19.VR,VHIA,R1>.VLB,(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)R1=.)P,(2.P,$3.Sp(20.$19.VR,VHIA,R1?.)(20.$19.VR,VHIA,Vh,))P,(2.$3.(18.$19.VR,VHIA,R20.)(18.$19.VR,VHIA,Vh,))P,(2.$3.(21.$19.VR,VHIA,R21.)(21.$19.VR,VHIA,Vh,))P,(2.$3.(22.$19.VR,VHIA,R22.)(22.$19.VR,VHIA,Vh,))P,(2.$3.(23.$19.VR,VHIA,R23.)(23.$19.VR,VHIA,Vh,))P,(2.$3.(40.$19.VR,VHIA,R24.)(40.$19.VR,VHIA,Vh,))P,(25.$19.R24.VFB,(17.$28.(29.R14.)(17.$28.(29.R13.)(17.$28.(29.R12.)(2:.$28.)))))P,(25.$19.R25.(6.VFB,+20.)(17.$28.(29.R12.)(2:.$28.)))P,(25.$19.R26.(6.(2;.VFB,+3.)(2<.(2=.VR,)))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.+?1.))(17.$28.(2>.(27.&8.=))(17.$28.(2>.(27.&8.+?3.))(17.$28.(2>.(27.&8.+?3.))(17.$28.(2>.(27.&8.+?3.))(2:.$28.))))))))))P,(25.$19.R27.(6.(2?.&40.Vsp,)-68.)(17.$28.(29.Vs11,)(17.$28.(29.Vs10,)(17.$28.(29.Vs9,)(17.$28.(29.Vs8,)(17.$28.(29.Vs7,)(17.$28.(29.Vs6,)(17.$28.(29.Vs5,)(17.$28.(29.Vs4,)(17.$28.(29.Vs3,)(17.$28.(29.Vs2,)(17.$28.(29.Vs1,)(17.$28.(29.Vs0,)(17.$28.(29.Vra,)(2:.$28.)))))))))))))))P,(25.$19.R28.Vsp1,(17.$28.(30.#18.R14.)(17.$28.(29.R12.)(17.$28.(29.R11.)(17.$28.(29.R10.)(17.$28.(29.R?.)(17.$28.(29.R>.)(17.$28.(29.R=.)(17.$28.(29.(27.&40.VFB,))(17.$28.(29.(27.&40.VFB,))(17.$28.(29.R<.)(17.$28.(30.#10.R13.)(17.$28.(29.(27.&40.VFB,))(2:.$28.))))))))))))))P,(31.$19.R29.(6.Vsp1,+78.)(6.(2?.&40.Vsp,)-68.))P,(31.$19.R2:.Vlo,Vsp1,)P,(32.$19.R2;.)P,(25.$19.R2<.VPP,(17.$28.(29.(27.&40.VP,))(2:.$28.)))P,(25.$19.R2=.VCUR,(26.Vct,Vcpad,===))P,(33.$19.R2>.VBUF,Vbs,)P,(34.$19.(2=.VR,)(20.$19.VR,VHIA,Vh,)R2?.VPP,+8.)P,(34.$19.(2=.VR,)(20.$19.VR,VHIA,Vh,)R30.VCUR,+20.)P,(34.$19.(2=.VR,)(20.$19.VR,VHIA,Vh,)R31.VBUF,(=.(>.(?.&8.)Vbs,)))P,(35.$19.VR,VHIA,Vh,VLB,VLF,(2?.&40.Vsp,)(2?.&40.Vsp,)(17.(9.$3.$3.)(:.$3.$3.VPP,(6.VPP,+8.))(17.(9.$3.$3.)(:.$3.$3.VCUR,(6.VCUR,+20.))(2:.(9.$3.$3.))))Vm,R32.)P,(36.$19.(2=.VR,)R33.Vslo,Vsp1,)P,(36.$19.(2=.VR,)R34.Vsp1,(2?.&40.Vsp,))(42.$19.(43.$19.VR,VHIA,R36.Vmo0,)(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(48.(49.(27.&40.+:;09<.)(27.&40.Vsp1,)Vgp,Vtp,R34.R33.R32.Vsp,(27.&40.Vsp1,)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.Vs2,(27.&40.(2<.(2=.VR,)))(27.&40.VPP,)(27.&40.VCUR,)(27.&40.(6.VFB,+20.))(27.&40.(6.(2;.VFB,+3.)(2<.(2=.VR,))))Vs8,Vs9,Vs10,(27.&40.VEND,)R29.R28.R27.R26.)VF,(27.&40.+:;134.)Vfc,(4:.(?.&40.))R35.(4;.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until k88. intros HH1 Ehcs Ehtop Estk Eflag Evol Efr FHD HLEN FSH SAVE RSL SThi STlo MI HPP HCUR HBUF OPP OCUR OBUF PRES0 SS1 SS2.
    rewrite <- Ehcs in OPP, OCUR, OBUF.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m mm PRES0 HCS1 Estk) as PRES. clear PRES0.
    (* [comment removed for export] *)
    assert (FINX : forall (mx : mem) (r p' : Z) (lw : word) (ja' jb' : list byte) (c24 c32 c40 c48 c56 c64 c88 : word)
                     (yra y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 t2v t3v t4v t5v t6v t8v t9v t10v t11v y28 y29 y30 y31 : word),
               HM asegs R HIA h1 LB LF' mx -> rw_cells asegs mx FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs mx (Z.shiftr FB 3 + al_sb AL) FSHG ->
               rw_cells asegs mx (bv_unsigned sp + -104) SAVEL ->
               rw_cells asegs mx sp1 [CB 24 ja'; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 c88; CB 16 jb'; C8 (Z_to_bv 64 FB)] ->
               stk asegs mx (sp1 + 120) (bv_unsigned sp + -104) -> stk asegs mx lo sp1 -> mem_inv asegs mx ->
               presW asegs R HIA h1 LB LF (bv_unsigned sp) (bv_unsigned sp) W m mx ->
               sshad asegs AL mx slo sp1 -> sshad asegs AL mx sp1 (bv_unsigned sp) ->
               rw_cells asegs mx PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> rw_cells asegs mx CUR (seq_cells ct cpad 0 0 0) -> -0x3000 < r <= 0 -> (r = 0 \/ r = -8320 -> p' = END) ->
               aevtA asegs (KF asegs R HIA h1 mo0) POST
                 (MS (mkR yra (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17
                          t2v t3v t4v t5v t6v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t8v t9v t10v t11v y28 y29 y30 y31)
                     F (Z_to_bv 64 0x0ab158) fc None mx (seg_rom asegs))).
    { intros. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
      eapply A_x509_policies_B.pol_fin with (hq := h1) (nodes := @nil Z) (p' := p') (hct := ct) (hcpad := cpad) (hcl := 0) (hcp := 0);
        first [ eassumption | reflexivity | exact CFB
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => rewrite Evol; clear; lia
                | |- hfr _ _ _ _ <= _ => rewrite Efr; unfold A_x509_policies_B.FFRpol; clear - B2 D0; unfold fr_charge; pose proof (Z.div_pos (END - P) 4 ltac:(lia) ltac:(lia)); nia
                | |- Z.of_nat (length _) <= _ => unfold A_x509_policies_B.CNTpol; cbn [length Z.of_nat]; apply Z.div_pos; [clear - B2; lia| clear; lia]
                | |- _ \/ _ => left; repeat split; reflexivity
                | |- seq_chain _ _ _ _ _ _ => apply chain_nil
                | |- List.NoDup [] => constructor
                | |- forall x, In x [] -> _ => intros x []
                end
              | match goal with |- ?g => idtac "FINX-LEFT:" g end ]. }
    idtac "HDR-FINX".
    pose proof (hcs_ok asegs R HIA h1) as CSOK1. pose proof (cs_ok_sb _ _ CSOK1) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO.
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof SLO as SLO'. unfold A_x509_policies_A.STKpol in SLO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    unfold seq_cells in HCUR.
    pose proof (hm_top asegs R HIA h1 _ _ _ HH1) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO' LOS ALO ACV NS1 NB1 NEED0; lia).
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (sp1 - lo))
      by (rewrite Ehcs; eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SLO' SP1 NS1 NB1 NEED0 TOP HTOP; lia]).
    assert (SCS01 : crange (hcs asegs R HIA h1) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (rewrite Ehcs; exact (hcs_stack asegs R HIA h)).
    assert (CFB1 : crange (hcs asegs R HIA h1) FB 64) by (rewrite Ehcs; exact CFB).
    dpose FRSH as (F0 & F1 & F2 & F3).
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
    assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h1 LB _ mm LB HH1 ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (CWP1 : client_wrange L (LB ++ fdata LF') lo (htop asegs R HIA h1) PP 8)
      by (rewrite Ehtop; eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]).
    assert (INHc : In (FB, 24) (LB ++ fdata LF')) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDc : In (FB + 32, 64 - 40) (LB ++ fdata LF')) by (apply in_or_app; right; cbn; right; left; reflexivity).
    pose proof (art_stk_high asegs R HIA) as STKH.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    pose proof (hm_abase asegs R HIA h1 _ _ mg HH1) as ABg.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "HDR-GT".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA h1) (PP := PP) (LENP := FB + 32) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO' NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO' NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "HGT-LEFT:" g end ]).
    clear SPT OLEN.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q <= END |- _ => rename H into Hqr end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    idtac "HDR-GT-BACK".
    (* [comment removed for export] *)
    zstep. if_cases Kg; zify_cond Kg.
    2:{ idtac "HDR-GT-ERR".
        do 3 zstep.
        first [ rewrite A_x509_get_san_A.swrap32_errsum'' by (clear - RRg; lia)
              | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - RRg; lia))
              | match goal with |- ?g => idtac "ERRSUM-LEFT" end ].
        lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
        eapply FINX with (p' := q); first [ eassumption | clear - RRg; lia | match goal with |- ?g => idtac "HDR-ERR-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kg RRg; try kland Kg; rewrite ?unsigned_lit in Kg by lia; rewrite ?Z_to_bv_unsigned in Kg; unfold bv_wrap, bv_modulus in Kg; cbn [Z.pow Z.of_N Pos.pow] in Kg; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq HqL]. clear HLg Kg RRg.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mx HHx) as AB2 end end.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "HDR-EMPTY".
      lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
      eapply FINX with (r := -9574) (p' := q); first [ eassumption | clear; lia | match goal with |- ?g => idtac "HDR-EMPTY-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    { idtac "HDR-MISMATCH".
      lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
      eapply FINX with (r := -9574) (p' := q); first [ eassumption | clear; lia | match goal with |- ?g => idtac "HDR-MM-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 13 zstep.
    idtac "HDR-LOOP".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into ml end.
    lazymatch goal with H : rw_cells _ ml CUR _ |- _ => change (rw_cells asegs ml CUR (seq_cells ct cpad 0 0 0)) in H end.
    assert (INV : pinv ml h1 (@nil Z) CUR ct cpad 0 0 w0 w1 w2 Lw (Z_to_bv 64 0) k88 ja jb).
    { unfold pinvx. spine; first [ eassumption | reflexivity | exact HCS1 | exact I
        | lazymatch goal with
          | |- havol _ _ _ _ <= _ => rewrite Evol; clear; lia
          | |- List.NoDup [] => constructor
          | |- _ \/ _ => left; repeat split; reflexivity
          | |- forall x, In x [] -> nodeF x => let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; destruct Hy
          end
        | match goal with |- ?g => idtac "HDR-INV-LEFT:" g end ]. }
    eapply (tloop (Z.to_nat (END - q)) q) with (e := 0);
      first [ exact INV | eassumption | (intros _; reflexivity) | rewrite Efr; clear; lia | cbn [length Z.of_nat]; clear; lia | clear - Hq Hqr; lia | match goal with |- ?g => idtac "HDR-LOOP-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L67922604617.0000001S". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV"] Lemma main_call : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)P,(1?.$19.VR,VHIA,Vh,VLB,VLF,Vm,)P,(54.$19.VR,VHIA,Vh,Vmo0,)P,(25.$19.Vm,VPP,(17.$28.(29.(27.&40.VP,))(2:.$28.)))P,(25.$19.Vm,VCUR,(26.Vct,Vcpad,===))P,(33.$19.Vm,VBUF,Vbs,)P,(31.$19.Vm,Vlo,(2?.&40.Vsp,))P,(36.$19.(2=.VR,)Vm,Vslo,(2?.&40.Vsp,))P,(32.$19.Vm,)P,(34.$19.(2=.VR,)(20.$19.VR,VHIA,Vh,)Vm,VPP,+8.)P,(34.$19.(2=.VR,)(20.$19.VR,VHIA,Vh,)Vm,VCUR,+20.)(55.$19.(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(56.(48.(49.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(27.&40.VPP,)(27.&40.VEND,)(27.&40.VCUR,)R13.R12.R11.R10.R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(27.&40.$57.)Vfc,(4:.(?.&40.))Vm,(4;.$19.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HK0 HPP HCUR HBUF ST SS MI OPP OCUR.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_policies_A.pro_walk with (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (ct := ct) (cpad := cpad); first [ exact HH | exact HPP | exact HCUR | exact HBUF | exact ST | exact SS | exact MI | exact OPP | exact OCUR | exact OBUF | eassumption
                             | match goal with |- ?g => idtac "PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    ddestruct P1 as (FB & sp1 & h1 & m1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & w0 & w1 & w2 & lenj
                   & ja & jb & k24 & k32 & k40 & k48 & k56 & k64 & k88
                   & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI1
                   & HPP1 & HCUR1 & HB1 & OPP1 & OCUR1 & OBUF1 & APP & APC & PRES0 & SS1 & SS2).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & _).
    intros mo1 [HK1 MF1].
    apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    eapply hdr_walk with (FB := FB) (sp1 := sp1) (h1 := h1);
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact APP | exact APC | exact HH1 | exact PRES0 | eassumption
            | match goal with |- ?g => idtac "HDR-PRE-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L47484010984.4L61435248169.200000=00DS1R3HIA1h3H36S2LF2H1". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 NB1 NEED0 CALLOC GT OIDH"] Theorem A_x509_policies_specE : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(58.$19.VR,VHIA,$45.$46.$47.(59.VR,)(5:.$5;.#4.)L,(?.&40.)$5<.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))$57.)")
(* [comment removed for export] *).
  Proof.
    unfold seq_parser_stmtE. intros until cpad. intros; subst.
    eapply main_call with (bs := bs) (ct := ct) (cpad := cpad) (d := d) (slo := slo);
      first [ eassumption | reflexivity
            | lazymatch goal with
              | |- (length _ < 511)%nat => match goal with H : (length _ <= LFMAX_CRT + 4)%nat |- _ => clear - H; unfold LFMAX_CRT in H; lia end
              | |- havol _ _ _ _ <= AVOL_MAX => match goal with H : havol _ _ _ _ + PHIpol _ <= AVOL_MAX |- _ => unfold A_x509_policies_B.PHIpol in H; clear - H; lia end
              end
            | match goal with |- ?g => idtac "SPEC-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 NB1 NEED0 CALLOC GT OIDH"] Theorem A_x509_policies_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(5=.$19.VR,VHIA,$45.$46.$47.(59.VR,)(5:.$5;.#4.)L,(?.&40.)$5<.$57.)")
(* [comment removed for export] *).
  Proof. exact (seq_parser_stmtE_A _ _ _ _ _ _ _ _ _ _ _ A_x509_policies_specE). Qed.
End Walk.

(* [comment removed for export] *)
