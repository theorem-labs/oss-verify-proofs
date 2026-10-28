(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_pkcs7_signers.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_E A_pkcs7_signers_F.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Ltac2 gd_tbl_A_pkcs7_signers_G () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signers_C.gvA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.CrtStmts.SNAME"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_crt_parse_stmts.pkcs7_getsigners_postA"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signers_C.PHIs"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signers_C.FFRs"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signers_C.CNTs"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x98e24]).
Local Ltac zchk_new ::= constr:([0x98a4c; 0x98b3c; 0x98b90; 0x98b94; 0x98b98; 0x98ba4; 0x98bb8; 0x98bbc; 0x98bc0; 0x98bc4; 0x98bd0; 0x98be0; 0x98c34; 0x98c38; 0x98c50; 0x98c58; 0x98c5c; 0x98c6c; 0x98ce8; 0x98cf0; 0x98cf4; 0x98d08; 0x98d0c; 0x98d2c; 0x98d30; 0x98d88; 0x98d8c; 0x98dc4; 0x98dc8]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z) (STKsi : Z).
  Hypothesis SIGNER : pkcs7_signer_stmtA asegs R HIA PHIsi FFRsi CNTsi STKsi A_PKCS7_SIGNER.
  Hypothesis PHIsi_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsi n <= PHIsi n'.
  Hypothesis FFRsi_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsi n d <= FFRsi n' d.
  Hypothesis CNTsi_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsi n <= CNTsi n'.
  Hypothesis STKsi0 : 0 <= STKsi.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55853786883.20000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation STKs := (A_pkcs7_signers_A.STKs R STKsi).
  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 1)%nat.
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
  Hypothesis HSG : rw_cells asegs m SIG (signer_cells 0 0 sj).
  Hypothesis ALS : SIG mod 8 = 0.
  Hypothesis SG0 : 0 < SIG.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIG SIGNER_SIZE.
  Hypothesis SGLO : SIG + SIGNER_SIZE <= lo.
  Hypothesis DSB : SIG + SIGNER_SIZE <= BUF \/ BUF + n <= SIG.
  Hypothesis HDA : rw_cells asegs m DALG (buf_cells dtg dpad dlen dq).
  Hypothesis ALD : DALG mod 8 = 0.
  Hypothesis DA0 : 0 < DALG.
  Hypothesis CRDA : client_range L (LB ++ fdata LF) lo DALG 24.
  Hypothesis DALO : DALG + 24 <= lo.
  Hypothesis Q1 : BUF <= dq. Hypothesis Q2 : 0 <= dlen. Hypothesis Q3 : dq + dlen <= BUF + n.
  Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
  Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
  Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKs.
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
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold A_pkcs7_signers_A.STKs in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Local Notation NB := (END - P).
  Local Notation POST := (pkcs7_getsigners_postA asegs R HIA (PHIs PHIsi CNTsi) (FFRs FFRsi CNTsi) (CNTs CNTsi) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END SIG DALG NB lo slo d dtg dpad dlen dq m mo0).
  Local Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].
  Local Notation gvA := (gvA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).
  Local Notation gvA_x := (A_pkcs7_signers_C.gvA_x R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).

  Ltac gvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).


  Local Notation sjZ := (SGJ (zeros 80) (Z_to_bv 8 0) (zeros 7) (zeros 96)).

  #[using="Type"] Lemma gvA_x_mo : forall (fx FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA) (moq : Model),
    gvA_x fx FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc -> HK asegs R HIA hc moq -> mo_frame moc moq ->
    gvA_x fx FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moq hc.
  Proof.
    intros until moq. intros D HKq MFq. gvA_open D.
    split; [exact HHc|]. split; [exact HKq|]. split; [eapply mo_frame_trans; [exact MFc| exact MFq]|].
    repeat match goal with |- _ /\ _ => split end; first [assumption | exact (proj1 SP1) | exact (proj2 SP1) | exact (proj1 Hpc) | exact (proj2 Hpc) | match goal with |- ?g => idtac "GVAXMO-LEFT:" g end].
  Qed.
  #[using="Type"] Lemma gvA_x_bud : forall (fx FB sp1 : Z) (W : list ivl) (PHIa FFRa PHIa' FFRa' : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA),
    gvA_x fx FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc -> PHIa <= PHIa' -> FFRa <= FFRa' ->
    gvA_x fx FB sp1 W PHIa' FFRa' w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc Lc mc moc hc.
  Proof.
    intros until hc. intros D LP LQ. gvA_open D.
    split; [exact HHc|]. split; [exact HKc|]. split; [exact MFc|]. split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HCSc|].
    split; [clear - HVc LP; lia|]. split; [clear - HFRc LQ; lia|].
    repeat match goal with |- _ /\ _ => split end; first [assumption | exact (proj1 SP1) | exact (proj2 SP1) | exact (proj1 Hpc) | exact (proj2 Hpc) | match goal with |- ?g => idtac "GVAXBUD-LEFT:" g end].
  Qed.





  (* [comment removed for export] *)
  #[using="Type"] Lemma gvA_mo : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_G ()) "PFB,$0.Psp1,$0.PW,(1.$2.)PPHIa,$0.PFFRa,$0.Pw0,(3.&40.)Pw1,(3.&40.)Pw2,(3.&40.)Plw,(3.&40.)Pb4,(3.&8.)Pk0,(3.&40.)Pk8,(3.&40.)Pk16,(3.&40.)Pk24,(3.&40.)Pj32,(1.(3.&8.))Pp,$0.Psgc,(1.$4.)PLc,(1.$5.)Pmc,P,(3.&40.)(6.(3.&8.))Pmoc,$7.Phc,(8.$9.VR,VHIA,)Pmoq,$7.P,(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(;.$9.VR,VHIA,R3.R2.)P,(<.R5.R3.)(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R4.R5.)")
(* [comment removed for export] *).
  Proof.
    exact (gvA_x_mo 0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11468125488.8L66198138163.800000O00mS1R3HIA1h4FFRa5FFRa'2hc4HFRc2LQS1R3HIA1h4PHIa5PHIa'2hc3HVc2LP". (* [comment removed for export] *)
  #[using="Type"] Lemma gvA_bud : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_G ()) "PFB,$0.Psp1,$0.PW,(1.$2.)PPHIa,$0.PFFRa,$0.PPHIa',$0.PFFRa',$0.Pw0,(3.&40.)Pw1,(3.&40.)Pw2,(3.&40.)Plw,(3.&40.)Pb4,(3.&8.)Pk0,(3.&40.)Pk8,(3.&40.)Pk16,(3.&40.)Pk24,(3.&40.)Pj32,(1.(3.&8.))Pp,$0.Psgc,(1.$4.)PLc,(1.$5.)Pmc,P,(3.&40.)(6.(3.&8.))Pmoc,$7.Phc,(8.$9.VR,VHIA,)P,(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R17.R16.R15.R14.R13.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(=.R15.R13.)P,(=.R15.R13.)(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R1:.R19.R18.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    exact (gvA_x_bud 0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L14282995869.18 L17905066372.8  L17991598320.218L31437125803.6  L38087549238.18 L39111570593.0  L39124720301.8  L40228640085.0  L44984951545.4  L46425563800.239L47028033785.219L5367532848.1   L59308633593.1  L59310680273.3  L5966946069.6   L65005791566.3  L68237972690.2  Q25019582490.223Q29612090062.223Q32352309670.224Q47700973017.224Q47713708799.223Q61338516829.22400000W01502C02X03>03?03W03X03c04m06306906=06H06_06g07007`08P0:K0;;0;k0<[S1R3HIA5STKsi1h2sp3SIG2lo4SGLO3SLO1a2HaS1R3HIA1h1d4rest4FFRa4BUDF3DnnS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC4HPOS3pre2nx4post2NBS1R3HIA1h2r24PHIa3BUDS1R3HIA5STKsi1h2sp2PP2lo4PPLO3SLO1a2HaSS1R3HIA1h1d2r24FFRa4BUDFSS1d2r24FFRaS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC3pre2nx4post3NXBS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC3pre2nx4postS4PHIaS2KZS2n22KZ3HP2S1R3HIA1h4rest4PHIa3BUDS1d4FFRaS2r24PHIaS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS4rest3cur2FB3sp13sgc3SP14SP1M3SZC3ALO3ACV3SPR3HAL4HPOS3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4post". (* [comment removed for export] *)
  #[using="IMG NS1 HMND FREE STKsi LFB PP0 CWP PPLO BIN SG0 CWS SGLO DA0 CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma CL3 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_G ()) "Pnodes,(1.$0.)Pcur,$0.PFB,$0.Psp1,$0.PPHIa,$0.PFFRa,$0.Pw0,(3.&40.)Pw1,(3.&40.)Pw2,(3.&40.)Plw,(3.&40.)Pb4,(3.&8.)Pk0,(3.&40.)Pk8,(3.&40.)Pk16,(3.&40.)Pk24,(3.&40.)Pj32,(1.(3.&8.))Pp,$0.Psgc,(1.$4.)PA,(1.$5.)PB,(1.$5.)PRR,P,P,(3.&40.)(6.(3.&8.))P,(1.$5.)SpPmc,P,(3.&40.)(6.(3.&8.))Pmoc,$7.Phc,(8.$9.VR,VHIA,)Pxra,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Ps4v,(3.&40.)Ps5v,(3.&40.)Ps6v,(3.&40.)Ps7v,(3.&40.)Ps8v,(3.&40.)Ps11v,(3.&40.)P,(>.(?.(1.$0.)R2=.(10.$0.)))P,(11.$9.L,(1.$4.)$12.R19.(13.$5.(13.$5.R1<.(13.$5.(14.(15.$0.R2>.))R1;.))VLB,)R2=.R2>.)P,(16.$0.R2?.)P,Px,$0.P,(17.$0.R1.R31.)(>.(17.$0.R2.(18.(19.$0.$0.)$0.(1:.$0.$0.)R20.)))P,(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R2?.R2>.(1;.(19.$0.$0.)(1<.$0.$0.VPP,(1=.VPP,+8.))(1;.(19.$0.$0.)(1<.$0.$0.VSIG,(1=.VSIG,+<8.))(10.(19.$0.$0.))))R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(13.$5.R1?.(13.$5.(14.(15.$0.R31.))R1>.))R1<.R1;.R1:.)P,A2.R1>.R1=.(13.$5.R20.(13.$5.(14.(15.$0.R32.))R1?.))P,PmX,P,(3.&40.)(6.(3.&8.))PmY,P,(3.&40.)(6.(3.&8.))PhX,(8.$9.VR,VHIA,)Prest',(1.$0.)Px,$0.P,A2.R24.R5.(13.$5.R26.(13.$5.(14.(15.$0.(1;.$0.R1.R2.)))R25.))P,(17.$0.R2.R39.)P,(>.(17.$0.R3.R4.))P,(1>.$9.VR,VHIA,R6.(13.$5.(13.$5.R29.(13.$5.(14.(15.$0.(1;.$0.R4.R5.)))R28.))VLB,)(1;.(19.$0.$0.)(1<.$0.$0.R39.+40.)VLF,)R8.)P,(?.$0.(1?.$9.VR,VHIA,R7.)(1?.$9.VR,VHIA,Vh,))P,(20.$9.VR,(21.R6.(13.$5.(13.$5.R2;.(13.$5.(14.(15.$0.(1;.$0.R6.R7.)))R2:.))VLB,))(1;.(19.$0.$0.)(1<.$0.$0.R3;.+40.)VLF,)R3:.(22.VR,)(1?.$9.VR,VHIA,R8.)(10.$2.)R:.R9.)A2.R2:.R:.(13.$5.R2<.(13.$5.(14.(15.$0.R8.))R2;.))P,(=.(1=.(1=.(23.$9.VR,VHIA,Vh,)R30.)(24.(25.(26.$0.R34.))$27.))$28.)P,(=.(1=.(1=.(29.$9.VR,VHIA,Vh,)R30.)(24.(25.(26.$0.R35.))(2:.(1=.Vd,+1.))))$2;.)P,(2<.$9.Vm,(22.VR,)(1?.$9.VR,VHIA,Vh,)(2=.&40.Vs0,)(2=.&40.Vsp,)Vd,)P,Pmc',P,(3.&40.)(6.(3.&8.))Pmoc',$7.Phc',(8.$9.VR,VHIA,)Py0,(3.&40.)Py1,(3.&40.)Py2,(3.&40.)Pya0,(3.&40.)Pya1,(3.&40.)Pya2,(3.&40.)Pya3,(3.&40.)Pya4,(3.&40.)Pya5,(3.&40.)Pya6,(3.&40.)Pya7,(3.&40.)Py3,(3.&40.)Py4,(3.&40.)Py5,(3.&40.)Py6,(3.&40.)Ps7',(3.&40.)P,(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R48.R47.(1;.(19.$0.$0.)(1<.$0.$0.VPP,(1=.VPP,+8.))(1;.(19.$0.$0.)(1<.$0.$0.VSIG,(1=.VSIG,+<8.))(10.(19.$0.$0.))))(1=.R46.(24.(25.(26.$0.R4:.))$27.))(1=.R45.(24.(25.(26.$0.R4:.))(2:.(1=.Vd,+1.))))R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.(13.$5.R38.R37.)R13.R12.R11.)P,A2.R37.R14.(13.$5.R39.R38.)(2>.$9.(2?.$9.VR,VHIA,(30.VPHIsi,VCNTsi,)(31.VFFRsi,VCNTsi,)(32.VCNTsi,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VSIG,VDALG,(33.VEND,VP,)Vlo,Vslo,Vd,Vdtg,Vdpad,Vdlen,Vdq,Vm,Vmo0,)(34.(35.(36.(37.&40.+98=>8.)(37.&40.R49.)Vgp,Vtp,R12.R11.R10.Vsp,(37.&40.R49.)R?.R>.R=.R<.R;.R:.R9.R8.(37.&40.R4:.)R25.R3.R24.R23.(37.&40.(38.(39.VR,)))R21.(37.&40.R4:.)(37.&40.(1=.(3:.R4:.+3.)(38.(39.VR,))))R20.R7.R6.R5.R4.)VF,(37.&40.+98=?0.)Vfc,(3;.(3.&40.))R15.(3<.$9.))R14.))(2>.$9.(2?.$9.VR,VHIA,(30.VPHIsi,VCNTsi,)(31.VFFRsi,VCNTsi,)(32.VCNTsi,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VSIG,VDALG,(33.VEND,VP,)Vlo,Vslo,Vd,Vdtg,Vdpad,Vdlen,Vdq,Vm,Vmo0,)(34.(35.(36.R20.(37.&40.R35.)Vgp,Vtp,R1?.R1>.R1=.Vsp,(37.&40.R35.)(37.&40.R37.)R1<.R1;.R1:.R19.R18.R17.R16.(37.&40.R36.)R11.R>.R10.R?.(37.&40.(38.(39.VR,)))R=.(37.&40.R36.)(37.&40.(1=.(3:.R36.+3.)(38.(39.VR,))))R<.R15.R14.R13.R12.)VF,(37.&40.+98=<4.)Vfc,(3;.(3.&40.))R23.(3<.$9.))R22.))")
(* [comment removed for export] *).
  Proof.
    intros nodes. induction nodes as [|n1 rest IH];
      intros cur FB sp1 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc A B RR mc moc hc xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s6v s7v s8v s11v
             HNE HC HNDn HNA D HR RP BUD BUDF UW K; [congruence|].
    pose proof D as D0. gvA_open D. rt_facts.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    destruct (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (<- & HIN & HAL & HPOS & pre & nx & post & Hsz1 & Hsz2 & HNODE & _ & HNX0 & HC').
    unfold NAME_NEXT in HNX0, Hsz1. unfold NAME_SIZE in Hsz2, HIN.
    pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite Hsz2 in NB.
    pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HC') as NXB.
    apply List.NoDup_cons_iff in HNDn. destruct HNDn as [Hn1 HNDr].
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc cur 64 HHc HIN) as OCUR.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc _ HIN) as [_ CCE]. cbn [fst snd] in CCE.
    (* [comment removed for export] *)
    ddestruct (rw_cells_split3 asegs mc cur pre [C8 (Z_to_bv 64 nx)] post ltac:(exact HNODE)) as (_ & CNX & _). rewrite Hsz1 in CNX.
    clear HNODE.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite FREE; reflexivity).
    clear CNX.
    eapply (free_stepA R HIA) with (STKsi := STKsi) (hc := hc) (moc := moc) (mc := mc) (Lc := A ++ SNAME (rev (cur :: rest)) ++ B) (x := cur) (k := 64)
                                   (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (W := X0) (lo := lo);
      first [ exact D0 | exact UW | exact SLO | exact SLOS | exact SLOL
            | lazymatch goal with
              | |- In (cur, 64) _ => apply in_or_app; right; apply in_or_app; left; cbn [rev]; rewrite SNAME_app; apply in_or_app; right; left; reflexivity
              | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
              | |- havol _ _ _ _ + _ + _ <= _ => cbn [length] in BUD; unfold AVOL_CALL in *; clear - BUD; lia
              | |- hfr _ _ _ _ + _ + _ <= _ => cbn [length] in BUDF; unfold fr_charge in *; clear - BUDF Dnn; lia
              | |- forall a, _ -> outside X0 a => intros a Ha; cbn; split; [clear - Ha PPLO LOS SLO NS1 STKsi0 NRT; lia| split; [clear - Ha SGLO LOS SLO NS1 STKsi0 NRT; lia| exact I]]
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m1 mo1 h1, _ => idtac
              end
            | eassumption
            | match goal with |- ?g => idtac "CL-FREE-LEFT:" g end ].
    cbv beta. intros m1 mo1 h1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 G1 HPf.
    pose proof (in_node A B cur rest) as HINL.
    pose proof (rm_node A B cur rest (HNA cur (or_introl eq_refl)) Hn1) as ELc.
    rewrite ELc in G1.
    (* [comment removed for export] *)
    assert (HC1 : name_chain asegs (fun _ => True) m1 ((A ++ SNAME (rev rest) ++ B) ++ LB) nx rest).
    { replace ((A ++ SNAME (rev rest) ++ B) ++ LB) with (lb_remove cur ((A ++ SNAME (rev (cur :: rest)) ++ B) ++ LB)).
      2:{ rewrite lb_remove_app_l by exact HINL. rewrite ELc. reflexivity. }
      eapply (chain_presx asegs L _ _ _ mc m1 _ _ sp1 []);
        [ exact HC'
        | intros x Hx; apply In_lb_remove_keep'; [eapply (chain_nodes_in asegs); [exact HC'| exact Hx]| cbn; intros E; subst x; exact (Hn1 Hx)]
        | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPf)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]
        | unfold NAME_SIZE; clear; lia
        | intros x _; exact I ]. }
    pose proof (RP _ _ hc rest cur HR (or_introl eq_refl) Hn1 HHc HSc HPf) as HR1.
    clear HHc PRES STlo MIc SSc HPf D0 HC HC' OCUR.
    pose proof G1 as G1'. ddestruct G1' as (HH1 & HK1 & MF1 & HT1 & HS1 & _).
    pose proof (AIh_laws asegs R HIA h1) as LAWS1. pose proof (KF_kinv asegs R HIA h1 mo1) as KINV1.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      destruct rest as [|n2 r2]; [exfalso; cbn in HC1; subst nx; clear - KZ; cbv in KZ; lia|].
      intros moq [HKq MFq].
      eapply (IH nx FB sp1 (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc A B RR m1 moq h1);
        [ congruence | exact HC1 | exact HNDr | intros x Hx; apply HNA; right; exact Hx
        | eapply gvA_mo; [exact G1| exact HKq| exact MFq]
        | exact HR1
        | intros mX mY hX rest' x HRx Hx Hnr HHx HSx HPx; eapply RP; [exact HRx| right; exact Hx| exact Hnr| exact HHx| exact HSx| exact HPx]
        | cbn [length] in BUD |- *; unfold AVOL_CALL in *; clear - BUD; lia
        | cbn [length] in BUDF |- *; unfold fr_charge in *; clear - BUDF Dnn; lia
        | exact UW | ].
      intros mc' moc' hc' z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 sk' G' R'.
      eapply K; [| exact R']. eapply gvA_bud; [exact G'| cbn [length]; unfold AVOL_CALL; clear; lia| cbn [length]; unfold fr_charge; clear - Dnn; lia].
    - (* [comment removed for export] *)
      destruct rest as [|n2 r2].
      2:{ exfalso. pose proof (chain_uncons asegs _ _ _ _ _ _ _ _ HC1) as (-> & HIN2 & _ & HP2 & _).
          pose proof (blocks_below_hm R HIA h1 _ _ m1 _ HH1 ltac:(intros b Hb; exact Hb)) as BB1. destruct (BB1 _ HIN2) as [_ C2]. cbn [fst snd] in C2.
          first [change 18446744073709551615 with (Z.ones 64) in KZ; rewrite Z.land_ones in KZ by (clear; lia) | idtac].
          rewrite ?Z.mod_small in KZ by (clear - HP2 C2 ACV; lia). rewrite ?unsigned_lit in KZ by (clear - HP2 C2 ACV; lia).
          clear - KZ HP2. lia. }
      cbn in HC1. subst nx.
      (* [comment removed for export] *)
      intros moq [HKq MFq].
      eapply K; [| exact HR1].
      eapply gvA_bud; [eapply gvA_mo; [exact G1| exact HKq| exact MFq]| cbn [length]; unfold AVOL_CALL; clear; lia| cbn [length]; unfold fr_charge; clear - Dnn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L14282995869.18 L17905066372.8  L17991598320.218L31437125803.6  L38087549238.18 L39124720301.8  L40228640085.0  L43139178913.0  L44984951545.4  L46425563800.239L47028033785.219L5367532848.1   L59308633593.1  L59310680273.3  L5966946069.6   L65005791566.3  L68237972690.2  Q25019582490.223Q29612090062.223Q32352309670.224Q47700973017.224Q47713708799.223Q61338516829.22400000W01502C02X03>03V03W03X03c04m06306906=06H06_06g07007`08P0:K0;;0;k0<[S1R3HIA5STKsi1h2sp3SIG2lo4SGLO3SLO1a2HaS1R3HIA1h1d4rest4FFRa4BUDF3DnnS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC4HPOS3pre2nx4post2NBS1R3HIA1h2r24PHIa3BUDS1R3HIA5STKsi1h2sp2PP2lo4PPLO3SLO1a2HaS1R3HIA1h1d2r24FFRa4BUDFSSS1d2r24FFRaS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC3pre2nx4post3NXBS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB4rest3cur2FB3sp13sgc3SZC3pre2nx4postS4PHIaS2KZS2n22KZ3HP2S1R3HIA1h4rest4PHIa3BUDS1d4FFRaS2r24PHIaS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3LOS4rest3cur2FB3sp13sgc3SP14SP1M3SZC3ALO3ACV3SPR3HAL4HPOS3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4postS1R5STKsi2LF2bs3LFB4rest3cur3sgc3SZC3pre2nx4post". (* [comment removed for export] *)
  #[using="IMG NS1 HMND FREE STKsi LFB PP0 CWP PPLO BIN SG0 CWS SGLO DA0 CRDA DALO SLOS SLOL SLO TOP SPA TPV LOS"] Lemma CL1 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_G ()) "Pnodes,(1.$0.)Pcur,$0.PFB,$0.Psp1,$0.PPHIa,$0.PFFRa,$0.Pw0,(3.&40.)Pw1,(3.&40.)Pw2,(3.&40.)Plw,(3.&40.)Pb4,(3.&8.)Pk0,(3.&40.)Pk8,(3.&40.)Pk16,(3.&40.)Pk24,(3.&40.)Pj32,(1.(3.&8.))Pp,$0.Psgc,(1.$4.)PA,(1.$5.)PB,(1.$5.)PRR,P,P,(3.&40.)(6.(3.&8.))P,(1.$5.)SpPmc,P,(3.&40.)(6.(3.&8.))Pmoc,$7.Phc,(8.$9.VR,VHIA,)Pxra,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Ps4v,(3.&40.)Ps5v,(3.&40.)Ps6v,(3.&40.)Ps7v,(3.&40.)Ps8v,(3.&40.)Ps11v,(3.&40.)P,(>.(?.(1.$0.)R2=.(10.$0.)))P,(11.$9.L,(1.$4.)$12.R19.(13.$5.(13.$5.R1<.(13.$5.(14.(15.$0.R2>.))R1;.))VLB,)R2=.R2>.)P,(16.$0.R2?.)P,Px,$0.P,(17.$0.R1.R31.)(>.(17.$0.R2.(18.(19.$0.$0.)$0.(1:.$0.$0.)R20.)))P,(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R2?.R2>.(1;.(19.$0.$0.)(1<.$0.$0.VPP,(1=.VPP,+8.))(1;.(19.$0.$0.)(1<.$0.$0.VSIG,(1=.VSIG,+<8.))(10.(19.$0.$0.))))R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(13.$5.R1?.(13.$5.(14.(15.$0.R31.))R1>.))R1<.R1;.R1:.)P,A2.R1>.R1=.(13.$5.R20.(13.$5.(14.(15.$0.R32.))R1?.))P,PmX,P,(3.&40.)(6.(3.&8.))PmY,P,(3.&40.)(6.(3.&8.))PhX,(8.$9.VR,VHIA,)Prest',(1.$0.)Px,$0.P,A2.R24.R5.(13.$5.R26.(13.$5.(14.(15.$0.(1;.$0.R1.R2.)))R25.))P,(17.$0.R2.R39.)P,(>.(17.$0.R3.R4.))P,(1>.$9.VR,VHIA,R6.(13.$5.(13.$5.R29.(13.$5.(14.(15.$0.(1;.$0.R4.R5.)))R28.))VLB,)(1;.(19.$0.$0.)(1<.$0.$0.R39.+40.)VLF,)R8.)P,(?.$0.(1?.$9.VR,VHIA,R7.)(1?.$9.VR,VHIA,Vh,))P,(20.$9.VR,(21.R6.(13.$5.(13.$5.R2;.(13.$5.(14.(15.$0.(1;.$0.R6.R7.)))R2:.))VLB,))(1;.(19.$0.$0.)(1<.$0.$0.R3;.+40.)VLF,)R3:.(22.VR,)(1?.$9.VR,VHIA,R8.)(10.$2.)R:.R9.)A2.R2:.R:.(13.$5.R2<.(13.$5.(14.(15.$0.R8.))R2;.))P,(=.(1=.(1=.(23.$9.VR,VHIA,Vh,)R30.)(24.(25.(26.$0.R34.))$27.))$28.)P,(=.(1=.(1=.(29.$9.VR,VHIA,Vh,)R30.)(24.(25.(26.$0.R35.))(2:.(1=.Vd,+1.))))$2;.)P,(2<.$9.Vm,(22.VR,)(1?.$9.VR,VHIA,Vh,)(2=.&40.Vs0,)(2=.&40.Vsp,)Vd,)P,Pmc',P,(3.&40.)(6.(3.&8.))Pmoc',$7.Phc',(8.$9.VR,VHIA,)Py0,(3.&40.)Py1,(3.&40.)Py2,(3.&40.)Pya0,(3.&40.)Pya1,(3.&40.)Pya2,(3.&40.)Pya3,(3.&40.)Pya4,(3.&40.)Pya5,(3.&40.)Pya6,(3.&40.)Pya7,(3.&40.)Py3,(3.&40.)Py4,(3.&40.)Py5,(3.&40.)Py6,(3.&40.)Ps7',(3.&40.)P,(:.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R48.R47.(1;.(19.$0.$0.)(1<.$0.$0.VPP,(1=.VPP,+8.))(1;.(19.$0.$0.)(1<.$0.$0.VSIG,(1=.VSIG,+<8.))(10.(19.$0.$0.))))(1=.R46.(24.(25.(26.$0.R4:.))$27.))(1=.R45.(24.(25.(26.$0.R4:.))(2:.(1=.Vd,+1.))))R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.(13.$5.R38.R37.)R13.R12.R11.)P,A2.R37.R14.(13.$5.R39.R38.)(2>.$9.(2?.$9.VR,VHIA,(30.VPHIsi,VCNTsi,)(31.VFFRsi,VCNTsi,)(32.VCNTsi,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VSIG,VDALG,(33.VEND,VP,)Vlo,Vslo,Vd,Vdtg,Vdpad,Vdlen,Vdq,Vm,Vmo0,)(34.(35.(36.(37.&40.+98=50.)(37.&40.R49.)Vgp,Vtp,R12.R11.R10.Vsp,(37.&40.R49.)R?.R>.R=.R<.R;.R:.R9.R8.(37.&40.R4:.)R25.R23.R24.R3.(37.&40.(38.(39.VR,)))R21.(37.&40.R4:.)(37.&40.(1=.(3:.R4:.+3.)(38.(39.VR,))))R20.R7.R6.R5.R4.)VF,(37.&40.+98=58.)Vfc,(3;.(3.&40.))R15.(3<.$9.))R14.))(2>.$9.(2?.$9.VR,VHIA,(30.VPHIsi,VCNTsi,)(31.VFFRsi,VCNTsi,)(32.VCNTsi,)Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VSIG,VDALG,(33.VEND,VP,)Vlo,Vslo,Vd,Vdtg,Vdpad,Vdlen,Vdq,Vm,Vmo0,)(34.(35.(36.R20.(37.&40.R35.)Vgp,Vtp,R1?.R1>.R1=.Vsp,(37.&40.R35.)(37.&40.R37.)R1<.R1;.R1:.R19.R18.R17.R16.(37.&40.R36.)R11.R?.R10.R>.(37.&40.(38.(39.VR,)))R=.(37.&40.R36.)(37.&40.(1=.(3:.R36.+3.)(38.(39.VR,))))R<.R15.R14.R13.R12.)VF,(37.&40.+98=2<.)Vfc,(3;.(3.&40.))R23.(3<.$9.))R22.))")
(* [comment removed for export] *).
  Proof.
    intros nodes. induction nodes as [|n1 rest IH];
      intros cur FB sp1 PHIa FFRa w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc A B RR mc moc hc xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s6v s7v s8v s11v
             HNE HC HNDn HNA D HR RP BUD BUDF UW K; [congruence|].
    pose proof D as D0. gvA_open D. rt_facts.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as Dnn.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    destruct (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (<- & HIN & HAL & HPOS & pre & nx & post & Hsz1 & Hsz2 & HNODE & _ & HNX0 & HC').
    unfold NAME_NEXT in HNX0, Hsz1. unfold NAME_SIZE in Hsz2, HIN.
    pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite Hsz2 in NB.
    pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HC') as NXB.
    apply List.NoDup_cons_iff in HNDn. destruct HNDn as [Hn1 HNDr].
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc cur 64 HHc HIN) as OCUR.
    pose proof (blocks_below_hm R HIA hc _ _ mc _ HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc _ HIN) as [_ CCE]. cbn [fst snd] in CCE.
    (* [comment removed for export] *)
    ddestruct (rw_cells_split3 asegs mc cur pre [C8 (Z_to_bv 64 nx)] post ltac:(exact HNODE)) as (_ & CNX & _). rewrite Hsz1 in CNX.
    clear HNODE.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite FREE; reflexivity).
    clear CNX.
    eapply (free_stepA R HIA) with (STKsi := STKsi) (hc := hc) (moc := moc) (mc := mc) (Lc := A ++ SNAME (rev (cur :: rest)) ++ B) (x := cur) (k := 64)
                                   (PHIa := PHIa) (FFRa := FFRa) (slo := slo) (d := d) (W := X0) (lo := lo);
      first [ exact D0 | exact UW | exact SLO | exact SLOS | exact SLOL
            | lazymatch goal with
              | |- In (cur, 64) _ => apply in_or_app; right; apply in_or_app; left; cbn [rev]; rewrite SNAME_app; apply in_or_app; right; left; reflexivity
              | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
              | |- havol _ _ _ _ + _ + _ <= _ => cbn [length] in BUD; unfold AVOL_CALL in *; clear - BUD; lia
              | |- hfr _ _ _ _ + _ + _ <= _ => cbn [length] in BUDF; unfold fr_charge in *; clear - BUDF Dnn; lia
              | |- forall a, _ -> outside X0 a => intros a Ha; cbn; split; [clear - Ha PPLO LOS SLO NS1 STKsi0 NRT; lia| split; [clear - Ha SGLO LOS SLO NS1 STKsi0 NRT; lia| exact I]]
              | |- 0 <= _ < 2 ^ 64 => clear; lia
              | |- _ mod 2 = 0 => reflexivity
              | |- forall m1 mo1 h1, _ => idtac
              end
            | eassumption
            | match goal with |- ?g => idtac "CL-FREE-LEFT:" g end ].
    cbv beta. intros m1 mo1 h1 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 G1 HPf.
    pose proof (in_node A B cur rest) as HINL.
    pose proof (rm_node A B cur rest (HNA cur (or_introl eq_refl)) Hn1) as ELc.
    rewrite ELc in G1.
    (* [comment removed for export] *)
    assert (HC1 : name_chain asegs (fun _ => True) m1 ((A ++ SNAME (rev rest) ++ B) ++ LB) nx rest).
    { replace ((A ++ SNAME (rev rest) ++ B) ++ LB) with (lb_remove cur ((A ++ SNAME (rev (cur :: rest)) ++ B) ++ LB)).
      2:{ rewrite lb_remove_app_l by exact HINL. rewrite ELc. reflexivity. }
      eapply (chain_presx asegs L _ _ _ mc m1 _ _ sp1 []);
        [ exact HC'
        | intros x Hx; apply In_lb_remove_keep'; [eapply (chain_nodes_in asegs); [exact HC'| exact Hx]| cbn; intros E; subst x; exact (Hn1 Hx)]
        | eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HPf)| intros b Hb; apply in_or_app; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]
        | unfold NAME_SIZE; clear; lia
        | intros x _; exact I ]. }
    pose proof (RP _ _ hc rest cur HR (or_introl eq_refl) Hn1 HHc HSc HPf) as HR1.
    clear HHc PRES STlo MIc SSc HPf D0 HC HC' OCUR.
    pose proof G1 as G1'. ddestruct G1' as (HH1 & HK1 & MF1 & HT1 & HS1 & _).
    pose proof (AIh_laws asegs R HIA h1) as LAWS1. pose proof (KF_kinv asegs R HIA h1 mo1) as KINV1.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      destruct rest as [|n2 r2]; [exfalso; cbn in HC1; subst nx; clear - KZ; cbv in KZ; lia|].
      intros moq [HKq MFq].
      eapply (IH nx FB sp1 (PHIa + AVOL_CALL) (FFRa + fr_charge (d + 1)) w0 w1 w2 lw b4 k0 k8 k16 k24 j32 p sgc A B RR m1 moq h1);
        [ congruence | exact HC1 | exact HNDr | intros x Hx; apply HNA; right; exact Hx
        | eapply gvA_mo; [exact G1| exact HKq| exact MFq]
        | exact HR1
        | intros mX mY hX rest' x HRx Hx Hnr HHx HSx HPx; eapply RP; [exact HRx| right; exact Hx| exact Hnr| exact HHx| exact HSx| exact HPx]
        | cbn [length] in BUD |- *; unfold AVOL_CALL in *; clear - BUD; lia
        | cbn [length] in BUDF |- *; unfold fr_charge in *; clear - BUDF Dnn; lia
        | exact UW | ].
      intros mc' moc' hc' z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 sk' G' R'.
      eapply K; [| exact R']. eapply gvA_bud; [exact G'| cbn [length]; unfold AVOL_CALL; clear; lia| cbn [length]; unfold fr_charge; clear - Dnn; lia].
    - (* [comment removed for export] *)
      destruct rest as [|n2 r2].
      2:{ exfalso. pose proof (chain_uncons asegs _ _ _ _ _ _ _ _ HC1) as (-> & HIN2 & _ & HP2 & _).
          pose proof (blocks_below_hm R HIA h1 _ _ m1 _ HH1 ltac:(intros b Hb; exact Hb)) as BB1. destruct (BB1 _ HIN2) as [_ C2]. cbn [fst snd] in C2.
          first [change 18446744073709551615 with (Z.ones 64) in KZ; rewrite Z.land_ones in KZ by (clear; lia) | idtac].
          rewrite ?Z.mod_small in KZ by (clear - HP2 C2 ACV; lia). rewrite ?unsigned_lit in KZ by (clear - HP2 C2 ACV; lia).
          clear - KZ HP2. lia. }
      cbn in HC1. subst nx.
      
      intros moq [HKq MFq].
      eapply K; [| exact HR1].
      eapply gvA_bud; [eapply gvA_mo; [exact G1| exact HKq| exact MFq]| cbn [length]; unfold AVOL_CALL; clear; lia| cbn [length]; unfold fr_charge; clear - Dnn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
