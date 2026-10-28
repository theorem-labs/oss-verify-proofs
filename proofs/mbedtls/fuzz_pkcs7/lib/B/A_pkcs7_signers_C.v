(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_pkcs7_signers_C () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_chain"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_blocks"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.NAME_SIZE"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "Walk.CNTs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "Walk.SINV"; "Walk.PHIs"; "Walk.FFRs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_junk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Walk.Call.gvA"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_cells"; "Stdlib.Sorting.Permutation.Permutation"; "RocqVerifyHarness.AgentSubmission.Spec.CrtStmts.SNAME"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_crt_parse_stmts.pkcs7_getsigners_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.to_nat"].


Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

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
  (* [comment removed for export] *)
  Hypothesis PHIsi_sadd : forall a b, 0 <= a -> 0 <= b -> PHIsi a + PHIsi b <= PHIsi (a + b).
  Hypothesis FFRsi_sadd : forall a b d, 0 <= a -> 0 <= b -> FFRsi a d + FFRsi b d <= FFRsi (a + b) d.
  Hypothesis CNTsi_sadd : forall a b, 0 <= a -> 0 <= b -> CNTsi a + CNTsi b <= CNTsi (a + b).
  Hypothesis STKsi0 : 0 <= STKsi.
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  (* [comment removed for export] *)
  Local Notation STKs := (A_pkcs7_signers_A.STKs R STKsi).

  (* [comment removed for export] *)
  #[using="Type"] Lemma signer_chain_presx0 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "Pm1,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PL1,(2.$3.)PL2,(2.$3.)PSP,$4.PX,(2.$5.)Pa,$4.Pl,(2.(6.$4.(2.$4.)))P,(7.$8.R8.R6.R2.R1.)P,Pb,$3.P,(9.$3.R1.(:.R3.))(9.$3.R2.R8.)P,(;.$8.(<.VR,)R7.R6.R5.R:.R9.)P,Pb,$3.P,(9.$3.R1.(:.R5.))P,(=.=(>.$4.$4.R2.))(?.R9.(10.$4.$4.R3.)(>.$4.$4.R3.))(7.$8.R;.R9.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros m1 m' L1 L2 SP X a l. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H HIN HP HDJ; [exact H|].
    ddestruct H as (-> & Hin & Hal & Hpos & inext & nxt & j & HR & HN & HC).
    assert (Hin2 : In (a', SIGNER_SIZE) L2) by (apply HIN; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    split; [reflexivity|]. split; [exact Hin2|]. split; [exact Hal|]. split; [exact Hpos|].
    dexists inext, nxt, j. split; [| split].
    - eapply heap_presx_rw_cells; [exact HP| exact HR| |].
      + eapply client_range_block; [exact Hin2| lia| cbn [cells_size csize Nat.add signer_cells]; unfold SIGNER_SIZE; lia].
      + cbn [cells_size csize Nat.add signer_cells]. apply (HDJ (a', SIGNER_SIZE)); [| unfold SIGNER_SIZE; cbn; lia].
        apply in_or_app; left. apply in_or_app; right. left. reflexivity.
    - eapply chain_presx; [exact HN| | exact HP| unfold NAME_SIZE; lia|].
      + intros x Hx. apply HIN. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
      + intros x Hx. apply (HDJ (x, NAME_SIZE)); [| unfold NAME_SIZE; cbn; lia]. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
    - eapply IH; [exact HC| | exact HP|].
      + intros b Hb. apply HIN. apply in_or_app; right. exact Hb.
      + intros b Hb Hk. apply HDJ; [| exact Hk]. apply in_or_app; right. exact Hb.
  Qed.

  #[using="Type"] Lemma name_chain_presx0 : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "Pm1,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PL1,(2.$3.)PL2,(2.(6.$4.$4.))PSP,$4.PX,(2.$5.)Pa,$4.Pnames,(2.$4.)P,(11.$8.L,(2.$12.)$13.R8.R6.R2.R1.)P,Px,$4.P,(9.$4.R1.R3.)(9.(6.$4.$4.)(14.$4.$4.R2.$15.)R8.)P,(;.$8.(<.VR,)R7.R6.R5.R:.R9.)P,Px,$4.P,(9.$4.R1.R5.)(?.R8.R2.$15.)(11.$8.L,(2.$12.)$13.R;.R9.R6.R5.)")
(* [comment removed for export] *).
  Proof. intros. eapply chain_presx; [eassumption| eassumption| eassumption| unfold NAME_SIZE; lia| assumption]. Qed.

  (* [comment removed for export] *)
  Definition CNTs (n : Z) : Z := CNTsi n + n / 2 + 1.
  Definition PHIs (n : Z) : Z := PHIsi n + (n / 2 + 1) * (2 * 200 + 2 * AVOL_CALL) + (CNTs n + 1) * AVOL_CALL.
  Definition FFRs (n d : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "(16.(16.A2.VFFRsi,O2.(16.O1.+1.)(17.(16.(18.O2.+2.)+2.)(19.=(1:.(16.O1.+1.)))))(17.(16.(1;.O2.)+1.)(19.=(1:.(16.O1.+1.)))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition SINV (d c cnt PHIa FFRa nLc : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "(1<.(1=.=O5.)(1<.(1=.=O4.)(1<.(1=.(17.+2.O4.)O5.)(1<.(1=.O3.(16.A1.VPHIsi,O5.(17.O4.(16.(17.+2.+<8.)(17.+2.$1>.)))))(1<.(1=.O2.(16.A2.VFFRsi,O5.(16.O6.+1.)(17.O4.(1:.(16.O6.+1.)))))(1=.O1.(16.A1.VCNTsi,O5.O4.)))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma half_le : forall cnt c n, 2 * cnt <= c -> c <= n -> cnt <= n / 2.
  Proof. intros cnt c n0 H1 H2. apply Z.div_le_lower_bound; [clear; lia| clear - H1 H2; lia]. Qed.

  (* [comment removed for export] *)
  #[using="PHIsi_sadd FFRsi_sadd CNTsi_sadd"] Lemma sinv_step : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "Pd,$4.Pc,$4.Pcnt,$4.PPHIa,$4.PFFRa,$4.PnLc,$4.Pc2,$4.PPHIx,$4.PFFRx,$4.Pk,$4.P,(1=.=R:.)P,(1?.R;.R:.R9.R8.R7.R6.)P,(1=.+2.R6.)P,(1=.R6.A1.VPHIsi,R7.)P,(1=.R6.A2.VFFRsi,R8.(16.R>.+1.))P,(1=.R6.A1.VCNTsi,R9.)(1?.R10.(16.R?.R:.)(16.R>.+1.)(16.(16.R=.(16.(17.+2.+<8.)$1>.))R9.)(16.(16.R<.(1:.(16.R10.+1.)))R8.)(16.(16.R7.+1.)R;.))")
(* [comment removed for export] *).
  Proof.
    (intros d0 c cnt PHIa FFRa nLc c2 PHIx FFRx k Dnn dd_H; ddestruct dd_H as (C0 & N0 & H2 & HP & HF & HC); intros HC2 PX FX KX).
    pose proof (PHIsi_sadd c c2 ltac:(clear - C0; lia) ltac:(clear - HC2; lia)) as S1. pose proof (FFRsi_sadd c c2 (d0 + 1) ltac:(clear - C0; lia) ltac:(clear - HC2; lia)) as S2.
    pose proof (CNTsi_sadd c c2 ltac:(clear - C0; lia) ltac:(clear - HC2; lia)) as S3.
    unfold SINV, AVOL_CALL, fr_charge. clear - Dnn C0 N0 H2 HP HF HC HC2 PX FX KX S1 S2 S3. unfold AVOL_CALL, fr_charge in *. repeat split; lia.
  Qed.

  #[using="PHIsi_mono FFRsi_mono CNTsi_mono"] Lemma sinv_zero : forall d, 0 <= d -> SINV d 0 0 0 0 0.
  Proof.
    intros d0 Dnn. pose proof (PHIsi_mono 0 0 ltac:(clear; lia)) as M2. pose proof (FFRsi_mono 0 0 (d0 + 1) ltac:(clear; lia)) as M3. pose proof (CNTsi_mono 0 0 ltac:(clear; lia)) as M4.
    unfold SINV. clear - Dnn M2 M3 M4. unfold AVOL_CALL, fr_charge. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PHIsi_mono FFRsi_mono CNTsi_mono"] Lemma sinv_head : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "Pd,$4.Pc,$4.Pc1,$4.PPHIx,$4.PFFRx,$4.Pk,$4.P,(1=.=R6.)P,(1=.+2.R5.)P,(1=.R6.R7.)P,(1=.R6.A1.VPHIsi,R7.)P,(1=.R6.A2.VFFRsi,R8.(16.R:.+1.))P,(1=.R6.A1.VCNTsi,R9.)(1?.R<.R;.+1.(16.=R9.)(16.=R8.)R7.)")
(* [comment removed for export] *).
  Proof.
    intros d0 c c1 PHIx FFRx k Dnn C1 C2 PX FX KX.
    pose proof (PHIsi_mono c1 c ltac:(clear - C1 C2; lia)) as M2. pose proof (FFRsi_mono c1 c (d0 + 1) ltac:(clear - C1 C2; lia)) as M3. pose proof (CNTsi_mono c1 c ltac:(clear - C1 C2; lia)) as M4.
    unfold SINV. clear - Dnn C1 C2 PX FX KX M2 M3 M4. unfold AVOL_CALL, fr_charge. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PHIsi_mono FFRsi_mono CNTsi_mono PHIsi_sadd FFRsi_sadd"] Lemma sinv_bounds : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "Pd,$4.Pc,$4.Pcnt,$4.PPHIa,$4.PFFRa,$4.PnLc,$4.PNB,$4.P,(1=.=R7.)P,(1?.R8.R7.R6.R5.R4.R3.)P,(1=.R8.R3.)(1<.(1=.(16.R5.+1.)(1;.R4.))Prest,$4.P,(1=.=R1.)P,(1=.(16.R;.R2.)R6.)(1<.(1=.(16.(16.(16.R:.(16.(17.+2.+<8.)(17.+2.$1>.)))A1.VPHIsi,R3.)(17.(16.(1;.R7.)+1.)$1>.))(20.R7.))(1=.(16.(16.(16.R9.(17.+2.(1:.(16.R=.+1.))))A2.VFFRsi,R3.(16.R=.+1.))(17.(16.(1;.R7.)+1.)(1:.(16.R=.+1.))))(21.R7.R=.))))")
(* [comment removed for export] *).
  Proof.
    (intros d0 c cnt PHIa FFRa nLc NB0 Dnn dd_H; ddestruct dd_H as (C0 & N0 & H2 & HP & HF & HC); intros CN).
    pose proof (half_le cnt c NB0 H2 CN) as HL.
    pose proof (CNTsi_mono c NB0 ltac:(clear - C0 CN; lia)) as M4.
    split; [unfold CNTs; clear - HC HL M4; lia|].
    intros rest R0 RN.
    pose proof (PHIsi_sadd c rest C0 R0) as S1. pose proof (FFRsi_sadd c rest (d0 + 1) C0 R0) as S2.
    pose proof (PHIsi_mono (c + rest) NB0 ltac:(clear - C0 R0 RN; lia)) as M2. pose proof (FFRsi_mono (c + rest) NB0 (d0 + 1) ltac:(clear - C0 R0 RN; lia)) as M3.
    unfold PHIs, FFRs. unfold CNTs. clear - Dnn C0 N0 H2 HP HF HC CN HL M2 M3 M4 S1 S2. unfold AVOL_CALL, fr_charge in *. rewrite !Z.max_r by lia.
    set (q := NB0 / 2) in *.
    assert (M1 : cnt * (d0 + 1 + 3) <= q * (d0 + 1 + 3)) by (clear - HL Dnn N0; nia).
    split; [lia|]. lia.
  Qed.

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
  Local Notation POST := (pkcs7_getsigners_postA asegs R HIA PHIs FFRs CNTs h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END SIG DALG NB lo slo d dtg dpad dlen dq m mo0).
  Local Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].

  (* [comment removed for export] *)
  Definition gvA (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "(1<.(22.$8.VR,VHIA,O1.(23.$3.O4.VLB,)(24.(6.$4.$4.)(14.$4.$4.O15.+40.)VLF,)O3.)(1<.(25.$8.VR,VHIA,O1.O2.)(1<.(26.Vmo0,O2.)(1<.(27.$4.(28.$8.VR,VHIA,O1.)(28.$8.VR,VHIA,Vh,))(1<.(27.$4.(29.$8.VR,VHIA,O1.)(29.$8.VR,VHIA,Vh,))(1<.(27.$4.(2:.$8.VR,VHIA,O1.)(2:.$8.VR,VHIA,Vh,))(1<.Px,$4.P,(2;.$8.VR,VHIA,Vh,R1.)(2;.$8.VR,VHIA,O1.R2.)(1<.(1=.(2<.$8.VR,VHIA,O1.)(16.(2<.$8.VR,VHIA,Vh,)O12.))(1<.(1=.(2=.$8.VR,VHIA,O1.)(16.(2=.$8.VR,VHIA,Vh,)O11.))(1<.(2>.$8.VR,VHIA,Vh,VLB,VLF,(2?.&40.Vsp,)(2?.&40.Vsp,)O13.Vm,O3.)(1<.(1<.(1=.(30.(2?.&40.Vsp,)+;0.)O14.)(1=.O14.(30.(2?.&40.Vsp,)+:0.)))(1<.(27.$4.(31.O14.+20.)=)(1<.(27.$4.(31.O15.+40.)=)(1<.(32.VR,VLB,VLF,O15.+40.)(1<.(33.(2;.$8.VR,VHIA,Vh,)O15.+40.)(1<.(34.$8.O3.O15.(24.$12.(35.O10.)(24.$12.(35.O?.)(24.$12.(35.O>.)(36.$12.)))))(1<.(34.$8.O3.(16.O15.+20.)(24.$12.(35.O=.)(36.$12.)))(1<.(34.$8.O3.(16.(37.O15.+3.)(38.(39.VR,)))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.O<.)(24.$12.(3:.(3;.&8.+?3.))(24.$12.(3:.(3;.&8.+?3.))(24.$12.(3:.(3;.&8.+?3.))(36.$12.))))))))))(1<.(34.$8.O3.(16.(2?.&40.Vsp,)-68.)(24.$12.(35.Vs11,)(24.$12.(35.Vs10,)(24.$12.(35.Vs9,)(24.$12.(35.Vs8,)(24.$12.(35.Vs7,)(24.$12.(35.Vs6,)(24.$12.(35.Vs5,)(24.$12.(35.Vs4,)(24.$12.(35.Vs3,)(24.$12.(35.Vs2,)(24.$12.(35.Vs1,)(24.$12.(35.Vs0,)(24.$12.(35.Vra,)(36.$12.)))))))))))))))(1<.(34.$8.O3.O14.(24.$12.(35.O;.)(24.$12.(35.O:.)(24.$12.(35.O9.)(24.$12.(35.O8.)(24.$12.(3<.#10.O7.)(24.$12.(35.(3;.&40.O15.))(36.$12.))))))))(1<.(3=.$8.O3.(16.O14.+38.)(16.(2?.&40.Vsp,)-68.))(1<.(3=.$8.O3.Vlo,O14.)(1<.(34.$8.O3.VPP,(24.$12.(35.(3;.&40.O6.))(36.$12.)))(1<.(1<.(1=.VP,O6.)(1=.O6.VEND,))(1<.(34.$8.O3.VSIG,O5.)(1<.(27.$3>.(3?.O5.)#<8.)(1<.(34.$8.O3.VDALG,(40.Vdtg,Vdpad,Vdlen,Vdq,))(1<.(41.$8.O3.VBUF,Vbs,)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VPP,+8.)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VSIG,+<8.)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VDALG,+18.)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VBUF,(43.(44.(0.&8.)Vbs,)))(1<.(45.$8.O3.)(46.$8.(39.VR,)O3.Vslo,(2?.&40.Vsp,)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
  Definition gvA_x (fx : Z) (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 k16 k24 : word) (j32 : list byte)
      (p : Z) (sgc : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "(1<.(22.$8.VR,VHIA,O1.(23.$3.O4.VLB,)(24.(6.$4.$4.)(14.$4.$4.O15.+40.)VLF,)O3.)(1<.(25.$8.VR,VHIA,O1.O2.)(1<.(26.Vmo0,O2.)(1<.(27.$4.(28.$8.VR,VHIA,O1.)(28.$8.VR,VHIA,Vh,))(1<.(27.$4.(29.$8.VR,VHIA,O1.)(29.$8.VR,VHIA,Vh,))(1<.(27.$4.(2:.$8.VR,VHIA,O1.)(2:.$8.VR,VHIA,Vh,))(1<.Px,$4.P,(2;.$8.VR,VHIA,Vh,R1.)(2;.$8.VR,VHIA,O1.R2.)(1<.(1=.(2<.$8.VR,VHIA,O1.)(16.(2<.$8.VR,VHIA,Vh,)O12.))(1<.(1=.(2=.$8.VR,VHIA,O1.)(16.(2=.$8.VR,VHIA,Vh,)O11.))(1<.(2>.$8.VR,VHIA,Vh,VLB,VLF,(2?.&40.Vsp,)(2?.&40.Vsp,)O13.Vm,O3.)(1<.(1<.(1=.(30.(2?.&40.Vsp,)(16.+;0.O16.))O14.)(1=.O14.(30.(2?.&40.Vsp,)(16.+:0.O16.))))(1<.(27.$4.(31.O14.+20.)=)(1<.(27.$4.(31.O15.+40.)=)(1<.(32.VR,VLB,VLF,O15.+40.)(1<.(33.(2;.$8.VR,VHIA,Vh,)O15.+40.)(1<.(34.$8.O3.O15.(24.$12.(35.O10.)(24.$12.(35.O?.)(24.$12.(35.O>.)(36.$12.)))))(1<.(34.$8.O3.(16.O15.+20.)(24.$12.(35.O=.)(36.$12.)))(1<.(34.$8.O3.(16.(37.O15.+3.)(38.(39.VR,)))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.(3;.&8.+?1.))(24.$12.(3:.O<.)(24.$12.(3:.(3;.&8.+?3.))(24.$12.(3:.(3;.&8.+?3.))(24.$12.(3:.(3;.&8.+?3.))(36.$12.))))))))))(1<.(34.$8.O3.(16.(2?.&40.Vsp,)-68.)(24.$12.(35.Vs11,)(24.$12.(35.Vs10,)(24.$12.(35.Vs9,)(24.$12.(35.Vs8,)(24.$12.(35.Vs7,)(24.$12.(35.Vs6,)(24.$12.(35.Vs5,)(24.$12.(35.Vs4,)(24.$12.(35.Vs3,)(24.$12.(35.Vs2,)(24.$12.(35.Vs1,)(24.$12.(35.Vs0,)(24.$12.(35.Vra,)(36.$12.)))))))))))))))(1<.(34.$8.O3.O14.(24.$12.(35.O;.)(24.$12.(35.O:.)(24.$12.(35.O9.)(24.$12.(35.O8.)(24.$12.(3<.(58.(16.+10.O16.))O7.)(24.$12.(35.(3;.&40.O15.))(36.$12.))))))))(1<.(3=.$8.O3.(16.O14.(16.+38.O16.))(16.(2?.&40.Vsp,)-68.))(1<.(3=.$8.O3.Vlo,O14.)(1<.(34.$8.O3.VPP,(24.$12.(35.(3;.&40.O6.))(36.$12.)))(1<.(1<.(1=.VP,O6.)(1=.O6.VEND,))(1<.(34.$8.O3.VSIG,O5.)(1<.(27.$3>.(3?.O5.)#<8.)(1<.(34.$8.O3.VDALG,(40.Vdtg,Vdpad,Vdlen,Vdq,))(1<.(41.$8.O3.VBUF,Vbs,)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VPP,+8.)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VSIG,+<8.)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VDALG,+18.)(1<.(42.$8.(39.VR,)(2;.$8.VR,VHIA,Vh,)O3.VBUF,(43.(44.(0.&8.)Vbs,)))(1<.(45.$8.O3.)(46.$8.(39.VR,)O3.Vslo,(2?.&40.Vsp,)))))))))))))))))))))))))))))))))))").
  Definition gvA_sg := gvA_x 32.
  #[using="Type"] Lemma gvA_x0 : gvA_x 0 = gvA.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma gvA_x32 : gvA_x 32 = gvA_sg.
  Proof. reflexivity. Qed.

  Ltac gvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKsi LFB PP0 CWP PPLO DPB SG0 CWS SGLO DSB DA0 CRDA DALO D1 D2 D3 SLOS SLOL SLO TOP SPH LOS"] Lemma ret_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_C ()) "PFB,$4.Psp1,$4.PW,(2.$5.)PPHIa,$4.PFFRa,$4.Pw0,(0.&40.)Pw1,(0.&40.)Pw2,(0.&40.)Plw,(0.&40.)Pb4,(0.&8.)Pk0,(0.&40.)Pk8,(0.&40.)Pk16,(0.&40.)Pk24,(0.&40.)Pj32,(2.(0.&8.))Pp,$4.Pinext,$4.Psnext,$4.Psj',$47.Pnames0,(2.$4.)Psg,(2.(6.$4.(2.$4.)))PLc,(2.$3.)Pmc,P,(0.&40.)(1.(0.&8.))Pmoc,$48.Phc,(49.$8.VR,VHIA,)Pr,$4.Pxra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ps3v,(0.&40.)Ps5v,(0.&40.)Ps6v,(0.&40.)Ps7v,(0.&40.)Ps8v,(0.&40.)Ps11v,(0.&40.)P,(4:.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(4;.R20.R1?.R1>.)R1;.R1:.R19.R18.)P,(11.$8.L,(2.$12.)$13.R1;.(23.$3.R1<.VLB,)R21.R1>.)P,(7.$8.R1<.(23.$3.R1=.VLB,)R21.R1>.)P,(4<.$3.R1>.(23.$3.(4=.R20.)(:.R1?.)))P,(1=.(43.(44.$3.R1?.))(1;.(30.VEND,VP,)))P,(1=.R32.(20.(30.VEND,VP,)))P,(1=.R32.(21.(30.VEND,VP,)Vd,))P,Px,$4.P,(4>.(24.(6.$4.$4.)(14.$4.$4.VPP,(16.VPP,+8.))(24.(6.$4.$4.)(14.$4.$4.VSIG,(16.VSIG,+<8.))(36.(6.$4.$4.))))R1.)(4>.R37.R2.)P,(1<.(=.(4?.(50.+2.+1?.))R1?.)(=.R1?.(50.+2.+1?.)))(51.$8.(52.$8.VR,VHIA,$20.$21.$1;.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VSIG,VDALG,(30.VEND,VP,)Vlo,Vslo,Vd,Vdtg,Vdpad,Vdlen,Vdq,Vm,Vmo0,)(53.(54.(55.R1?.(3;.&40.R38.)Vgp,Vtp,R1>.R1=.R1<.Vsp,(3;.&40.R38.)R1;.R1:.R19.R18.R17.R16.R15.R14.(3;.&40.R39.)(3;.&40.R20.)R?.R>.R=.R<.R;.(3;.&40.R39.)(3;.&40.(16.(37.R39.+3.)(38.(39.VR,))))R:.R13.R12.R11.R10.)VF,(3;.&40.+98;40.)Vfc,(56.(0.&40.))R23.(57.$8.))R22.))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros D HNC HSC PERM CNT PHI FFR HW Hr. gvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKsi0 NRT TOP HT; lia]).
    pose proof (fresh_apart_grow R HIA hc Lc LB LF mc FB 64 FRSH HHc) as FRSH3.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lc ++ LB) LF mc FB 64 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH & IND & AP & _ & F8 & FBLO & _ & _).
    (* [comment removed for export] *)
    chunk_to_stk RSL. stk_merge_into RSL STb.
    pose proof (presW_hmono R HIA h hc LB LF _ _ _ m mc PRES HCSc HSc) as PRESh.
    pose proof (presW_init_at R HIA hc _ _ (Lc ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKsi0 NRT; lia)) as PRES2.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply epi_walk with (h := h) (lo := lo) (slo := slo) (bs := bs) (PP := PP) (SIG := SIG) (DALG := DALG) (BUF := BUF) (STKsi := STKsi)
                           (h3 := hc) (LBn := Lc) (m0 := m) (m2x := mc) (WA := W) (WB := []);
        first [ exact HHc | exact HCSc | exact PRESh | exact PRES2 | exact CFB | exact Hr
              | lazymatch goal with |- lo <= bv_unsigned sp - A_pkcs7_signers_A.STKs _ _ => exact SLO end
              | eassumption | reflexivity
              | match goal with |- ?g => idtac "RET-EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)) as HPX9f.
    assert (HPX9 : heap_presx asegs L (Lc ++ LB) (bv_unsigned sp) [] mc m9).
    { eapply heap_presx_weaken; [exact HPX9f| intros b Hb; apply in_app_iff; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]. }
    assert (CRsp : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((Lc ++ LB) ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    unfold pkcs7_getsigners_postA.
    deexists 15. dexists m9, mo9, h4, r, p, inext, snext, sj', names0, sg, Lc.
    split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hr|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
    split.
    { pose proof (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES9) as HPF. rewrite HSc in HPF. unfold SIGNER_SIZE.
      eapply presA_weaken; [exact HPF| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| exact HW]. }
    split; [rewrite E4top; exact HTc|]. split; [rewrite E4stk; exact HSc|]. split; [rewrite E4flag; exact HFc|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSc x Hx)|].
    split; [rewrite E4vol; clear - HVc PHI; lia|].
    split; [rewrite E4fr; clear - HFRc FFR; lia|].
    split; [exact CNT|].
    split; [eapply (presA_rw_cells asegs R); [exact (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)| exact PPc| apply CRsp; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hpc|].
    split; [eapply (presA_rw_cells asegs R); [exact (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)| exact CSG| cbn [cells_size csize Nat.add length signer_cells]; apply CRsp; [exact SGLO| exact (client_range_of_w L _ _ _ _ _ CWS)]| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)| exact DAc| cbn [cells_size csize Nat.add length buf_cells]; apply CRsp; [exact DALO| exact CRDA]| exact I]|].
    split.
    { eapply (name_chain_presx0 mc m9 (Lc ++ LB) (Lc ++ LB) (bv_unsigned sp) []); [exact HNC| | exact HPX9| intros x _; exact I].
      intros x Hx. eapply (chain_nodes_in asegs); [exact HNC| exact Hx]. }
    split.
    { eapply (signer_chain_presx0 mc m9 (Lc ++ LB) (Lc ++ LB) (bv_unsigned sp) []); [exact HSC| | exact HPX9| intros b _ _; exact I].
      intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
    split; [exact PERM|]. exact HH4.
  Qed.
  End Call.
End Walk.
