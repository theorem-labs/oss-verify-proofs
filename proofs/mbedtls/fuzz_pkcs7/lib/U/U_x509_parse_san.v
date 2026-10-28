(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_oid U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_get_name U_x509_parse_san_A U_x509_parse_san_B U_x509_parse_san_C U_x509_parse_san_D.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_x509_parse_san () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_parse_san_A.x509_parse_san_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.U_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_free_named_data_list_shallow.U_FREE"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.U.U_x509_parse_san_A.x509_parse_san_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_parse_san_A.U_X509_PARSE_SAN"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (SB SAN BUF sp0 slen lo : Z) (bs : list byte).
  Notation CTX := (san_ctx usegs L HI U_CALLOC U_FREE sp tp h LB SB SAN BUF sp0 slen lo bs).
  Hypothesis HC : CTX.

  Notation X := [(SAN, SAN + 80)].
  Notation W := [(SAN, SAN + 80); (bv_unsigned sp - 80, bv_unsigned sp)].
  Notation POST := (x509_parse_san_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB SAN lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Let epi_walk' := epi_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let IBB := in_block_below' L HI sp tp h LB SB SAN BUF sp0 slen lo bs HC.
  Let heap_W' := heap_W L HI sp tp mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let presx_W' := presx_W L HI sp tp m h LB SB SAN BUF sp0 slen lo bs HC.
  (* [comment removed for export] *)
  Ltac call_memset :=
    let SPM := fresh "SPM" in
    pose proof U_memset_spec as SPM; unfold memset_stmt in SPM;
    lazymatch goal with
    | |- aevtM ?segs _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply aevtM_cut_evt;
        [ eassumption
        | eapply SPM; rewrite ?(unsigned_lit SAN) by dlia; rewrite ?(unsigned_lit 80) by (clear; lia); try eassumption
        | unfold memset_post; rewrite ?(unsigned_lit SAN) by dlia; rewrite ?(unsigned_lit 80) by (clear; lia);
          rewrite ?(unsigned_lit 0) by (clear; lia); post_call segs mx ]
    end;
    clear SPM;
    match goal with H : rw_cells _ _ SAN _ |- _ => change (Z.to_nat 80) with 80%nat in H; change (0 mod 256) with 0 in H end.


  (* [comment removed for export] *)
  Ltac ro_const A n RO :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
      let bs := eval vm_compute in (match image_bytes sg A n with Some bs => bs | None => [] end) in
      match goal with MI : mem_inv sg mx |- _ =>
        pose proof (ro_image_bytes_at sg mx A bs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO end
    end.

  (* [comment removed for export] *)
  Ltac san_t0 HSAN :=
    lazymatch type of HSAN with rw_cells ?sg ?mx ?A _ =>
      apply (rw_cells_zeros sg mx A 80 [C4 (Z_to_bv 64 0); CB 76 (repeat (Z_to_bv 8 0) 76)]) in HSAN;
        [| cbn; repeat split; reflexivity | reflexivity] end.
  Ltac chk :=
    let K := fresh "K" in if_cases K; zify_cond K;
    [ exfalso; rewrite ?land_7_mod in K; first [ clear_disj; lia | lia ] | clear K ].
  Let ms_walk' := ms_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let ip_walk' := ip_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let dir_walk' := dir_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB SB SAN BUF sp0 slen lo bs HC.
  Let on1_walk' := on1_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB SB SAN BUF sp0 slen lo bs HC.

  #[using="HC epi_walk' heap_W' presx_W' ms_walk' ip_walk' dir_walk' on1_walk'"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ptgw,(0.&40.)Ppdw,(0.&40.)P,(1.$2.VL,VHI,Vh,VLB,Vm,Vmo,)P,(3.$2.Vm,VSB,(4.R3.R2.Vslen,Vsp0,))P,(3.$2.Vm,VSAN,(5.$6.(7.#50.(8.(0.&8.)(9.&8.=)#50.))(:.$6.)))P,(;.$2.Vm,VBUF,Vbs,)P,(<.$2.Vm,Vlo,(=.&40.Vsp,))P,(>.$2.Vm,)(?.$2.Vmo,(10.$2.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VSAN,Vlo,Vm,Vmo,)(11.(12.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(9.&40.VSB,)(9.&40.VSAN,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(9.&40.+289;8.)Vfc,(13.(0.&40.))Vm,(14.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tgw pdw HH HSB HSAN HBUF ST MI.
    open_sctx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof (conj HH I) as HHbox. unfold buf_cells in HSB.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 80%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. chk. zstep. zstep. zstep. chk. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg ?mx ?A (CB 16 ?j :: ?rest) =>
      set (JJ := j) in FR; clearbody JJ;
      change (rw_cells sg mx A (CB 16 JJ :: rest)) with (rw_cells sg mx A ([] ++ CB 16 JJ :: rest)) in FR;
      apply (rw_cells_split_CB sg mx A [] 16 JJ rest [8; 8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR
    end.
    cb8_to_c8 FR ([] : list cell). lazymatch type of FR with rw_cells _ _ _ (?c :: _) => cb8_to_c8 FR [c] end.
    lazymatch type of HSB with rw_cells ?sg ?mx ?A (C4 ?v :: C4 ?w :: ?rest) =>
      change (rw_cells sg mx A (C4 v :: C4 w :: rest)) with (rw_cells sg mx A ([] ++ C4 v :: C4 w :: rest)) in HSB;
      apply (rw_cells_join_C4C4 sg mx A [] v w rest) in HSB; cbn [app] in HSB end.
    set (t := bv_unsigned (zx32 tgw)) in *.
    assert (TL : 0 <= Z.land t 223 <= 223).
    { split; [apply Z.land_nonneg; right; clear; lia|]. rewrite Z.land_comm. apply land_le_l. clear; lia. }
    zstep. if_cases KT; zify_cond KT.
    { (* [comment removed for export] *)
      san_t0 HSAN. eapply epi_walk'; try eassumption. { exact (proj1 HHbox). } { clear; lia. } { cbn. reflexivity. } { clear; lia. } { clear; lia. } }
    assert (HK : 128 <= Z.land t 223 <= 135) by (clear -KT TL; lia).
    clear KT TL. set (v := Z.land t 223) in *. clearbody v.
    assert (CV : v = 128 \/ v = 129 \/ v = 130 \/ v = 131 \/ v = 132 \/ v = 133 \/ v = 134 \/ v = 135) by (clear -HK; lia).
    clear HK. destruct CV as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; do 7 zstep.
    - (* [comment removed for export] *) eapply on1_walk'; try eassumption. exact (proj1 HHbox).
    - (* [comment removed for export] *) eapply ms_walk'; try eassumption. exact (proj1 HHbox). left; reflexivity.
    - (* [comment removed for export] *) eapply ms_walk'; try eassumption. exact (proj1 HHbox). right; left; reflexivity.
    - (* [comment removed for export] *)
      san_t0 HSAN. eapply epi_walk'; try eassumption. { exact (proj1 HHbox). } { clear; lia. } { cbn. reflexivity. } { clear; lia. } { clear; lia. }
    - (* [comment removed for export] *) eapply dir_walk'; try eassumption. exact (proj1 HHbox).
    - (* [comment removed for export] *)
      san_t0 HSAN. eapply epi_walk'; try eassumption. { exact (proj1 HHbox). } { clear; lia. } { cbn. reflexivity. } { clear; lia. } { clear; lia. }
    - (* [comment removed for export] *) eapply ms_walk'; try eassumption. exact (proj1 HHbox). right; right; reflexivity.
    - (* [comment removed for export] *) eapply ip_walk'; try eassumption. exact (proj1 HHbox).
  Qed.
End Walk.

Lemma U_x509_parse_san_spec : ltac2:(CDefT.buildp (gd_tbl_P_x509_parse_san ()) "PL,$15.PHI,(16.$2.R1.)P,(17.$18.(19.R2.)$1:.)P,(17.$18.(1;.R3.)$1<.)P,(1=.=(1>.R4.))(1?.$2.R5.R4.$20.)")
(* [comment removed for export] *).
Proof.
  intros L HI HCALLOC HFREE HLS. unfold x509_parse_san_stmt, U_X509_PARSE_SAN.
  intros until pdw. intros HH HSB HSAN HBUF B1 B2 B3 B4 D1 D2 ALB ALS NZSB NZS NZB ST SLO ACL HTOP SPA DHI DIM1 DIM2 DSB DSS DSBUF
    CRSB CWS CRBUF TP MI -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HSAN) as SANB. pose proof (rw_cells_bound _ _ _ _ HSB) as SBB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in SANB, SBB.
  change (Z.of_nat 80) with 80 in SANB. change (Z.of_nat 24) with 24 in SBB.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
  eapply main_walk; try eassumption.
  unfold san_ctx. repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption; dlia.
Qed.
