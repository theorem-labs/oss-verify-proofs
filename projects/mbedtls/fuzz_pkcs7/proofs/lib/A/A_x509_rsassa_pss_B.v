(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int_loops A_asn1_get_int
     A_oid A_oid_md_alg A_asn1_get_alg_A A_asn1_get_alg A_asn1_get_alg_null_A A_asn1_get_alg_null A_x509_hash_alg_A A_x509_hash_alg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_x509_rsassa_pss_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib.
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
Ltac2 gd_tbl_A_x509_rsassa_pss_B () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.A.A_x509_rsassa_pss_A.pss_fctx"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.A.A_x509_rsassa_pss_A.x509_pss_postA"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"].
   (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis GSBH : al_gsb AL = AGSB.
  Hypothesis MCI : arl_memcmp_i R = A_WRAP_BCMP.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis GI : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG 48.
  Hypothesis GALG : asn1_get_alg_stmtA asegs R HIA A_ASN1_GET_ALG.
  Hypothesis GNULL : asn1_get_alg_null_stmtA asegs R HIA A_ASN1_GET_ALG_NULL.
  Hypothesis GHASH : x509_hash_stmtA asegs R HIA A_X509_HASH_ALG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo slo : Z) (bs : list byte) (ptag ppad plen : word).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis HAP : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_B ()) "(0.(1.(2.$3.Vpp,=)(2.$3.(4.&40.Vplen,)=))(1.(5.VBUF,Vpp,)(5.(6.Vpp,(4.&40.Vplen,))(6.VBUF,(7.(8.(9.&8.)Vbs,))))))")
(* [comment removed for export] *).
  Hypothesis B47 : BUF + Z.of_nat (length bs) + 8 <= 2^47.
  Hypothesis D12 : MD + 4 <= MGF \/ MGF + 4 <= MD.
  Hypothesis D13 : MD + 4 <= SALT \/ SALT + 4 <= MD.
  Hypothesis D23 : MGF + 4 <= SALT \/ SALT + 4 <= MGF.
  Hypothesis D1P : MD + 4 <= PAR \/ PAR + 24 <= MD.
  Hypothesis D2P : MGF + 4 <= PAR \/ PAR + 24 <= MGF.
  Hypothesis D3P : SALT + 4 <= PAR \/ PAR + 24 <= SALT.
  Hypothesis D1B : Z.of_nat (length bs) = 0 \/ MD + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MD.
  Hypothesis D2B : Z.of_nat (length bs) = 0 \/ MGF + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MGF.
  Hypothesis D3B : Z.of_nat (length bs) = 0 \/ SALT + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= SALT.
  Hypothesis ALP : PAR mod 8 = 0.
  Hypothesis AL1 : MD mod 4 = 0.
  Hypothesis AL2 : MGF mod 4 = 0.
  Hypothesis AL3 : SALT mod 4 = 0.
  Hypothesis PARB : 0 < PAR /\ PAR + 24 <= 2^64.
  Hypothesis MDB : 0 < MD /\ MD + 4 <= 2^64.
  Hypothesis MGFB : 0 < MGF /\ MGF + 4 <= 2^64.
  Hypothesis SALTB : 0 < SALT /\ SALT + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_PSS_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 288 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLO4 : lo <= bv_unsigned sp - 416 - arl_need_amem R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis SLO5 : lo <= bv_unsigned sp - 336 - arl_need_bcmp R.
  Hypothesis RTB0 : 0 <= arl_need_bcmp R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DSP : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS1 : MD + 4 <= lo \/ bv_unsigned sp <= MD.
  Hypothesis DS2 : MGF + 4 <= lo \/ bv_unsigned sp <= MGF.
  Hypothesis DS3 : SALT + 4 <= lo \/ bv_unsigned sp <= SALT.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CRP : client_range L (LB ++ fdata LF) lo PAR 24.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo MD 4.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo MGF 4.
  Hypothesis CR3 : client_range L (LB ++ fdata LF) lo SALT 4.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MD 4.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MGF 4.
  Hypothesis CW3 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SALT 4.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_PSS_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_pss_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo slo).
  Local Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation fctx := (pss_fctx R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 PAR MD MGF SALT BUF lo slo bs).

  Ltac fctx_open D :=
    destruct D as (HH & ECS & ETOP & ESTK & HKI & EFLAG & EVOL & EFR & SP1 & SP1M & FH & FSH & CFB & FBAL & FB0 & FBS1
                   & FWH & FWD & FWS & SUBLF & APP & AP1 & AP2 & AP3 & AP4 & ST1 & SEPF & STK2 & SPILL & OMD & OMGF & OSALT & MI & PRES & WL & WCF & SFF
                   & SS1 & SS2 & FRSH & F64);
    unfold pss_fshl in FSH.
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  (* [comment removed for export] *)
  Ltac fctx_build :=
    lazymatch goal with |- pss_fctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac end;
    unfold pss_fctx, pss_fshl; spine; first [ eassumption | match goal with |- ?g => idtac "FCTX-LEFT:" g end ].

  (* [comment removed for export] *)
  #[using="Type"] Lemma swrap32_errsum' : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_B ()) "Pr,$3.Pc,$3.P,(1.(:.-10000.R2.)(5.R2.=))P,(1.(5.(;.(<.+2.+40.)+10000.)R2.)(:.R2.(<.+2.+40.)))(2.$3.(=.&20.(6.(>.R4.+10000000000000000.)R3.))(6.R4.(;.R3.(<.+2.+40.))))")
(* [comment removed for export] *).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  Ltac fin_postA PRES :=
    apply evtA_done; unfold x509_pss_postA;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    [ lazymatch goal with |- HM _ _ _ _ _ _ _ => eassumption end | ..];
    (lazymatch goal with
     | |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ => exact H end
     | _ => idtac end);
    (lazymatch goal with
     | |- presA _ _ _ _ _ _ _ _ _ _ => eapply presW_presA; exact PRES
     | |- rw_cells _ _ _ _ => idtac
     | |- forall mo, HK _ _ _ _ mo <-> _ =>
         first [ assumption
               | let mo' := fresh "mo" in intros mo';
                 repeat (eapply iff_trans; [ match goal with H : forall mo, HK _ _ _ _ mo <-> _ |- _ => apply H end | ]);
                 apply iff_refl ]
     | |- _ => first [ assumption | reflexivity | congruence | (clear_disj; clear_mods; lia) | idtac ] end).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L20653842230.2  L20660446595.2  L52064949428.172L576250137.173  L64962538913.0  Q10598873147.192Q15684298282.19200000600=00>00c00d01201@S2r'1ES2r'2R2FS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1SS2LF2bs3LFB2FBS2LF2bs3LFB2FB". (* [comment removed for export] *)
  #[using="IMG LFB PARB MDB MGFB SALTB SLO SLOS SLOL TOP SPH CR1 CR2 CR3"] Lemma final_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_B ()) "PFB,$3.Psp1,$3.Ph1,(?.$10.VR,VHIA,)Pm0,P,(9.&40.)(11.(9.&8.))Pmm,P,(9.&40.)(11.(9.&8.))Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Pxra,(9.&40.)Px5,(9.&40.)Px6,(9.&40.)Px7,(9.&40.)Px10,(9.&40.)Px11,(9.&40.)Px12,(9.&40.)Px13,(9.&40.)Px14,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Px17,(9.&40.)Ps3v,(9.&40.)Ps4v,(9.&40.)Ps5v,(9.&40.)Ps9v,(9.&40.)Ps10v,(9.&40.)Px28,(9.&40.)Px29,(9.&40.)Px30,(9.&40.)Px31,(9.&40.)Ppc,$3.PEND,$3.Pv1,(9.&40.)Pv2,(9.&40.)Pv3,(9.&40.)P,(12.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VPAR,VMD,VMGF,VSALT,VBUF,Vlo,Vslo,Vbs,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)P,(13.$10.R1?.(6.R23.+20.)(14.$15.(16.(17.&40.R6.))(18.$15.)))P,(13.$10.R20.VMD,(14.$15.(19.R5.)(18.$15.)))P,(13.$10.R21.VMGF,(14.$15.(19.R5.)(18.$15.)))P,(13.$10.R22.VSALT,(14.$15.(19.R5.)(18.$15.)))P,(1.(5.=R:.)(:.R:.(<.+2.+40.)))P,(1.(5.=R:.)(:.R:.(<.+2.+40.)))(1:.$10.(1;.VR,)(1<.$10.VR,VHIA,Vh,)(1=.$10.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,R26.)(1>.(1?.R21.(17.&40.R28.)Vgp,Vtp,R20.R1?.R1>.Vsp,(17.&40.R28.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(17.&40.R29.)R15.R14.R13.(17.&40.(6.R29.+20.))(17.&40.R;.)(17.&40.R29.)R12.R11.(17.&40.(6.(20.R29.+3.)(21.(1;.VR,))))R10.R?.R>.R=.)VF,(17.&40.+:;<70.)Vfc,(22.(9.&40.))R25.(23.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until v3. intros D HPL HMD HMGF HSALT PC0 END0.
    pose proof D as D'. fctx_open D'.
    rt_facts.
    (* [comment removed for export] *)
    do 8 zstep.
    rewrite ?(Z.mod_small pc 18446744073709551616), ?(Z.mod_small END 18446744073709551616) by (first [exact PC0 | exact END0]).
    ddestruct (x509_mismatch_select pc END 18446744073709542554 (proj1 PC0) (proj1 END0) ltac:(clear; lia)) as (r' & ER & R1 & R2).
    first [ rewrite ER | match goal with |- ?g => idtac "SELECT-FORM:" g end ]. clear ER.
    eapply epi_walk with (r := r'); first [ eassumption
           | destruct (Z.eq_dec pc END) as [E|NE]; [apply R1 in E; clear - E; lia| specialize (R2 NE); clear - R2; lia]
           | match goal with |- ?g => idtac "FINAL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06T0@C23922862675.227C60407910007.255C60410007123.226C9885597303.254 D10592533181.227D10594630297.255D10679970627.255D16069757090.255D16071854214.227D23019327375.255D2455419791.255 D2457516971.227 D31157489305.255D32456773204.255D32458870384.227D34669522109.227D53003915860.255D53315247896.227D53317345084.255D55713995580.255D56536395888.227D57174308711.227D57176405827.255D57209973095.227D5984197035.227 D60109446735.227D60111543915.255D60746685720.227D62010114892.255D62012212072.227D68221095944.227D68223193132.255K15211865226.227K15431550238.255K20344210014.254K20346307194.227K21633682478.254K28491953354.227K28494050542.254K2870125178.227 K29378133114.227K29380230238.255K30469703802.227K55340869294.254K55342966410.227K63185631086.254K64406893342.254K64631974602.227L10912730231.1  L15207968540.2  L15421361836.3  L15934535645.1  L1685717371.0   L20077122534.3  L20341950956.2  L21635418012.2  L21644325741.3  L21654730866.2  L21850448153.229L23496140401.180L2354636449.0   L24023900370.0  L24624535421.3  L2621559066.2   L27817787439.229L27830503198.200L28496445276.2  L2883004908.3   L29008469930.203L29010574176.204L29391009772.3  L30482580460.2  L31168136491.1  L34603895532.0  L35530538413.3  L3574711452.0   L363719563.2    L3800000119.1   L38551529394.0  L39188636933.0  L41251426164.1  L41663468825.210L42411609006.0  L42488948659.2  L42710287031.1  L47870616696.2  L48455046775.1  L49233373885.3  L5021251703.1   L50370324495.2  L512883055.1    L53524301853.228L53526451744.17 L53527181501.3  L53770459319.1  L53849999973.230L55339068700.2  L5545697849.24  L55531866784.2  L55569906807.1  L56777281756.11 L576250137.180  L576250137.210  L576250137.228  L5777911226.217 L57781587882.3  L58033257459.2  L58039649675.2  L5867774410.2   L59308586248.2  L60008475720.2  L60206496545.0  L60448817524.1  L62275882349.3  L63039843019.228L63196478684.2  L64009471222.1  L64392444076.2  L64509800762.2  L64526681523.2  L64635806044.2  L66151402056.3  L66151427842.16 L66298372189.2  L66812728480.3  L66925224597.201L68496899164.0  L7378504036.2   L8044624804.2   L8282379303.2   L881835912.0    L8846472116.1   L8978951910.236 L8978951910.238 L9815049232.17  L9815049296.11  L9817103909.180 O12455021570.227O13883737491.254O13885834679.227O17215019116.255O20866770946.227O20868868134.255O26874497858.227O26876595046.254O27054683959.227O27056781075.254O30010457231.225O30012554411.253O3078286936.225 O31374125227.253O33083286018.227O34121989575.254O34124086755.227O35686498818.227O35688596006.254O3821773283.227 O3823870407.255 O424351700.225  O426448880.253  O44938202843.225O44940300031.253O49699726460.252O49701823576.225O5147960994.227 O5150058118.254 O52616826440.227O53464606246.254O54391770150.255O55209884805.225O55211981985.253O55518239188.225O56400461122.227O59402460144.253O62525548706.227O64471909102.253O64474006218.225O67171060367.225O68276681350.254O69758822.254   O7505213564.252 P15844561461.232P21209329432.235P21209329432.254P21209329432.256P21658526154.225P24619795966.252P324046647.235  P324046647.254  P324046647.256  P35248564789.204P35517378350.253P356858156.227  P35916180322.204P35916180349.232P38605639612.235P38605639612.254P38605639612.256P42484919333.225P42487016449.253P42639610088.235P42639610088.254P42639610088.256P47874275067.253P47876372191.225P49228642366.252P49230739482.225P53529750042.225P55517763591.227P55519860771.254P58043275016.255P58047639617.253P62260666314.225P62262763502.253P64538971685.225P66292560634.225P66294657758.253P66816411171.255P66818508295.227P67623312062.235P67623312062.254P67623312062.256P7365450727.254 P7367547843.227 P7903954312.235 P7903954312.254 P7903954312.256 P8046242051.227 P8048339239.254 Q10592533181.227Q10594630297.255Q10596643758.200Q10598611232.226Q10598871740.199Q10821824020.235Q10821824020.254Q10821824020.256Q11133374175.227Q11135471355.255Q11661329559.250Q11661334259.248Q11663378672.221Q12254003355.249Q12254003355.251Q1228145612.248 Q1228149160.250 Q12658605510.235Q12658605510.237Q12658605510.254Q12658605510.256Q12658605510.258Q14452457048.227Q15684299949.199Q15756061900.232Q15844561461.232Q16178735000.227Q16180832188.255Q16401581652.255Q17611649746.204Q17698853560.232Q19546951509.229Q19559401572.200Q19561563119.201Q19700360397.232Q19700360402.204Q20704173822.249Q20704173822.251Q21765573510.255Q21767670690.227Q23411989076.255Q23613318552.227Q2383289165.232 Q25714205560.232Q26030071964.227Q26032169144.255Q26032445052.235Q26032445052.254Q26032445052.256Q26314584654.235Q26314584654.254Q26314584654.256Q26316671538.222Q26316671538.249Q26316671538.251Q26387688446.248Q26387691930.250Q27311265013.249Q27311265013.251Q27940405518.232Q27940405521.204Q27942454161.227Q27944551349.255Q2803826605.227 Q2805923721.255 Q29775981542.227Q29778078658.255Q30280298753.228Q31155634332.230Q31157489305.255Q31349872378.229Q31542961001.232Q32444242563.255Q32456773204.255Q32754042668.255Q32756139784.227Q33135353571.255Q33137450695.227Q33314635563.204Q33422860542.249Q33422860542.251Q34357517856.231Q34667034333.225Q34669522109.227Q34671242789.201Q3482791591.232 Q3482791608.204 Q34964382778.227Q34966479902.255Q34966786778.235Q34966786778.254Q34966786778.256Q35248564789.204Q35653441506.198Q35916180322.204Q35916180349.232Q37567955584.229Q38237949967.232Q38237949968.204Q38260859415.228Q38792230180.226Q41414298335.227Q42439168719.227Q42441265899.255Q42441548847.235Q42441548847.254Q42441548847.256Q44172294453.249Q44172294453.251Q44298944140.222Q44298944140.249Q44298944140.251Q44301027056.235Q44301027056.254Q44301027056.256Q44331990745.225Q45482765142.237Q45482765142.256Q45482765142.258Q47160535739.255Q47621266200.249Q47621266200.251Q48068040746.204Q48119910507.235Q48119910507.254Q48119910507.256Q48447188180.232Q48849104909.232Q50370142516.232Q508607704.230  Q51107054235.249Q51107054235.251Q53317345084.255Q54093299348.232Q54481541668.231Q55182376490.204Q55256112523.249Q55256112523.251Q55713995580.255Q5640262893.200 Q57389425963.204Q57389425972.232Q58040652597.249Q58040652597.251Q58972088531.232Q58972775020.204Q58972775027.232Q59615273459.248Q59615277975.250Q59865603600.227Q59867425008.235Q59867425008.254Q59867425008.256Q59867700788.255Q60109315147.198Q60216640444.255Q61690386318.249Q61690386318.251Q62192426563.255Q63435846322.249Q63435846322.251Q64228675114.234Q64228675114.253Q64228675114.255Q65934997350.255Q65937094466.227Q66220707762.255Q66222804886.227Q66345447362.227Q66585072679.204Q66901779611.249Q66901779611.251Q67126153328.221Q67892150791.249Q67892150791.251Q6912043757.232 Q7757653350.201 Q8699324297.227 Q8701202793.235 Q8701202793.254 Q8701202793.256 Q8701421485.255 Q9080220968.232 Q9080220983.204 Q9356559653.232 Q9356559674.204 Q9631850907.200 Q9634015760.201 Q9644304042.229 Q9644583048.227 Q9646680236.255 00000400800<00@00e01J01o03I04c04d04e04f05K06006U07:07_07`07a07b08G08l09Q0:60:70:e0;S0;T0<;0<b0>H0?n0@i0BE0CA0D=0E:0F70G40H>0IH0Jd0K`0L[0MV0NQ0OM0PJ0PK0PL0PM0PP0PQ0P\0P]0P^0P_0P`0QE0S>0S?0S@0SA0SI0Sn0TS0TT0TU0TV0TW0TX0TY0T]0T^0T_0T`0Ta0Te0Tf0Tg0Tk0UP0UQ0UR0UV0UW0U[0U\0U]0Ue0Ui0X10Xc0Xd0Xe0Xf0Xg0YO0YP0YT0Z90Z^0[C0[h0[i0\30\40\50\=0\C0\D0\E0\I0\J0^N0^O0^P0^Q0^Y0^Z0^[0^d0_>0_?0_@0_e0_f0_g0_h0_n0_o0`30`40`50`]0aB0c;0c<0c=0c>0c?0c@0cA0cB0cC0cD0cE0cF0cG0cH0cI0cJ0cK0cL0cM0cN0cO0cP0cQ0cR0cS0cT0cU0cV0cW0cX0cY0cZ0c[0cn0dA0dB0dC0dD0dE0dF0dG0dH0dI0dJ0dK0e00e^0fL0g:0gZ0h40hk0ib0jY0k>0k^0l50lY0m=0mj0nW0oD0og10J11611b12N12e13<13V14014J14o15T15k16N16n17N18118G18]19c1;C1<01<]1=J1=n1>R1?C1@41@e1AK1B11B?1BM1B[1C:1CH1D11DZ1EC1EQ1E_1Em1F;1FI1F\1Fo1G=1GK1H41Hg1IP1JF1K91K]1Kk1LC1LD1LR1L`1Ln1NR1Nm1PQ1R51SY1U=1Va1Vb1Vc1WJ1X11X21X@1XS1Xa1Y61YK1Z:1Zi1[X1\=1\b1]G1]Z1]m1^@1^N1^\1^]1^^1_;1_X1`51`R1`a1a01aF1a\1b?1b^1bl1cN1cm1d;1dI1d`1e71eP1ei1f;1f<1f=1fb1gA1gO1g]1i<1j[1k81kU1lL1mC1n:1n;1n]1n^1n_1oA1oO1o]20@20_20m21C21Y22G23523c23d23e24824K24^25C25h26M26l27_28R29E29S29T29U29l2:c2;Z2<Q2=12>U2>g2?F2?Y2?l2?m2@M2A62AM2AN2AO2AP2A^2B02BB2BC2BD2Bc2C62CI2CJ2CK2CL2CM2CN2CO2CP2Cd2D22D32D42DB2DC2DD2F=2H62Io2J02J12J22J32JW2Je2K82KK2KY2KZ2K[2L:2LH2M32N62O92P<2Pg2Q@2QY2RH2S72SI2S[2Sm2T?2TQS2FBS2FBS2FBS2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP13FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP13FB03ALO3ACV3SPRFFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOS2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOS2FB3sp1FS1R2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB3TOP2FB3sp12h14ETOP3SP13FB03ALO3ACV3SPR4HTOPS1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB3TOP2FB3sp12h14ETOP3SP13FB03ALO3ACV3SPR4HTOPS2LF2MD2lo2bs3LFB2FB3sp12pc3END3x253AP12x23x263x273x324POSTS2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x433AP43PC13PC22EB2KE1q2Lw3Hqr2Hq3HqL3x273x443x453x465POST0S2LF3MGF2lo2bs3LFB2FB3sp13x433AP21q2Lw3x273x443x453x465POST0S2LF3MGF2lo2bs3LFB2FB3sp12pc3END3x253AP22x23x263x273x324POSTS2LF4SALT2lo2bs3LFB2FB3sp13x433AP31q2Lw3x273x443x453x465POST0S2LF4SALT2lo2bs3LFB2FB3sp12pc3END3x253AP32x23x263x273x324POSTS2LF4SALT2lo2bs3LFB2FB3sp13x433AP31q2Lw3x273x443x453x465POST0S2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x253AP43PC13PC22EB2KE2x23x263x273x324POSTS2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x253AP43PC13PC22EB2KE2x23x263x273x324POSTS2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x433AP43PC13PC22EB2KE1q2Lw3Hqr2Hq3HqL3x273x443x453x465POST0S2LF3MGF2lo2bs3LFB2FB3sp12pc3END3x253AP22x23x263x273x324POSTS2LF2MD2lo2bs3LFB2FB3sp13x433AP11q2Lw3x273x443x453x465POST0S2LF2MD2lo2bs3LFB2FB3sp12pc3END3x253AP12x23x263x273x324POSTS2LF2MD2lo2bs3LFB2FB3sp13x433AP11q2Lw3x273x443x453x465POST0S2LF3MGF2lo2bs3LFB2FB3sp13x433AP21q2Lw3x273x443x453x465POST0S2LF4SALT2lo2bs3LFB2FB3sp12pc3END3x253AP32x23x263x273x324POSTFFFS1lSS2FB3x272HxFFFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC13PC22EB3ALO3ACV3SPRSSFS2sp3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFFFFFS2FBSFSFS2FBSSS2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1SFS2FBFS2FBFFS2FB3FB0S2FBS1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC12EB3ALO3ACV3SPR1q2Lw2Hq3HqL2q23Hq2S3BUF2bs3B474BUF02pc3END3PC12EB1q2Lw2Hq3HqL2q23Hq2FFFFS1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9FS2FBS3BUF2bs3B474BUF02pc3END3PC12EB1q3HqrS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS2FB2x22HxFFS2ri3RRiS1i2HiSSS2FBFS1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC12EB3ALO3ACV3SPR1q2Lw2LR2Hq3HqLFFFS2ri3RRiFFS1r2RR2KrS2FB2r03F641q1r1H2H02q02H4FFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1SFFS1r2RRSS2FBFFS3BUF2bs3B474BUF02pc3END3PC12EB1q3Hqr2HqS3BUF2bs3B474BUF02pc3END3PC12EB1q3HqrS1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC13PC22EB3ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2sp2lo3SLO3sp13SP1S2sp2lo3SLO3sp13SP1FFFFFFFFFFS2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp13SP1S1R2LF4SALT2bs3LFB2FB3AP32HB5Ha_st5Hl_st5SAEstS1R2LF4SALT2bs3LFB2FB3AP32HB5Ha_st5Hl_st5SAEstS1R2LF4SALT2bs3LFB2FB3AP32HB5Ha_st5Hl_st5SAEstS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2sp2bs3LFB2FB3sp14FBS1S1R2LF3slo2bs3LFB4SLOS2FB3sp14SEPF2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs3LFB4SLOS2FB3sp14SEPF2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs3LFB4SLOS2FB3sp14SEPF2HB5Ha_st5Hl_st5SAEstS2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp13SP1S1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2bs3LFB2FB3sp14FBS1S2LF3BUF2bs3LFB2FB2pc3END3AP43PC22KES2LF3BUF2bs3LFB2FB2pc3END3AP43PC22KES1R2LF3BUF2bs3LFB2FB3AP42HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB3AP42HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB3AP42HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS1R2LF2MD2bs3LFB2FB3AP12HB5Ha_st5Hl_st5SAEstS1R2LF2MD2bs3LFB2FB3AP12HB5Ha_st5Hl_st5SAEstS1R2LF2MD2bs3LFB2FB3AP12HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FB3sp14FBS1S2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP1S2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP1S2LF2bs3LFB2FB3sp14FBS1S1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS2LF2sp2bs3LFB3sp13SP1S2LF2sp2bs3LFB3sp13SP1S2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp12pc3END3SP13PC12EB1q2Lw3Hqr2LR2Hq3HqLS1R2LF2sp3BUF2lo2bs3LFB3SLO3LOS3DS42FB3sp12pc3END3x253SP14SEPF3PC13PC22EB2KE2x23x263x273x324POSTS1R2LF3MGF2bs3LFB2FB3AP22HB5Ha_st5Hl_st5SAEstS1R2LF3MGF2bs3LFB2FB3AP22HB5Ha_st5Hl_st5SAEstS1R2LF3MGF2bs3LFB2FB3AP22HB5Ha_st5Hl_st5SAEstS2LF2sp2MD2lo2bs3LFB3SLO3DS13sp13SP1S2LF2sp2MD2lo2bs3LFB3SLO3DS13sp13SP1S1R2LF2sp2bs3LFB2FB3sp14FBS12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2bs3LFB2FB3sp14FBS12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2bs3LFB2FB3sp14FBS12HB5Ha_st5Hl_st5SAEstS2LF2sp4SALT2lo2bs3LFB3SLO3DS33sp13SP1S2LF2sp4SALT2lo2bs3LFB3SLO3DS33sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF3LFB1l3B472FB3END2EB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEst1l3B473END2EBS1R2LF3BUF3LFB1l3B472FB3END2EB2HB5Ha_st5Hl_st5SAEstS1R2LF4SALT2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF2lo2bs3LFB3LOS3ALOFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS2LF3BUF2bs3LFB2pc3PC11q2HqS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRFFS1R2LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOS1R2LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOFS2LF2bs3LFB2FBS2LF2bs3LFB1q2Lw2LRS2LF2bs3LFB2FBS2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3sp1S1R2LF2sp2lo2bs3LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo2bs3LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo2bs3LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS2LF2bs3LFB2FBS2LF2bs3LFB2FBFFS2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2bs3LFB3sp1S2LF2bs3LFB3sp1S2LF2sp2bs3LFB3sp13SP1S2LF2sp2bs3LFB3sp13SP1S1R2LF3MGF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF2MD2bs3LFB2FB2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB3END2EB1q2Lw3HqLS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FB3sp14FBS1S2LF2sp2lo2bs3LFB3sp13SP1S2LF2sp2lo2bs3LFB3sp13SP1S2LF2bs3LFB2FB3FB0FFS1R2LF2sp2lo2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M3FB03ALO3ACV3SPRS2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S1R2LF2sp2lo2bs3LFB3SLO2FB3sp13SP12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo2bs3LFB3SLO2FB3sp13SP12HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo2bs3LFB3SLO2FB3sp13SP12HB5Ha_st5Hl_st5SAEstFS1R3HIA1h2LF2sp2lo2bs3LFB3TOP4HTOPFFS1R2LF2MD2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2lo2bs3LFBS2LF2lo2bs3LFBS1R2LF3MGF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstFFS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF3BUF3LFB1l3B472FB3END2EB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF3LFB1l3B472FB3END2EB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF3LFB1l3B472FB3END2EB2HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB2FBFFS2LF2bs3LFB2FB3sp14FBS1S1R2LF2sp2lo2bs3LFB3SLO3LOS2FB3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS2LF2bs3LFB2FB3FB0S1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBFS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS1R2LF2sp2lo2bs3LFB3SLO2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3sp14FBS1FFFS2LF2bs3LFB2FBS2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0FFS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB3B47S2LF3BUF2bs3LFB3B47FFFFFFFS1R2LF2lo2bs3LFB3LOSS2LF2bs3LFB2FBFFS2LF2bs3LFB2FBFFS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPR2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPR2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPR2HB5Ha_st5Hl_st5SAEstFFFFS1R2LF4SALT2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS2LF2bs3LFB2FBFFS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2FB3sp13SP14HTOP2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2FB3sp13SP14HTOP2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2FB3sp13SP14HTOP2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS2LF2sp2lo2bs3LFB3sp13SP1S2LF2sp2lo2bs3LFB3sp13SP1S1R2LF2sp2lo2bs3LFB3SLO3LOS3SPH3sp13SP13ALO3ACVS1R2LF2sp2lo2bs3LFB3SLO3LOS3SPH3sp13SP13ALO3ACVS2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0". (* [comment removed for export] *)
  #[using="IMG GT GI pp plen LFB HAP B47 D1B D2B D3B PARB MDB MGFB SALTB BUF0 SLO SLOS SLOL LOS TOP SPH DS1 DS2 DS3 DS4 CR1 CR2 CR3 CR4"] Lemma trail_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_B ()) "PFB,$3.Psp1,$3.Ph1,(?.$10.VR,VHIA,)Pm0,P,(9.&40.)(11.(9.&8.))Pmm,P,(9.&40.)(11.(9.&8.))Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Pxra,(9.&40.)Px5,(9.&40.)Px6,(9.&40.)Px7,(9.&40.)Px10,(9.&40.)Px11,(9.&40.)Px12,(9.&40.)Px13,(9.&40.)Px14,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Px17,(9.&40.)Ps3v,(9.&40.)Ps4v,(9.&40.)Ps5v,(9.&40.)Ps9v,(9.&40.)Px28,(9.&40.)Px29,(9.&40.)Px30,(9.&40.)Px31,(9.&40.)Ppc,$3.PEND,$3.Plw,(9.&40.)Ptw,(9.&40.)Pv1,(9.&40.)Pv2,(9.&40.)Pv3,(9.&40.)P,(12.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VPAR,VMD,VMGF,VSALT,VBUF,Vlo,Vslo,Vbs,R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(13.$10.R20.(6.R24.+20.)(14.$15.(16.(17.&40.R8.))(18.$15.)))P,(13.$10.R21.(6.R25.+40.)(14.$15.(16.R7.)(18.$15.)))P,(13.$10.R22.(6.R26.+>0.)(14.$15.(19.R7.)(18.$15.)))P,(13.$10.R23.VMD,(14.$15.(19.R7.)(18.$15.)))P,(13.$10.R24.VMGF,(14.$15.(19.R7.)(18.$15.)))P,(13.$10.R25.VSALT,(14.$15.(19.R7.)(18.$15.)))P,(24.$10.R26.VBUF,Vbs,)P,(25.$10.(1;.VR,)(1<.$10.VR,VHIA,Vh,)R27.VBUF,(7.(8.(9.&8.)Vbs,)))P,(5.VBUF,R10.)P,(5.R11.R10.)P,(5.R11.(6.VBUF,(7.(8.(9.&8.)Vbs,))))(1:.$10.(1;.VR,)(1<.$10.VR,VHIA,Vh,)(1=.$10.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,R2<.)(1>.(1?.R27.(17.&40.R2>.)Vgp,Vtp,R26.R25.R24.Vsp,(17.&40.R2>.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.(17.&40.R2?.)R1;.R1:.R19.(17.&40.(6.R2?.+20.))(17.&40.R12.)(17.&40.R2?.)R18.(17.&40.(6.R2?.+40.))(17.&40.(6.(20.R2?.+3.)(21.(1;.VR,))))R17.R16.R15.R14.)VF,(17.&40.+:;:44.)Vfc,(22.(9.&40.))R2;.(23.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until v3. intros D HPL HLN HTRL HMD HMGF HSALT HBUF OBUF PC1 PC2 EB.
    fctx_open D.
    rt_facts.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP. rewrite ETOP, ESTK in HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *)
      zstep.
      eapply epi_walk with (r := 0); first [ fctx_build | eassumption | clear; lia | match goal with |- ?g => idtac "T-RET0-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    frame_aobj FSH (FB + 32) 1%nat as OPL.
    frame_aobj FSH (FB + 64) 1%nat as OLENP.
    pose proof (hm_abase asegs R HIA h1 _ _ m4 HH) as AB.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "T-GT-CALL".
    callxA_sp sp1 (eapply SPT with (CS := CS) (PP := FB + 32) (LENP := FB + 64) (P := pc) (END := END) (BUF := BUF) (bs := bs) (tag := 163) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by qlia; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA)); try solve_crange; try qlia; try pqlia).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "T-GT-LEFT:" g end.
    clear SPT OPL OLENP.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (FB + 64) [C8 ?lq] |- _ => rename H into HL5; rename lq into Lw end.
    match goal with H : rw_cells _ m5 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HP5; rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into RR end.
    match goal with H : pc <= q <= _ |- _ => rename H into Hqr end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases K98; zify_cond K98.
    { (* [comment removed for export] *)
      idtac "T-SKIP".
      eapply final_walk with (pc := q); first [ fctx_build | eassumption | clear - Hqr PC1 PC2 EB BUF0 B47; lia | clear - PC2 PC1 EB BUF0 B47; lia
                                              | match goal with |- ?g => idtac "T-SKIP-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "T-GT-ERR".
      eapply err_walk; first [ fctx_build | eassumption | clear - RR; lia | match goal with |- ?g => idtac "T-GT-ERR-LEFT:" g end ]. }
    assert (R0 : r = 0) by (clear - Kr RR; rewrite ?unsigned_lit in Kr by lia; lia). subst r. destruct (HL0 eq_refl) as [Hq HqL]. clear HL0 Kr RR K98.
    (* [comment removed for export] *)
    zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    (* [comment removed for export] *)
    do 8 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : rw_cells _ m6 (Z.shiftr FB 3 + al_sb AL) ?cs |- _ => rename H into FSH6 end.
    frame_aobj FSH6 (FB + 32) 1%nat as OPL.
    pose proof FSH6 as FSc. chunk_split FSc 28%nat FSa FSb. chunk_split FSb 1%nat FS28 FSd. clear FSa FSd.
    replace (Z.shiftr FB 3 + al_sb AL + 28) with (Z.shiftr (FB + 224) 3 + al_sb AL) in FS28
      by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - F64; Z.div_mod_to_equations; lia).
    assert (OTRL : aobj asegs AL CS m6 (FB + 224) 4).
    { apply (aobj_partial AL CS m6 (FB + 224) 4 FS28); [clear - F64; Z.div_mod_to_equations; lia| clear - FB0; lia| clear; lia| eapply crange_sub; [exact CFB| clear; lia| clear; lia]]. }
    clear FS28.
    pose proof GI as SPI. unfold asn1_get_int_stmtA, A_ASN1_GET_INT in SPI.
    idtac "T-GI-CALL".
    callxA_sp sp1 (eapply SPI with (CS := CS) (PP := FB + 32) (VALP := FB + 224) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by qlia; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA)); try solve_crange; try qlia; try pqlia).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "T-GI-LEFT:" g end.
    clear SPI OPL OTRL.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : rw_cells _ m7 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HP7; rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into ri end.
    match goal with H : ri = 0 -> _ |- _ => rename H into HI0 end.
    match goal with H : _ < ri <= 0 |- _ => rename H into RRi end.
    match goal with H : q <= q2 <= _ |- _ => rename H into Hq2 end.
    (* [comment removed for export] *)
    zstep. if_cases Ki; zify_cond Ki.
    2:{ (* [comment removed for export] *)
      idtac "T-GI-ERR".
      zstep. zstep. zstep.
      first [ rewrite swrap32_errsum' by (clear - RRi; lia) | match goal with |- ?g => idtac "T-GI-ERR-FORM:" g end ].
      zstep. zstep. zstep.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
      zstep.
      eapply epi_walk; first [ fctx_build | eassumption | clear - RRi; lia | match goal with |- ?g => idtac "T-GI-ERR-LEFT:" g end ]. }
    clear HI0 Ki RRi.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases KM; zify_cond KM.
    2:{ (* [comment removed for export] *)
      idtac "T-MIS".
      zstep. zstep. zstep.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
      zstep.
      first [ replace (Z_to_bv 64 18446744073709542554) with (Z_to_bv 64 (-9062)) by (apply bv_eq; reflexivity)
            | match goal with |- ?g => idtac "T-MIS-LIT-FORM:" g end ].
      eapply epi_walk with (r := -9062); first [ fctx_build | eassumption | clear; lia | match goal with |- ?g => idtac "T-MIS-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 4 zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    zstep. if_cases KT; zify_cond KT.
    { (* [comment removed for export] *)
      idtac "T-NOT1".
      zstep. zstep.
      first [ replace (Z_to_bv 64 18446744073709542656) with (Z_to_bv 64 (-8960)) by (apply bv_eq; reflexivity)
            | match goal with |- ?g => idtac "T-NOT1-LIT-FORM:" g end ].
      eapply epi_walk with (r := -8960); first [ fctx_build | eassumption | clear; lia | match goal with |- ?g => idtac "T-NOT1-LEFT:" g end ]. }
    idtac "T-FINAL".
    eapply final_walk with (pc := q2); first [ fctx_build | eassumption | clear - Hq2 Hq HqL Hqr PC1 PC2 EB BUF0 B47 LR; lia | clear - PC2 PC1 EB BUF0 B47; lia
                                             | match goal with |- ?g => idtac "T-FINAL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04L0@C21622782031.244C23922862675.226C60407910007.245C60410007123.225D10592533181.226D10594630297.245D16069757090.245D16071854214.226D2455419791.245 D2457516971.226 D32456773204.245D32458870384.226D34669522109.226D37742650898.245D4469934859.245 D53315247896.226D53317345084.245D56536395888.226D57174308711.226D57176405827.245D57209973095.226D5984197035.226 D60109446735.226D60111543915.245D60746685720.226D62010114892.245D62012212072.226D66343133634.245D68221095944.226D68223193132.245K12788809570.243K15211865226.226K18144114932.245K20344210014.243K20346307194.226K25257366260.243K28491953354.226K28494050542.244K2870125178.226 K29378133114.226K29380230238.245K30469703802.226K45345693029.243K55340869294.243K55342966410.226K57501103871.243K64588871167.245K64631974602.226L10912730231.1  L12790887366.2  L15207968540.2  L17698505537.6  L18146440006.2  L1873264954.2   L20341950956.2  L20407710113.0  L21644325741.3  L21654730866.2  L23496140401.179L25259235654.2  L25852787945.6  L2621559066.2   L26958513406.3  L27830503198.199L27832556821.220L28496445276.2  L2883004908.3   L29008469930.202L29010574176.203L29391009772.3  L30482580460.2  L34603895532.0  L363719563.2    L3800000119.1   L41251426164.1  L41663468825.201L42488948659.2  L43593967708.10 L45333647334.3  L47870616696.2  L48455046775.1  L49233373885.3  L5021251703.1   L53524301853.219L53527181501.3  L53849999973.221L55339068700.2  L55531866784.2  L55569906807.1  L56641624225.0  L57507102029.2  L576250137.179  L576250137.201  L576250137.219  L58039649675.2  L59308586248.2  L60448817524.1  L62275882349.3  L63039843019.219L64471802871.1  L64526681523.2  L64578086330.3  L64635806044.2  L66151402056.3  L66298372189.2  L66812728480.3  L66925224597.200L7378504036.2   L8044624804.2   L8282379303.2   L881835912.0    L9218998790.10  L9218998790.8   L9817103909.179 O12455021570.226O13885834679.226O16218136134.245O17215019116.245O20866770946.226O20868868134.245O26874497858.226O26876595046.243O27054683959.226O27056781075.243O30010457231.224O30012554411.243O3078286936.224 O33083286018.226O34121989575.243O34124086755.226O34737915504.243O35686498818.226O35688596006.243O37620147270.243O3821773283.226 O3823870407.245 O424351700.224  O426448880.243  O44938202843.224O44940300031.243O45805362779.243O49699726460.242O49701823576.224O50089233477.243O5147960994.226 O5150058118.244 O52614729324.243O52616826440.226O55209884805.224O55211981985.243O55518239188.224O56400461122.226O62525548706.226O64471909102.243O64474006218.224O64933068547.245O66670657413.242O67171060367.224P15844561461.222P21658526154.224P26945427069.242P34505026841.222P35248564789.203P356858156.226  P358955272.243  P35916180322.203P35916180349.222P42484919333.224P42487016449.243P47874275067.243P47876372191.224P49228642366.242P49230739482.224P53529750042.224P55517763591.226P55519860771.243P58043275016.245P62260666314.224P62262763502.243P64538971685.224P65652972339.222P66292560634.224P66294657758.243P66816411171.245P66818508295.226P7365450727.243 P7367547843.226 P8046242051.226 Q10592533181.226Q10594630297.245Q10596643758.199Q10598689179.238Q10598689189.220Q10598871740.198Q11133374175.226Q11135471355.245Q14995519657.222Q15684299949.198Q15684450186.238Q15684450228.220Q15756061900.222Q15844561461.222Q16178735000.226Q16180832188.245Q17611649746.203Q17698853560.222Q19559401572.199Q19561452143.220Q19561563119.200Q19700360397.222Q19700360402.203Q21765573510.245Q21767670690.226Q22573912516.245Q23613318552.226Q2383289165.222 Q26030071964.226Q26032169144.245Q27940405518.222Q27940405521.203Q27942454161.226Q27944551349.245Q2803826605.226 Q2805923721.245 Q29775981542.226Q29778078658.245Q31542961001.222Q32754042668.245Q32756139784.226Q32848272094.245Q33135353571.245Q33137450695.226Q33314635563.203Q34505026841.222Q34669522109.226Q34671230885.220Q34671242789.200Q3482791591.222 Q3482791608.203 Q34964382778.226Q34966479902.245Q35248564789.203Q35653441506.197Q35916180322.203Q35916180349.222Q38237949967.222Q38237949968.203Q41414298335.226Q42439168719.226Q42441265899.245Q4469934859.245 Q48068040746.203Q48447188180.222Q520100276.220  Q55182376490.203Q5638147814.220 Q5640262893.199 Q57389425963.203Q57389425972.222Q58972775020.203Q58972775027.222Q59865603600.226Q59867700788.245Q60109315147.197Q60526069789.245Q65652972339.222Q65934997350.245Q65937094466.226Q66220707762.245Q66222804886.226Q66343133634.245Q66585072679.203Q7757653350.200 Q8699324297.226 Q8701421485.245 Q9080220968.222 Q9080220983.203 Q9356559653.222 Q9356559674.203 Q9631850907.199 Q9633971088.220 Q9634015760.200 Q9644583048.226 Q9646680236.245 00000600:00>00B00g01L02f04@04A04B04g05L06106206W06X06Y07>07c08H08m08n09\0:J0:K0;20;Y0<>0=d0?J0?h0@c0A`0Ba0C]0DZ0EW0FT0G^0Hh0JI0KE0Kg0Lg0Mb0N_0OT0PQ0PR0PS0PT0Pj0Pk0Q30Q40Q50Q60Q70S00S10S?0SG0SH0Sm0TR0TS0TT0TU0TV0TW0TX0TY0TZ0T^0Tb0UG0UH0Uc0Ud0Ue0Ui0Uj0Uk0X30X40X50X60X70X;0X<0X=0Xb0YG0Yl0Ym0Z30Z70Z80\<0\=0\>0\?0\@0\I0\J0\K0]00]10]20]80]90]:0]O0_H0_I0_J0_K0_L0_M0_N0_O0_P0_Q0_R0_S0_T0_U0_V0_W0_X0_Y0_Z0_[0_\0_]0_^0__0_`0_a0_b0_c0_d0_e0_f0_g0_h0_i0_j0`=0`P0`Q0`R0`S0`T0`U0`V0`W0`X0a=0a]0cK0cb0dG0d^0e50eY0f=0f`0gC0gZ0h10hK0he0i?0id0jI0j`0k@0k`0lC0mN0md0n:0o@10`11D11h12N12\12j13813F13T13b14014>14T14b15015>15V15W15e16317W18219V1;:1<^1>B1?f1@M1A41A51AC1AV1Ak1B@1B]1C:1CW1D41DC1DR1Dh1E>1E]1F41FK1Fb1G;1GT1Gf1Gg1H51HC1HQ1J01KO1Kl1LI1LJ1Ll1Lm1Ln1M<1MJ1MX1Mn1ND1NT1Nk1OK1OY1P01P>1PL1P^1Q01QC1QV1QW1QX1Ql1R<1R=1R>1R?1R@1RA1RQ1R_1Rm1SX1TC1T\1U51Ud1VS1Ve1W71WI1W[1WmS4SALTS2FBS2FBS2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP13FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP13FB03ALO3ACV3SPRFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOS2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOS2FB3sp1FS1R2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB3TOP2FB3sp12h14ETOP3SP13FB03ALO3ACV3SPR4HTOPS1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB3TOP2FB3sp12h14ETOP3SP13FB03ALO3ACV3SPR4HTOPS2LF2sp4SALT2lo2bs3LFB3SLO3DS3S2LF2MD2lo2bs3LFB2FB3sp12pc3END3x253AP12x23x263x273x324POSTS2LF4SALT2lo2bs3LFB2FB3sp13x433AP31q2Lw3x273x443x453x465POST0S2LF3MGF4SALT2lo2bs3LFB2FB3sp13x433AP21q2Lw3x273x443x453x465POST0S2LF3MGF2lo2bs3LFB2FB3sp12pc3END3x253AP22x23x263x273x324POSTS2LF4SALT2lo2bs3LFB2FB3sp13x433AP31q2Lw3x273x443x453x465POST0S2LF4SALT2lo2bs3LFB2FB3sp12pc3END3x253AP32x23x263x273x324POSTS2LF4SALT2lo2bs3LFB2FB3sp13x433AP31q2Lw3x273x443x453x465POST0S2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x253AP43PC13PC22EB2KE2x23x263x273x324POSTS2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x253AP43PC13PC22EB2KE2x23x263x273x324POSTS2LF4SALT3BUF2lo2bs3LFB2FB3sp12pc3END3x433AP43PC13PC22EB2KE1q2Lw3Hqr2Hq3HqL3x273x443x453x465POST0S2LF3MGF2lo2bs3LFB2FB3sp12pc3END3x253AP22x23x263x273x324POSTS2LF2sp4SALT2lo2bs3LFB3DS33sp13SP1S2LF2MD4SALT2lo2bs3LFB2FB3sp13x433AP11q2Lw3x273x443x453x465POST0S2LF2MD2lo2bs3LFB2FB3sp12pc3END3x253AP12x23x263x273x324POSTS2LF4SALT2lo2bs3LFB2FB3sp13x433AP31q2Lw3x273x443x453x465POST0S2LF4SALT3BUF2bs3LFB3D3B2pc3END3PC12EB1q2Lw2LR2Hq3HqLS2LF4SALT2lo2bs3LFB2FB3sp12pc3END3x253AP32x23x263x273x324POSTFFFS3BUF2pc3END3PC11q3HqrFS2ri3RRiFSFFS1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC13PC22EB3ALO3ACV3SPRFS2pc3END1q3HqrS2sp3sp1FS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFFFFFSFS2FBS2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS3BUF2pc3PC11q2Lw2Hq2q23Hq2FFS2FBFFS1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC12EB3ALO3ACV3SPR1q2Lw2Hq3HqL2q23Hq2FFFFS2FBSFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS1i2HiS2FBFS1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC12EB3ALO3ACV3SPR1q2Lw2LR2Hq3HqLFFFFS1r2RR2KrFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFS1r2RRSFS3END1q2Lw3HqL2q23Hq2S1R2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF03SLO3LOS2FB3sp12pc3END3SP13FB03PC13PC22EB3ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2sp2lo3SLO3sp13SP1S2sp2lo3SLO3sp13SP1FFFFFFFFS2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp13SP1S1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3D133D233D3P3SLO3DSP3DS13DS23DS33sp12pc3END3SP13PC12EB1q2Lw3Hqr2LR2Hq3HqLS2LF4SALT2bs3LFB2FB3AP3S2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp13SP1S2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FB3sp14FBS1S2LF3BUF2bs3LFB2FB2pc3END3AP43PC22KES2LF3BUF2bs3LFB2FB2pc3END3AP43PC22KES1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FB3sp14FBS1S2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP1S2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP1S2LF2bs3LFB2FB3sp14FBS1S1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS2LF2sp4SALT3BUF2lo2bs3LFB3SLO3DS33sp12pc3END3SP13PC12EB1q2Lw3Hqr2LR2Hq3HqLS2LF2sp2bs3LFB3sp13SP1S2LF2sp2bs3LFB3sp13SP1S2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp12pc3END3SP13PC12EB1q2Lw3Hqr2LR2Hq3HqLS1R2LF2sp3BUF2lo2bs3LFB3SLO3LOS3DS42FB3sp12pc3END3x253SP14SEPF3PC13PC22EB2KE2x23x263x273x324POSTS2LF2sp2MD2lo2bs3LFB3SLO3DS13sp13SP1S2LF2sp2MD2lo2bs3LFB3SLO3DS13sp13SP1S2LF2sp4SALT2lo2bs3LFB3SLO3DS33sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF4SALT2bs3LFB5SALTBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2lo2bs3LFB3LOS3ALOFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS2LF3BUF2bs3LFB2pc3PC11q2HqS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOS1R2LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOFS2LF2bs3LFB2FBS2LF2bs3LFB1q2Lw2LRS2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2bs3LFB3sp1S2LF2bs3LFB3sp1S2LF2sp2bs3LFB3sp13SP1S2LF2sp2bs3LFB3sp13SP1S2LF3BUF2bs3LFB3END2EB1q2Lw3HqLS2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FB3sp14FBS1S2LF2MD3MGF4SALT2bs3LFBS2LF2sp2lo2bs3LFB3sp13SP1S2LF2sp2lo2bs3LFB3sp13SP1S2LF2bs3LFB2FB3FB0FS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M3FB03ALO3ACV3SPRS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP14SP1M3FB03ALO3ACV3SPRS2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1FS1R3HIA1h2LF2sp2lo2bs3LFB3TOP4HTOPFFS2LF2lo2bs3LFBS2LF2lo2bs3LFBS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSS2LF4SALT2bs3LFBS2LF2bs3LFB2FB3sp14FBS1S1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2bs3LFB2FBS2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF3BUF2bs3LFB3B47S2LF3BUF2bs3LFB3B47FFS1R2LF2lo2bs3LFB3LOSS2LF4SALT2bs3LFBFFFFFS2LF4SALT2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS2LF2sp2lo2bs3LFB3sp13SP1S2LF2sp2lo2bs3LFB3sp13SP1S1R2LF2sp2lo2bs3LFB3SLO3LOS3SPH3sp13SP13ALO3ACVS1R2LF2sp2lo2bs3LFB3SLO3LOS3SPH3sp13SP13ALO3ACVS2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0". (* [comment removed for export] *)
  #[using="IMG GT GI pp plen LFB HAP B47 D13 D23 D3P D1B D2B D3B AL3 PARB MDB MGFB SALTB BUF0 SLO SLOS SLOL LOS TOP SPH DSP DS1 DS2 DS3 DS4 CR1 CR2 CR3 CR4 CW3"] Lemma salt_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_B ()) "PFB,$3.Psp1,$3.Ph1,(?.$10.VR,VHIA,)Pm0,P,(9.&40.)(11.(9.&8.))Pmm,P,(9.&40.)(11.(9.&8.))Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Pxra,(9.&40.)Px5,(9.&40.)Px6,(9.&40.)Px7,(9.&40.)Px10,(9.&40.)Px11,(9.&40.)Px12,(9.&40.)Px13,(9.&40.)Px14,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Px17,(9.&40.)Ps4v,(9.&40.)Ps5v,(9.&40.)Ps9v,(9.&40.)Px28,(9.&40.)Px29,(9.&40.)Px30,(9.&40.)Px31,(9.&40.)Ppc,$3.PEND,$3.Plw,(9.&40.)Ptw,(9.&40.)Pv1,(9.&40.)Pv2,(9.&40.)Pv3,(9.&40.)P,(12.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VPAR,VMD,VMGF,VSALT,VBUF,Vlo,Vslo,Vbs,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)P,(13.$10.R1?.(6.R23.+20.)(14.$15.(16.(17.&40.R8.))(18.$15.)))P,(13.$10.R20.(6.R24.+40.)(14.$15.(16.R7.)(18.$15.)))P,(13.$10.R21.(6.R25.+>0.)(14.$15.(19.R7.)(18.$15.)))P,(13.$10.R22.VMD,(14.$15.(19.R7.)(18.$15.)))P,(13.$10.R23.VMGF,(14.$15.(19.R7.)(18.$15.)))P,(13.$10.R24.VSALT,(14.$15.(19.R7.)(18.$15.)))P,(24.$10.R25.VBUF,Vbs,)P,(25.$10.(1;.VR,)(1<.$10.VR,VHIA,Vh,)R26.VBUF,(7.(8.(9.&8.)Vbs,)))P,(5.VBUF,R10.)P,(5.R11.R10.)P,(5.R11.(6.VBUF,(7.(8.(9.&8.)Vbs,))))(1:.$10.(1;.VR,)(1<.$10.VR,VHIA,Vh,)(1=.$10.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,R2;.)(1>.(1?.R26.(17.&40.R2=.)Vgp,Vtp,R25.R24.R23.Vsp,(17.&40.R2=.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.(17.&40.R2>.)(17.&40.VSALT,)R1:.R19.(17.&40.(6.R2>.+20.))(17.&40.R12.)(17.&40.R2>.)R18.(17.&40.(6.R2>.+40.))(17.&40.(6.(20.R2>.+3.)(21.(1;.VR,))))R17.R16.R15.R14.)VF,(17.&40.+:;9?4.)Vfc,(22.(9.&40.))R2:.(23.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until v3. intros D HPL HLN HTRL HMD HMGF HSALT HBUF OBUF PC1 PC2 EB.
    fctx_open D.
    rt_facts.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP. rewrite ETOP, ESTK in HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *)
      zstep.
      eapply epi_walk with (r := 0); first [ fctx_build | eassumption | clear; lia | match goal with |- ?g => idtac "S-RET0-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    frame_aobj FSH (FB + 32) 1%nat as OPL.
    frame_aobj FSH (FB + 64) 1%nat as OLENP.
    pose proof (hm_abase asegs R HIA h1 _ _ m4 HH) as AB.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "S-GT-CALL".
    callxA_sp sp1 (eapply SPT with (CS := CS) (PP := FB + 32) (LENP := FB + 64) (P := pc) (END := END) (BUF := BUF) (bs := bs) (tag := 162) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by qlia; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA)); try solve_crange; try qlia; try pqlia).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "S-GT-LEFT:" g end.
    clear SPT OPL OLENP.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (FB + 64) [C8 ?lq] |- _ => rename H into HL5; rename lq into Lw end.
    match goal with H : rw_cells _ m5 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HP5; rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into RR end.
    match goal with H : pc <= q <= _ |- _ => rename H into Hqr end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases K98; zify_cond K98.
    { (* [comment removed for export] *)
      idtac "S-SKIP".
      eapply trail_walk with (pc := q); first [ fctx_build | eassumption | clear - Hqr PC1; lia | clear - Hqr; lia
                                              | match goal with |- ?g => idtac "S-SKIP-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "S-GT-ERR".
      eapply err_walk; first [ fctx_build | eassumption | clear - RR; lia | match goal with |- ?g => idtac "S-GT-ERR-LEFT:" g end ]. }
    assert (R0 : r = 0) by (clear - Kr RR; rewrite ?unsigned_lit in Kr by lia; lia). subst r. destruct (HL0 eq_refl) as [Hq HqL]. clear HL0 Kr RR K98.
    (* [comment removed for export] *)
    do 7 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : rw_cells _ m6 (Z.shiftr FB 3 + al_sb AL) ?cs |- _ => rename H into FSH6 end.
    frame_aobj FSH6 (FB + 32) 1%nat as OPL.
    pose proof GI as SPI. unfold asn1_get_int_stmtA, A_ASN1_GET_INT in SPI.
    idtac "S-GI-CALL".
    callxA_sp sp1 (eapply SPI with (CS := CS) (PP := FB + 32) (VALP := SALT) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by qlia; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA)); try solve_crange; try qlia; try pqlia).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "S-GI-LEFT:" g end.
    clear SPI OPL.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : rw_cells _ m7 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HP7; rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into ri end.
    match goal with H : ri = 0 -> _ |- _ => rename H into HI0 end.
    match goal with H : _ < ri <= 0 |- _ => rename H into RRi end.
    match goal with H : q <= q2 <= _ |- _ => rename H into Hq2 end.
    (* [comment removed for export] *)
    zstep. if_cases Ki; zify_cond Ki.
    { idtac "S-GI-ERR".
      eapply err_walk; first [ fctx_build | eassumption | clear - RRi; lia | match goal with |- ?g => idtac "S-GI-ERR-LEFT:" g end ]. }
    clear HI0 Ki RRi.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KM; zify_cond KM.
    { idtac "S-MIS".
      eapply mis_walk; first [ fctx_build | eassumption | match goal with |- ?g => idtac "S-MIS-LEFT:" g end ]. }
    idtac "S-TRAIL".
    eapply trail_walk with (pc := q2); first [ fctx_build | eassumption | clear - Hq2 Hq Hqr PC1; lia | clear - Hq2 HqL Hqr; lia
                                             | match goal with |- ?g => idtac "S-TRAIL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="CR4"] Lemma cr_buf_in : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_B ()) "PFB,$3.P,Pb,$26.P,(27.$26.R1.(28.$26.VLB,(29.VLF,)))(27.$26.R2.(28.$26.VLB,(29.(14.(2:.$3.$3.)(2;.$3.$3.R3.+100.)VLF,))))(2<.(2=.VR,)(28.$26.VLB,(29.(14.(2:.$3.$3.)(2;.$3.$3.R2.+100.)VLF,)))Vlo,VBUF,(7.(8.(9.&8.)Vbs,)))")
(* [comment removed for export] *).
  Proof.
    intros FB SUB a Ha. destruct (CR4 a Ha) as [X|[X|(b & Hb & Hr)]]; [left; exact X| right; left; exact X|].
    right; right. exists b. split; [apply SUB, Hb| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "08R0@C15451156087.268C17025492443.295C17027589631.266C18973515383.267C23922862675.241C60407910007.269C60410007123.240D10598873120.239D1183003300.239 D11881314541.239D11887227860.312D11893914196.269D12487411903.312D16071854214.241D17896916644.239D1841806854.314 D21466499710.312D22376362595.239D2455419791.269 D2457516971.241 D25978651083.312D26710745608.312D28475068030.312D287820991.312  D32452627693.239D32456773204.269D32458870384.241D32463194068.312D32955868935.312D37729595429.312D42997166435.239D43590587279.269D44623623359.312D46319441828.239D4849823700.312 D4856243796.269 D4860454125.239 D49046872702.312D50626680719.269D51725652000.239D52052325902.312D53001427924.312D55582339907.269D56532072916.312D56536395888.241D57174308711.241D57176405827.269D57209973095.241D58745984032.239D5984197035.241 D60109446735.295D60111543915.269D60481168739.239D60810806975.312D62010114892.269D62012212072.241D62022713845.239D62151899352.295D62153996540.269D65321586499.269D66117636222.312D68221095944.241D68422848703.312D894727806.312  K14296855534.268K15211865226.241K20344210014.268K20346307194.241K20904097774.268K21212095580.295K21214192760.266K23534836062.268K28491953354.241K28494050542.268K2870125178.241 K29378133114.241K29380230238.269K30469703802.241K30643071838.269K32732121518.268K36465839390.295K36467936570.269K37675953582.268K3829823730.268 K3831920854.295 K4854476434.268 K4856573622.295 K55088519473.295K55090616597.266K55340869294.268K55342966410.241K56629301086.269K64631974602.241K66612309342.268K6934319418.268 K6936416542.295 L10189253931.14 L10472357438.284L10912730231.1  L10937800883.2  L11157718690.2  L11770334151.8  L13176305223.3  L1384581504.245 L13951498865.2  L14307637340.2  L14789452616.0  L14946134576.245L15207968540.2  L15844561421.7  L15874321104.2  L16126219789.286L16126400797.237L16626113666.3  L17698505537.6  L18478757147.14 L18538772363.2  L18926711580.272L19980016842.7  L20250968439.1  L20341950956.2  L20660446724.4  L20889648220.2  L21218866939.2  L21644325741.3  L21653067925.236L21654730866.2  L21806333978.3  L22706556809.5  L23066351725.3  L23179818103.1  L23290037434.3  L23316010429.3  L23496140401.194L23524578028.2  L2385107540.3   L24206288344.1  L25333246874.245L25852787945.6  L2621559066.2   L27452082063.195L27452082063.284L27830503198.214L27832556821.235L28496445276.2  L2883004908.3   L29008469930.217L29010574176.218L29332734626.2  L29391009772.3  L29755727029.6  L29796553743.2  L30204477567.14 L30269976884.1  L30482580460.2  L30645526764.3  L31311140727.1  L31438869703.8  L31543112430.7  L31863022963.4  L32249658231.1  L32717210140.2  L32750658443.2  L34483742513.1  L34603895532.0  L34783991938.3  L34921825242.3  L35378541105.1  L35634424007.8  L35915950914.4  L36021046681.2  L36181700215.1  L363719563.2    L36428190876.0  L36463206329.4  L37411586167.1  L3741920777.2   L37669889564.2  L3800000119.1   L38235734261.1  L38258729506.1  L38330469153.0  L3834554993.3   L38426000759.1  L39097178740.1  L39348637477.0  L39360307575.1  L4047020194.2   L40828744610.10 L41251426164.1  L41409160545.3  L41663468825.216L42296925391.6  L42488948659.2  L42999085160.1  L43547807394.2  L43593967708.10 L43873902599.2  L44684207283.2  L4516103729.1   L45441985216.2  L45549956724.1  L46938023093.6  L47388760509.3  L47743185883.19 L47870616696.2  L48134333217.0  L48455046775.1  L4858166289.3   L4858179046.1   L48602918719.4  L48648552217.2  L49037504437.6  L49233373885.3  L49581074596.8  L5021251703.1   L51862332981.14 L52064983732.245L52941874306.3  L53321206827.2  L53524301853.285L53527181501.3  L54344395383.1  L55085943702.3  L55339068700.2  L55504905889.0  L55531866784.2  L55569906807.1  L56635360492.3  L57031302710.5  L57107117165.3  L57389116431.2  L57533275511.1  L576250137.194  L576250137.216  L576250137.285  L58772375409.2  L58790154276.6  L58972524609.3  L59308586248.2  L59308632694.1  L59561404390.3  L59863886524.7  L60056205954.3  L60448817524.1  L61340284039.272L61723085474.2  L62013528937.3  L62275882349.3  L62890547962.15 L63039843019.285L63344940145.2  L64526681523.2  L64635806044.2  L64903376861.2  L65019204385.0  L66151402056.3  L66151427842.16 L66298372189.2  L66614109932.2  L66812728480.3  L66925224597.215L66986308662.0  L67170930818.3  L6849307162.246 L6939050937.3   L6972365175.1   L7378504036.2   L7810317169.2   L8044624804.2   L8282379303.2   L881835912.0    L8932515595.250 L9080220944.4   L9218998790.10  L9218998790.8   L9241608207.2   L9356559676.13  L9817103909.194 O10567734856.241O11932660720.266O12455021570.241O13885834679.241O1476819786.266 O14785264606.241O1478916974.295 O17025492443.295O17027589631.266O20866770946.241O20868868134.269O21228041722.268O21230138846.241O21889411622.268O23073414694.268O25796986027.266O25875884833.295O25877981957.268O26197467120.266O26874497858.241O26876595046.268O27054683959.241O28722692754.295O30010457231.239O30012554411.266O30575988358.268O3078286936.239 O32535777404.265O33083286018.241O3405057148.265 O34124086755.241O35590701227.266O35686498818.241O35688596006.268O3821773283.241 O39302861384.241O424351700.239  O426448880.266  O43849271089.295O43851368213.269O44938202843.239O46624095890.295O49699726460.265O49701823576.239O50098657974.266O50100755090.295O50702732434.295O50704829622.269O513637345.295  O5147960994.241 O5150058118.268 O515734469.268  O52616826440.241O55209884805.239O55518239188.239O56400461122.241O56414299794.295O56901989141.268O56904086321.295O59296584550.268O59623432085.266O59625529265.295O61407898106.268O62525548706.241O62974493734.269O64474006218.239O65975700241.295O67171060367.239O67497840678.269O67531149958.268O67665823590.268O68656898801.295O7869890042.268 P10923283201.266P11166205072.312P13949872342.241P15880662374.312P16610922021.295P18523612460.241P21212095580.295P21214192760.266P21658526154.239P21800653407.312P23053224686.266P23297204153.312P23311337278.265P29341089936.312P32765882668.241P34789739045.295P35248564789.218P356858156.241  P35916180322.218P36470424762.312P3750407227.312 P4055573136.312 P41419110342.295P41421207522.266P42306967500.312P42484919333.239P42487016449.266P43539319952.312P44686601985.266P45435023811.312P47385135934.265P47876372191.239P48588551390.295P48592878970.312P48641682878.295P49228642366.265P49230739482.239P52940256805.295P53325842703.312P53529750042.239P55517763591.241P57094022894.266P58255185640.312P58784454130.268P59570159139.312P60050384933.295P60052482049.269P61714466960.312P62260666314.239P62262763502.266P63339218646.241P63341315826.268P64538971685.239P65069474093.312P65659605000.312P66292560634.239P66818508295.241P67165209125.295P67167306241.266P7367547843.241 P7806593522.268 P8046242051.241 Q10592533181.241Q10594630297.269Q10596643758.214Q10596643873.305Q10598689189.235Q10598709037.213Q11133374175.241Q11135471355.269Q11136189078.269Q11138286258.295Q11166205072.312Q1534142442.312 Q15684450228.235Q15684462908.213Q15686527536.305Q15766564435.295Q15768661623.269Q15880662374.312Q15985628819.314Q16178735000.241Q16180832188.269Q17611649746.218Q19546636663.286Q19546885735.237Q19550963923.312Q19559401572.214Q19561452143.235Q19561563119.215Q19561563119.236Q19700360402.218Q21767670690.241Q21800653407.312Q21913100034.214Q21927794988.304Q22137998182.236Q23291923405.269Q23294020585.295Q23297204153.312Q23613318552.241Q26030071964.241Q26030071964.295Q26032169144.269Q26841708030.286Q26841725678.237Q27868694011.269Q27940405521.218Q27942454161.241Q2803826605.241 Q28772277507.266Q29341089936.312Q29775981542.241Q29918556092.269Q31025985043.312Q32756139784.241Q33137450695.241Q33314635563.218Q33889592827.269Q34669522109.241Q34671230885.235Q34671242789.215Q34964382778.241Q34964382778.295Q34966479902.269Q35248564789.218Q35653441506.207Q35916180322.218Q3750407227.312 Q38237949968.218Q38248387216.295Q38250484404.269Q40267031762.312Q4055573136.312 Q41414298335.241Q42439168719.241Q42439168719.295Q42441265899.269Q43539319952.312Q45435023811.312Q46709851922.266Q48068040746.218Q48358016498.269Q48360113622.295Q51738186393.269Q51740007853.237Q51740283581.286Q520100276.235  Q52866601253.269Q52868698369.295Q52968037308.269Q53325842703.312Q55182376490.218Q5638147814.235 Q5640262893.214 Q57389425963.218Q58741773977.269Q58746442789.236Q58972775020.218Q59570159139.312Q59578101107.314Q59865603600.241Q59865603600.295Q59867700788.269Q60109315147.207Q61714466960.312Q6197499568.312 Q64771638073.265Q65937094466.241Q66222804886.241Q66585072679.218Q7524508337.304 Q7526556831.214 Q7757653350.215 Q8699324297.241 Q8699324297.295 Q8701421485.269 Q9080220983.218 Q9090756535.295 Q9092853651.269 Q9356559655.239 Q9356559660.275 Q9356559674.218 Q9391324968.265 Q9631850907.214 Q9633971088.235 Q9634015760.215 Q9634015760.236 Q9640255788.312 Q9644500888.237 Q9644583048.241 Q9644583048.286 Q9644583048.295 Q9646680236.269 00000400500600:00>00B00F00k00l01Q02:02_03H04_04`06f06g07L07M07N08708808908b09G09l0:Q0;:0;;0;<0;a0;b0<K0<L0=50=Z0>?0>@0>A0>f0?S0@<0@a0AJ0Ao0BT0C90C^0DC0DD0E60Ed0FI0G20GY0H@0Hg0JL0Km0LR0LS0N10NZ0N[0O20Om0PC0Q?0QV0QW0QX0Qn0Rk0SB0TL0UV0VJ0WF0X:0XO0Y`0ZX0Zm0[O0\50\U0]90]V0]o0^D0_?0`30a00aF0ag0bL0c>0c?0c@0cA0cB0cT0c_0c`0ca0cb0cc0cd0ce0d?0d@0di0eN0eO0ee0fT0fU0g>0gV0gW0gX0gf0gg0gh0gi0hN0hO0hP0hd0he0hi0hj0hk0jP0jQ0jZ0j_0kD0kR0kZ0l?0lh0mM0n20n30n40n50n60n70n80nN0nV0nf0nk0nl0nm0o10oC0o[0ok0oo10010110510610710C10G10Y10h11011411511611711;11<11=11A11E11J11K11L11P11T11U11Y11Z11j11n11o12T12k12l13013113L13T13U13Y13Z13^14414515;15<15=15A15B15F15G15H15^15_16;16<16@16A16B16C18I18J18N18O18P18Q18R18V18W18j18k19319719\1:A1:m1:n1;D1;P1;V1;Z1;[1<71<81<<1<e1<f1<n1<o1=b1?h1?i1?j1?k1@31@41@=1@`1@a1@b1@c1AH1AI1AJ1Ao1B01B11B21B31B41B:1B;1B<1BK1BL1Ba1Bi1CX1E=1E>1E?1E@1EA1EB1EC1ED1EE1EF1EG1EH1EI1EJ1EK1EL1EM1EN1EO1EP1EQ1ER1ES1ET1EU1EV1EW1EX1EY1EZ1E[1E\1E]1E^1E_1E`1Ea1Eb1Ec1Ed1Ee1Ef1Eg1Eh1Ei1Ej1Ek1El1Em1En1Eo1F01F11F21FE1FF1FG1FH1FI1FJ1FK1FL1FM1FN1FO1FP1FQ1FR1FS1FT1FU1FV1FW1FX1G;1GU1Gl1Io1JS1Jj1Jk1Jl1KL1LX1M81OC1O]1P71PN1Q21QW1Qn1RR1TY1U31UM1V11VQ1X81X[1Y>1YX1Z;1Zd1[>1[U1\k1^A1^e1_?1_Y1`=1`Y1a31aX1b81c^1d51eb1fF1ff1g@1g`1h@1hW1hn1iQ1in1kV1kl1mL1n01nP1o41oK20120?20M20[20m21;21I21W21e21f21g21h22B22P22^23023L23d23e23f24424B25M26\27g2962:A2;L2<W2=b2>m2?T2?U2@22@S2@a2@b2@c2@d2A22AG2A`2B52BG2BU2Bc2C@2C]2Cl2D:2D;2DQ2D_2EB2EY2F22FD2FR2F`2Fn2G<2GY2H:2HW2HX2I:2I;2I<2IJ2I\2Ij2JA2JB2JP2Jf2K@2KV2KW2KX2Kf2L=2LV2M32MA2MO2Ma2Mo2NK2Nk2O92O:2OQ2O_2Om2P?2PM2P[2Pn2Po2QF2QG2QH2QI2Q]2Q^2R12R?2R@2RA2RO2Rl2SE2SS2T>2Tm2UX2V12VN2Vg2W;2WS2Wg2X52XG2XY2Xk2Y=2YS2Ye2Z72ZM2Zc2[5S2FBFFS2FBS2FBS2FBS2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3SLO3LOS2FB3sp13SP13FB03SPR4SP1RFS2LF2sp3PAR2MD3MGF4SALT3BUF2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp13END3FB02EB3SPR4SP1R1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obs4LENO3x592HxFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13SP13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOS2FB3sp13obsS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOS2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS1R2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3TOP2FB3sp12h14ETOP3SP13FB03SPR4SP1R3obsS1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB4PARB3MDB4MGFB5SALTB3TOP2FB3sp12h14ETOP3SP13FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB3TOP2FB3sp12h14ETOP3SP13FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsFS2LF4SALT2bs3LFB2FB3AP3S2LF2MD2lo2bs3LFB2FB3sp12pc3END3x253AP12x23x263x273x324POSTS2LF3MGF2bs3LFB2FB3AP2S2LF3MGF2lo2bs3LFB2FB3sp12pc3END3x253AP22x23x263x273x324POSTS2LF4SALT2bs3LFB2FB3AP3FFS2LF3MGF2bs3LFB2FB3AP2S2LF4SALT2lo2bs3LFB2FB3sp12pc3END3x253AP32x23x263x273x324POSTS2LF4SALT2bs3LFB2FB3AP3S2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x253AP43PC13PC22EB2KE2x23x263x273x324POSTS2LF3BUF2lo2bs3LFB2FB3sp12pc3END3x253AP43PC13PC22EB2KE2x23x263x273x324POSTS2LF3BUF2bs3LFB2FB2pc3END3AP43PC13PC22EB2KE1q3Hqr2HqS2LF3MGF2lo2bs3LFB2FB3sp12pc3END3x253AP22x23x263x273x324POSTS2LF3BUF2bs3LFB2FB2pc3END3AP43PC13PC22EB2KE1q3Hqr2HqS2LF2MD2bs3LFB2FB3AP1S2LF2sp3BUF2lo2bs3LFB3DS43sp13END3SP12EB1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS2LF2sp3BUF2lo2bs3LFB3DS43sp12pc3END3SP13PC12EB1q3Hqr2HqS2LF2MD2bs3LFB2FB3AP1S2LF2sp4SALT2lo2bs3LFB3DS33sp13SP1S2LF2sp4SALT2lo2bs3LFB3DS33sp13SP13obsS2LF2sp2MD2lo2bs3LFB3DS13sp13SP1S2LF2sp2MD2lo2bs3LFB3DS13sp13SP13obsS2LF2sp2lo2bs3LFB3sp13SP13obsS2LF2sp2lo2bs3LFB3sp13SP1S2LF2MD2bs3LFB2FB3AP1S2LF2MD2lo2bs3LFB2FB3sp12pc3END3x253AP12x23x263x273x324POSTS2LF3BUF2bs3LFB2FB2pc3END3AP43PC13PC22EB2KE1q3Hqr2HqS2LF4SALT2lo2bs3LFB2FB3sp12pc3END3x253AP32x23x263x273x324POSTS2LF3MGF2bs3LFB2FB3AP2S2LF2sp3MGF2lo2bs3LFB3DS23sp13SP1S2LF2sp3MGF2lo2bs3LFB3DS23sp13SP13obsS3BUF2bs3END2EB1q2Lw3HqL2q23Qtg3QLw2qp3Hq23QLR3HQPFFFFS1R2lo3LOS2FB4SEPFS2sp2lo3sp1FFFSFFS2sp3BUF2lo2bs3DS43sp13SP1FS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FS3BUF2pc3END3PC11q3HqrS3BUF2bs3END2EB1q2Lw3HqL2q23ALw2ap3Hq24HAP23AL9FS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS1R3HIA1h2sp3TOP3sp13SP1FFS2r23RR22r'2R3FFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFS2MD3MGF4SALT3x592HxFS2FBFFS2LF2sp3PAR2MD3MGF4SALT3BUF2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF02FB3sp12pc3END3FB03PC13PC22EB3SPR4SP1RFS1q2Lw2LRS3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2pc3END1q3HqrS2sp3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFFFFFS1R2sp2lo4SLO53sp13SP1S2FB3FB0S3BUF2bs2ap4HAP1S3MGFFFS2FBS1R2lo3LOS2FB4SEPFS3BUF2bs3END2EB1q2Lw3HqLS2sp3SPH3sp13SP1S2FBFFS2FBSFS3MGF2FB3AP2S2FBS1R2lo3LOS2FB4SEPFS3BUF2bs2FB3AP4S2LF3LFBS2FBFSFS2FBFFS2FBS2loS3MGFSFS2FBS2FBSS2FBFS2r'2R11r2KS1q1HS2FBFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2sp3MGF2lo3DS23sp13SP1FS2FBFS3BUF2pc3PC11q2Lw2Hq2q23Hq2S2r23RR2FS2FBFS2FBS1R2sp2lo4SLO43sp13SP1FS2sp3BUF2lo2bs3DS43sp13END3SP12EB1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL9FSS2FBFS2FBFFS1R2sp2lo4SLO33sp13SP1FS1R2lo3slo4SLOS4SLOL3ALO3ACVFS2bsFFFS2LF2sp3PAR2MD3MGF4SALT3BUF2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF02FB3sp13END3FB02EB3SPR4SP1R1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obs2r3FS2FBFFSFS2FBFS2sp2lo3SLO3sp13SP1FS2FB3FB0S2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obs2r3FS1R2sp2lo4SLO53sp13SP1S3BUF2bs3B47S1i2HiS2KSFS2sp2FB3sp13SP13FB04FBS13SPRFS2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp13obsFS3ALw2K9FS3BUF2bs3B473END2EB1q2Lw3HqL2q23ALw2ap3Hq24HAP23AL9S2LF2sp3PAR2MD3MGF4SALT3BUF2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF02FB3sp13END3FB02EB3SPR4SP1R1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obs2r3FFFS2lo3sp1SS1r2RR2KrS3sp12r04SP1M1q1r1H2H02q02H42FB3F64FFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1SFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB2FB3sp1FFFFFS1r2RRSFS2sp2lo3sp13SP1FS3END1q2Lw3HqL2q23Hq2S2FB3FB0S1R2sp2lo3slo3SLO4SLOS4SLOL3sp13SP13ALO3ACV3SPRS2LF2sp3PAR2MD3MGF4SALT3BUF2bs3LFB3B474PARB3MDB4MGFB5SALTB4BUF02FB3sp12pc3END3FB03PC13PC22EB3SPR4SP1RFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFFFFFFFS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS2LF3MGF2bs3LFB2FB3AP23obsS2LF2bs3LFB2FB3sp14FBS1S2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3D123D233D2P3SLO3DSP3DS13DS23DS32pc3END3PC12EB1q2Lw3Hqr2Hq3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPF3obsS2LF2bs3LFB2FB3sp14FBS1FFS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF3MGF3BUF2bs3LFB3D2B3END2EB1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obs4LENOS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2sp3PAR2MD3MGF4SALT3BUF2lo2bs3LFB3D123D233D2P3SLO3DSP3DS13DS23DS33sp12pc3END3SP13PC12EB1q2Lw3Hqr2Hq3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS2LF2sp2bs3LFB2FB3sp14FBS1S2LF3MGF2bs3LFB2FB3AP23obsS2LF2bs3LFB2FB3sp14FBS1S1R2LF2lo2bs3LFB3LOS2FB3sp14SEPF3obsS2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp13SP1S2LF2bs3LFB2FB3sp14FBS1S2LF3BUF2bs3LFB2FB2pc3END3AP43PC22KES2LF2sp2MD3MGF4SALT3BUF2lo2bs3LFB3D1B3D2B3D3B3SLO3DS13DS23DS33DS43sp12pc3END3SP13PC12EB1q2Lw3Hqr2Hq3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS2LF3MGF2bs3LFB2FB3AP23obsS2LF3MGF2bs3LFB2FB3AP23obsS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPF3obsS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2sp3MGF3BUF2lo2bs3LFB3SLO3DS23sp12pc3END3SP13PC12EB1q2Lw3Hqr2Hq3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS2LF3MGF2bs3LFB2FB3AP23obsS1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP13obsS2LF2sp2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FB3sp14FBS1S2LF2sp3BUF2lo2bs3LFB3DS43sp13END3SP12EB1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obs4LENOS2LF2sp3BUF2lo2bs3LFB3DS43sp13END3SP12EB1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obs4LENOS1R2LF2lo2bs3LFB3LOS3sp13ALO3ACV3obsS2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp2bs3LFB2FB3sp14FBS1S1R2LF2lo2bs3LFB3LOS2FB3sp14SEPF3obsS2LF3MGF4SALT2bs3LFB3D233obsS2LF2sp2bs3LFB2FB3sp14FBS1S2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP1S1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2sp2MD3BUF2lo2bs3LFB3SLO3DS13sp12pc3END3SP13PC12EB1q2Lw3Hqr2Hq3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS2LF2bs3LFB2FB3sp14FBS1S2LF2sp2MD3MGF4SALT3BUF2lo2bs3LFB3D123D233D2B3D3B3SLO3DS23DS43END2EB1q2Lw3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPF3obsS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF3MGF2bs3LFB2FB3AP23obsS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FB3sp14FBS1S1R2LF2sp2lo2bs3LFB3SLO3LOS2FB4SEPFS1R2LF2bs3LFB2FB3sp14SEPF3obsS2LF2sp4SALT3BUF2lo2bs3LFB3SLO3DS33sp12pc3END3SP13PC12EB1q2Lw3Hqr2Hq3HqL2q23ALw2ap3Hq24HAP14HAP23AL93obsS2LF2sp2bs3LFB3sp13SP1S1R2LF2sp3BUF2lo2bs3LFB3SLO3LOS3DS42FB3sp12pc3END3x253SP14SEPF3PC13PC22EB2KE2x23x263x273x324POSTS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPF3obsS1R2LF2lo2bs3LFB3LOS2FB3sp14SEPFS2LF2sp2MD2lo2bs3LFB3SLO3DS13sp13SP1S2LF2bs3LFB2FB3sp14FBS1S2LF2sp4SALT2lo2bs3LFB3SLO3DS33sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBFFFS2LF2sp2bs3LFB3sp13SP13obsS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB3obsS1R2LF2lo2bs3LFB3LOS3ALO3obsS1R2LF2lo2bs3LFB3LOS3ALOFFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1R3obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1R3obsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1RS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB2FB3sp14FBAL3FB03SPR4SP1RS1R2LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOFS2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP13obsS2LF2bs3LFB2FBFFFS2LF2bs3LFB2FBS2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3sp13obsS2LF2sp2lo2bs3LFB3sp1S2LF2bs3LFB2FB3obsS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2bs3LFB3sp1S2LF2bs3LFB2FBFS2LF2sp2bs3LFB3sp13SP1S2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP3obsS2LF2bs3LFB2FB3sp14FBS1S2LF2sp2lo2bs3LFB3sp13SP1S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2sp2lo2bs3LFB3SLO3sp13SP13obsS2LF2sp2lo2bs3LFB3SLO3sp13SP1FS1R3HIA1h2LF2sp2lo2bs3LFB3TOP4HTOPFFS2LF2lo2bs3LFBS2LF2lo2bs3LFB3obsS2LF2lo2bs3LFBS1R3HIA1h2LF2bs3LFB3obsFS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOS3obsS1R2LF3slo2bs3LFB4SLOSFFS2LF2bs3LFB2FBS2LF2bs3LFB2FB3sp14FBS1S2LF2sp2lo2bs3LFB3sp13SP1S2LF2sp2lo2bs3LFB3sp13SP13obsS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FBS1R2LF2lo2bs3LFB3LOS2FB4SEPFS1R2LF2lo2bs3LFB3LOS2FB4SEPF3obsS2LF2bs3LFB2FBFS2LF2bs3LFB2FB3sp14FBS1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF3BUF2bs3LFB3B47FS2LF2bs3LFB2FB3obs1c2HcFFFS1R2LF2lo2bs3LFB3LOSFS2LF2bs3LFB3sp13obsS2LF2bs3LFB2FBFFS2LF2bs3LFB2FBS2LF2sp2lo2bs3LFB3sp13SP13obsS2LF2sp2lo2bs3LFB3sp13SP1S2LF2bs3LFB2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOP3obsS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS2LF2sp2lo2bs3LFB3sp13SP1S2LF2sp2lo2bs3LFB3sp13SP13obsS2LF2sp2lo2bs3LFB3sp13SP1S2LF2bs3LFB3sp14SP1RS2LF2bs3LFB3sp14SP1R3obsS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB2FBS2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB03obsS2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB0S2LF2bs3LFB2FB3FB03obsS2LF2bs3LFB2FB3FB03obsS2LF2bs3LFB2FB3FB0". (* [comment removed for export] *)
  #[using="IMG GSBH MCI GT GI GALG GHASH pp plen LFB HAP B47 D12 D13 D23 D2P D3P D1B D2B D3B AL2 AL3 PARB MDB MGFB SALTB BUF0 SLO SLO3 RTS0 SLO4 SLO5 RTB0 SLOS SLOL LOS TOP SPH DSP DS1 DS2 DS3 DS4 CR1 CR2 CR3 CR4 CW1 CW2 CW3 TPV"] Lemma mgf_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss_B ()) "PFB,$3.Psp1,$3.Ph1,(?.$10.VR,VHIA,)Pm0,P,(9.&40.)(11.(9.&8.))Pmm,P,(9.&40.)(11.(9.&8.))Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Pxra,(9.&40.)Px5,(9.&40.)Px6,(9.&40.)Px7,(9.&40.)Px10,(9.&40.)Px11,(9.&40.)Px12,(9.&40.)Px13,(9.&40.)Px14,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Px17,(9.&40.)Ps5v,(9.&40.)Ps10v,(9.&40.)Px28,(9.&40.)Px29,(9.&40.)Px30,(9.&40.)Px31,(9.&40.)Ppc,$3.PEND,$3.Plw,(9.&40.)Ptw,(9.&40.)Pia1,(9.&40.)Pia2,(9.&40.)Pia3,(9.&40.)Pia4,(9.&40.)Pib1,(9.&40.)Pib2,(9.&40.)Pib3,(9.&40.)Pib4,(9.&40.)Pv1,(9.&40.)Pv2,(9.&40.)Pv3,(9.&40.)P,(12.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VPAR,VMD,VMGF,VSALT,VBUF,Vlo,Vslo,Vbs,R29.R28.R27.R26.R25.R24.R23.R22.)P,(13.$10.R26.(6.R2:.+20.)(14.$15.(16.(17.&40.R10.))(18.$15.)))P,(13.$10.R27.(6.R2;.+40.)(14.$15.(16.R?.)(18.$15.)))P,(13.$10.R28.(6.R2<.+>0.)(14.$15.(19.R?.)(18.$15.)))P,(13.$10.R29.(6.R2=.+60.)(14.$15.(19.R?.)(14.$15.(19.R>.)(14.$15.(16.R=.)(14.$15.(16.R<.)(18.$15.))))))P,(13.$10.R2:.(6.R2>.+:0.)(14.$15.(19.R<.)(14.$15.(19.R;.)(14.$15.(16.R:.)(14.$15.(16.R9.)(18.$15.))))))P,(13.$10.R2;.(6.R2>.+18.)(14.$15.(16.(17.&40.(6.R2?.+40.)))(18.$15.)))P,(13.$10.R2<.VMD,(14.$15.(19.R:.)(18.$15.)))P,(13.$10.R2=.VMGF,(14.$15.(19.R:.)(18.$15.)))P,(13.$10.R2>.VSALT,(14.$15.(19.R:.)(18.$15.)))P,(24.$10.R2?.VBUF,Vbs,)P,(25.$10.(1;.VR,)(1<.$10.VR,VHIA,Vh,)R30.VBUF,(7.(8.(9.&8.)Vbs,)))P,(5.VBUF,R1;.)P,(5.R1<.R1;.)P,(5.R1<.(6.VBUF,(7.(8.(9.&8.)Vbs,))))(1:.$10.(1;.VR,)(1<.$10.VR,VHIA,Vh,)(1=.$10.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,R35.)(1>.(1?.R30.(17.&40.R37.)Vgp,Vtp,R2?.R2>.R2=.Vsp,(17.&40.R37.)R2<.R2;.R2:.R29.R28.R27.R26.R25.(17.&40.R38.)(17.&40.VSALT,)(17.&40.VMGF,)R24.(17.&40.(6.R38.+20.))(17.&40.R1=.)(17.&40.R38.)(17.&40.(6.R38.+60.))R23.(17.&40.(6.(20.R38.+3.)(21.(1;.VR,))))R22.R21.R20.R1?.)VF,(17.&40.+:;934.)Vfc,(22.(9.&40.))R34.(23.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until v3. intros D HPL HLN HTRL HAID HAPR SL24 HMD HMGF HSALT HBUF OBUF PC1 PC2 EB.
    fctx_open D.
    rt_facts.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP. rewrite ETOP, ESTK in HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    assert (SP16 : sp1 mod 16 = 0) by (clear - SP1M; Z.div_mod_to_equations; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV; lia).
    assert (INF : In (FB, 256) ((FB, 256) :: LF)) by (left; reflexivity).
    assert (INH : In (FB, 24) (LB ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; left; reflexivity).
    assert (IND : In (FB + 32, 216) (LB ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *)
      zstep.
      eapply epi_walk with (r := 0); first [ fctx_build | eassumption | clear; lia | match goal with |- ?g => idtac "M-RET0-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 6 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    frame_aobj FSH (FB + 32) 1%nat as OPL.
    frame_aobj FSH (FB + 64) 1%nat as OLENP.
    pose proof (hm_abase asegs R HIA h1 _ _ m4 HH) as AB.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "M-GT-CALL".
    callxA_sp sp1 (eapply SPT with (CS := CS) (PP := FB + 32) (LENP := FB + 64) (P := pc) (END := END) (BUF := BUF) (bs := bs) (tag := 161) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by qlia; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA)); try solve_crange; try qlia; try pqlia).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "M-GT-LEFT:" g end.
    clear SPT OPL OLENP.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (FB + 64) [C8 ?lq] |- _ => rename H into HL5; rename lq into Lw end.
    match goal with H : rw_cells _ m5 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HP5; rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into RR end.
    match goal with H : pc <= q <= _ |- _ => rename H into Hqr end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases K98; zify_cond K98.
    { (* [comment removed for export] *)
      idtac "M-SKIP".
      eapply salt_walk with (pc := q); first [ fctx_build | eassumption | clear - Hqr PC1; lia | clear - Hqr; lia
                                             | match goal with |- ?g => idtac "M-SKIP-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "M-GT-ERR".
      eapply err_walk; first [ fctx_build | eassumption | clear - RR; lia | match goal with |- ?g => idtac "M-GT-ERR-LEFT:" g end ]. }
    assert (R0 : r = 0) by (clear - Kr RR; rewrite ?unsigned_lit in Kr by lia; lia). subst r. destruct (HL0 eq_refl) as [Hq HqL]. clear HL0 Kr RR K98.
    (* [comment removed for export] *)
    do 9 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : rw_cells _ m6 (Z.shiftr FB 3 + al_sb AL) ?cs |- _ => rename H into FSH6 end.
    frame_aobj FSH6 (FB + 32) 1%nat as OPL.
    frame_aobj FSH6 (FB + 96) 3%nat as OAID.
    frame_aobj FSH6 (FB + 160) 3%nat as OAPR.
    pose proof GALG as SPG. unfold asn1_get_alg_stmtA, A_ASN1_GET_ALG in SPG. specialize SPG with (h := h1). rewrite ECS, ETOP in SPG.
    idtac "M-GALG-CALL".
    callxA_sp sp1
      (eapply SPG with (LB := LB) (LF := (FB, 256) :: LF) (PP := FB + 32) (ALG := FB + 96) (PAR := FB + 160) (P := q) (END := q + bv_unsigned Lw)
                       (BUF := BUF) (bs := bs) (lo := lo);
       rewrite ?(unsigned_lit sp1) by qlia;
       first [ eassumption | reflexivity | exact OPL | exact OAID | exact OAPR | exact LOS | exact BUF0 | exact SP16
             | lazymatch goal with
               | |- BUF <= q => clear - Hqr PC1; lia
               | |- q <= q + _ => clear - LR; lia
               | |- q + _ <= BUF + _ => clear - HqL EB; lia
               | |- BUF + _ < 2 ^ 63 => clear - B47; lia
               | |- FB + _ + _ <= FB + _ \/ _ => clear; lia
               | |- _ = 0 \/ FB + _ + _ <= BUF \/ _ => clear - AP4; lia
               | |- (FB + _) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
               | |- 0 < FB + _ => clear - FB0; lia
               | |- lo <= sp1 - 32 - _ => clear - SLO4 SP1; lia
               | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
               | |- FB + _ + _ <= lo \/ _ => left; clear - SEPF LOS; lia
               | |- _ = 0 \/ BUF + _ <= lo \/ _ => clear - DS4 SP1; lia
               | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
               end
             | match goal with |- ?g => idtac "M-GALG-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "M-GALG-LEFT:" g end.
    clear SPG OPL OAID OAPR.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : rw_cells _ m7 (FB + 96) [C4 ?c1; C4 ?c2; C8 ?c3; C8 ?c4] |- _ => rename H into FALG; rename c3 into ALw; rename c4 into APw end.
    match goal with H : rw_cells _ m7 (FB + 160) [C4 ?c1; C4 ?c2; C8 ?c3; C8 ?c4] |- _ => rename H into FPAR; rename c1 into Qtg; rename c2 into Qpd; rename c3 into QLw; rename c4 into QPw end.
    match goal with H : rw_cells _ m7 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HP7; rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r2 end.
    match goal with H : r2 = 0 -> _ |- _ => rename H into HA0 end.
    match goal with H : _ < r2 <= 0 |- _ => rename H into RR2 end.
    match goal with H : q <= q2 <= _ |- _ => rename H into Hq2 end.
    pose proof (bv_unsigned_in_range 64 ALw) as ALR. unfold bv_modulus in ALR. cbn [Z.pow Z.of_N Pos.pow] in ALR.
    pose proof (bv_unsigned_in_range 64 QLw) as QLR. unfold bv_modulus in QLR. cbn [Z.pow Z.of_N Pos.pow] in QLR.
    (* [comment removed for export] *)
    do 6 zstep.
    ddestruct (x509_err_select r2 18446744073709542656 ltac:(clear - RR2; lia) ltac:(clear; lia)) as (r' & ER & R1 & R2 & R3).
    first [ rewrite ER | match goal with |- ?g => idtac "M-SELECT-FORM:" g end ]. clear ER.
    (* [comment removed for export] *)
    zstep. if_cases KS; zify_cond KS.
    { idtac "M-GALG-ERR".
      assert (NE : r2 <> 0) by (intros E0; pose proof (proj2 R2 E0) as E'; clear - E' KS; subst r'; rewrite ?unsigned_lit in KS by lia; lia).
      specialize (R3 NE).
      eapply epi_walk with (r := r'); first [ fctx_build | eassumption | clear - R3 RR2; lia | match goal with |- ?g => idtac "M-GALG-ERR-LEFT:" g end ]. }
    assert (R20 : r2 = 0).
    { apply (proj1 R2). clear - KS R1. rewrite ?Z_to_bv_unsigned in KS. unfold bv_wrap, bv_modulus in KS. cbn [Z.pow Z.of_N Pos.pow] in KS.
      Z.div_mod_to_equations. lia. }
    assert (R'0 : r' = 0) by (apply (proj2 R2); exact R20). subst r'.
    subst r2. ddestruct (HA0 eq_refl) as (ap & qp & EAP & EQP & HAP1 & HAP2 & HQP). subst APw QPw. clear HA0 KS R1 R2 R3 RR2.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases K9; zify_cond K9.
    { (* [comment removed for export] *)
      idtac "M-LEN9".
      zstep. zstep.
      first [ replace (Z_to_bv 64 18446744073709543250) with (Z_to_bv 64 (-8366)) by (apply bv_eq; reflexivity)
            | match goal with |- ?g => idtac "M-LEN9-LIT-FORM:" g end ].
      eapply epi_walk with (r := -8366); first [ fctx_build | eassumption | clear; lia | match goal with |- ?g => idtac "M-LEN9-LEFT:" g end ]. }
    assert (AL9 : bv_unsigned ALw = 9) by (clear - K9 ALR; rewrite ?unsigned_lit in K9 by lia; lia).
    clear K9.
    (* [comment removed for export] *)
    do 5 zstep.
    replace (Z_to_bv 64 360848 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_memcmp_i R)) by (rewrite MCI; reflexivity).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    pose proof (hcs_img_cs R HIA h IMG GSBH) as ICS. pose proof (hm_img_shadow asegs R HIA) as ISH.
    set (obs := firstn (Z.to_nat 9) (skipn (Z.to_nat (ap - BUF)) bs)).
    assert (LENO : Z.of_nat (length obs) = 9) by (subst obs; apply bytes_at_sub_length; clear - HAP1 HAP2 AL9 Hq2 HqL EB; lia).
    lazymatch goal with HB : bytes_at _ m8 BUF bs |- _ =>
      assert (HOB : bytes_at asegs m8 ap obs) by (subst obs; eapply bytes_at_sub; [exact HB| exact HAP1| clear; lia| clear - HAP1 HAP2 AL9 Hq2 HqL EB; lia]) end.
    clearbody obs.
    lazymatch goal with OB : aobj _ _ _ m8 BUF _ |- _ =>
      assert (OOB : aobj asegs AL CS m8 ap 9) by (eapply aobj_sub; [exact OB| exact HAP1| clear - HAP1 HAP2 AL9 Hq2 HqL EB; lia]) end.
    ro_str 0x263e0 9%nat as ROS. img_aobj 0x263e0 9 as ORO.
    pose proof (artA_bcmp asegs R HIA) as SPB. specialize SPB with (h := h1). rewrite ECS, ETOP in SPB.
    idtac "M-BCMP-CALL".
    callxA_sp sp1
      (eapply SPB with (LB := LB) (LF := (FB, 256) :: LF) (P := 0x263e0) (Q := ap) (n := 9) (lo := lo) (qs := obs);
       rewrite ?(unsigned_lit sp1) by qlia;
       first [ exact ROS | exact HOB | exact ORO | exact OOB | exact LENO | exact LOS | eassumption | reflexivity
             | lazymatch goal with
               | |- lo <= sp1 - arl_need_bcmp R => clear - SLO5 SP1; lia
               | |- crange _ lo _ => eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]
               | |- 156640 + 9 <= lo \/ _ => left; clear - ACV ALO LOS; lia
               | |- ap + 9 <= lo \/ _ => clear - DS4 SP1 HAP1 HAP2 AL9 Hq2 HqL EB; lia
               | |- 9 = 0 \/ 156640 + 9 + 8 <= _ => right; clear; lia
               | |- 9 = 0 \/ ap + 9 + 8 <= _ => right; clear - B47 HAP1 HAP2 AL9 Hq2 HqL EB; lia
               | |- 9 < _ => clear; lia
               | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
               end
             | match goal with |- ?g => idtac "M-BCMP-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "M-BCMP-LEFT:" g end.
    clear SPB ROS ORO OOB ICS ISH.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB.
    2:{ (* [comment removed for export] *)
      idtac "M-NOTMGF1".
      zstep. zstep. zstep.
      first [ replace (Z_to_bv 64 18446744073709543250) with (Z_to_bv 64 (-8366)) by (apply bv_eq; reflexivity)
            | match goal with |- ?g => idtac "M-NOTMGF1-LIT-FORM:" g end ].
      eapply epi_walk with (r := -8366); first [ fctx_build | eassumption | clear; lia | match goal with |- ?g => idtac "M-NOTMGF1-LEFT:" g end ]. }
    clear KB.
    (* [comment removed for export] *)
    do 3 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    match goal with H : rw_cells _ m9 (Z.shiftr FB 3 + al_sb AL) ?cs |- _ => rename H into FSH9 end.
    frame_aobj FSH9 (FB + 160) 3%nat as OAPR.
    match goal with H : rw_cells _ m9 (FB + 160) _ |- _ => rename H into FPAR9 end.
    match goal with H : rw_cells _ m9 MGF _ |- _ => rename H into HMGF9 end.
    match goal with H : HM _ _ _ h1 _ _ m9 |- _ => rename H into HH9 end.
    match goal with H : stk _ m9 lo sp1 |- _ => rename H into ST9 end.
    match goal with H : sshad _ _ m9 slo sp1 |- _ => rename H into SS9 end.
    match goal with H : mem_inv _ m9 |- _ => rename H into MI9 end.
    idtac "M-HASH-CALL".
    eapply (evtA_cut_mono asegs AL CS (hcs asegs R HIA h1)).
    { eapply GHASH with (h := h1) (LB := LB) (LF := (FB, 256) :: LF) (ALG := FB + 160) (MGF := MGF) (BUF := BUF) (ap := qp) (atag := Qtg) (apad := Qpd) (alen := QLw) (lo := lo) (slo := slo) (bs := bs);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HH9 | exact FPAR9 | exact HMGF9 | exact ST9 | exact SS9 | exact MI9 | exact B47 | exact D2B | exact AL2 | exact MGFB | exact BUF0
              | exact RTS0 | exact RTB0 | exact SLOS | exact SLOL | exact SP16 | exact TPV | reflexivity
              | lazymatch goal with
                | |- (length _ < 512)%nat => cbn [length]; clear - LFB; lia
                | |- bytes_at _ _ _ _ => eassumption
                | |- (_ = 0 /\ _) \/ _ => clear - HQP Hq2 HqL EB QLR; lia
                | |- MGF + 4 <= FB + 160 \/ _ => clear - AP2; lia
                | |- (FB + 160) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- 0 < FB + 160 /\ _ => clear - FB0 FBS1 SP1 SPR; lia
                | |- lo <= sp1 - X509_HASH_STACK_A => unfold X509_HASH_STACK_A; clear - SLO SP1; lia
                | |- lo <= sp1 - 112 - _ => clear - SLO3 SP1; lia
                | |- lo <= sp1 - X509_HASH_STACK_A - _ => unfold X509_HASH_STACK_A; clear - SLO5 SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite ETOP; clear - SP1 TOP; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- FB + 160 + 24 <= lo \/ _ => left; clear - SEPF LOS; lia
                | |- MGF + 4 <= lo \/ _ => clear - DS2 SP1; lia
                | |- _ = 0 \/ BUF + _ <= lo \/ _ => clear - DS4 SP1; lia
                | |- client_range _ _ lo (FB + 160) 24 => apply (client_range_block _ _ _ _ _ _ _ IND); clear; lia
                | |- client_range _ _ lo MGF 4 => eapply client_range_inside; [exact CW2| exact SUBLF| clear; lia| clear; lia]
                | |- client_range _ _ lo BUF _ => apply cr_buf_in; exact SUBLF
                | |- client_wrange _ _ lo _ MGF 4 => rewrite ETOP; eapply client_wrange_inside; [exact CW2| exact SUBLF| clear; lia| clear; lia]
                | |- aobj _ _ _ _ (FB + 160) 24 => rewrite ECS; exact OAPR
                | |- aobj _ _ _ _ MGF 4 => rewrite ECS; eassumption
                | |- aobj _ _ _ _ BUF _ => rewrite ECS; eassumption
                end
              | match goal with |- ?g => idtac "M-HASH-PRE-LEFT:" g end ]. }
    { intros xq Hxq. first [ exact Hxq | rewrite <- ECS; exact Hxq ]. }
    intros ms' PO. unfold x509_hash_postA in PO. rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m10 & h2 & r3 & vh
                    & Ems & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SSlo2 & Ea0 & Hr3 & HMGF10).
    subst ms' a0'.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    clear HMGF9 SS9 MI9 OAPR ST9 HH9.
    try match goal with H : abase _ _ m9 |- _ => clear H end.
    rewrite ESTK in HP2.
    (* [comment removed for export] *)
    presA_transport HP2. clear HP2.
    (* [comment removed for export] *)
    assert (ECS2 : hcs asegs R HIA h2 = CS) by (rewrite Ehcs2; exact ECS).
    assert (ETOP2 : htop asegs R HIA h2 = htop asegs R HIA h) by (rewrite Ehtop2; exact ETOP).
    assert (ESTK2 : hstkhi asegs R HIA h2 = hstkhi asegs R HIA h) by (rewrite Estk2; exact ESTK).
    assert (EFLAG2 : hflag asegs R HIA h2 = hflag asegs R HIA h) by (rewrite Eflag2; exact EFLAG).
    assert (EVOL2 : havol asegs R HIA h2 = havol asegs R HIA h) by (rewrite Evol2; exact EVOL).
    assert (EFR2 : hfr asegs R HIA h2 = hfr asegs R HIA h) by (rewrite Efr2; exact EFR).
    assert (HKI2' : forall mo, HK asegs R HIA h2 mo <-> HK asegs R HIA h mo) by (intros mo; eapply iff_trans; [apply HKI2| apply HKI]).
    clear ECS ETOP ESTK EFLAG EVOL EFR HKI Ehcs2 Ehtop2 Estk2 Eflag2 Evol2 Efr2 HKI2.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KH; zify_cond KH.
    { idtac "M-HASH-ERR".
      eapply epi_walk with (h1 := h2) (r := r3); first [ fctx_build | eassumption | exact Hr3 | match goal with |- ?g => idtac "M-HASH-ERR-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KM; zify_cond KM.
    { idtac "M-MIS".
      eapply mis_walk with (h1 := h2); first [ fctx_build | eassumption | match goal with |- ?g => idtac "M-MIS-LEFT:" g end ]. }
    idtac "M-SALT".
    eapply salt_walk with (h1 := h2) (pc := q2); first [ fctx_build | eassumption | clear - Hq2 Hq Hqr PC1; lia | clear - Hq2 HqL Hqr; lia
                                                       | match goal with |- ?g => idtac "M-SALT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
