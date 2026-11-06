(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_info P_rsa_parse_pubkey.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_asn1_get_tag_stmt A_oid A_oid_pk_alg A_oid_ec_grp_algid
     A_asn1_get_bitstring_null A_pk_defs A_pk_info A_pk_type A_pk_parse_A A_pk_parse_B A_pk_parse_C A_pk_parse_D A_pk_parse_E.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_pk_parse_F () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.A_pk_parse_E.DINV2"; "OSSVerify.KrLib.Lib.Cells.C1"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.A.A_pk_parse_B.EPIQ"; "WalkPKF.Call.XF"; "OSSVerify.KrLib.A.A_pk_parse_D.TVAL"; "WalkPKF.Call.CQ"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.P.P_pk_info.pk_info_of"; "OSSVerify.KrLib.A.A_pk_info.A_PK_INFOS"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "WalkPKF.Call.SBQ"; "WalkPKF.Call.SCQ"; "OSSVerify.KrLib.LibA.ARt.wcover"; "WalkPKF.Call.SDQ"; "WalkPKF.Call.SEQ"].


(* [comment removed for export] *)
Lemma swrap32_as_modA : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31). reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L10736246414.7 L13045237767.9 L14897237694.9 L19405846407.9 L19629527575.10L23421541755.9 L23421687016.9 L32532082058.9 L32532259865.9 L38715811453.4 L42464375761.3 L4539841608.9  L8929279494.9  L8929359765.9  00000=00K00R00Y00g01001901F01S01V01Y01i02302=S1u2Hu1v1q2VDS1u1v2VB1q3V13S1u1v1qS1u1v1qS1u1v2VB1q3V13S1u1v1H1qS1u1v1H1qS1u1v2VB1q2LTS1u1v2VB1q2GES1uS1uS1u2Hu1v2VB1q2VDS1u1v2VB1qS1u1v2VB1q". (* [comment removed for export] *)
Lemma rsa_err_mapA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "Pu,$0.P,(1.=R1.)P,(2.(3.(4.&20.(5.R2.+6<.))(6.+2.+40.))+=.)(7.(2.(8.(6.+2.+1?.))(4.&20.(5.R3.+????????????<500.)))(2.(4.&20.(5.R3.+????????????<500.))=))")
(* [comment removed for export] *).
Proof.
  intros u Hu H. rewrite !swrap32_as_modA in *.
  pose proof (Z.mod_pos_bound (u + 108) (2^32) ltac:(lia)) as VB.
  pose proof (Z.div_mod (u + 108) (2^32) ltac:(lia)) as VD.
  set (v := (u + 108) mod 2^32) in *. set (q := (u + 108) / 2^32) in *.
  assert (E1 : (u + 108 + 2^31) mod 2^32 = (v + 2^31) mod 2^32).
  { replace (u + 108 + 2^31) with (v + 2^31 + q * 2^32) by lia. apply Z_mod_plus_full. }
  rewrite E1 in H.
  assert (V13 : v < 13).
  { destruct (Z_lt_dec v (2^31)) as [LT|GE].
    - rewrite (Z.mod_small (v + 2^31) (2^32)) in H by lia. rewrite Z.mod_small in H by lia. lia.
    - replace (v + 2^31) with (v - 2^31 + 1 * 2^32) in H by lia. rewrite Z_mod_plus_full in H. rewrite (Z.mod_small (v - 2^31) (2^32)) in H by lia.
      replace (v - 2^31 - 2^31) with (v - 2^32 + 2^64 + (-1) * 2^64) in H by lia. rewrite Z_mod_plus_full in H. rewrite Z.mod_small in H by lia. lia. }
  assert (E2 : (u + 18446744073709536512 + 2^31) mod 2^32 = v + 2^31 - 15212).
  { replace (u + 18446744073709536512 + 2^31) with (v + 2^31 - 15212 + (q + 2^32) * 2^32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite E2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section WalkPKF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_PK.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_PK.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP END PKA lo STKk : Z) (P BUF : Z) (bs : list byte).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis STK0 : 176 + arl_need_smalloc R <= STKk.
  Hypothesis SLO : lo <= bv_unsigned sp - STKk.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis PKB : 0 <= PKA /\ PKA + 16 <= 2^64.
  Hypothesis ENDB : 0 <= END < 2^64.

  Local Notation BLEN := (Z.of_nat (length bs)).
  Local Notation X00 := [(PP, PP + 8); (PKA, PKA + 16)].
  Hypothesis HBS0 : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, BLEN) LB.
  Hypothesis BP : BUF <= P. Hypothesis PE : P <= END. Hypothesis EB : END <= BUF + BLEN.
  Hypothesis B47 : BUF + BLEN < 2^47. Hypothesis BUF0 : 0 < BUF. Hypothesis BL30 : BLEN < 2^30.
  Hypothesis PPAL : PP mod 8 = 0. Hypothesis PP0 : 0 < PP. Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PKAL : PKA mod 8 = 0. Hypothesis PK0 : 0 < PKA. Hypothesis PKLO : PKA + 16 <= lo.
  Hypothesis CWK : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PKA 16.
  Hypothesis DPK : PP + 8 <= PKA \/ PKA + 16 <= PP.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + BLEN <= PP.
  Hypothesis DKB : PKA + 16 <= BUF \/ BUF + BLEN <= PKA.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_PK in UARG; unfold A_SMALLOC_2_PK in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation F1 := (C1 (Z_to_bv 8 241)). Local Notation F2 := (C1 (Z_to_bv 8 242)). Local Notation F3 := (C1 (Z_to_bv 8 243)).
  Local Notation F8 := (C1 (Z_to_bv 8 248)). Local Notation Z0 := (C1 (Z_to_bv 8 0)). Local Notation P4 := (C1 (Z_to_bv 8 4)).
  Local Notation FSH0 :=
    [F1; F1; F1; F1;  F8; F8; F2; F2;  F8; F8; F8; F2;  F2; F2; F2; F2;  Z0; F2; F2; F2;  Z0; Z0; Z0; F2;  F2; F2; F2; F2;  P4; F2; P4; F3].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis STK2 : 176 + 32 + arl_need_bcmp R <= STKk.
  Hypothesis RTCL : forall mx, arl_rtc R mx -> asan_rtc mx.

  Local Notation EPIQ' := (A_pk_parse_B.EPIQ R HIA LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo).
  Local Notation DINV2' := (A_pk_parse_E.DINV2 R HIA LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP END PKA lo P BUF bs).
  Local Notation TVAL' := (A_pk_parse_D.TVAL).

  (* [comment removed for export] *)
  Definition XF (hq : HST asegs R HIA) (LBq : list blk) (WB : list ivl) (m2x : mem) (p' : Z) (pk0 pk1 : word) (mm : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "(7.(9.$:.VR,VHIA,O8.O7.VLF,(;.&40.Vsp,)(<.VR,)O6.O5.O1.)(7.(=.$:.O1.VPP,(>.$?.(10.(11.&40.O4.))(12.$?.)))(7.(7.(1.VP,O4.)(1.O4.VEND,))(=.$:.O1.VPKA,(>.$?.(10.O3.)(>.$?.(10.O2.)(12.$?.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition CQ (RA ENTRY : Z) (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem)
      (kv : word) (p2 e1 : Z) (pk0 pk1 a0v a1v a2v s4v s6v s9v : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "Lms,$13.(14.P,(15.&40.)(16.(15.&8.))Lmm,P,(15.&40.)(16.(15.&8.))(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt1,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La3,(15.&40.)(14.(15.&40.)La4,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(7.(17.$13.R>.(18.(19.(11.&40.O14.)(11.&40.O?.)Vgp,Vtp,R<.R;.R:.Vsp,(11.&40.O?.)O6.O5.O4.R9.R8.R7.R6.R5.(11.&40.O10.)(11.&40.O10.)O3.(11.&40.O9.)O2.(11.&40.VPKA,)(11.&40.(1:.(1;.VR,)))O1.(11.&40.(5.O10.+40.))(11.&40.(5.(1<.O10.+3.)(1:.(1;.VR,))))R4.R3.R2.R1.)VF,(11.&40.O13.)Vfc,(1=.(15.&40.))R=.(1>.$:.)))(7.(1?.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,O12.O10.O?.O>.O=.(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?3.))(12.$?.)))))))))))))))))))))))))))))))))O;.O:.O9.O8.O7.R=.)(9.$:.VR,VHIA,O>.O=.VLF,(;.&40.Vsp,)(<.VR,)O11.O<.R=.))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11158032613.79L25876784085.20L29784460045.79L39348729613.79L45146172909.7900000O01101K01g03GS2LF2sp2PP3PKA2bs3LFB1B1k2H02HkS1B1k2r02HB2Hk1a2Ha1q1r1H2H02q02H4S2LF2sp2PP3PKA2bs3LFB1B2H0S1R2LF2sp2PP3PKA2bs3LFB1B2H0S1R2LF2sp2PP3PKA2lo4STKk3BUF2bs3SLO3LFB3PPB3PKB3PP03PK04PKLO3DPK3DPB3DKB3NB14STK21B1k2H02Hk1a2Ha". (* [comment removed for export] *)
  #[using="LF sp PP PKA lo STKk BUF bs SLO LFB PPB PKB PP0 PK0 PKLO DPK DPB DKB NB1 STK2"] Lemma aobj_partial : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "PCSx,P,$0.SpPmX,P,(15.&40.)(16.(15.&8.))PB,$0.Pk,$0.P,(=.$:.R3.(5.(1<.R2.+3.)(1:.(1;.VR,)))(>.$?.(20.(11.&8.R1.))(12.$?.)))P,(17.$0.(3.R3.+8.)=)P,(1.=R4.)P,(7.(1.+1.R4.)(1.R4.+7.))P,(21.R8.R6.R5.)(22.$:.(1;.VR,)R9.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros CSx mX B k H HB H0 Hk HC. split; [exact HC|]. intros a Ha. exists (Z_to_bv 8 k). split.
    - rewrite (shadow_of_granule AL a B HB ltac:(lia)).
      replace (shadow_of AL B) with (Z.shiftr B 3 + al_sb AL) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
      destruct H as [[_ HB'] _]. cbn [cells_bytes cbytes app] in HB'. exact HB'.
    - right. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
      clear - Ha HB Hk. Z.div_mod_to_equations. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Tactic Notation "partial_aobj" constr(FSHx) constr(idx) constr(A) constr(hq) "as" ident(OH) :=
    let FSc := fresh "FSc" in let FSa := fresh "FSa" in let FSb := fresh "FSb" in let FS1 := fresh "FS1" in let FSd := fresh "FSd" in
    pose proof FSHx as FSc; chunk_split FSc idx FSa FSb; chunk_split FSb 1%nat FS1 FSd; clear FSa FSd;
    lazymatch type of FS1 with rw_cells _ ?mx ?a _ =>
      replace a with (Z.shiftr A 3 + al_sb AL) in FS1
        by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; lazymatch goal with F64x : _ mod 64 = 0 |- _ => clear - F64x; Z.div_mod_to_equations; lia end);
      assert (OH : aobj asegs AL (hcs asegs R HIA hq) mx A 4)
        by (apply (aobj_partial _ mx A 4 FS1);
            [ lazymatch goal with F64x : _ mod 64 = 0 |- _ => clear - F64x; Z.div_mod_to_equations; lia end
            | lazymatch goal with F0x : 0 < ?fb |- _ => lazymatch A with context [fb] => clear - F0x; lia end end
            | clear; lia
            | lazymatch goal with CFBx : crange _ _ 256 |- _ => eapply crange_sub; [exact CFBx| clear; lia| clear; lia] end ])
    end; clear FS1.

  Ltac open_dinv2 D :=
    destruct D as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & o0 & o1 & o2 & o3 & ptag & ppad & plen
                   & HHq & FHD & LPKC & LOID & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MIq
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & PPC & PRES).

  Ltac merge_stk :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with SL : rw_cells _ mx (?q + 8) [C8 _; C8 _; C8 _], S48 : rw_cells _ mx (?q + 48) [C8 _],
                          STA : stk _ mx ?q (?q + 8), STB : stk _ mx (?q + 32) (?q + 48), STC : stk _ mx (?q + 56) _ |- _ =>
        chunk_to_stk SL; chunk_to_stk S48;
        stk_merge_into STA SL; stk_merge_into STA STB; stk_merge_into STA S48; stk_merge_into STA STC end end.

  (* [comment removed for export] *)
  Ltac at_done :=
    lazymatch goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb AL) _ |- _ => norm_b8 H end;
    apply evtA_done.
  Ltac epiq_body :=
    unfold A_pk_parse_B.EPIQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    deexists 25; deexists 32; split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | (unfold XF; repeat match goal with |- _ /\ _ => split end; first [ eassumption | idtac ]) | idtac ].
  Ltac cq_body :=
    unfold CQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    deexists 12; split; [reflexivity|]; split; [| eassumption];
    unfold A_pk_parse_E.DINV2; deexists 9; eexists; deexists 7;
    repeat match goal with |- _ /\ _ => split end; first [ eassumption | idtac ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L13022865252.74L17510108875.72L19343747074.72L40819170905.72L66392575453.7500001E01\02602K02gS1R2LF2sp2PP3PKA2lo4STKk3BUF2bs3SLO3LFB3PPB3PKB3PP03PK04PKLO3DPK3DPB3DKB3NB14STK21u1ES2LF2sp2PP3PKA2bs3LFB1uS2LF2sp2PP3PKA2bs3LFB1u2HuS2LF2sp2PP3PKA2bs3LFBS2LF2sp2PP3PKA2bs3LFB1u1x2X4". (* [comment removed for export] *)
  #[using="R LF sp PP PKA lo STKk BUF bs SLO LFB PPB PKB PP0 PK0 PKLO DPK DPB DKB NB1 STK2"] Lemma lor4_13 : forall u, 0 <= u -> Z.lor u 4 = 13 -> u = 9 \/ u = 13.
  Proof.
    intros u Hu H. pose proof (Z.add_lor_land u 4) as E. rewrite H in E.
    set (x := Z.land u 4) in *.
    assert (X4 : 0 <= x <= 4). { subst x. split; [apply Z.land_nonneg; lia|]. rewrite Z.land_comm. apply MpiCoreAux.land_le_l; lia. }
    assert (XX : Z.land x 4 = x). { subst x. rewrite <- Z.land_assoc. rewrite (Z.land_diag 4). reflexivity. }
    assert (X04 : x = 0 \/ x = 4).
    { assert (C5 : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4) by lia.
      destruct C5 as [E0|[E0|[E0|[E0|E0]]]]; rewrite E0 in XX |- *; cbn in XX; first [left; reflexivity| right; reflexivity| discriminate XX]. }
    clearbody x. destruct X04 as [-> | ->]; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SBQ (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem) (kv : word) (p5 e1 r : Z) (pk0 pk1 : word)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "Lms,$13.(23.(7.(24.(17.$0.O3.=))(25.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,O9.O9.VLB,O8.Vm,O=.O;.O:.(11.&40.O3.)(26.O9.O8.O<.O7.O5.O2.O1.)R1.))(23.(14.$0.Lid,$0.(14.(15.&40.)La2v,(15.&40.)(7.(17.$0.O3.=)(7.(23.(17.$0.R2.+9.)(17.$0.R2.+=.))(7.(23.(17.$0.(27.O6.)+2.)(17.$0.(27.O6.)+3.))(28.+:?5;<.+=6>24.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O2.O1.(11.&40.VPKA,)(11.&40.R2.)R1.(11.&40.VPP,)(11.&40.-4000.)(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))R3.))))))(23.(14.(15.&40.)La2v,(15.&40.)(7.(17.$0.O3.=)(7.(23.(17.$0.(27.O6.)+2.)(17.$0.(27.O6.)+3.))(28.+:?5:0.+:?670.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O2.O1.(11.&40.(5.O;.+:0.))(11.&40.VPKA,)R1.(11.&40.VPP,)(11.&40.-4000.)(11.&40.(5.O;.+>0.))R2.))))(23.(7.(17.$0.O3.=)(7.(17.$0.(27.O6.)+1.)(28.+:?55<.+;1180.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O2.O1.O1.(11.&40.O5.)(11.&40.(29.O4.O5.))(11.&40.VPP,)(11.&40.(5.O;.+20.))(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))R1.)))(14.$0.Lrc,$0.(14.(15.&40.)La1v,(15.&40.)(14.(15.&40.)La2v,(15.&40.)(14.(15.&40.)Ls6v,(15.&40.)(14.(15.&40.)Ls9v,(15.&40.)(7.(17.$0.O3.=)(7.(7.(2.(8.(6.+2.+1?.))R5.)(2.R5.=))(28.+:?61<.+;0178.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O2.O1.(11.&40.VPKA,)R4.R3.(11.&40.R5.)R2.R1.R6.))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "04k0@D16071854214.231D40338479819.220D43080244883.220D57793146470.220D59521016234.220D64280614944.220D9785981640.231 K12226132804.220K44164039966.220K64113782398.220L12221849778.2  L14215840308.216L14587613338.194L15756368110.21 L15822417165.1  L15934535645.1  L16078575714.11 L16137017629.204L1685717371.0   L17454813295.1  L1747688473.24  L17561480300.194L18538772363.2  L19131885611.1  L19684562151.1  L19700568303.21 L20491039487.191L21654730866.2  L21850448026.188L21866712442.1  L22078896779.2  L23268210308.0  L24023900370.0  L24624919580.216L2545017180.207 L2621559066.1   L26530156621.207L26864060502.223L27817441514.214L27817804316.216L27940730156.21 L29010379890.193L29010569984.184L29022582655.2  L30439224333.1  L32431276449.0  L33342826784.198L33695720602.191L3379302262.223 L33985112333.1  L3482475141.21  L34852063412.2  L35653441506.11 L36314615039.2  L363719563.2    L37353703961.195L37687006330.2  L38235734261.1  L38334051855.2  L38551529394.0  L38948636245.0  L39088874870.21 L39188636933.0  L39332115127.192L39332637397.0  L41083926835.196L41202928732.217L42411609006.0  L42921373482.214L43300649301.0  L43810982283.2  L44168158952.3  L45921596632.1  L47870616696.2  L494542275.189  L49893919779.2  L49952884613.192L50365866937.197L50616353292.191L50616353292.193L50616353292.195L50925318027.2  L51264064568.7  L52765036985.199L53530622489.207L53530622489.216L53735527649.192L56787311448.1  L57389109526.21 L576250010.207  L58039649675.2  L59272923917.1  L59308586248.2  L60098763854.3  L61900301956.0  L62406578796.192L64009471222.1  L64118060424.2  L64850595401.0  L66062374527.193L66062374527.194L66151427842.16 L66298372189.2  L66812728480.3  L67653551064.2  L67989683843.2  L7738195705.2   L8707557133.1   L881835912.0    L9080220944.4   L9356559676.13  L9783143000.1   O14061664741.231O14941307720.231O17217116232.231O18906182176.231O3821773283.231 O39302861384.231O42843274679.231O44938202843.231O45969540168.231O52616826440.231O55209884805.231O64474006218.231O65961212488.231P18523612460.231P21647862485.231P22094145580.231P29008688568.220P34857851411.231P356858156.231  P36312780344.220P37693867741.231P38605639612.222P38605639612.231P43817786156.231P47876372191.231P50927926572.231P58041177900.231P66292560634.231P66453878491.222P66453878491.231P66818508295.231P67988155428.231P7740881908.222 P7740881908.231 P7750690063.220 Q10033386496.205Q10046132249.202Q10592236593.216Q10594415769.218Q10649498761.227Q10651829299.207Q10651864072.226Q10752139055.220Q10821824020.222Q10821824020.231Q10883697563.202Q1195234662.206 Q12063573683.225Q12076400817.216Q12078415920.225Q12658605510.222Q12658605510.224Q12658605510.231Q12658605510.233Q13268182738.225Q13270328915.216Q13435319996.201Q13732992821.226Q15068987923.220Q15470177032.197Q1547996552.225 Q1554221501.216 Q16071706518.201Q16071854214.231Q16611301420.216Q16625916953.225Q17458927065.212Q17701933971.227Q17703789353.207Q17757173815.217Q1867768678.231 Q19135999389.212Q19136195757.201Q19198257066.205Q19546836326.216Q19561696871.204Q19940505025.209Q20187259808.216Q21162993424.203Q21293441397.220Q21538057956.219Q21540267236.220Q21767670690.231Q24064611734.220Q25745664918.217Q26314584654.222Q26314584654.231Q26316671538.203Q26827176686.204Q27663034001.216Q27783623434.216Q27798763327.225Q2803826605.231 Q28197635908.220Q29312881359.203Q29323580945.208Q29775981542.231Q30441621867.210Q30802955094.217Q31155634335.214Q31170348313.197Q31255363489.203Q31526414380.222Q31526414380.231Q3194347860.227 Q32459096316.216Q34669208210.217Q34863972393.231Q37427005260.202Q38144578741.217Q38144578741.226Q38461683681.216Q38463452116.225Q39285966485.216Q39600066135.227Q4133323135.225 Q4135371262.216 Q41638331817.202Q42024731732.202Q42445523223.216Q43082486931.219Q43138029699.222Q43138029699.231Q43324197004.211Q43324197006.213Q44298944140.203Q44298944140.217Q44298944140.226Q44301027056.222Q44301027056.231Q45482765142.224Q45482765142.233Q45669665938.209Q47228431932.222Q47228431932.231Q47386034592.205Q47390328249.202Q47799422583.202Q47801698636.225Q48117823211.220Q48119910507.222Q48119910507.231Q48234175664.219Q48523164961.213Q49698585326.218Q50556521588.206Q50558264627.203Q50558408971.202Q508607707.214  Q51725458861.204Q51740006843.205Q51740073104.215Q51959565844.210Q52747231024.220Q53440817288.203Q53441189040.202Q53580790879.219Q53913538102.201Q54520642956.203Q55026446740.215Q5596578838.222 Q5596578838.231 Q57759385376.206Q57828105177.231Q58207055645.218Q58974185687.219Q59617715404.225Q59619648079.225Q59621696206.216Q59709694911.231Q60714092706.208Q6085996819.203 Q61847600818.227Q63116569710.203Q63435846322.217Q63435846322.226Q64228675114.221Q64228675114.230Q64278663712.219Q65424847505.219Q65426765969.220Q66729066265.202Q66731311911.203Q66733293089.209Q66733420561.200Q66733423387.206Q66901779611.217Q66901779611.226Q67128036471.202Q67581897521.206Q67866752433.200Q67866754747.206Q67877226119.203Q67879566009.202Q68075300161.225Q6909946601.219 Q7243851811.211 Q7339423222.220 Q9356756743.223 Q9633884056.204 Q9644516505.216 Q9644583048.231 Q9672141798.231 00001G01H02@03<03=04405C06807107j07k09W0:;0;00;40;70;K0;o0<00<40<\0==0=>0=B0=F0>D0>h0>i0?J0?N0?O0?P0?Q0A=0Aa0Af0BJ0CQ0DW0E;0F00FT0FU0FV0FZ0F[0G>0Gb0Gc0Gg0Ha0Hb0I:0I;0I<0I`0Ia0Ie0Il0Im0In0Jg0Jh0KL0KM0L40LX0LY0LZ0L[0L\0L]0Lb0Lc0Ld0Ll0MT0N70N[0O?0Oc0Od0P80P[0Q?0Qc0RK0RP0R[0S?0S@0SD0SJ0ST0SU0T60T70T80T90T]0UA0U[0U\0U]0Ue0Uf0Ug0Uk0Ul0V;0Vn0W30W40W50W60W70W80W90W:0W;0W<0W=0W>0W?0W@0X@0XA0YA0ZY0[V0\V0]n0^o0_g0`_0a_0b_0c_0d_0e@0f80g00h90i90im0ja0l80m10mm0nF0o00oF10010F10G11;11o12I13713P13i14B15616>17218:18S18l19B19X19Y19o1:01:11:j1;f1<?1<X1=B1=X1>B1>a1>b1?L1?b1@81@g1AV1AW1AX1AY1AZ1BG1C41D41D51D_1EO1F?1F]1G31G]1H61HO1Hi1Hj1Ic1Jg1KH1LN1Lm1MW1Mm1NG1NH1NI1NJ1Nc1OM1ON1Oh1PF1Pd1Q=1QV1R@1RA1RZ1S31SM1Sg1T@1Tm1Tn1To1UY1VC1Va1W?1W]1XM1Y=1ZE1[M1\Q1]E1^91^h1_Z1`31`L1a_1bo1d?1d@1dj1eL1f:1fT1fn1gX1gn1hD1hn1ij1j[1k51kO1l@1lo1mI1n31n41n51nK1o=1og20Q20R20S20T20U21c21d22a23^23_23`25326F27227^28J29F2:?2;M2<I2=B2=`2>>2>W2>m2?_2@N2A=2Ao2BH2C22C\2C]2D<2DU2E12EM2ENS1R2LF2sp2PP3PKA2lo4STKk2bs3LOS3SLO3LFB3PPB3PKB3NB14STK22FB3sp12kv3SP13SPR4SP1R2F04PPBDFS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4info4PPBD2HB5Ha_st5Hl_stS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4info4PPBD2HB5Ha_st5Hl_st3pk1FS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv3pk14PPBD2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3PKA2bs3TOP3LFB3PPB3PKB2FB3sp12hq2kv3SP13ETq3SPR4SP1R2F04PPBDS2LF2PP2bs3LFB2FB2kv4info3APP4PPBD2HB5Ha_st5Hl_st3pk1S2LF2PP3BUF2bs3LFB2FB2kv4info3APB4PPBD2HB5Ha_st5Hl_st3pk1S2LF2PP3PKA2bs3LFB2FB2kv4info3APK4PPBD2HB5Ha_st5Hl_st3pk1FS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12kv2p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP13ALO3ACV2F0S2FBS1lS1X3KVR1r3KEC1q1H2H0S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDSS2FBS1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9S2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFS2FBS2FBS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F03F8'S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDS2FBFSSS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12kv2p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS1R2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBD2HB5Ha_st5Hl_st5SAEst5CM8st2x12HxS1R2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBD2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP13ALO3ACV2F0S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFFS2FBSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2FBS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F0FS1R3HIA1h2sp2lo3TOP4HTOPFFS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2loS2FB2F0SSS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP13ALO3ACV2F03F1'SS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDSS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDSFSFFS3sp1FFS2gv3GVRS2LF2sp2PP3PKA2bs3LFB3PKB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS3END2p52e14Hp2e3HeES2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB3PKB2FB3sp12kv4PPBDS3sp1S2FB3sp12F0S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2FBS1i2HiS1R2lo3LOSSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFFSS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2FB2r03F641q1r1H2H02q02H4FFS2sp3sp1FFS2FBSS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS3sp1FFFFFFFFFFFFFS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDFS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv4info3SP14FBLO4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv4info3SP14FBLO4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP3PKA2lo4STKk2bs3SLO3LFB4PKLO3NB14STK23sp12kv3SP14PPBDS1R2LF2PP3BUF2bs3LFB2FB2kv3APB4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3BUF2bs3LFB2FB2kv3APB4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS2LF2sp2PP2bs3LFB3sp12kv3SP14PPBDS1R2LF2PP3PKA2bs3LFB2FB2kv3APK4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3PKA2bs3LFB2FB2kv3APK4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk3BUF2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP13ALO4BUFC4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2PP2bs3LFB2FB2kv3APP4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv3APP4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv4info3ALO3F1'4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2kv4PPBDFS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP3PKA2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB4PPBDS2LF2PP2bs3LFB2kv4PPBDFS2LF2PP2bs3LFB2FB4PPBDFFS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv2F04PPBD2HBFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB4PPBDS2LF2PP2bs3LFB2FB4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv3SPR2F03F8'4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv3SPR2F03F8'4PPBDFFFFS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP13ALO4PPBDFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS2LF2PP2bs3LFB2FB4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB3sp12kv4PPBDFS2LF2sp2PP3PKA2bs3LFB3PKB4PKAL2FB3sp12kv3SPR4SP1R2F04PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB2FB3sp12kv3SP14HTOP4PPBD2HB5Ha_st5Hl_stS2LF2sp2PP2bs3LFB3sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv2F04PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDFFFS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_stFFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP2bs3TOP3LFB2FB3sp12kv3SP14HTOP4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv4info3ALO4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_stS1R2LF2PP3PKA2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB4PPBDS2LF2PP2bs3LFB2FB4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP2bs3TOP3LFB2FB2kv4HTOP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_st3pk1S2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_st3pk1S1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFFS2LF2PP2bs3LFB2FB4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFFFFS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3sp12kv3SP14PPBD2HB5Ha_st5Hl_stFS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp12kv3SPR4SP1R2F04PPBDS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PKAL2FB3sp12kv3SPR4SP1R2F04PPBDFFS1R2LF2sp2PP3PKA2bs3LFB3PPB3PKB2FB3sp12kv3SPR4SP1R2F03F8'4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3PKA2bs3LFB3PPB3PKB2FB3sp12kv3SPR4SP1R2F03F8'4PPBD2HB5Ha_st5Hl_st5SAEstS2LF2PP2bs3LFB2FB2kv3pk14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv3pk14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv3pk14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3sp12kv3SP14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFS2LF2PP2bs3LFB3sp12kv4SP1R4PPBDS2LF2PP2bs3LFB2FB2F04PPBDS2LF2PP2bs3LFB2FB2kv2F04PPBDS2LF2PP2bs3LFB2FB2kv2F04PPBDF". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB HBS0 BIN BP EB B47 BUF0 BL30 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB NB1 STK2 RTCL"] Lemma seg_B : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "PWX,(2:.$2;.)PWB,(2:.$2;.)PFB,$0.Psp1,$0.Phq,(2<.$:.VR,VHIA,)PLBq,(2:.$2=.)Pm2x,P,(15.&40.)(16.(15.&8.))Pmm,P,(15.&40.)(16.(15.&8.))Pkv,(15.&40.)Pp5,$0.Pe1,$0.Pr,$0.Pinfo,$0.Ppk1,(15.&40.)Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Pa1,(15.&40.)Pa2,(15.&40.)Pa3,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)P,(7.(1.(29.(;.&40.Vsp,)+;0.)R19.)(1.R19.(29.(;.&40.Vsp,)+:0.)))P,(17.$0.(3.R1:.+20.)=)P,Px,$0.P,(2>.$:.VR,VHIA,Vh,R1.)(2>.$:.VR,VHIA,R1<.R2.)P,(17.$0.(2?.$:.VR,VHIA,R1;.)(2?.$:.VR,VHIA,Vh,))P,(17.$0.(30.$:.VR,VHIA,R1<.)(30.$:.VR,VHIA,Vh,))P,(17.$0.(3.R1?.+40.)=)P,(31.VR,VLB,VLF,R20.+100.)P,(31.VR,R1>.VLF,R21.+100.)P,Pb,$2=.P,(32.$2=.R1.VLB,)(32.$2=.R2.R21.)P,(1?.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R25.R23.R22.R21.R20.(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?3.))(12.$?.)))))))))))))))))))))))))))))))))R1=.R1<.R1;.(11.&40.R19.)R18.R1>.)P,(9.$:.VR,VHIA,R22.R21.VLF,(;.&40.Vsp,)(<.VR,)R25.R20.R1?.)P,(23.(17.$0.R1<.=)(17.$0.R1<.-3?80.))P,P,(17.$0.R1=.=)(7.(17.$0.R1=.(33.$34.(27.R21.)))(32.$0.R1=.$34.))(35.$:.(1;.VR,)(2>.$:.VR,VHIA,R25.)(36.R29.R28.R27.R26.R25.R24.R23.R21.R20.R1?.R1>.(11.&40.R1=.)R1<.)(18.(19.(11.&40.+:?484.)(11.&40.R26.)Vgp,Vtp,R1;.R1:.R19.Vsp,(11.&40.R26.)(11.&40.R1>.)R18.R17.R16.R15.R14.R13.R12.(11.&40.R27.)(11.&40.R27.)(11.&40.VPP,)(11.&40.R1?.)(11.&40.-4000.)(11.&40.(5.R27.+:0.))(11.&40.(1:.(1;.VR,)))(11.&40.(5.R27.+>0.))(11.&40.(5.R27.+40.))(11.&40.(5.(1<.R27.+3.)(1:.(1;.VR,))))R11.R10.R?.R>.)VF,(11.&40.+:?484.)Vfc,(1=.(15.&40.))R22.(1>.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB RV INFO.
    open_dinv2 D.
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; apply SUBq; exact BIN).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (WLa : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WLq : wlow R LBq LF) by (split; [exact (proj2 (proj2 (proj2 PRESB)))| apply (art_data_lo asegs R HIA)]).
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]).
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPBD. cbn [cells_size csize Nat.add] in PPBD.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *)
      assert (RNZ : r <> 0) by (intros E0; rewrite E0 in KR; apply KR; reflexivity).
      merge_stk. at_done. unfold SBQ. left. split; [exact RNZ|]. epiq_body.
      all: first [ (clear - Hp2a Hp2e HeE; lia) | match goal with |- ?g => idtac "SB-EXIT-LEFT:" g end ]. }
    assert (R0 : r = 0).
    { destruct RV as [E0|E0]; [exact E0|]. exfalso. rewrite E0 in KR. vm_compute in KR. discriminate KR. }
    destruct (INFO R0) as [EINFO INFO1]. clear KR.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
    zstep. zstep. zstep.
    pose proof (bv_unsigned_in_range 64 (sx32 kv)) as KVR. unfold bv_modulus in KVR. cbn [Z.pow Z.of_N Pos.pow] in KVR.
    zstep. if_cases KEC; zify_cond KEC.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KRSA; zify_cond KRSA.
      + (* [comment removed for export] *)
        do 4 zstep. do 3 zstep.
        at_done. unfold SBQ. right; right; right; right. exists (-15488). deexists 4. split; [exact R0|]. split; [clear; lia|]. cq_body.
        all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SB-OTHER-LEFT:" g end ].
      + (* [comment removed for export] *)
        assert (TV1 : TVAL' kv = 1).
        { unfold A_pk_parse_D.TVAL. clear - KRSA KVR. rewrite ?unsigned_lit in KRSA by lia.
          assert (E1 : bv_unsigned (sx32 kv) = 1) by (first [exact KRSA | lia]). rewrite E1. reflexivity. }
        assert (EI : info = A_RSA_INFO) by (rewrite EINFO, TV1; reflexivity).
        do 6 zstep. do 5 zstep.
        (* [comment removed for export] *)
        do 8 zstep.
        match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH1 end.
        frame_aobj FSH1 (FB + 32) 2%nat as OL32.
        lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ hq _ _ mx |- _ =>
          pose proof (hm_abase asegs R HIA hq LBq _ mx HHc) as AB1; pose proof (RTCL mx (hm_rtc asegs R HIA hq _ _ mx HHc)) as RT1;
          pose proof (hm_img_shadow asegs R HIA hq _ _ mx HHc) as ISH1 end end.
        pose proof (hcs_img_cs R HIA hq IMG (proj2 (proj2 (proj2 IMG')))) as ICS.
        lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
          assert (OI1 : aobj asegs AL (hcs asegs R HIA hq) mx info 4) by (rewrite EI; eapply aobj_img; [exact ICS| exact ISH1| vm_compute; reflexivity]) end.
        pose proof (A_pk_get_type_spec AL IMG L) as GT'. unfold pk_get_type_stmtA, A_PK_GET_TYPE in GT'.
        (* [comment removed for export] *)
        zstep.
        callxA_sp sp1 (eapply GT' with (CS := hcs asegs R HIA hq) (A := FB + 32) (info := info) (lo := lo);
                       rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                       try (exact (art_alwf asegs R HIA));
                       first [ solve_crange
                             | (right; left; exact EI)
                             | (intros _; exact OI1)
                             | lazymatch goal with
                               | |- _ => clear - SP1 SP1M SLO NS1 NB1 STK0 STK2 F0 F1' F8' F64 ALO LOS ACP ACV; first [lia | Z.div_mod_to_equations; lia]
                               end
                             | match goal with |- ?g => idtac "GT-PRE-LEFT:" g end ]).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "GT-LEFT:" g end.
        clear OL32 AB1 RT1 OI1 ISH1.
        match goal with H : info = A_RSA_INFO -> ?t = 1 |- _ => pose proof (H EI) as TY1; clear H end.
        lazymatch type of TY1 with ?t = 1 => subst t end.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        zstep.
        zstep.
        (* [comment removed for export] *)
        do 3 zstep.
        lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ hq _ _ mx |- _ =>
          pose proof (hm_abase asegs R HIA hq LBq _ mx HHc) as AB2 end end.
        do 5 zstep.
        clear AB2.
        at_done. unfold SBQ. right; right; right; left. split; [exact R0|]. split; [exact TV1|]. cq_body.
        all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SB-RSA-LEFT:" g end ].
    - (* [comment removed for export] *)
      assert (TV23 : TVAL' kv = 2 \/ TVAL' kv = 3).
      { unfold A_pk_parse_D.TVAL. clear - KEC KVR.
        assert (E23 : bv_unsigned (sx32 kv) = 2 \/ bv_unsigned (sx32 kv) = 3) by (set (X := bv_unsigned (sx32 kv)) in *; clearbody X; Z.div_mod_to_equations; lia).
        destruct E23 as [E|E]; rewrite E; [left| right]; reflexivity. }
      partial_aobj FSHX 30%nat (FB + 240) hq as OGID.
      zstep. zstep. zstep. zstep.
      pose proof (bv_unsigned_in_range 64 (sx32 gv)) as GVR. unfold bv_modulus in GVR. cbn [Z.pow Z.of_N Pos.pow] in GVR.
      zstep. if_cases K13; zify_cond K13.
      + (* [comment removed for export] *)
        do 4 zstep.
        at_done. unfold SBQ. right; right; left. eexists. split; [exact R0|]. split; [exact TV23|]. cq_body.
        all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SB-ECP-LEFT:" g end ].
      + (* [comment removed for export] *)
        assert (GID : bv_unsigned (sx32 gv) = 9 \/ bv_unsigned (sx32 gv) = 13).
        { apply lor4_13; [clear - GVR; lia|]. clear - K13 GVR. rewrite ?unsigned_lit in K13 by lia.
          first [ exact K13 | (apply NNPP; exact K13) | lia ]. }
        frame_aobj FSHX (FB + 160) 3%nat as OPAR.
        do 4 zstep.
        zstep. if_cases KTAG; zify_cond KTAG.
        * (* [comment removed for export] *)
          zstep. zstep.
          zstep. if_cases KLEN; zify_cond KLEN.
          -- do 3 zstep.
             at_done. unfold SBQ. right; right; right; right. exists (-15616). deexists 4. split; [exact R0|]. split; [clear; lia|]. cq_body.
             all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SB-8410L-LEFT:" g end ].
          -- (* [comment removed for export] *)
             zstep. zstep.
             rewrite <- (Z_to_bv_bv_unsigned (sx32 gv)).
             destruct GID as [EG|EG]; rewrite EG.
             ++ at_done. unfold SBQ. right; left. exists 9. eexists. split; [exact R0|]. split; [left; reflexivity|]. split; [exact TV23|]. cq_body.
                all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SB-SG9-LEFT:" g end ].
             ++ at_done. unfold SBQ. right; left. exists 13. eexists. split; [exact R0|]. split; [right; reflexivity|]. split; [exact TV23|]. cq_body.
                all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SB-SG13-LEFT:" g end ].
        * (* [comment removed for export] *)
          do 2 zstep. do 3 zstep.
          at_done. unfold SBQ. right; right; right; right. exists (-15616). deexists 4. split; [exact R0|]. split; [clear; lia|]. cq_body.
          all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SB-8410T-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SCQ (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem) (kv : word) (p5 e1 r : Z) (pk0 pk1 : word)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "Lms,$13.(23.(14.(15.&40.)La1v,(15.&40.)(14.(15.&40.)La2v,(15.&40.)(14.(15.&40.)Ls9v,(15.&40.)(7.(24.(17.$0.O3.=))(28.+:?61<.+;0178.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O2.O1.(11.&40.VPKA,)R3.R2.(11.&40.O3.)(11.&40.-4000.)R1.R4.)))))(7.(17.$0.O3.=)(28.+:?5=8.+=71;<.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O2.O1.(11.&40.VPKA,)(11.&40.O5.)(11.&40.(29.O4.O5.))(11.&40.VPP,)(11.&40.-4000.)(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))R1.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L14215840310.186L24624919582.186L29010569984.185L35653441506.11 L38235734261.1  L38948636245.0  L39332637397.0  L41202928732.187L43300649301.0  L60098763854.3  L64850595401.0  L66151426447.10 L9080220944.4   L9356559676.13  Q10649498761.196Q10651864074.195Q13732992823.195Q17701933971.196Q3194347860.196 Q39600066135.196Q45353655733.195Q61847600818.19600001Y03B03C03[03_03`03a04B04C04M04N04^04m05`06306F06Y06l06m06n07A08;S1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDFS1R3HIA1h2sp2lo3TOP4HTOPS2loSSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDSS1R2lo3LOSSS1r2RR2r02KR1q1HS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDFFS2LF2PP2bs3LFB4PPBDS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBD". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB BIN BP EB BUF0 PPAL CWP CWK"] Lemma seg_C : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "PWX,(2:.$2;.)PWB,(2:.$2;.)PFB,$0.Psp1,$0.Phq,(2<.$:.VR,VHIA,)PLBq,(2:.$2=.)Pm2x,P,(15.&40.)(16.(15.&8.))Pmm,P,(15.&40.)(16.(15.&8.))Pkv,(15.&40.)Pp5,$0.Pe1,$0.Pr,$0.Ppk0,(15.&40.)Ppk1,(15.&40.)Pxra,(15.&40.)Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Pa1,(15.&40.)Pa2,(15.&40.)Pa3,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)P,(7.(1.(29.(;.&40.Vsp,)+;0.)R1:.)(1.R1:.(29.(;.&40.Vsp,)+:0.)))P,(17.$0.(3.R1;.+20.)=)P,Px,$0.P,(2>.$:.VR,VHIA,Vh,R1.)(2>.$:.VR,VHIA,R1=.R2.)P,(17.$0.(2?.$:.VR,VHIA,R1<.)(2?.$:.VR,VHIA,Vh,))P,(17.$0.(30.$:.VR,VHIA,R1=.)(30.$:.VR,VHIA,Vh,))P,(17.$0.(3.R20.+40.)=)P,(31.VR,VLB,VLF,R21.+100.)P,(31.VR,R1?.VLF,R22.+100.)P,Pb,$2=.P,(32.$2=.R1.VLB,)(32.$2=.R2.R22.)P,(1?.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R26.R24.R23.R22.R21.(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?3.))(12.$?.)))))))))))))))))))))))))))))))))R1>.R1=.R1<.R1:.R19.R1?.)P,(9.$:.VR,VHIA,R23.R22.VLF,(;.&40.Vsp,)(<.VR,)R26.R21.R20.)P,(7.(2.(8.(6.+2.+1?.))R1=.)(1.R1=.=))(35.$:.(1;.VR,)(2>.$:.VR,VHIA,R25.)(37.R29.R28.R27.R26.R25.R24.R23.R21.R20.R1?.R1>.R1=.R1<.)(18.(19.R1;.(11.&40.R26.)Vgp,Vtp,R1:.R19.R18.Vsp,(11.&40.R26.)(11.&40.R1>.)R17.R16.R15.R14.R13.R12.R11.(11.&40.R27.)(11.&40.R27.)(11.&40.VPP,)(11.&40.R1?.)(11.&40.-4000.)(11.&40.VPKA,)(11.&40.(1:.(1;.VR,)))(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))(11.&40.(5.R27.+40.))(11.&40.(5.(1<.R27.+3.)(1:.(1;.VR,))))R10.R?.R>.R=.)VF,(11.&40.+:?5;<.)Vfc,(1=.(15.&40.))R22.(1>.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB RR.
    open_dinv2 D.
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; apply SUBq; exact BIN).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (WLa : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WLq : wlow R LBq LF) by (split; [exact (proj2 (proj2 (proj2 PRESB)))| apply (art_data_lo asegs R HIA)]).
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]).
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPBD. cbn [cells_size csize Nat.add] in PPBD.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { assert (RNZ : r <> 0) by (intros E0; rewrite E0 in KR; apply KR; reflexivity).
      do 3 zstep.
      at_done. unfold SCQ. left. deexists 3. split; [exact RNZ|]. cq_body.
      all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SC-FREE-LEFT:" g end ]. }
    assert (R0 : r = 0) by (clear - KR RR; Z.div_mod_to_equations; lia).
    clear KR.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
    do 6 zstep.
    at_done. unfold SCQ. right. split; [exact R0|]. cq_body.
    all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SC-SPK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L35653441506.11 L38235734261.1  L38948636245.0  L39332637397.0  L43300649301.0  L60098763854.3  L64850595401.0  L66062374908.186L9080220944.4   L9356559676.13  Q10033454561.194Q47386101825.19400000H00L00M00N00O00Y00Z01601E02802i03PS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSS1R2lo3LOSSS2LF2sp2PP3PKA2bs3LFB2FB3sp1S2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB3sp13SP14HTOP". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB BIN BP EB BUF0 PPAL CWP CWK NB1 STK2"] Lemma seg_C4 : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "PWX,(2:.$2;.)PWB,(2:.$2;.)PFB,$0.Psp1,$0.Phq,(2<.$:.VR,VHIA,)PLBq,(2:.$2=.)Pm2x,P,(15.&40.)(16.(15.&8.))Pmm,P,(15.&40.)(16.(15.&8.))Pkv,(15.&40.)Pp5,$0.Pe1,$0.Pr,$0.Ppk0,(15.&40.)Ppk1,(15.&40.)Pxra,(15.&40.)Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Pa1,(15.&40.)Pa2,(15.&40.)Pa3,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)Ps9v,(15.&40.)P,(7.(1.(29.(;.&40.Vsp,)+;0.)R1;.)(1.R1;.(29.(;.&40.Vsp,)+:0.)))P,(17.$0.(3.R1<.+20.)=)P,Px,$0.P,(2>.$:.VR,VHIA,Vh,R1.)(2>.$:.VR,VHIA,R1>.R2.)P,(17.$0.(2?.$:.VR,VHIA,R1=.)(2?.$:.VR,VHIA,Vh,))P,(17.$0.(30.$:.VR,VHIA,R1>.)(30.$:.VR,VHIA,Vh,))P,(17.$0.(3.R21.+40.)=)P,(31.VR,VLB,VLF,R22.+100.)P,(31.VR,R20.VLF,R23.+100.)P,Pb,$2=.P,(32.$2=.R1.VLB,)(32.$2=.R2.R23.)P,(1?.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R27.R25.R24.R23.R22.(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?3.))(12.$?.)))))))))))))))))))))))))))))))))R1?.R1>.R1=.R1;.R1:.R20.)P,(9.$:.VR,VHIA,R24.R23.VLF,(;.&40.Vsp,)(<.VR,)R27.R22.R21.)P,(7.(2.(8.(6.+2.+1?.))R1>.)(1.R1>.=))(35.$:.(1;.VR,)(2>.$:.VR,VHIA,R26.)(37.R2:.R29.R28.R27.R26.R25.R24.R22.R21.R20.R1?.R1>.R1=.)(18.(19.R1<.(11.&40.R27.)Vgp,Vtp,R1;.R1:.R19.Vsp,(11.&40.R27.)(11.&40.R1?.)R18.R17.R16.R15.R14.R13.R12.(11.&40.R28.)(11.&40.R28.)(11.&40.VPP,)(11.&40.R20.)(11.&40.-4000.)(11.&40.VPKA,)(11.&40.(1:.(1;.VR,)))R=.(11.&40.(5.R28.+40.))(11.&40.(5.(1<.R28.+3.)(1:.(1;.VR,))))R11.R10.R?.R>.)VF,(11.&40.+:?5:0.)Vfc,(1=.(15.&40.))R23.(1>.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s9v. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB RR.
    pose proof D as D0. open_dinv2 D0.
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; apply SUBq; exact BIN).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (WLa : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WLq : wlow R LBq LF) by (split; [exact (proj2 (proj2 (proj2 PRESB)))| apply (art_data_lo asegs R HIA)]).
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]).
    zstep. zstep.
    eapply evtA_eq; [| eapply (seg_C WX WB FB sp1 hq LBq m2x mm kv p5 e1 r pk0 pk1); eassumption]. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SDQ (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem) (kv : word) (e1 r : Z) (pk0 pk1 : word)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "Lms,$13.(23.(14.(15.&40.)La1v,(15.&40.)(14.(15.&40.)La2v,(15.&40.)(7.(24.(17.$0.O3.=))(28.+:?61<.+;0178.O<.O;.O:.O9.O8.O7.O6.O5.O4.O4.O2.O1.(11.&40.VPKA,)R2.R1.(11.&40.O3.)(11.&40.-4000.)(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))R3.))))(7.(17.$0.O3.=)(25.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,O8.O8.VLB,O7.Vm,O<.O:.O9.(11.&40.=)(26.O8.O7.O;.O6.O4.O2.O1.)R1.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01>0@D25066864133.201D28498761192.201D37285929031.201D43863175048.201D4451634193.201 D60109196847.201K13481535851.201K2431698795.201 K38744182635.201K44164039966.201K49737312673.201K56923556715.201K61279323496.201K64038415723.201K9840090748.201 K9927252587.201 L1153949703.7   L13477261981.2  L1685717371.0   L17561480300.199L23182876091.2  L2419170461.2   L24624768681.11 L29010569984.189L32743128527.2  L33342826784.203L35653441506.11 L38235734261.1  L38748296349.2  L38948636245.0  L39332637397.0  L40051937615.2  L41083926835.201L41202928732.191L41202929119.189L43300649301.0  L44168742175.3  L49733071447.2  L50365866937.202L52765036985.204L53271535775.189L56911057053.2  L60098763854.3  L61277509919.2  L62406578796.197L64025917085.2  L64850595401.0  L66151426447.10 L68446757602.7  L9080220944.4   L9356559676.13  L9835808138.2   L9922970013.2   P23170010975.201P32737099528.201P40057967496.201Q10649498761.200Q10649498890.198Q10651864073.199Q10651864074.197Q13732992820.199Q13732992823.197Q17701933584.198Q17701933971.200Q28496781288.200Q28498761192.201Q3194347735.198 Q3194347860.200 Q37216054521.198Q39600066135.200Q39600066516.198Q4451634193.201 Q4453582353.200 Q45353655733.197Q45353655734.199Q61556549392.199Q61847600818.200Q61847600945.19800000100d00e00f01Y02U03A03m04Y05F06206^07K08708c09O09S09T09U0:60:70:80:d0:e0:f0;I0;a0;e0;f0;g0;h0;i0<P0=10=R0=S0=T0=U0>80>[0?<0?=0?G0?H0?i0?j0?k0@;0@N0@]0AP0AQ0AR0BV0Cb0Dn0EA0ET0Eg0F:0FM0F`0G30GF0Gk0HP0HQ0HR0Hl0Hm0Hn0IS0J80JK0J^0K>0L80M2FS2LF2sp2PP3PKA2bs3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stFFS2LF2sp2PP3PKA2bs3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP3PKA2lo2bs3LOS3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP3PKA2bs3LFB3DPK2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2e1FSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFFS3END1P3BUF4ENDB2BP4BUF02p52e14Hp2a4Hp2e3HeEFFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS1R3HIA1h2sp2lo3TOP4HTOPS2loFSSFS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDSFFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFS1R2lo3LOSFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFSS1r2RR2r02KR1q1HS1P2p52e14Hp2a4Hp2eS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRFFS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK22e14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12e13SP14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12e13SP14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stFFS2LF2PP2bs3LFB3PPB4PPBD2HBFFS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB3PPB4PPBD2HB5Ha_stS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBDS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBD". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB ENDB BIN BP EB BUF0 PPAL PPLO CWP PKLO CWK DPK DPB NB1 STK2"] Lemma seg_D : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "PWX,(2:.$2;.)PWB,(2:.$2;.)PFB,$0.Psp1,$0.Phq,(2<.$:.VR,VHIA,)PLBq,(2:.$2=.)Pm2x,P,(15.&40.)(16.(15.&8.))Pmm,P,(15.&40.)(16.(15.&8.))Pkv,(15.&40.)Pp5,$0.Pe1,$0.Pr,$0.Ppk0,(15.&40.)Ppk1,(15.&40.)Pxra,(15.&40.)Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Pa1,(15.&40.)Pa2,(15.&40.)Pa3,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)P,(7.(1.(29.(;.&40.Vsp,)+;0.)R1:.)(1.R1:.(29.(;.&40.Vsp,)+:0.)))P,(17.$0.(3.R1;.+20.)=)P,Px,$0.P,(2>.$:.VR,VHIA,Vh,R1.)(2>.$:.VR,VHIA,R1=.R2.)P,(17.$0.(2?.$:.VR,VHIA,R1<.)(2?.$:.VR,VHIA,Vh,))P,(17.$0.(30.$:.VR,VHIA,R1=.)(30.$:.VR,VHIA,Vh,))P,(17.$0.(3.R20.+40.)=)P,(31.VR,VLB,VLF,R21.+100.)P,(31.VR,R1?.VLF,R22.+100.)P,Pb,$2=.P,(32.$2=.R1.VLB,)(32.$2=.R2.R22.)P,(1?.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R26.R24.R23.R22.R21.(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?3.))(12.$?.)))))))))))))))))))))))))))))))))R1>.R1=.R1<.R1:.R19.R1?.)P,(9.$:.VR,VHIA,R23.R22.VLF,(;.&40.Vsp,)(<.VR,)R26.R21.R20.)P,(38.VR,VLB,VLF,(;.&40.Vsp,)R28.VPP,+8.)P,(38.VR,R24.VLF,(;.&40.Vsp,)R28.VPP,+8.)P,(7.(2.(8.(6.+2.+1?.))R1?.)(1.R1?.=))(35.$:.(1;.VR,)(2>.$:.VR,VHIA,R27.)(39.R2;.R2:.R29.R28.R27.R26.R25.R23.R21.R20.R1?.R1>.)(18.(19.R1=.(11.&40.R28.)Vgp,Vtp,R1<.R1;.R1:.Vsp,(11.&40.R28.)(11.&40.R20.)R19.R18.R17.R16.R15.R14.R13.(11.&40.R29.)(11.&40.R29.)(11.&40.VPP,)(11.&40.R21.)(11.&40.-4000.)(11.&40.VPKA,)(11.&40.(1:.(1;.VR,)))(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))(11.&40.(5.R29.+40.))(11.&40.(5.(1<.R29.+3.)(1:.(1;.VR,))))R12.R11.R10.R?.)VF,(11.&40.+:?5=8.)Vfc,(1=.(15.&40.))R24.(1>.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB WCa WCb RR.
    open_dinv2 D.
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; apply SUBq; exact BIN).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (WLa : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WLq : wlow R LBq LF) by (split; [exact (proj2 (proj2 (proj2 PRESB)))| apply (art_data_lo asegs R HIA)]).
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]).
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPBD. cbn [cells_size csize Nat.add] in PPBD.
    assert (E1R : 0 <= e1 < 2^64) by (clear - Hp2a Hp2e HeE ENDB BP BUF0; lia).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { assert (RNZ : r <> 0) by (intros E0; rewrite E0 in KR; apply KR; reflexivity).
      do 3 zstep.
      at_done. unfold SDQ. left. deexists 2. split; [exact RNZ|]. cq_body.
      all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SD-FREE-LEFT:" g end ]. }
    assert (R0 : r = 0) by (clear - KR RR; Z.div_mod_to_equations; lia).
    clear KR.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ hq _ _ mx |- _ =>
      pose proof (hm_abase asegs R HIA hq LBq _ mx HHc) as AB1 end end.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KEQ; zify_cond KEQ.
    2:{ exfalso. apply KEQ. reflexivity. }
    (* [comment removed for export] *)
    zstep. zstep.
    merge_stk. at_done. unfold SDQ. right. split; [exact R0|]. epiq_body.
    all: first [ (clear - Hp2a Hp2e HeE; lia) | match goal with |- ?g => idtac "SD-EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SEQ (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem) (kv : word) (p5 e1 : Z) (pk0 pk1 : word)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "Lms,$13.(23.(14.$0.Lrc,$0.(14.(15.&40.)La1v,(15.&40.)(14.(15.&40.)La2v,(15.&40.)(7.(7.(2.(8.(6.+2.+1?.))R3.)(2.R3.=))(28.+:?61<.+;0178.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.(11.&40.VPKA,)R2.R1.(11.&40.R3.)(11.&40.(5.O:.+20.))(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))R4.)))))(25.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,O8.O8.VLB,O7.Vm,O<.O:.O9.(11.&40.=)(26.O8.O7.O;.O6.O3.O2.O1.)R1.))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01>0@D25066864133.202D28498761192.202D37285929031.202D43863175048.202D4451634193.202 D60109196847.202K13481535851.202K2431698795.202 K38744182635.202K44164039966.202K49737312673.202K56923556715.202K61279323496.202K64038415723.202K9840090748.202 K9927252587.202 L13477261981.2  L14948329643.189L1685717371.0   L17561480300.199L23182876091.2  L2419170461.2   L24624768681.11 L32743128527.2  L33342826784.203L35653441506.11 L38235734261.1  L38748296349.2  L38948636245.0  L39332637397.0  L40051937615.2  L41083926835.201L41202929119.190L41202929119.191L43300649301.0  L44168742175.3  L49733071447.2  L50365866937.202L52225222276.0  L52765036985.204L53271535775.190L56911057053.2  L60098763854.3  L60242231282.2  L61277509919.2  L62406578796.197L64025917085.2  L64850595401.0  L68446757602.7  L9080220944.4   L9356559676.13  L9835808138.2   L9922970013.2   P23170010975.202P32737099528.202P40057967496.202Q10649498890.199Q10649498890.200Q10651864073.199Q10651864074.198Q13732992820.199Q13732992823.198Q17701933584.199Q17701933584.200Q28496781288.201Q28498761192.202Q3194347735.199 Q3194347735.200 Q37216054521.199Q39600066516.199Q39600066516.200Q4451634193.202 Q4453582353.201 Q45353655733.198Q45353655734.199Q61556549392.200Q61847600945.199Q61847600945.20000000100d00e00f01Y02U03A03m04Y05F06206^07K08708c09O09P09Q09R0:30:40:50:a0:b0;E0;]0;a0;b0;c0;d0;e0<L0<m0=N0=O0=P0=Q0>40>50>X0?90?:0?D0?M0?N0?o0@00@10@D0@S0AF0AG0AH0BL0CX0Dd0E70EJ0E]0F00FC0FV0Fi0G<0Ga0HF0HG0HH0Hb0Hc0Hd0II0In0JA0JT0K40Kn0LhFS2LF2sp2PP3PKA2bs3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stFFS2LF2sp2PP3PKA2bs3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP3PKA2lo2bs3LOS3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP3PKA2bs3LFB3DPK2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stFFSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFFS3END1P3BUF4ENDB2BP4BUF02p52e14Hp2a4Hp2e3HeEFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS1R3HIA1h2sp2lo3TOP4HTOPS2loFSSFS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDSFFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFS1R2lo3LOSS3a0w3A0RFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFSS1P2p52e14Hp2a4Hp2eS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRFFS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK22e14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12e13SP14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12e13SP14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stFFS2LF2PP2bs3LFB3PPB4PPBD2HBFFS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB3PPB4PPBD2HB5Ha_stS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBDS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBD". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB ENDB BIN BP EB BUF0 PPAL PPLO CWP PKLO CWK DPK DPB NB1 STK2"] Lemma seg_E : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "PWX,(2:.$2;.)PWB,(2:.$2;.)PFB,$0.Psp1,$0.Phq,(2<.$:.VR,VHIA,)PLBq,(2:.$2=.)Pm2x,P,(15.&40.)(16.(15.&8.))Pmm,P,(15.&40.)(16.(15.&8.))Pkv,(15.&40.)Pp5,$0.Pe1,$0.Ppk0,(15.&40.)Ppk1,(15.&40.)Pa0w,(15.&40.)Pxra,(15.&40.)Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Pa1,(15.&40.)Pa2,(15.&40.)Pa3,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)P,(7.(1.(29.(;.&40.Vsp,)+;0.)R1:.)(1.R1:.(29.(;.&40.Vsp,)+:0.)))P,(17.$0.(3.R1;.+20.)=)P,Px,$0.P,(2>.$:.VR,VHIA,Vh,R1.)(2>.$:.VR,VHIA,R1=.R2.)P,(17.$0.(2?.$:.VR,VHIA,R1<.)(2?.$:.VR,VHIA,Vh,))P,(17.$0.(30.$:.VR,VHIA,R1=.)(30.$:.VR,VHIA,Vh,))P,(17.$0.(3.R20.+40.)=)P,(31.VR,VLB,VLF,R21.+100.)P,(31.VR,R1?.VLF,R22.+100.)P,Pb,$2=.P,(32.$2=.R1.VLB,)(32.$2=.R2.R22.)P,(1?.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R26.R24.R23.R22.R21.(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?3.))(12.$?.)))))))))))))))))))))))))))))))))R1>.R1=.R1<.R1;.R1:.R1?.)P,(9.$:.VR,VHIA,R23.R22.VLF,(;.&40.Vsp,)(<.VR,)R26.R21.R20.)P,(38.VR,VLB,VLF,(;.&40.Vsp,)R28.VPP,+8.)P,(38.VR,R24.VLF,(;.&40.Vsp,)R28.VPP,+8.)(35.$:.(1;.VR,)(2>.$:.VR,VHIA,R26.)(3:.R2:.R29.R28.R27.R26.R25.R24.R22.R21.R20.R1?.R1>.)(18.(19.R1<.(11.&40.R27.)Vgp,Vtp,R1;.R1:.R19.Vsp,(11.&40.R27.)R1=.R18.R17.R16.R15.R14.R13.R12.(11.&40.R28.)(11.&40.R28.)(11.&40.VPP,)(11.&40.R20.)(11.&40.(5.R28.+20.))(11.&40.VPKA,)(11.&40.(1:.(1;.VR,)))(11.&40.(5.(1<.VPP,+3.)(1:.(1;.VR,))))(11.&40.(5.R28.+40.))(11.&40.(5.(1<.R28.+3.)(1:.(1;.VR,))))R11.R10.R?.R>.)VF,(11.&40.+:?55<.)Vfc,(1=.(15.&40.))R23.(1>.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB WCa WCb.
    open_dinv2 D.
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; apply SUBq; exact BIN).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (WLa : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WLq : wlow R LBq LF) by (split; [exact (proj2 (proj2 (proj2 PRESB)))| apply (art_data_lo asegs R HIA)]).
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]).
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPBD. cbn [cells_size csize Nat.add] in PPBD.
    assert (E1R : 0 <= e1 < 2^64) by (clear - Hp2a Hp2e HeE ENDB BP BUF0; lia).
    pose proof (bv_unsigned_in_range 64 a0w) as A0R. unfold bv_modulus in A0R. cbn [Z.pow Z.of_N Pos.pow] in A0R.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
      zstep. zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ hq _ _ mx |- _ =>
        pose proof (hm_abase asegs R HIA hq LBq _ mx HHc) as AB1 end end.
      zstep. zstep. zstep.
      zstep. if_cases KEQ; zify_cond KEQ.
      2:{ exfalso. apply KEQ. reflexivity. }
      zstep. zstep.
      merge_stk. at_done. unfold SEQ. right. epiq_body.
      all: first [ (clear - Hp2a Hp2e HeE; lia) | match goal with |- ?g => idtac "SE-EXIT-LEFT:" g end ].
    - (* [comment removed for export] *)
      do 5 zstep.
      zstep. if_cases KG; zify_cond KG.
      + (* [comment removed for export] *)
        do 3 zstep.
        at_done. unfold SEQ. left. exists (-15104). deexists 2. split; [clear; lia|]. cq_body.
        all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SE-FREE1-LEFT:" g end ].
      + (* [comment removed for export] *)
        zstep. zstep. do 3 zstep.
        pose proof (rsa_err_mapA (bv_unsigned a0w) ltac:(clear - A0R; lia)) as RRm.
        at_done. unfold SEQ. left. exists (bv_swrap 32 (bv_unsigned a0w + 18446744073709536512)). deexists 2.
        split; [apply RRm; clear - KG; first [ exact KG | lia ]|]. cq_body.
        all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "SE-FREE2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L17561480300.196L33342826784.200L35653441506.11 L38235734261.1  L38948636245.0  L3916269619.7   L39332637397.0  L41083926835.198L43300649301.0  L50365866937.199L52765036985.201L60098763854.3  L62406578796.194L64850595401.0  L9080220944.4   L9356559676.13  00000L00j01B01F01G01[01\02>02?02]03;03E03a03b04104dS2LF2sp2PP3PKA2bs3LFB2FB3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp11HS1R3HIA1h2sp2lo3TOP4HTOPS2loSS3END2p22e14Hp2e3HeESS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP11HSS2LF2sp2PP3PKA2bs3LFB2FB3sp11HS2LF2sp2PP3PKA2bs3LFB2FB3sp11HS1R2lo3LOSS2LF2sp2PP3PKA2bs3LFB2FB3sp1SS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB BIN CWP CWK"] Lemma seg_F : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_F ()) "PWX,(2:.$2;.)PWB,(2:.$2;.)PFB,$0.Psp1,$0.Phq,(2<.$:.VR,VHIA,)PLBq,(2:.$2=.)Pm2x,P,(15.&40.)(16.(15.&8.))Pmm,P,(15.&40.)(16.(15.&8.))Pkv,(15.&40.)Pp2,$0.Pe1,$0.Ppk0,(15.&40.)Ppk1,(15.&40.)Pxra,(15.&40.)Pt0,(15.&40.)Pt1,(15.&40.)Pt2,(15.&40.)Pa0,(15.&40.)Pa1,(15.&40.)Pa2,(15.&40.)Pa3,(15.&40.)Pa4,(15.&40.)Pa5,(15.&40.)Pa6,(15.&40.)Pa7,(15.&40.)Pt3,(15.&40.)Pt4,(15.&40.)Pt5,(15.&40.)Pt6,(15.&40.)Ps4v,(15.&40.)Ps5v,(15.&40.)Ps6v,(15.&40.)Ps7v,(15.&40.)Ps9v,(15.&40.)Ps10v,(15.&40.)P,(7.(1.(29.(;.&40.Vsp,)+;0.)R20.)(1.R20.(29.(;.&40.Vsp,)+:0.)))P,(17.$0.(3.R21.+20.)=)P,Px,$0.P,(2>.$:.VR,VHIA,Vh,R1.)(2>.$:.VR,VHIA,R23.R2.)P,(17.$0.(2?.$:.VR,VHIA,R22.)(2?.$:.VR,VHIA,Vh,))P,(17.$0.(30.$:.VR,VHIA,R23.)(30.$:.VR,VHIA,Vh,))P,(17.$0.(3.R26.+40.)=)P,(31.VR,VLB,VLF,R27.+100.)P,(31.VR,R25.VLF,R28.+100.)P,Pb,$2=.P,(32.$2=.R1.VLB,)(32.$2=.R2.R28.)P,(1?.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R2<.R2:.R29.R28.R27.(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?1.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?8.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.=))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?2.))(>.$?.(20.(11.&8.+4.))(>.$?.(20.(11.&8.+?3.))(12.$?.)))))))))))))))))))))))))))))))))R24.R23.R22.R21.R20.R25.)P,(9.$:.VR,VHIA,R29.R28.VLF,(;.&40.Vsp,)(<.VR,)R2<.R27.R26.)(35.$:.(1;.VR,)(2>.$:.VR,VHIA,R2:.)(25.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R2:.R2:.VLB,R29.Vm,R2>.R2<.R2;.R11.(26.R2:.R29.R2=.R28.R25.R23.R22.))(18.(19.R21.(11.&40.R2;.)Vgp,Vtp,R20.R1?.R1>.Vsp,(11.&40.R2;.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(11.&40.R2<.)(11.&40.R2<.)R11.R10.R?.R>.(11.&40.(1:.(1;.VR,)))R=.R<.(11.&40.(5.(1<.R2<.+3.)(1:.(1;.VR,))))R15.R14.R13.R12.)VF,(11.&40.+:?61<.)Vfc,(1=.(15.&40.))R27.(1>.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s10v. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB.
    open_dinv2 D.
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; apply SUBq; exact BIN).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (WLa : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WLq : wlow R LBq LF) by (split; [exact (proj2 (proj2 (proj2 PRESB)))| apply (art_data_lo asegs R HIA)]).
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]).
    (* [comment removed for export] *)
    zstep. zstep.
    merge_stk. at_done. epiq_body.
    all: first [ (clear - Hp2a Hp2e HeE; lia) | match goal with |- ?g => idtac "SF-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkPKF.
