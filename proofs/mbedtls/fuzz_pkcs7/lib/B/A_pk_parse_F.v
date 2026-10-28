(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_info P_rsa_parse_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_asn1_get_tag_stmt A_oid A_oid_pk_alg A_oid_ec_grp_algid
     A_asn1_get_bitstring_null A_pk_defs A_pk_info A_pk_type A_pk_parse_A A_pk_parse_B A_pk_parse_C A_pk_parse_D A_pk_parse_E.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_pk_parse_F () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_E.DINV2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_B.EPIQ"; "WalkPKF.Call.XF"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_D.TVAL"; "WalkPKF.Call.CQ"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.P.P_pk_info.pk_info_of"; "RocqVerifyHarness.AgentSubmission.B.A_pk_info.A_PK_INFOS"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkPKF.Call.SBQ"; "WalkPKF.Call.SCQ"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "WalkPKF.Call.SDQ"; "WalkPKF.Call.SEQ"].


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
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
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
      (kv : word) (p2 e1 : Z) (pk0 pk1 a0v a1v a2v s3v s6v : word) : machine_state -> Prop := fun ms =>
    exists (mm : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2v a3 a4 a5 a6 a7
                 (Z_to_bv 64 FB) s3v (Z_to_bv 64 PP) (Z_to_bv 64 e1) s6v (Z_to_bv 64 PKA)
                 (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (FB + 160)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB)
                 t3 t4 t5 t6)
              F (Z_to_bv 64 ENTRY) fc None mm (seg_rom asegs)
      /\ DINV2' WX FB sp1 hq LBq
           [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
            F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0] kv p2 e1 pk0 pk1 mm
      /\ presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mm
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
    destruct D as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen
                   & HHq & FHD & LPKC & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MIq
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & Hp1a & Hp1b & PPC & PRES).

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
    unfold A_pk_parse_E.DINV2; deexists 9; eexists; eexists; deexists 3;
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
      : machine_state -> Prop := fun ms =>
    (r <> 0 /\ EPIQ' hq hq LB LBq m WX FB sp1 (Z_to_bv 64 r) (XF hq LBq WB m2x p5 pk0 pk1) ms)
    \/ (exists id : Z, r = 0 /\ (id = 9 \/ id = 13) /\ (TVAL' kv = 2 \/ TVAL' kv = 3)
          /\ CQ 722272 723668 WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1
               (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 id) (Z_to_bv 64 PKA) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-16384)) ms)
    \/ (exists a2v : word, r = 0 /\ (TVAL' kv = 2 \/ TVAL' kv = 3)
          /\ CQ 722492 723804 WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1
               (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 PKA) a2v (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-16384)) ms)
    \/ (r = 0 /\ TVAL' kv = 1
          /\ CQ 722424 731364 WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1
               pk1 (Z_to_bv 64 p5) (Z_to_bv 64 (e1 - p5)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (FB + 32)) ms)
    \/ (exists (rc : Z) (a1v a2v : word), r = 0 /\ (- (2 ^ 31) < rc /\ rc < 0)
          /\ CQ 722720 726848 WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1
               (Z_to_bv 64 PKA) a1v a2v (Z_to_bv 64 rc) (Z_to_bv 64 (-16384)) ms)
(* [comment removed for export] *).

  #[using="Type"] Lemma segB_swr : forall y, - 2 ^ 31 <= zswrap 32 y < 2 ^ 31.
  Proof. intros y. clear - y. unfold zswrap. change (32 - 1) with 31. pose proof (Z.mod_pos_bound (y + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. Qed.
  #[using="Type"] Lemma segB_tval : forall kv, TVAL' kv = zswrap 32 (zlow 32 (bv_unsigned kv)) mod 2 ^ 32.
  Proof.
    intros kv. clear - kv. unfold A_pk_parse_D.TVAL, sx32, zswrap, zlow. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite swrap32_as_modA. change (2 ^ Z.of_N 64) with (2 ^ 64). change (32 - 1) with 31.
    pose proof (bv_unsigned_in_range 64 kv) as KR. unfold bv_modulus in KR. change (2 ^ Z.of_N 64) with (2 ^ 64) in KR.
    Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma segB_tv23 : forall kv, zlow 64 (zswrap 32 (zlow 32 (bv_unsigned kv)) + -2) < zlow 64 2 -> TVAL' kv = 2 \/ TVAL' kv = 3.
  Proof.
    intros kv H. clear - H. rewrite segB_tval. pose proof (segB_swr (zlow 32 (bv_unsigned kv))) as B.
    set (x := zswrap 32 (zlow 32 (bv_unsigned kv))) in *. clearbody x. unfold zlow in H. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma segB_tv1 : forall kv, zlow 64 (zswrap 32 (zlow 32 (bv_unsigned kv))) = zlow 64 1 -> TVAL' kv = 1.
  Proof.
    intros kv H. clear - H. rewrite segB_tval. pose proof (segB_swr (zlow 32 (bv_unsigned kv))) as B.
    set (x := zswrap 32 (zlow 32 (bv_unsigned kv))) in *. clearbody x. unfold zlow in H. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma segB_lor13 : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> zlow 64 (Z.lor x 4) = zlow 64 13 -> x = 9 \/ x = 13.
  Proof.
    intros x Hx H. clear - Hx H. unfold zlow in H. pose proof (Z.add_lor_land x 4) as E.
    assert (L4 : 0 <= Z.land x 4 <= 4).
    { split; [apply Z.land_nonneg; right; lia|].
      assert (D2 : Z.land (Z.ldiff 4 x) (Z.land 4 x) = 0).
      { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
        destruct (Z.testbit 4 n), (Z.testbit x n); reflexivity. }
      pose proof (Z.lor_ldiff_and 4 x) as R4.
      rewrite <- Z.lxor_lor in R4 by exact D2. rewrite <- (Z.add_nocarry_lxor _ _ D2) in R4.
      assert (H04 : 0 <= 4) by lia. pose proof (proj2 (Z.ldiff_nonneg 4 x) (or_introl H04)). rewrite Z.land_comm. lia. }
    assert (V : Z.lor x 4 = 13).
    { set (v := Z.lor x 4) in *. set (w := Z.land x 4) in *. clearbody v w. Z.div_mod_to_equations. lia. }
    set (w := Z.land x 4) in *.
    assert (WW : Z.land w 4 = w) by (subst w; rewrite <- Z.land_assoc, Z.land_diag; reflexivity).
    assert (W04 : w = 0 \/ w = 4).
    { assert (C5 : w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4) by lia.
      destruct C5 as [E0|[E0|[E0|[E0|E0]]]]; rewrite E0 in WW |- *; cbn in WW; first [left; reflexivity| right; reflexivity| discriminate WW]. }
    clearbody w. lia.
  Qed.
  Ltac segB_bfacts :=
    repeat match goal with
    | H : (if ?a <? ?b then false else true) = _ |- _ => destruct (Z.ltb_spec a b); cbn in H; try discriminate H; clear H
    | H : (if ?a =? ?b then false else true) = _ |- _ => destruct (Z.eqb_spec a b); cbn in H; try discriminate H; clear H
    end.
  Ltac segB_norm :=
    repeat match goal with |- context [al_sb ?A + Z.shiftr ?x 3] => rewrite (Z.add_comm (al_sb A) (Z.shiftr x 3)) end;
    repeat match goal with H : context [al_sb ?A + Z.shiftr ?x 3] |- _ => rewrite (Z.add_comm (al_sb A) (Z.shiftr x 3)) in H end;
    repeat match goal with H : rw_cells _ _ _ [] |- _ => clear H end;
    repeat match goal with H : rw_cells _ _ (?b + 164) _ |- _ => replace (b + 164) with (b + 160 + 4) in H by lia end;
    repeat match goal with H : rw_cells _ _ (?b + 180) _ |- _ => replace (b + 180) with (b + 176 + 4) in H by lia end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "04k0@D16071854214.231D40338479819.220D43080244883.220D57793146470.220D59521016234.220D64280614944.220D9785981640.231 K12226132804.220K44164039966.220K64113782398.220L12221849778.2  L14215840308.216L14587613338.194L15756368110.21 L15822417165.1  L15934535645.1  L16078575714.11 L16137017629.204L1685717371.0   L17454813295.1  L1747688473.24  L17561480300.194L18538772363.2  L19131885611.1  L19684562151.1  L19700568303.21 L20491039487.191L21654730866.2  L21850448026.188L21866712442.1  L22078896779.2  L23268210308.0  L24023900370.0  L24624919580.216L2545017180.207 L2621559066.1   L26530156621.207L26864060502.223L27817441514.214L27817804316.216L27940730156.21 L29010379890.193L29010569984.184L29022582655.2  L30439224333.1  L32431276449.0  L33342826784.198L33695720602.191L3379302262.223 L33985112333.1  L3482475141.21  L34852063412.2  L35653441506.11 L36314615039.2  L363719563.2    L37353703961.195L37687006330.2  L38235734261.1  L38334051855.2  L38551529394.0  L38948636245.0  L39088874870.21 L39188636933.0  L39332115127.192L39332637397.0  L41083926835.196L41202928732.217L42411609006.0  L42921373482.214L43300649301.0  L43810982283.2  L44168158952.3  L45921596632.1  L47870616696.2  L494542275.189  L49893919779.2  L49952884613.192L50365866937.197L50616353292.191L50616353292.193L50616353292.195L50925318027.2  L51264064568.7  L52765036985.199L53530622489.207L53530622489.216L53735527649.192L56787311448.1  L57389109526.21 L576250010.207  L58039649675.2  L59272923917.1  L59308586248.2  L60098763854.3  L61900301956.0  L62406578796.192L64009471222.1  L64118060424.2  L64850595401.0  L66062374527.193L66062374527.194L66151427842.16 L66298372189.2  L66812728480.3  L67653551064.2  L67989683843.2  L7738195705.2   L8707557133.1   L881835912.0    L9080220944.4   L9356559676.13  L9783143000.1   O14061664741.231O14941307720.231O17217116232.231O18906182176.231O3821773283.231 O39302861384.231O42843274679.231O44938202843.231O45969540168.231O52616826440.231O55209884805.231O64474006218.231O65961212488.231P18523612460.231P21647862485.231P22094145580.231P29008688568.220P34857851411.231P356858156.231  P36312780344.220P37693867741.231P38605639612.222P38605639612.231P43817786156.231P47876372191.231P50927926572.231P58041177900.231P66292560634.231P66453878491.222P66453878491.231P66818508295.231P67988155428.231P7740881908.222 P7740881908.231 P7750690063.220 Q10033386496.205Q10046132249.202Q10592236593.216Q10594415769.218Q10649498761.227Q10651829299.207Q10651864072.226Q10752139055.220Q10821824020.222Q10821824020.231Q10883697563.202Q1195234662.206 Q12063573683.225Q12076400817.216Q12078415920.225Q12658605510.222Q12658605510.224Q12658605510.231Q12658605510.233Q13268182738.225Q13270328915.216Q13435319996.201Q13732992821.226Q15068987923.220Q15470177032.197Q1547996552.225 Q1554221501.216 Q16071706518.201Q16071854214.231Q16611301420.216Q16625916953.225Q17458927065.212Q17701933971.227Q17703789353.207Q17757173815.217Q1867768678.231 Q19135999389.212Q19136195757.201Q19198257066.205Q19546836326.216Q19561696871.204Q19940505025.209Q20187259808.216Q21162993424.203Q21293441397.220Q21538057956.219Q21540267236.220Q21767670690.231Q24064611734.220Q25745664918.217Q26314584654.222Q26314584654.231Q26316671538.203Q26827176686.204Q27663034001.216Q27783623434.216Q27798763327.225Q2803826605.231 Q28197635908.220Q29312881359.203Q29323580945.208Q29775981542.231Q30441621867.210Q30802955094.217Q31155634335.214Q31170348313.197Q31255363489.203Q31526414380.222Q31526414380.231Q3194347860.227 Q32459096316.216Q34669208210.217Q34863972393.231Q37427005260.202Q38144578741.217Q38144578741.226Q38461683681.216Q38463452116.225Q39285966485.216Q39600066135.227Q4133323135.225 Q4135371262.216 Q41638331817.202Q42024731732.202Q42445523223.216Q43082486931.219Q43138029699.222Q43138029699.231Q43324197004.211Q43324197006.213Q44298944140.203Q44298944140.217Q44298944140.226Q44301027056.222Q44301027056.231Q45482765142.224Q45482765142.233Q45669665938.209Q47228431932.222Q47228431932.231Q47386034592.205Q47390328249.202Q47799422583.202Q47801698636.225Q48117823211.220Q48119910507.222Q48119910507.231Q48234175664.219Q48523164961.213Q49698585326.218Q50556521588.206Q50558264627.203Q50558408971.202Q508607707.214  Q51725458861.204Q51740006843.205Q51740073104.215Q51959565844.210Q52747231024.220Q53440817288.203Q53441189040.202Q53580790879.219Q53913538102.201Q54520642956.203Q55026446740.215Q5596578838.222 Q5596578838.231 Q57759385376.206Q57828105177.231Q58207055645.218Q58974185687.219Q59617715404.225Q59619648079.225Q59621696206.216Q59709694911.231Q60714092706.208Q6085996819.203 Q61847600818.227Q63116569710.203Q63435846322.217Q63435846322.226Q64228675114.221Q64228675114.230Q64278663712.219Q65424847505.219Q65426765969.220Q66729066265.202Q66731311911.203Q66733293089.209Q66733420561.200Q66733423387.206Q66901779611.217Q66901779611.226Q67128036471.202Q67581897521.206Q67866752433.200Q67866754747.206Q67877226119.203Q67879566009.202Q68075300161.225Q6909946601.219 Q7243851811.211 Q7339423222.220 Q9356756743.223 Q9633884056.204 Q9644516505.216 Q9644583048.231 Q9672141798.231 00001G01H02@03<03=04405C06807107j07k09W0:;0;00;40;70;K0;o0<00<40<\0==0=>0=B0=F0>D0>h0>i0?J0?N0?O0?P0?Q0A=0Aa0Af0BJ0CQ0DW0E;0F00FT0FU0FV0FZ0F[0G>0Gb0Gc0Gg0Ha0Hb0I:0I;0I<0I`0Ia0Ie0Il0Im0In0Jg0Jh0KL0KM0L40LX0LY0LZ0L[0L\0L]0Lb0Lc0Ld0Ll0MT0N70N[0O?0Oc0Od0P80P[0Q?0Qc0RK0RP0R[0S?0S@0SD0SJ0ST0SU0T60T70T80T90T]0UA0U[0U\0U]0Ue0Uf0Ug0Uk0Ul0V;0Vn0W30W40W50W60W70W80W90W:0W;0W<0W=0W>0W?0W@0X@0XA0YA0ZY0[V0\V0]n0^o0_g0`_0a_0b_0c_0d_0e@0f80g00h90i90im0ja0l80m10mm0nF0o00oF10010F10G11;11o12I13713P13i14B15616>17218:18S18l19B19X19Y19o1:01:11:j1;f1<?1<X1=B1=X1>B1>a1>b1?L1?b1@81@g1AV1AW1AX1AY1AZ1BG1C41D41D51D_1EO1F?1F]1G31G]1H61HO1Hi1Hj1Ic1Jg1KH1LN1Lm1MW1Mm1NG1NH1NI1NJ1Nc1OM1ON1Oh1PF1Pd1Q=1QV1R@1RA1RZ1S31SM1Sg1T@1Tm1Tn1To1UY1VC1Va1W?1W]1XM1Y=1ZE1[M1\Q1]E1^91^h1_Z1`31`L1a_1bo1d?1d@1dj1eL1f:1fT1fn1gX1gn1hD1hn1ij1j[1k51kO1l@1lo1mI1n31n41n51nK1o=1og20Q20R20S20T20U21c21d22a23^23_23`25326F27227^28J29F2:?2;M2<I2=B2=`2>>2>W2>m2?_2@N2A=2Ao2BH2C22C\2C]2D<2DU2E12EM2ENS1R2LF2sp2PP3PKA2lo4STKk2bs3LOS3SLO3LFB3PPB3PKB3NB14STK22FB3sp12kv3SP13SPR4SP1R2F04PPBDFS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4info4PPBD2HB5Ha_st5Hl_stS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4info4PPBD2HB5Ha_st5Hl_st3pk1FS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv3pk14PPBD2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3PKA2bs3TOP3LFB3PPB3PKB2FB3sp12hq2kv3SP13ETq3SPR4SP1R2F04PPBDS2LF2PP2bs3LFB2FB2kv4info3APP4PPBD2HB5Ha_st5Hl_st3pk1S2LF2PP3BUF2bs3LFB2FB2kv4info3APB4PPBD2HB5Ha_st5Hl_st3pk1S2LF2PP3PKA2bs3LFB2FB2kv4info3APK4PPBD2HB5Ha_st5Hl_st3pk1FS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12kv2p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP13ALO3ACV2F0S2FBS1lS1X3KVR1r3KEC1q1H2H0S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDSS2FBS1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9S2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFS2FBS2FBS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F03F8'S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDS2FBFSSS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12kv2p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS1R2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBD2HB5Ha_st5Hl_st5SAEst5CM8st2x12HxS1R2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBD2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP13ALO3ACV2F0S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFFS2FBSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2FBS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F0FS1R3HIA1h2sp2lo3TOP4HTOPFFS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2loS2FB2F0SSS1R2sp2lo4STKk3LOS3SLO3NB14STK22FB3sp13SP13ALO3ACV2F03F1'SS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDSS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDSFSFFS3sp1FFS2gv3GVRS2LF2sp2PP3PKA2bs3LFB3PKB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS3END2p52e14Hp2e3HeES2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB3PKB2FB3sp12kv4PPBDS3sp1S2FB3sp12F0S2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDFS2FBS1i2HiS1R2lo3LOSSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFFSS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv4PPBDS2FB2r03F641q1r1H2H02q02H4FFS2sp3sp1FFS2FBSS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS3sp1FFFFFFFFFFFFFS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDFS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv4info3SP14FBLO4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv4info3SP14FBLO4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP3PKA2lo4STKk2bs3SLO3LFB4PKLO3NB14STK23sp12kv3SP14PPBDS1R2LF2PP3BUF2bs3LFB2FB2kv3APB4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3BUF2bs3LFB2FB2kv3APB4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS2LF2sp2PP2bs3LFB3sp12kv3SP14PPBDS1R2LF2PP3PKA2bs3LFB2FB2kv3APK4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3PKA2bs3LFB2FB2kv3APK4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk3BUF2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP13ALO4BUFC4PPBDS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp12kv3SP14FBLO4PPBDS1R2LF2PP2bs3LFB2FB2kv3APP4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv3APP4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv4info3ALO3F1'4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2kv4PPBDFS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP3PKA2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3BUF2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB4PPBDS2LF2PP2bs3LFB2kv4PPBDFS2LF2PP2bs3LFB2FB4PPBDFFS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv2F04PPBD2HBFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB4PPBDS2LF2PP2bs3LFB2FB4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv3SPR2F03F8'4PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp12kv3SPR2F03F8'4PPBDFFFFS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP13ALO4PPBDFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS2LF2PP2bs3LFB2FB4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB3sp12kv4PPBDFS2LF2sp2PP3PKA2bs3LFB3PKB4PKAL2FB3sp12kv3SPR4SP1R2F04PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB2FB3sp12kv3SP14HTOP4PPBD2HB5Ha_st5Hl_stS2LF2sp2PP2bs3LFB3sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv2F04PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDFFFS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_stFFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP3END3BUF3LFB1l2EB3B474BL302FB2kv4BUFC4PPBD2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP2bs3TOP3LFB2FB3sp12kv3SP14HTOP4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv4info3ALO4PPBD2HB5Ha_st5Hl_st3pk1S1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB2kv3ALO4PPBD2HB5Ha_st5Hl_st5SAEstFS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_stS1R2LF2PP3PKA2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB4PPBDS2LF2PP2bs3LFB2FB4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP2bs3TOP3LFB2FB2kv4HTOP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_st3pk1S2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS2LF2PP2bs3LFB2FB2kv4info4PPBD2HB5Ha_st5Hl_st3pk1S1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS2LF2PP3PKA2bs3LFB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFFS2LF2PP2bs3LFB2FB4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFFFFS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3sp12kv3SP14PPBD2HB5Ha_st5Hl_stFS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp12kv3SPR4SP1R2F04PPBDS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PKAL2FB3sp12kv3SPR4SP1R2F04PPBDFFS1R2LF2sp2PP3PKA2bs3LFB3PPB3PKB2FB3sp12kv3SPR4SP1R2F03F8'4PPBD2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3PKA2bs3LFB3PPB3PKB2FB3sp12kv3SPR4SP1R2F03F8'4PPBD2HB5Ha_st5Hl_st5SAEstS2LF2PP2bs3LFB2FB2kv3pk14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv3pk14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2kv3pk14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3sp12kv3SP14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp12kv3SP14PPBDS1R2LF2sp2PP2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP14PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS1R2LF2PP2bs3LFB2FB2kv4PPBD2HBS2LF2PP2bs3LFB2FB2kv4PPBDS2LF2PP2bs3LFB2FB4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp13SP14HTOP4PPBDS1R3HIA1h2LF2sp2PP2bs3TOP3LFB3sp12kv3SP14HTOP4PPBDS2LF2PP2bs3LFB2FB2kv4PPBDS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2kv4PPBD2HB5Ha_st5Hl_stFS2LF2PP2bs3LFB3sp12kv4SP1R4PPBDS2LF2PP2bs3LFB2FB2F04PPBDS2LF2PP2bs3LFB2FB2kv2F04PPBDS2LF2PP2bs3LFB2FB2kv2F04PPBDF". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB HBS0 BIN BP EB B47 BUF0 BL30 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB NB1 STK2 RTCL"] Lemma seg_B : forall (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x mm : mem)
      (kv : word) (p5 e1 r info : Z) (pk1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 ->
    sp1 mod 32 = 0 ->
    (forall x : Z, hcs asegs R HIA h x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h ->
    hstkhi asegs R HIA hq = hstkhi asegs R HIA h ->
    FB mod 64 = 0 ->
    fresh_apart R LB LF FB 256 ->
    fresh_apart R LBq LF FB 256 ->
    (forall b : blk, In b LB -> In b LBq) ->
    DINV2' WX FB sp1 hq LBq
      [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
       F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0] kv p5 e1 (Z_to_bv 64 info) pk1 mm ->
    presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mm ->
    r = 0 \/ r = -16256 ->
    (r = 0 -> info = pk_info_of A_PK_INFOS (TVAL' kv) /\ In info A_PK_INFOS) ->
    evtA asegs AL (hcs asegs R HIA hq) (SBQ WX WB FB sp1 hq LBq m2x kv p5 e1 r (Z_to_bv 64 info) pk1)
      (MS (mkR (Z_to_bv 64 722220) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 FB) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 e1) (Z_to_bv 64 (-16384)) (Z_to_bv 64 (FB + 96))
              (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (FB + 160)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB)
              t3 t4 t5 t6)
          F (Z_to_bv 64 722220) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB RV INFO.
    open_dinv2 D. clear SPA PE ENDB.
    rt_facts. clear UARG SM2.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
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
    destruct RV as [R0|RN].
    2:{ lx_pre. lx_run_tac (PLAN [721756] [] 20%N). lx_tree.
        all: try subst lxm. segB_norm.
        merge_stk. at_done. unfold SBQ. left. split; [clear - RN; lia|]. epiq_body.
        all: clear - Hp2a Hp2e HeE; lia. }
    subst r. destruct (INFO eq_refl) as [EINFO INFO1]. clear INFO.
    pose proof (A_pk_get_type_spec AL IMG L) as GT'. unfold pk_get_type_stmtA, A_PK_GET_TYPE in GT'.
    lx_pre. lxr_path. lxr_abase. lxr_pose. lx_pre.
    lx_run_tac (PLAN [721756; 723668; 723804; 731364; 726848; 727388; 722736] [] 200%N).
    lx_tree. all: lxu_chk_leaves 722736.
    all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
    all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 726848) _ _ _ (seg_rom _)] =>
           try subst lxm; segB_norm;
           at_done; unfold SBQ; right; right; right; right;
           exists (-15488), (Z_to_bv 64 1), (Z_to_bv 64 2); split; [reflexivity|]; split; [lia|];
           cq_body | |- _ => idtac end.
    all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 723804) _ _ _ (seg_rom _)] =>
           try subst lxm; segB_norm; segB_bfacts;
           let TV := fresh "TV23" in assert (TV : TVAL' kv = 2 \/ TVAL' kv = 3) by (apply segB_tv23; assumption);
           at_done; unfold SBQ; right; right; left;
           exists (Z_to_bv 64 13); split; [reflexivity|]; split; [exact TV|];
           cq_body | |- _ => idtac end.
    all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 723668) _ _ _ (seg_rom _)] =>
           try subst lxm; segB_norm; segB_bfacts;
           let TV := fresh "TV23" in assert (TV : TVAL' kv = 2 \/ TVAL' kv = 3) by (apply segB_tv23; assumption);
           at_done; unfold SBQ; right; left;
           exists (zswrap 32 (zlow 32 (bv_unsigned gv))); split; [reflexivity|];
           split; [apply segB_lor13; [apply segB_swr| assumption]|]; split; [exact TV|];
           cq_body | |- _ => idtac end.
    segB_norm. segB_bfacts.
    assert (TV1 : TVAL' kv = 1) by (apply segB_tv1; assumption).
    assert (EI : info = A_RSA_INFO) by (rewrite EINFO, TV1; reflexivity).
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH1 end.
    frame_aobj FSH1 (FB + 32) 2%nat as OL32.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ hq _ _ mx |- _ =>
      pose proof (RTCL mx (hm_rtc asegs R HIA hq _ _ mx HHc)) as RT1;
      pose proof (hm_img_shadow asegs R HIA hq _ _ mx HHc) as ISH1 end end.
    pose proof (hcs_img_cs R HIA hq IMG (proj2 (proj2 (proj2 IMG')))) as ICS.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      assert (OI1 : aobj asegs AL (hcs asegs R HIA hq) mx info 4) by (rewrite EI; eapply aobj_img; [exact ICS| exact ISH1| vm_compute; reflexivity]) end.
    callxA_sp sp1 (eapply GT' with (CS := hcs asegs R HIA hq) (A := FB + 32) (info := info) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | (right; left; exact EI)
                         | (intros _; exact OI1)
                         | lazymatch goal with
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 STK0 STK2 F0 F1' F8' F64 ALO LOS ACP ACV FBLO; first [lia | Z.div_mod_to_equations; lia]
                           end ]).
    clear OL32 RT1 OI1 ISH1.
    match goal with H : info = A_RSA_INFO -> ?t = 1 |- _ => pose proof (H EI) as TY1; clear H end.
    lazymatch type of TY1 with ?t = 1 => subst t end.
    lx_pre. lxr_path. lxr_abase. lxr_pose. lx_pre.
    lx_run_tac (PLAN [721756; 723668; 723804; 731364; 726848; 727388; 722736] [] 200%N).
    lx_tree. all: lxu_chk_leaves 722736.
    all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
    all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 731364) _ _ _ (seg_rom _)] =>
           segB_norm; at_done; unfold SBQ; right; right; right; left;
           split; [reflexivity|]; split; [exact TV1|];
           cq_body | |- _ => idtac end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SCQ (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem) (kv : word) (p5 e1 r : Z) (pk0 pk1 : word)
      : machine_state -> Prop := fun ms =>
    (exists a1v a2v : word, r <> 0
          /\ CQ 722720 726848 WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1
               (Z_to_bv 64 PKA) a1v a2v (Z_to_bv 64 r) (Z_to_bv 64 (-16384)) ms)
    \/ (r = 0
          /\ CQ 722524 894296 WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1
               (Z_to_bv 64 PKA) (Z_to_bv 64 p5) (Z_to_bv 64 (e1 - p5)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 (-16384)) ms)
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L14215840310.186L24624919582.186L29010569984.185L35653441506.11 L38235734261.1  L38948636245.0  L39332637397.0  L41202928732.187L43300649301.0  L60098763854.3  L64850595401.0  L66151426447.10 L9080220944.4   L9356559676.13  Q10649498761.196Q10651864074.195Q13732992823.195Q17701933971.196Q3194347860.196 Q39600066135.196Q45353655733.195Q61847600818.19600001Y03B03C03[03_03`03a04B04C04M04N04^04m05`06306F06Y06l06m06n07A08;S1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12p52e14Hp2a4Hp2e3HeE3ACV3SPR4SP1R2F04BUFC4PPBDFS1R3HIA1h2sp2lo3TOP4HTOPS2loSSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDSS1R2lo3LOSSS1r2RR2r02KR1q1HS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDFFS2LF2PP2bs3LFB4PPBDS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBD". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB BIN BP EB BUF0 PPAL CWP CWK"] Lemma seg_C : forall (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x mm : mem) (kv : word) (p5 e1 r : Z) (pk0 pk1 : word)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 ->
      sp1 mod 32 = 0 ->
      (forall x : Z, hcs asegs R HIA h x -> hcs asegs R HIA hq x) ->
      htop asegs R HIA hq = htop asegs R HIA h ->
      hstkhi asegs R HIA hq = hstkhi asegs R HIA h ->
      FB mod 64 = 0 ->
      fresh_apart R LB LF FB 256 ->
      fresh_apart R LBq LF FB 256 ->
      (forall b : blk, In b LB -> In b LBq) ->
      DINV2' WX FB sp1 hq LBq
        [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
         F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0] kv p5 e1 pk0 pk1 mm ->
      presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mm ->
      -2^31 < r <= 0 ->
      evtA asegs AL (hcs asegs R HIA hq) (SCQ WX WB FB sp1 hq LBq m2x kv p5 e1 r pk0 pk1)
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 e1) (Z_to_bv 64 (-16384)) (Z_to_bv 64 PKA)
               (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (FB + 160)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
            F (Z_to_bv 64 722272) fc None mm (seg_rom asegs))
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
    pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
    pose proof (art_alwf asegs R HIA) as ALWF.
    clear UARG STK2 SPA SM2 PPLO PP0 PKLO PKAL PK0 PE NB1 ENDB DPK DPB DKB BL30 B47.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [722736; 722776; 726848; 894296] [] 60%N). lx_tree.
    all: lazymatch goal with Hs : ?x = ?y |- context [MS _ _ _ _ _ ?x _] => subst x end.
    all: apply evtA_done.
    all: repeat match goal with |- context [al_sb AL + ?x] => rewrite (Z.add_comm (al_sb AL) x) end.
    all: unfold SCQ.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 726848) _ _ _ _] => left; exists a1, a2; split; [lia|]
         | |- _ => right; split; [lia|] end.
    all: cq_body.
    all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L35653441506.11 L38235734261.1  L38948636245.0  L39332637397.0  L43300649301.0  L60098763854.3  L64850595401.0  L66062374908.186L9080220944.4   L9356559676.13  Q10033454561.194Q47386101825.19400000H00L00M00N00O00Y00Z01601E02802i03PS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSS1R2lo3LOSSS2LF2sp2PP3PKA2bs3LFB2FB3sp1S2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB3sp13SP14HTOP". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB BIN BP EB BUF0 PPAL CWP CWK NB1 STK2"] Lemma seg_C4 :
    forall (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x mm : mem) (kv : word) (p5 e1 r : Z)
      (pk0 pk1 xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 ->
    sp1 mod 32 = 0 ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h ->
    hstkhi asegs R HIA hq = hstkhi asegs R HIA h ->
    FB mod 64 = 0 ->
    fresh_apart R LB LF FB 256 ->
    fresh_apart R LBq LF FB 256 ->
    (forall b, In b LB -> In b LBq) ->
    DINV2' WX FB sp1 hq LBq
      [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
       F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0] kv p5 e1 pk0 pk1 mm ->
    presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mm ->
    -2^31 < r <= 0 ->
    evtA asegs AL (hcs asegs R HIA hq) (SCQ WX WB FB sp1 hq LBq m2x kv p5 e1 r pk0 pk1)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 e1) (Z_to_bv 64 (-16384)) (Z_to_bv 64 PKA)
               (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (FB + 160)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB)
               t3 t4 t5 t6)
          F (Z_to_bv 64 722492) fc None mm (seg_rom asegs))
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
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    clear SCS SCS0.
    pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
    pose proof (art_alwf asegs R HIA) as ALWF.
    pose proof (munch_refl [] mm) as MU0. pose proof (wmono_refl asegs mm) as WM0.
    clear UARG SPA SM2 PPLO PP0 PKLO PKAL PK0 PE ENDB DPK DPB DKB BL30 B47.
    lx_run_tac (PLAN [726848; 894296; 722776] [] 40%N). lx_tree.
    all: subst lxm.
    - revert LXKT. destruct (Z.eqb_spec (zlow 64 r) (zlow 64 0)) as [KE|KE]; intros LXKT; [discriminate LXKT|]. clear LXKT.
      assert (RNZ : r <> 0) by (intros E0; apply KE; rewrite E0; reflexivity).
      rewrite !(Z.add_comm (al_sb AL) (Z.shiftr _ 3)).
      at_done. unfold SCQ. left. eexists; eexists. split; [exact RNZ|]. cq_body.
      all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "C4-FREE-LEFT:" g end ].
    - revert LXKF. destruct (Z.eqb_spec (zlow 64 r) (zlow 64 0)) as [KE|KE]; intros LXKF; [|discriminate LXKF]. clear LXKF.
      assert (R0 : r = 0) by (clear - KE RR; unfold zlow in KE; Z.div_mod_to_equations; lia).
      rewrite !(Z.add_comm (al_sb AL) (Z.shiftr _ 3)).
      at_done. unfold SCQ. right. split; [exact R0|]. cq_body.
      all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "C4-SPK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SDQ (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem) (kv : word) (e1 r : Z) (pk0 pk1 : word)
      : machine_state -> Prop := fun ms =>
    (exists a1v a2v : word, r <> 0
          /\ CQ 722720 726848 WX WB FB sp1 hq LBq m2x kv e1 e1 pk0 pk1
               (Z_to_bv 64 PKA) a1v a2v (Z_to_bv 64 r) (Z_to_bv 64 (-16384)) ms)
    \/ (r = 0 /\ EPIQ' hq hq LB LBq m WX FB sp1 (Z_to_bv 64 0) (XF hq LBq WB m2x e1 pk0 pk1) ms)
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB ENDB BIN BP EB BUF0 PPAL PPLO CWP PKLO CWK DPK DPB NB1 STK2"] Lemma seg_D :
    forall (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x mm : mem) (kv : word) (p5 e1 r : Z) (pk0 pk1 : word)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 ->
    sp1 mod 32 = 0 ->
    (forall x : Z, hcs asegs R HIA h x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h ->
    hstkhi asegs R HIA hq = hstkhi asegs R HIA h ->
    FB mod 64 = 0 ->
    fresh_apart R LB LF FB 256 ->
    fresh_apart R LBq LF FB 256 ->
    (forall b : blk, In b LB -> In b LBq) ->
    DINV2' WX FB sp1 hq LBq
      [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2; F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0]
      kv p5 e1 pk0 pk1 mm ->
    presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mm ->
    wcover R LB LF (bv_unsigned sp) WX PP 8 ->
    wcover R LBq LF (bv_unsigned sp) WB PP 8 ->
    - (2 ^ 31) < r <= 0 ->
    evtA asegs (arl_AL R) (hcs asegs R HIA hq) (SDQ WX WB FB sp1 hq LBq m2x kv e1 r pk0 pk1)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb (arl_AL R))) (Z_to_bv 64 PP) (Z_to_bv 64 e1) (Z_to_bv 64 (-16384))
             (Z_to_bv 64 PKA) (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (FB + 160)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb (arl_AL R)))
             (Z_to_bv 64 FB) t3 t4 t5 t6)
          F (Z_to_bv 64 722524) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB WCa WCb RR.
    open_dinv2 D.
    rt_facts. clear UARG SPA SM2 PP0 PKAL PK0 PE DKB BL30 B47.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPBD. cbn [cells_size csize Nat.add] in PPBD.
    assert (E1R : 0 <= e1 < 2^64) by (clear - Hp2a Hp2e HeE ENDB BP BUF0; lia).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (E1H : e1 < 2^63) by (clear - HeE EB BUFC ACV ACP; lia).
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
    pose proof (art_alwf asegs R HIA) as ALWF.
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8)
      by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]).
    lxr_pose.
    (* [comment removed for export] *)
    lx_pre. lx_run_tac (PLAN [726848; 721756; 722736] [(722536, DSplit); (722544, DSplit); (722556, DSplit); (722560, DSplit)] 80%N).
    lx_tree.
    all: lxu_chk_leaves 722736.
    all: lxr_leaf.
    all: match goal with H : rw_cells _ _ _ [C8 _; C8 _; C8 (Z_to_bv 64 (al_sb AL + Z.shiftr PP 3))] |- _ =>
           rewrite (Z.add_comm (al_sb AL) (Z.shiftr PP 3)) in H end.
    all: try match goal with H : rw_cells _ _ (?fb + 164) _ |- _ => replace (fb + 164) with (fb + 160 + 4) in H by lia end.
    all: try match goal with H : rw_cells _ _ (?fb + 180) _ |- _ => replace (fb + 180) with (fb + 176 + 4) in H by lia end.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 726848) _ _ _ (seg_rom _)] =>
             apply evtA_done; unfold SDQ; left; do 2 eexists; split; [| cq_body]
         | |- context [MS _ _ (Z_to_bv 64 721756) _ _ _ (seg_rom _)] =>
             apply evtA_done; unfold SDQ; right; split; [| merge_stk; epiq_body]
         end.
    (* [comment removed for export] *)
    all: first [ (clear - Hp2a Hp2e HeE Hp1a Hp1b; lia) | exact PPC | (lx_prune; clear_disj; lia) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SEQ (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x : mem) (kv : word) (p5 e1 : Z) (pk0 pk1 : word)
      : machine_state -> Prop := fun ms =>
    (exists (rc : Z) (a1v a2v : word), (- (2 ^ 31) < rc /\ rc < 0)
          /\ CQ 722720 726848 WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1
               (Z_to_bv 64 PKA) a1v a2v (Z_to_bv 64 rc) (Z_to_bv 64 (FB + 32)) ms)
    \/ EPIQ' hq hq LB LBq m WX FB sp1 (Z_to_bv 64 0) (XF hq LBq WB m2x e1 pk0 pk1) ms
(* [comment removed for export] *).

  Lemma se_rcA : forall u, 0 <= u -> 0 <= - zlow 64 (zswrap 32 (zlow 32 (u + 108))) + 12 ->
    - 2 ^ 31 < zswrap 32 (zlow 32 (u + -15104)) < 0.
  Proof.
    intros u U H.
    assert (E1 : forall x, zswrap 32 (zlow 32 x) = bv_swrap 32 x).
    { intros x. rewrite swrap32_as_modA. unfold zswrap, zlow. change (2 ^ (32 - 1)) with (2 ^ 31).
      rewrite Z.add_mod_idemp_l by (clear; lia). reflexivity. }
    rewrite !E1 in H |- *.
    replace (bv_swrap 32 (u + -15104)) with (bv_swrap 32 (u + 18446744073709536512)).
    - apply rsa_err_mapA; [exact U| unfold zlow in H; clear - H; lia].
    - rewrite !swrap32_as_modA. f_equal.
      replace (u + 18446744073709536512 + 2 ^ 31) with ((u + -15104 + 2 ^ 31) + 4294967296 * 2 ^ 32) by (clear; lia).
      rewrite Z_mod_plus_full. reflexivity.
  Qed.

  Ltac se_fix mx :=
    repeat match goal with
    | H : rw_cells _ mx (?b + 164) _ |- _ => replace (b + 164) with (b + 160 + 4) in H by (clear; lia)
    | H : rw_cells _ mx (?b + 180) _ |- _ => replace (b + 180) with (b + 176 + 4) in H by (clear; lia)
    end.

  Ltac se_cq_leaf :=
    apply evtA_done; unfold SEQ; left;
    lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r3) _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
      exists r3 end;
    do 2 eexists; split;
    [ first [ (clear; lia)
            | lazymatch goal with |- _ < zswrap 32 (zlow 32 (bv_unsigned ?w + _)) < _ =>
                apply (se_rcA (bv_unsigned w)); [exact (proj1 (bv_unsigned_in_range 64 w))| assumption] end ]
    | cq_body ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "01>0@D25066864133.202D28498761192.202D37285929031.202D43863175048.202D4451634193.202 D60109196847.202K13481535851.202K2431698795.202 K38744182635.202K44164039966.202K49737312673.202K56923556715.202K61279323496.202K64038415723.202K9840090748.202 K9927252587.202 L13477261981.2  L14948329643.189L1685717371.0   L17561480300.199L23182876091.2  L2419170461.2   L24624768681.11 L32743128527.2  L33342826784.203L35653441506.11 L38235734261.1  L38748296349.2  L38948636245.0  L39332637397.0  L40051937615.2  L41083926835.201L41202929119.190L41202929119.191L43300649301.0  L44168742175.3  L49733071447.2  L50365866937.202L52225222276.0  L52765036985.204L53271535775.190L56911057053.2  L60098763854.3  L60242231282.2  L61277509919.2  L62406578796.197L64025917085.2  L64850595401.0  L68446757602.7  L9080220944.4   L9356559676.13  L9835808138.2   L9922970013.2   P23170010975.202P32737099528.202P40057967496.202Q10649498890.199Q10649498890.200Q10651864073.199Q10651864074.198Q13732992820.199Q13732992823.198Q17701933584.199Q17701933584.200Q28496781288.201Q28498761192.202Q3194347735.199 Q3194347735.200 Q37216054521.199Q39600066516.199Q39600066516.200Q4451634193.202 Q4453582353.201 Q45353655733.198Q45353655734.199Q61556549392.200Q61847600945.199Q61847600945.20000000100d00e00f01Y02U03A03m04Y05F06206^07K08708c09O09P09Q09R0:30:40:50:a0:b0;E0;]0;a0;b0;c0;d0;e0<L0<m0=N0=O0=P0=Q0>40>50>X0?90?:0?D0?M0?N0?o0@00@10@D0@S0AF0AG0AH0BL0CX0Dd0E70EJ0E]0F00FC0FV0Fi0G<0Ga0HF0HG0HH0Hb0Hc0Hd0II0In0JA0JT0K40Kn0LhFS2LF2sp2PP3PKA2bs3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stFFS2LF2sp2PP3PKA2bs3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP3PKA2lo2bs3LOS3LFB2FB3sp12e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP3PKA2bs3LFB3DPK2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2e13APP4PPBD2HB5Ha_st5Hl_stFFSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFFS3END1P3BUF4ENDB2BP4BUF02p52e14Hp2a4Hp2e3HeEFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS1R3HIA1h2sp2lo3TOP4HTOPS2loFSSFS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDSFFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HSS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBD1HS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFS1R2lo3LOSS3a0w3A0RFS2LF2sp2PP3PKA2bs3LFB2FB3sp14PPBDFSS1P2p52e14Hp2a4Hp2eS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRFFS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK22e14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12e13SP14PPBD2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp12e13SP14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stFFS2LF2PP2bs3LFB3PPB4PPBD2HBFFS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2e14PPBD2HB5Ha_st5Hl_stS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB4PPBDS2LF2PP2bs3LFB3PPB4PPBD2HB5Ha_stS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBDS2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F04PPBD". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPB PKB ENDB BIN BP EB BUF0 PPAL PPLO CWP PKLO CWK DPK DPB NB1 STK2"] Lemma seg_E : forall (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x mm : mem)
      (kv : word) (p5 e1 : Z) (pk0 pk1 a0w xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 ->
    sp1 mod 32 = 0 ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h ->
    hstkhi asegs R HIA hq = hstkhi asegs R HIA h ->
    FB mod 64 = 0 ->
    fresh_apart R LB LF FB 256 ->
    fresh_apart R LBq LF FB 256 ->
    (forall b, In b LB -> In b LBq) ->
    DINV2' WX FB sp1 hq LBq
      [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
       F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0]
      kv p5 e1 pk0 pk1 mm ->
    presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mm ->
    wcover R LB LF (bv_unsigned sp) WX PP 8 ->
    wcover R LBq LF (bv_unsigned sp) WB PP 8 ->
    evtA asegs AL (hcs asegs R HIA hq) (SEQ WX WB FB sp1 hq LBq m2x kv p5 e1 pk0 pk1)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0w a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 FB) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 e1) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 PKA)
             (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (FB + 160)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB)
             t3 t4 t5 t6)
          F (Z_to_bv 64 722424) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros WX WB FB sp1 hq LBq m2x mm kv p5 e1 pk0 pk1 a0w xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB WCa WCb.
    open_dinv2 D.
    rt_facts.
    clear UARG SM2 SPA TPV HBS0 PE B47 BL30 PP0 PKAL PK0 DKB RTCL.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq LBq _ _ HHq) as HTOP. rewrite ETq, ESq in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSq| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA hq) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA hq) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSq| exact SCS0]).
    clear SCS0 SCS.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; apply SUBq; exact BIN).
    destruct (hm_apart asegs R HIA hq LBq _ mm HHq) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; apply SUBq; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC. clear HBR1.
    assert (CWPq : client_wrange L (LBq ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hq) PP 8).
    { rewrite ETq. eapply client_wrange_mono; [exact CWP| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]]. }
    pose proof (hm_abase asegs R HIA hq LBq _ mm HHq) as AB0.
    pose proof (art_alwf asegs R HIA) as ALWF.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [722736; 726848; 721756] [] 150%N).
    lx_tree.
    all: lxu_chk_leaves 722736.
    all: repeat match goal with H : context [al_sb AL + Z.shiftr ?x 3] |- _ => rewrite (Z.add_comm (al_sb AL) (Z.shiftr x 3)) in H end.
    all: rewrite ?(Z.add_comm (al_sb AL) (Z.shiftr FB 3)).
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 721756) _ _ ?mx _] =>
             (* [comment removed for export] *)
             se_fix mx;
             assert (HHx : HM asegs R HIA hq LBq ((FB, 256) :: LF) mx) by lx_hm_at;
             assert (PRx : presW asegs R HIA hq LB LF (bv_unsigned sp) (arl_stklo R) WX m mx)
               by (eapply presW_munch; [exact PRES | eassumption | eassumption | unfold w_client | ];
                   repeat (apply Forall_cons; [cbn [fst snd]; replace (PP + 8 - PP) with 8 by (clear; lia) | ]); try apply Forall_nil;
                   first [ eassumption | exact (proj1 OPP) ]);
             assert (PRBx : presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mx)
               by (eapply presW_munch; [exact PRESB | eassumption | eassumption | unfold w_client | ];
                   repeat (apply Forall_cons; [cbn [fst snd]; replace (PP + 8 - PP) with 8 by (clear; lia) | ]); try apply Forall_nil;
                   first [ eassumption | exact (proj1 OPP) ]);
             apply evtA_done; unfold SEQ; right; merge_stk; epiq_body
         | |- context [MS _ _ (Z_to_bv 64 726848) _ _ ?mx _] =>
             (* [comment removed for export] *)
             (* [comment removed for export] *)
             (* [comment removed for export] *)
             lazymatch goal with LX : mx = ?m0 |- _ => subst mx; se_fix m0 end; se_cq_leaf
         end.
    all: first [ (clear - Hp2a Hp2e HeE; lia) | exact PPC ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L17561480300.196L33342826784.200L35653441506.11 L38235734261.1  L38948636245.0  L3916269619.7   L39332637397.0  L41083926835.198L43300649301.0  L50365866937.199L52765036985.201L60098763854.3  L62406578796.194L64850595401.0  L9080220944.4   L9356559676.13  00000L00j01B01F01G01[01\02>02?02]03;03E03a03b04104dS2LF2sp2PP3PKA2bs3LFB2FB3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp11HS1R3HIA1h2sp2lo3TOP4HTOPS2loSS3END2p22e14Hp2e3HeESS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP11HSS2LF2sp2PP3PKA2bs3LFB2FB3sp11HS2LF2sp2PP3PKA2bs3LFB2FB3sp11HS1R2lo3LOSS2LF2sp2PP3PKA2bs3LFB2FB3sp1SS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB BIN CWP CWK"] Lemma seg_F : forall (WX WB : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (m2x mm : mem)
      (kv : word) (p2 e1 : Z) (pk0 pk1 : word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s5v s6v s7v s8v s9v : word),
    bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 ->
    sp1 mod 32 = 0 ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h ->
    hstkhi asegs R HIA hq = hstkhi asegs R HIA h ->
    FB mod 64 = 0 ->
    fresh_apart R LB LF FB 256 ->
    fresh_apart R LBq LF FB 256 ->
    (forall b, In b LB -> In b LBq) ->
    DINV2' WX FB sp1 hq LBq
      [F1; F1; F1; F1; F8; F8; F2; F2; Z0; F2; F2; F2; Z0; Z0; Z0; F2;
       F2; F2; F2; F2; P4; F2; P4; F3; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0] kv p2 e1 pk0 pk1 mm ->
    presW asegs R HIA hq LBq LF (bv_unsigned sp) (arl_stklo R) WB m2x mm ->
    evtA asegs AL (hcs asegs R HIA hq)
      (EPIQ' hq hq LB LBq m WX FB sp1 s3v (XF hq LBq WB m2x p2 pk0 pk1))
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 FB) s3v s4v s5v s6v s7v s8v s9v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB)
             t3 t4 t5 t6)
          F (Z_to_bv 64 722720) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until s9v. intros SP1 SP1M HCSq ETq ESq F64 FRSH FRSHq SUBq D PRESB.
    open_dinv2 D.
    (* [comment removed for export] *)
    zstep. zstep.
    merge_stk. at_done. epiq_body.
    all: first [ (clear - Hp2a Hp2e HeE; lia) | match goal with |- ?g => idtac "SF-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkPKF.
