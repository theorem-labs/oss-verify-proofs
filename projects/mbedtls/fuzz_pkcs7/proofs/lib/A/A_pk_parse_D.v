(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_info P_rsa_parse_pubkey.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_asn1_get_tag_stmt A_oid A_oid_pk_alg A_oid_ec_grp_algid A_asn1_get_bitstring_null A_pk_defs A_pk_info A_pk_parse_B A_pk_parse_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_pk_parse_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0c36045ca9996a7e 0 7 0 1 57 1 91 1 92 1 97 1 103 1 104 1P0d9951800e6bf8f3 1 1 32 3 0 1 103 1 106 1 10 57 2 80 2 83 2 91 2 92 2 97 2 99 2 104 2 105 2 107 64P166ea0bcf3fb17ec 0 4 0 1 56 1 103 1 104 1P21d2712f42822093 0 9 0 1 80 1 83 1 91 1 92 1 97 1 99 1 103 1 104 1P2a523030713a109a 0 4 0 1 56 1 103 1 104 1P2f8c7a1af1eaee10 1 1 32 3 0 1 103 1 106 1 10 57 2 80 2 83 2 91 2 92 2 97 2 99 2 104 2 105 2 107 64P32af4ca7252ce6fe 0 7 0 1 57 1 91 1 92 1 97 1 103 1 104 1P3f6d77b13af56e28 0 4 0 1 91 1 92 1 97 1N030855e31388da20N092b1311254ca9f2N1eacd26455254ffcN2abfd2a514352a47"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_pk_parse_D () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.A.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.LibA.ARt.HM"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C4"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.LibA.ARt.HST"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "WalkPKD.Call.DINV"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.A.A_pk_parse_B.EPIQ"; "OSSVerify.KrLib.A.A_pk_parse_C.XE"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "A_PK_SETUP_PK"; "OSSVerify.KrLib.P.P_pk_info.pk_info_of"; "OSSVerify.KrLib.A.A_pk_info.A_PK_INFOS"; "WalkPKD.Call.TVAL"; "Stdlib.Lists.List.In"; "WalkPKD.Call.CALLQ_SETUP"].


Definition A_PK_SETUP_PK : Z := 0x0b027c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L11607912823.3L16046331926.4L4136524212.4 L54713065586.400000100800?00DSS1x1d1HS1x1d1DS1x1d". (* [comment removed for export] *)
Lemma swrap32_mod64_addB : forall x d, -2^31 <= x + d < 2^31 -> bv_swrap 32 (x mod 2^64 + (2^64 + d)) = x + d.
Proof.
  intros x d H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  pose proof (Z.div_mod x (2^64) ltac:(lia)) as D.
  replace (x mod 2^64 + (2^64 + d) + 2^31) with ((x + d + 2^31) + ((1 - x / 2^64) * 2^32) * 2^32) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section WalkPKD.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
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
  Hypothesis OIDPK : oid_lookup1_stmtA asegs R HIA A_OID_GET_PK_ALG OID_PK_ALG_STACK_A.
  Hypothesis OIDGA : oid_lookup1_stmtA asegs R HIA A_OID_GET_EC_GRP_ALGID OID_EC_GRP_ALGID_STACK_A.
  Hypothesis GETBSN : asn1_get_bitstring_null_stmtA asegs AL A_ASN1_GET_BITSTRING_NULL.

  Local Notation EPIQ' := (A_pk_parse_B.EPIQ R HIA LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo).
  Local Notation XE' := (A_pk_parse_C.XE PP END PKA P).

  (* [comment removed for export] *)
  Ltac merge_stk :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with SL : rw_cells _ mx (?q + 8) [C8 _; C8 _; C8 _], S48 : rw_cells _ mx (?q + 48) [C8 _],
                          STA : stk _ mx ?q (?q + 8), STB : stk _ mx (?q + 32) (?q + 48), STC : stk _ mx (?q + 56) _ |- _ =>
        chunk_to_stk SL; chunk_to_stk S48;
        stk_merge_into STA SL; stk_merge_into STA STB; stk_merge_into STA S48; stk_merge_into STA STC end end.
  (* [comment removed for export] *)
  Ltac fin_epiq :=
    merge_stk;
    lazymatch goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb AL) _ |- _ => norm_b8 H end;
    apply evtA_done; left; eexists; unfold A_pk_parse_B.EPIQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    do 25 eexists; do 32 eexists; split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | idtac ].



  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11158032613.82L25876784085.20L29784460045.82L39348729613.82L45146172909.8200000O01101K01g03GS2LF2sp2PP3PKA2bs3LFB1B1k2H02HkS1B1k2r02HB2Hk1a2Ha1q1r1H2H02q02H4S2LF2sp2PP3PKA2bs3LFB1B2H0S1R2LF2sp2PP3PKA2bs3LFB1B2H0S1R2LF2sp2PP3PKA2lo4STKk3BUF2bs3SLO3LFB3PPB3PKB3PP03PK04PKLO3DPK3DPB3DKB3NB14STK21B1k2H02Hk1a2Ha". (* [comment removed for export] *)
  Lemma aobj_partial : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_D ()) "PCSx,P,$0.SpPmX,P,(1.&40.)(2.(1.&8.))PB,$0.Pk,$0.P,(3.$4.R3.(5.(6.R2.+3.)(7.(8.VR,)))(9.$:.(;.(<.&8.R1.))(=.$:.)))P,(>.$0.(?.R3.+8.)=)P,(10.=R4.)P,(11.(10.+1.R4.)(10.R4.+7.))P,(12.R8.R6.R5.)(13.$4.(8.VR,)R9.R8.R7.R6.)")
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

  Local Notation FSH1 :=
    [F1; F1; F1; F1;  F8; F8; F2; F2;  Z0; Z0; Z0; F2;  F2; F2; F2; F2;  Z0; F2; F2; F2;  Z0; Z0; Z0; F2;  F2; F2; F2; F2;  P4; F2; P4; F3].

  (* [comment removed for export] *)
  Definition DINV (FB sp1 : Z) (h1 : HST asegs R HIA) (sh : list cell) (kv : word) (p2 e1 : Z) (mm : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_D ()) "(14.(1.&40.)Lw0,(1.&40.)(14.(1.&40.)Lw1,(1.&40.)(14.(1.&40.)Lw2,(1.&40.)(14.(1.&40.)Lpc0,(1.&40.)(14.(1.&40.)Lpc1,(1.&40.)(14.(1.&40.)LLw,(1.&40.)(14.(1.&40.)Lkpad,(1.&40.)(14.(1.&40.)Lgv,(1.&40.)(14.(1.&40.)Lgpad,(1.&40.)(14.$0.Lpp,$0.(14.(1.&40.)Lo0,(1.&40.)(14.(1.&40.)Lo1,(1.&40.)(14.(1.&40.)Lo2,(1.&40.)(14.(1.&40.)Lo3,(1.&40.)(14.(1.&40.)Lptag,(1.&40.)(14.(1.&40.)Lppad,(1.&40.)(14.(1.&40.)Lplen,(1.&40.)(11.(15.$4.VR,VHIA,O6.VLB,(9.(16.$0.$0.)(17.$0.$0.O8.+100.)VLF,)O1.)(11.(3.$4.O1.O8.(9.$:.(18.R11.)(9.$:.(18.R10.)(9.$:.(18.R?.)(=.$:.)))))(11.(3.$4.O1.(5.O8.+20.)(9.$:.(18.R>.)(9.$:.(18.R=.)(=.$:.))))(11.(3.$4.O1.(5.O8.+40.)(9.$:.(19.R7.)(9.$:.(19.R6.)(9.$:.(18.R5.)(9.$:.(18.R4.)(=.$:.))))))(11.(3.$4.O1.(5.O8.+80.)(9.$:.(18.R<.)(=.$:.)))(11.(3.$4.O1.(5.O8.+:0.)(9.$:.(19.R3.)(9.$:.(19.R2.)(9.$:.(18.R1.)(9.$:.(18.(<.&40.R8.))(=.$:.))))))(11.(3.$4.O1.(5.O8.+>0.)(9.$:.(19.O4.)(=.$:.)))(11.(3.$4.O1.(5.(5.O8.+>0.)+4.)(9.$:.(19.R;.)(=.$:.)))(11.(3.$4.O1.(5.O8.+?0.)(9.$:.(19.R:.)(=.$:.)))(11.(3.$4.O1.(5.(5.O8.+?0.)+4.)(9.$:.(19.R9.)(=.$:.)))(11.(3.$4.O1.(5.(6.O8.+3.)(7.(8.VR,)))O5.)(11.(3.$4.O1.(5.(1:.&40.Vsp,)-68.)(9.$:.(18.Vs11,)(9.$:.(18.Vs10,)(9.$:.(18.Vs9,)(9.$:.(18.Vs8,)(9.$:.(18.Vs7,)(9.$:.(18.Vs6,)(9.$:.(18.Vs5,)(9.$:.(18.Vs4,)(9.$:.(18.Vs3,)(9.$:.(18.Vs2,)(9.$:.(18.Vs1,)(9.$:.(18.Vs0,)(9.$:.(18.Vra,)(=.$:.)))))))))))))))(11.(3.$4.O1.(5.O7.+8.)(9.$:.(18.(<.&40.VPKA,))(9.$:.(18.(<.&40.(5.O8.+?0.)))(9.$:.(18.(<.&40.(5.(6.VPP,+3.)(7.(8.VR,)))))(=.$:.)))))(11.(3.$4.O1.(5.O7.+30.)(9.$:.(18.(<.&40.O8.))(=.$:.)))(11.(1;.$4.O1.O7.(5.O7.+8.))(11.(1;.$4.O1.(5.O7.+20.)(5.O7.+30.))(11.(1;.$4.O1.(5.O7.+38.)(5.(1:.&40.Vsp,)-68.))(11.(1;.$4.O1.Vlo,O7.)(11.(1<.$4.O1.)(11.(3.$4.O1.VPP,(9.$:.(18.(<.&40.O3.))(=.$:.)))(11.(13.$4.(8.VR,)(1=.$4.VR,VHIA,O6.)O1.VPP,+8.)(11.(3.$4.O1.VPKA,(9.$:.(18.(<.&40.=))(9.$:.(18.(<.&40.=))(=.$:.))))(11.(13.$4.(8.VR,)(1=.$4.VR,VHIA,O6.)O1.VPKA,+10.)(11.(1>.$4.O1.VBUF,Vbs,)(11.(13.$4.(8.VR,)(1=.$4.VR,VHIA,O6.)O1.VBUF,(1?.(20.(1.&8.)Vbs,)))(11.(10.VP,O3.)(11.(10.O3.O2.)(11.(10.O2.VEND,)(11.(21.(11.(>.$0.R8.=)(11.(>.$0.(1:.&40.R1.)=)(>.(1.&40.)R3.(<.&40.=))))(11.(10.VBUF,R8.)(11.(10.VP,R8.)(10.(5.R8.(1:.&40.R1.))O2.))))(22.$4.VR,VHIA,O6.VLB,VLF,(1:.&40.Vsp,)(23.VR,)(9.(16.$0.$0.)(17.$0.$0.VPP,(5.VPP,+8.))(9.(16.$0.$0.)(17.$0.$0.VPKA,(5.VPKA,+10.))(=.(16.$0.$0.))))Vm,O1.)))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac open_dinv D :=
    destruct D as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & o0 & o1 & o2 & o3 & ptag & ppad & plen
                   & HH1 & FHD & LPKC & LOID & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MI1
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & PPC & PRES).
  Ltac pack_dinv :=
    unfold DINV; do 9 eexists; eexists; do 7 eexists;
    repeat match goal with |- _ /\ _ => split end; first [ eassumption | idtac ].

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 GETBSN; try lx_pin1 OIDGA; try lx_pin1 OIDPK; try lx_pin1 RTCL; try lx_pin1 DPK; try lx_pin1 PKLO; try lx_pin1 PK0; try lx_pin1 PKAL; try lx_pin1 PPLO; try lx_pin1 PP0; try lx_pin1 PPAL; try lx_pin1 BUF0; try lx_pin1 PE; try lx_pin1 BP; try lx_pin1 ENDB; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 bs; try lx_pin1 BUF; try lx_pin1 P; try lx_pin1 lo; try lx_pin1 PKA; try lx_pin1 END; try lx_pin1 PP; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0190@D10637083017.179D14196765253.179D2459793318.177 D3162359814.179 D32074845714.178D32452690557.177D32604263317.180D3388366767.176 D36106837483.179D4438590009.178 D44709997423.178D45704738334.176D46795284844.179D50554376240.178D60109265000.179D60109265003.178D62011770190.180D66251787523.177D67370028906.178D68411655660.176D6899603433.176 L17561480300.193L19546883928.145L19589199734.1  L27111942217.1  L33342827300.197L35653441506.11 L38235734261.1  L38948636245.0  L39332637397.0  L41083927351.195L43300649301.0  L46887492116.7  L47230721779.142L47638600054.1  L48119718063.143L50365866429.196L5070094973.145 L52765037501.198L59578101107.183L60098763854.3  L62406578796.191L64850595401.0  L65276887190.142L6912107233.142 L9080220944.4   L9356559676.13  Q10523111605.187Q10592386206.184Q10637083011.186Q11657494700.184Q16178749883.184Q23927511196.187Q32074845716.185Q32440833928.183Q32681887702.184Q32681887705.187Q40216052035.183Q46795284838.186Q47230721776.187Q48117620904.184Q48132302231.183Q49563371192.187Q49754700707.185Q50554376246.185Q56525516080.183Q56531220660.184Q62011770180.187Q62507329528.185Q65266402725.183Q65276887190.188Q6897428434.183 Q6912107233.188 00000E00F00G00H00^01001K01L01M01N01O01a02602L02g03B03V03h03i03j04<04N04g04k04o05C05[05_05`05a06<06=06X06i06m07Z07n08L08`09709A09S09T09b0:00:?0;20;B0;P0;^0;_0;m0<L0<[0<\0<]0<^0<_0<m0=>0=k0>X0>Y0>Z0>i0>j0>k0?80?J0?X0?f0@40@BS2LF2PP2bs3LFB2FB3sp1FFFS2LF3PKA2bs3LFB2FB3sp1S2LF2bs3LFB2FB3sp1S1R3HIA2LF2bs3LFB2FB3sp12h1FFFFS2LF2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S2LF3PKA2bs3LFB2FB3sp1S1R2LF2lo2bs3LOS3LFB2FB3sp1S1R2LF2lo2bs3LOS3LFB2FB3sp1S1R2LF2bs3LFB2FB3sp1S2LF2bs3LFB2FB3sp1FFS2LF2bs3LFB2FB3sp1S2LF2bs3LFB2FB3sp1S2LF2bs3LFB2FB3sp12F03F8'S2FBS2PPS2LF2bs3LFB2FB3sp11HS1R3HIA1h2sp2lo3TOP4HTOPS2loSSS2LF2sp2bs3LFB2FB3sp13SP11HSS3END1P2p22e14Hp2a4Hp2e3HeES1R2LF2bs3LFB3ALOS2FBS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23ALOS2LF2bs3LFB2FB3sp11HS2LF2bs3LFB2FB3sp14SP1R2F03F8'S2LF2bs3LFB2FB3sp11HS2LF2bs3LFB2FB3sp11c2HcS1R2lo3LOSS2LF2bs3LFB2FB3sp1SS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS1R2LF2sp2bs3LFBS2LF2bs3LFB2FBS2LF2PP2bs3LFBFS2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS2LF3PKA2bs3LFBFFFFS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23ALOS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23ALOFFS2LF3PKA2bs3LFBFFS1R2LF2bs3LFBS2LF2PP3PKA2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB". (* [comment removed for export] *)
  #[using="STK2 NB1 DKB DPB CWK CWP BL30 B47 EB BIN HBS0 PKB PPB LFB TOP SLO STK0 LOS STKk NS1 IMG"]
  Lemma err_c8 : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_D ()) "PFB,$0.Psp1,$0.Ph1,(24.$4.VR,VHIA,)Pmm,P,(1.&40.)(2.(1.&8.))Pkv,(1.&40.)Pp2,$0.Pe1,$0.Pr,$0.Pxra,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Ps4v,(1.&40.)Ps5v,(1.&40.)Ps6v,(1.&40.)Ps7v,(1.&40.)Ps8v,(1.&40.)Ps9v,(1.&40.)Ps10v,(1.&40.)P,(11.(10.(25.(1:.&40.Vsp,)+;0.)R1=.)(10.R1=.(25.(1:.&40.Vsp,)+:0.)))P,(>.$0.(?.R1>.+20.)=)P,(>.P,$0.Sp(1=.$4.VR,VHIA,R1>.)(1=.$4.VR,VHIA,Vh,))P,(>.$0.(26.$4.VR,VHIA,R1?.)(26.$4.VR,VHIA,Vh,))P,(>.$0.(27.$4.VR,VHIA,R20.)(27.$4.VR,VHIA,Vh,))P,(>.$0.(?.R23.+40.)=)P,(28.VR,VLB,VLF,R24.+100.)P,(29.R25.R24.R23.(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?3.))(=.$:.)))))))))))))))))))))))))))))))))R21.R20.R1?.R22.)P,(11.(2:.(2;.(2<.+2.+1?.))R1?.)(2:.R1?.=))(2=.$4.(8.VR,)(1=.$4.VR,VHIA,R25.)Lms,$2>.(14.(1.&40.)La0v,(1.&40.)(2?.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R27.R27.VLB,VLB,Vm,(9.(16.$0.$0.)(17.$0.$0.VPP,(5.VPP,+8.))(9.(16.$0.$0.)(17.$0.$0.VPKA,(5.VPKA,+10.))(=.(16.$0.$0.))))R29.R28.R1.(30.VPP,VEND,VPKA,VP,R1.)R2.))(31.(32.R1?.(<.&40.R26.)Vgp,Vtp,R1>.R1=.R1<.Vsp,(<.&40.R26.)(<.&40.R20.)R1;.R1:.R19.R18.R17.R16.R15.(<.&40.R27.)(<.&40.R27.)R10.R?.R>.R=.R<.R;.R:.(<.&40.(5.(6.R27.+3.)(7.(8.VR,))))R14.R13.R12.R11.)VF,(<.&40.+:?3<4.)Vfc,(33.(1.&40.))R24.(34.$4.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros until s10v.
  intros SP1 SP1M Ehcs Ehtop Estk F64 FRSH D Hr.
  open_dinv D.
  rt_facts.
  rewrite <- Ehcs in CSOK, SCS0.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP.
  rewrite Ehtop, Estk in HTOP.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia | lx_side_lia ]).
  assert (SCS : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO STK0 NS1 TOP HTOP; lia | lx_side_lia ]]).
  assert (SCS1 : crange (hcs asegs R HIA h1) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h1) h1 LB LF mm FB 256 lo HH1 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS).
  change (256 / 8) with 32 in SBND, APS.
  pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
  pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
  assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; exact BIN).
  destruct (hm_apart asegs R HIA h1 LB _ mm HH1) as [HBR1 _].
  rewrite Forall_forall in HBR1.
  destruct (HBR1 _ ltac:(apply in_app_iff; left; exact BIN)) as (_ & _ & BUFC & _).
  cbn [fst snd] in BUFC.
  assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8).
    { eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]. }
  assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
  assert (WCPP : wcover R LB LF (bv_unsigned sp) X00 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  try lxg_b8u. lx_pre. lx_run_tac (PLAN [0x052c88; 0x067ce4; 0x0990e0; 0x09a118; 0x09a73c; 0x0a82c8; 0x0a8710; 0x0af184; 0x0af670; 0x0b0178; 0x0b0220; 0x0b027c; 0x0b0368; 0x0b1180; 0x0d6e24; 0x0d71bc] [] 442%N).
  lx_tree.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  all: (cut True; [ intros _ | ]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xaf184) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (merge_stk) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb AL) _ |- _ => norm_b8 H end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (eexists) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold A_pk_parse_B.EPIQ) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (do 25 eexists) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (do 32 eexists) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat match goal with |- _ /\ _ => split end; first [ eassumption | (exists r, p2; split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]; split; [exact Hr|]; split; [eassumption|]; split; [first [ clear - Hp2a Hp2e HeE; lia | lx_side_lia ]| eassumption]) | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "ERRC8-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xaf194 path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xaf184) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xaf194 path 1: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xaf184) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- True => exact I | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lxw err_c8: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TVAL (kv : word) : Z := bv_unsigned (sx32 kv) mod 2^32.
  Definition CALLQ_SETUP (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_D ()) "Lms,$2>.(14.P,(1.&40.)(2.(1.&8.))Lmm,P,(1.&40.)(2.(1.&8.))(14.(1.&40.)Lt0,(1.&40.)(14.(1.&40.)Lt1,(1.&40.)(14.(1.&40.)Lt2,(1.&40.)(14.(1.&40.)La2,(1.&40.)(14.(1.&40.)La3,(1.&40.)(14.(1.&40.)La4,(1.&40.)(14.(1.&40.)La5,(1.&40.)(14.(1.&40.)La6,(1.&40.)(14.(1.&40.)La7,(1.&40.)(14.(1.&40.)Lt3,(1.&40.)(14.(1.&40.)Lt4,(1.&40.)(14.(1.&40.)Lt5,(1.&40.)(14.(1.&40.)Lt6,(1.&40.)(14.(1.&40.)Lkv,(1.&40.)(14.$0.Lp5,$0.(14.$0.Le1,$0.(14.$0.Linfo,$0.(11.(>.$2>.R13.(31.(32.(<.&40.+:?484.)(<.&40.O2.)Vgp,Vtp,R11.R10.R?.Vsp,(<.&40.O2.)(<.&40.VPKA,)(<.&40.R1.)R>.R=.R<.R;.R:.R9.(<.&40.O3.)(<.&40.O3.)(<.&40.VPP,)(<.&40.R2.)(<.&40.-4000.)(<.&40.(5.O3.+:0.))(<.&40.(7.(8.VR,)))(<.&40.(5.O3.+>0.))(<.&40.(5.O3.+40.))(<.&40.(5.(6.O3.+3.)(7.(8.VR,))))R8.R7.R6.R5.)VF,(<.&40.$35.)Vfc,(33.(1.&40.))R12.(34.$4.)))(11.(29.O3.O2.O1.(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?3.))(=.$:.)))))))))))))))))))))))))))))))))R4.R3.R2.R12.)(11.(>.$0.R1.(36.$37.(38.R4.)))(39.$0.R1.$37.))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04g0@D10636937134.223D14197109858.223D16071854214.223D16071854214.234D3162115617.223 D36107017164.223D46794843979.223D49496112240.223D60109446735.223D67666003371.223D68221095944.223D68221095944.234D717153038.223  K15452675194.223K20981739667.221K22528888377.223K30691932129.222K30993319891.223K33484782784.222K35771704296.222K40598034112.221K4634225600.222 K51630569664.222K58743820992.222K61156572794.223K64183322703.223K65858155712.221L1056014037.42  L11001591018.196L13424629187.42 L14492240177.211L15464962028.2  L15756355153.16 L15766792130.42 L15846906171.42 L15934535645.1  L1685717371.0   L16936279633.0  L17561480300.219L17561480300.229L18538772363.2  L20977711877.2  L21197274889.42 L21654730866.2  L21850448153.212L22078896779.2  L22518399534.2  L23268210308.0  L23594014327.1  L2396210365.2   L24023900370.0  L24624821949.211L24671826045.1  L2621559066.1   L27111942217.1  L27346952255.211L27817441514.196L27940637587.16 L27942750720.42 L28697492879.2  L28764351619.9  L30507144274.2  L30662564814.9  L30696291447.1  L30784240051.2  L30997223346.3  L32879090465.0  L33342826784.223L33342826784.233L33472427862.2  L3480446377.42  L3482559546.16  L34852063412.2  L35653441506.11 L35784583294.2  L35905413235.42 L36012194261.220L36055287637.4  L363719563.2    L36694146884.0  L37687006330.2  L37811135095.1  L38069802256.10 L38235734261.1  L38948636245.0  L39332637397.0  L39790050952.9  L40279545204.1  L40585223510.2  L41083926835.221L41083926835.231L41112251147.42 L41202929119.211L42411609006.0  L42750710500.2  L43300649301.0  L43810982283.2  L44256719595.42 L45536337053.42 L45921596632.1  L46131931633.2  L4647100502.2   L47870616696.2  L48871635063.1  L50046389710.3  L50059654756.2  L50365866937.222L50365866937.232L50545063073.0  L50616353679.222L50678314462.3  L50925318027.2  L51582202539.197L51634926422.2  L52765036985.224L52765036985.234L53617080676.3  L53873477690.42 L55555508698.42 L55982268023.1  L56293046125.3  L56787311448.1  L56998170737.3  L58039649675.2  L58747656534.2  L58972524609.3  L59308586248.2  L59538641783.1  L60098763854.3  L61168858604.3  L62406578796.217L62406578796.227L63852571929.211L64009471222.1  L64179129035.1  L64482796004.2  L64850595401.0  L65520269536.2  L65862516566.2  L66062374908.211L66298372189.2  L66812728480.3  L67070089790.2  L67653551064.2  L67847239921.2  L67989683843.2  L881835912.0    L9080220944.4   L9356559676.13  L9783143000.1   L9993482097.2   P18523612460.222P18523612460.234P21647862485.221P21647862485.234P22094145580.222P22094145580.234P2386269722.220 P30511339222.222P30691932129.222P30772015653.222P34857851411.234P356858156.222  P356858156.234  P37693867741.223P37693867741.234P38605639612.203P42761764931.222P43817786156.234P46125136726.220P47876372191.221P47876372191.234P50048623811.222P50671478649.221P50927926572.221P50927926572.234P53607099331.220P56299840970.221P57003983574.220P58041177900.221P58041177900.234P64183322703.223P64484389699.220P66292560634.222P66292560634.234P66453878491.203P66818508295.223P66818508295.234P67064334489.220P67862424150.222P67988155428.222P67988155428.234P7740881908.203 P9986686422.222 Q10594415769.199Q10636937134.223Q10637080280.219Q10649498890.220Q10651829299.188Q10821824020.203Q1195234662.187 Q12076400817.197Q12078415899.197Q12658605510.203Q12658605510.205Q13731016165.219Q17027695041.223Q17458927065.193Q17681074618.223Q17681074618.234Q17701933584.220Q17703789353.188Q1867768678.223 Q1867768678.234 Q19135999389.193Q19547000785.197Q19856212711.223Q19940505025.190Q21767670690.223Q21767670690.234Q23865066771.197Q25745664918.198Q26314584654.203Q26316671538.184Q26480898663.223Q27573751300.223Q27573751300.234Q27663034001.197Q27663313085.223Q27942454161.223Q27942454161.234Q2803826605.223 Q2803826605.234 Q28694295695.223Q29743138348.183Q29775981542.223Q29775981542.234Q31155634335.195Q31339371283.197Q3194347735.220 Q32681607669.223Q32681607669.234Q33945187126.190Q34357517862.191Q34669208210.198Q3477426724.223 Q3477426724.234 Q34867094532.197Q36508117400.223Q3655110416.219 Q38144578741.198Q3848968117.189 Q39285966485.197Q39460178071.223Q39600066516.220Q4010030704.223 Q40798937756.190Q42412061296.223Q43324197004.192Q43324197006.194Q43907681865.197Q44298944140.184Q44298944140.198Q44301027056.203Q44885637135.190Q45482765142.205Q46002272309.198Q46794843979.223Q47228431932.203Q47647924635.197Q47649972529.197Q48118064779.223Q48119910507.203Q48523164961.194Q4924621080.223 Q49496112240.223Q50522501855.223Q50556521588.187Q508607707.195  Q51107054235.198Q51381972041.197Q51471717775.219Q51682470943.189Q51740073104.196Q54338530143.191Q54481541666.191Q54785822014.197Q55026446740.196Q55444398951.223Q5596578838.203 Q58207055645.199Q58974185687.200Q59619648100.197Q59621696206.197Q60321684161.231Q61847600945.220Q63435846322.198Q64228675114.202Q66901779611.198Q67140321772.183Q67778467980.189Q6909946601.200 Q7243851811.192 Q9356511367.226 Q9356758023.200 Q9644353070.197 Q9644583048.223 Q9644583048.234 Q9672141798.223 Q9672141798.234 Q9810218078.231 00000L00M01\02k02l02m03I03e04J04K05T06]07908709109G09H09^0:X0;R0<L0=F0>@0?:0@80@90A30AI0AJ0BR0BS0BT0CC0DB0EO0ER0ES0ET0F00FL0FM0FN0F`0Fa0G=0G>0G?0G@0GD0GE0GF0I90I=0IB0IF0K90L70Lf0Me0Mm0N;0N<0NQ0NR0NS0NT0NU0O30OQ0OR0PV0QJ0QK0Qc0Qd0R:0Ra0Rk0Rl0Rm0Rn0S20SD0SH0SI0SJ0Sg0Sk0Sl0TN0U00UF0Ub0Uc0Ud0Ue0Uf0W60XG0XL0XM0XN0XO0XS0X[0X\0Y:0YX0YY0Z50Z60Z70ZS0ZT0[20[P0[Q0[b0\e0\i0\j0\o0]00]10]20]>0]D0]H0]R0]S0]o0^K0^g0^h0^i0^j0^k0_50_60_R0_S0_T0_U0_]0_^0__0_`0_o0`b0`g0`h0a]0bR0bS0bT0cI0d>0e30fZ0f[0gO0iL0jA0k60le0nb0oO11>12312h13]14R16A16[17P18E19c1:=1;21;g1<\1<]1>L1>b1?81?e1A41BC1D21Dg1E\1FQ1G=1H21HQ1H_1Hm1I;1I]1JF1Ji1Jj1Jk1KT1LQ1L_1Lm1ML1NA1O61OD1Of1Og1Oh1PG1Pn1Po1Q01Qe1RZ1Rh1SG1Sl1T?1TM1TN1TO1Tn1U<1Ui1VV1Ve1W41W51WC1WY1Wo1XN1X\1X]1X^1X_1Y^1ZC1Zb1[41[F1[T1[b1\11\21]11]P1]Q1]R1]`1^M1^[1_:1_Y1_g1`:1`M1a21a31b01bC1bQ1c:1cH1cV1dC1eH1eg1eh1f61fD1fg1gF1gY1gg1h61hc1iB1iC1j:1jH1jg1jh1ji1kH1kg1kh1ki1l81lm1ln1n91nL1nZ1n[1o:1oY1om20A20R20c21421521621ES2LF2sp2PP3PKA2bs3LFB2FB3sp1FS1R2LF2sp2PP3PKA2lo4STKk2bs3LOS3SLO3LFB3PPB3PKB3NB14STK22FB3sp13SP13SPR4SP1R2F0S1R2LF2sp2PP3PKA2lo4STKk2bs3LOS3SLO3LFB3PPB3PKB3NB14STK22FB3sp13SP13SPR4SP1R2F0FFS2LF2sp2PP3PKA2bs3LFB2FB3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp1S1R2LF2sp2PP3PKA2lo2bs3LOS3LFB2FB3sp1FS1R3HIA1h2LF2sp2PP3PKA2bs3TOP3LFB3PPB3PKB2FB3sp12h13SP15Ehtop3SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3PKA2bs3TOP3LFB3PPB3PKB2FB3sp12h13SP15Ehtop3SPR4SP1R2F0S2LF2sp2PP3PKA2bs3LFB2FB3sp1S2LF2PP3PKA2lo2bs3LFB2FB3sp12p22e13x143APK2x23x153x163x174POSTS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2LF2PP3PKA2bs3LFB3DPKFS2LF2PP3BUF2bs3LFB3DPBS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2LF2PP2lo3BUF2bs3LFB2FB3sp12p22e13x143APB2x23x153x163x174POSTFS2LF2PP2lo2bs3LFB2FB3sp12p22e13x143APP2x23x153x163x174POSTS2PP2lo2bs4PPLO2FB3sp1FS1R2sp2PP2lo4STKk2bs3LOS3SLO3PP03NB14STK22FB3sp13SP14SP1M3ALO3ACV2F03F8'FFS1R2sp2lo4STKk3LOS3SLO3NB14STK23sp13SP13ALO3ACVS1R2sp2PP2lo4STKk2bs3LOS3SLO3PP03NB14STK22FB3sp13SP13ALO3ACV2F0S1R2sp2PP2lo4STKk3BUF2bs3LOS3SLO3PP04PPLO3NB14STK22FB3sp13SP13ALO3ACV2F04BUFCS1lSSS2LF2sp2PP3PKA2bs3LFB2FB3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp1FFS2PP2bs2FB3sp13APPFS2LF2sp2PP3PKA2bs3LFB2FB3sp1FFSS2FBFSS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12p22e14Hp2a3HeE3ACV3SPR4SP1R2F04BUFC2p52L53LR54Hp5a4HL5bS2FBS3sp1S2PPS1R2LF2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2EB4BUF02FB3sp12p22e14Hp2a3HeE3ACV3SPR4SP1R2F04BUFC2p52L53LR54Hp5a4HL5bS1R2LF2sp2PP3PKA2bs3LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2sp2lo4STKk3LOS3SLO3NB14STK23sp13SP13ALO3ACVS1R2sp2PP2lo4STKk2bs3LOS3SLO3PP03NB14STK22FB3sp13SP13ALO3ACV2F0S2r53RR5S2p22e12p53Hp5FS1P2p22e14Hp2a2p53Hp5FFFSS2LF2sp2PP3PKA2bs3LFB2FB3sp11HS2LF2sp2PP3PKA2bs3LFB2FB3sp11HFS1R2sp2PP2lo4STKk2bs3LOS3SLO3PP03NB14STK22FB3sp13SP14SP1M3ALO3ACV2F0S1R2sp2lo4STKk3LOS3SLO3NB14STK23sp13SP14SP1M3ALO3ACVFS1R3HIA1h2sp2lo3TOP4HTOPFS2PP3BUF2bs2FB3sp13APBS2LF2sp2PP3PKA2bs3LFB2FB3sp14info5INFORS2tv2E12E4FSFS2FBS2r53RR51r3KT51q1HS2loSSS3END1P2p22e14Hp2a3HeE2p53Hp5S2FBFS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP11HS2LF2sp2PP3PKA2bs3LFB2FB3sp13SP11HS2PP3BUF2bs3DPB2FB3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp1SFSFS1R2sp2PP2lo4STKk1P3BUF2bs3LOS3SLO2BP3PP03NB14STK22FB3sp12p23SP14Hp2a3ALO3ACV2F0S1R2sp2PP3END2lo4STKk3BUF2bs3LOS3SLO2EB3PP03NB14STK22FB3sp12e13SP13HeE3ALO3ACV2F0S3sp1FFFS2FBS2r53RR5FS2LF2sp2PP3PKA2bs3LFB2FB3sp11HS2LF2sp2PP3PKA2bs3LFB2FB3sp11HSS2LF2sp2PP3PKA2bs3LFB2FB3sp1FFS2LF2sp2PP3PKA2bs3LFB2FB3sp1FS2LF2sp2PP3PKA2bs3LFB2FB3sp11HS2LF2sp2PP3PKA2bs3LFB2FB3sp11HFS2PP2bs2FB3sp12F0S1R2sp2PP2lo4STKk2bs3LOS3SLO3PP03NB14STK22FB3sp13SP13ALO3ACV2F03F1'S2FBFS3sp1FFFS3BUF2bs3B47S1i2HiS2FBS1R2lo3LOSFS2LF2sp2PP3PKA2bs3LFB2FB3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp1FFFSS4info3HINFS2LF2sp2PP3PKA2bs3LFB2FB3sp1FFFS2sp3sp1FFSS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS3sp1FS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOFFS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK22p22e14Hp2a4Hp2e3HeE3ALO4BUFCFS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3ALO3F1'S1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK23sp12p22e13SP14Hp2a3HeE3ALO4BUFC2p52L53LR54Hp5a3KEQS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK23sp12p22e13SP14Hp2a4Hp2e3HeE3ALO4BUFCS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK23sp12p22e13SP14Hp2a3HeE3ALO4BUFC2p52L53LR54Hp5a3KEQS1R2LF3BUF2bs3LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK23sp12p22e13SP14Hp2a4Hp2e3HeE3ALO4BUFCS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK23sp12p22e13SP14Hp2a4Hp2e3HeE3ALO4BUFCS2LF2PP2lo2bs3LFB4PPLO3sp1S1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2PE2EB4PPLO4PKLO3NB14STK23sp13SP13ALO4BUFCS2LF2lo2bs3LFB2FB3sp14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOFS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK23sp12p22e13SP14Hp2a4Hp2e3HeE3ALO4BUFCS2LF2sp2bs3LFB3sp13SP1S2LF2sp2bs3LFB3sp13SP1S1R2LF3PKA2bs3LFB2FB3APK2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3PKA2lo4STKk3BUF2bs3LOS3SLO3LFB4PPLO4PKLO3NB14STK23sp13SP13ALO4BUFCS1R2LF2sp2PP3PKA2lo4STKk3BUF2bs3LOS3SLO3LFB4PPLO4PKLO3NB14STK23sp13SP13ALO4BUFCS1R2LF2sp2PP3END3PKA2lo4STKk1P3BUF2bs3LOS3SLO3LFB2BP2EB4PPLO4PKLO3NB14STK23sp12p22e13SP14Hp2a4Hp2e3HeE3ALO4BUFCS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2PP2bs3LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLOS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2PP2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3PKA2bs3LFB2FB2HB5Ha_st5Hl_stFFS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF3LFB1l2EB3B474BL302FB4BUFC2HB5Ha_st5Hl_st5SAEstS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp13SP1S1R2LF2sp2PP2lo4STKk2bs3SLO3LFB4PPLO3NB14STK23sp13SP1S2LF2PP2bs3LFBS1R2LF2PP2bs3LFB2FB2HB5Ha_st5Hl_stFFS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2sp2PP3PKA2bs3LFB2FB3sp13SPR2F03F8'FFS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP13ALOS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23sp13SP13ALOS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HBS2LF2bs3LFB2FBFFS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK23sp13SP1S1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK23sp13SP1S2LF2bs3LFB3sp1S2LF2bs3LFB3sp1FS2LF2bs3LFB2FBS2LF2sp2bs3LFB3sp13SP1S2LF2sp2bs3LFB3sp13SP1S1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBFFFS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP12HB5Ha_st5Hl_stS1R2LF2sp2lo2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2lo2bs3LFB3sp1S2LF2lo2bs3LFB3sp1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB3sp1FS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP12HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stFFS2LF2bs3LFB2FBS1R2LF2sp2lo2bs3LFB2FB3sp13SP12HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstFS1R2LF3END3BUF3LFB1l2EB3B474BL302FB4BUFC2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HBS2LF2PP2bs3LFBS1R2LF2bs3LFB2FB3ALO2HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23ALOS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF3PKA2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HBS2LF2bs3LFB2FBS2LF2bs3LFB3sp1S1R2LF2sp2lo2bs3LFB2FB3sp13SP12HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stFS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stFFS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stFFS2LF2bs3LFB3sp1S2LF2sp2PP3PKA2bs3LFB3PPB3PKB4PPAL2FB3sp13SPR4SP1R2F0FS1R2LF2sp2PP3PKA2bs3LFB3PPB3PKB2FB3sp13SPR4SP1R2F03F8'2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HBS2LF2bs3LFB2FBFS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB2FB2F0S2LF2bs3LFB2FB2F0S2LF2bs3LFB2FB2F0FFS2LF2bs3LFB3sp1". (* [comment removed for export] *)
  Lemma tail_114 : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_D ()) "PFB,$0.Psp1,$0.Ph1,(24.$4.VR,VHIA,)Pmm,P,(1.&40.)(2.(1.&8.))Pkv,(1.&40.)Pp2,$0.Pe1,$0.Pxra,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)P,(11.(10.(25.(1:.&40.Vsp,)+;0.)R16.)(10.R16.(25.(1:.&40.Vsp,)+:0.)))P,(>.$0.(?.R17.+20.)=)P,(>.P,$0.Sp(1=.$4.VR,VHIA,R17.)(1=.$4.VR,VHIA,Vh,))P,(>.$0.(26.$4.VR,VHIA,R18.)(26.$4.VR,VHIA,Vh,))P,(>.$0.(27.$4.VR,VHIA,R19.)(27.$4.VR,VHIA,Vh,))P,(>.$0.(?.R1<.+40.)=)P,(28.VR,VLB,VLF,R1=.+100.)P,(29.R1>.R1=.R1<.(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?3.))(=.$:.)))))))))))))))))))))))))))))))))R1:.R19.R18.R1;.)(2=.$4.(8.VR,)(1=.$4.VR,VHIA,R1=.)Lms,$2>.(21.(14.(1.&40.)La0v,(1.&40.)(2?.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R1?.R1?.VLB,VLB,Vm,(9.(16.$0.$0.)(17.$0.$0.VPP,(5.VPP,+8.))(9.(16.$0.$0.)(17.$0.$0.VPKA,(5.VPKA,+10.))(=.(16.$0.$0.))))R21.R20.R1.(30.VPP,VEND,VPKA,VP,R1.)R2.))(3:.R20.R1?.R1>.R1.))(31.(32.R18.(<.&40.R1>.)Vgp,Vtp,R17.R16.R15.Vsp,(<.&40.R1>.)R14.R13.R12.R11.R10.R?.R>.R=.(<.&40.R1?.)(<.&40.R1?.)(<.&40.VPP,)(<.&40.R19.)(<.&40.(5.R1?.+80.))(<.&40.(5.R1?.+:0.))(<.&40.(7.(8.VR,)))(<.&40.(5.R1?.+>0.))(<.&40.(5.R1?.+40.))(<.&40.(5.(6.R1?.+3.)(7.(8.VR,))))R<.R;.R:.R9.)VF,(<.&40.+:?410.)Vfc,(33.(1.&40.))R1<.(34.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M Ehcs Ehtop Estk F64 FRSH D. open_dinv D.
    rt_facts. rewrite <- Ehcs in CSOK, SCS0.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h1) h1 LB LF mm FB 256 lo HH1 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; exact BIN).
    destruct (hm_apart asegs R HIA h1 LB _ mm HH1) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC.
    assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8).
    { eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCPP : wcover R LB LF (bv_unsigned sp) X00 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    (* [comment removed for export] *)
    do 8 zstep.
    lazymatch goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH2 end.
    frame_aobj FSH2 (FB + 128) 1%nat as OLEN.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB2 end end.
    pose proof GETBSN as GB'. unfold asn1_get_bitstring_null_stmtA, A_ASN1_GET_BITSTRING_NULL in GB'.
    callxA_sp sp1 (eapply GB' with (CS := hcs asegs R HIA h1) (PP := PP) (LENP := FB + 128) (P := p2) (END := e1) (BUF := BUF) (bs := bs) (lo := lo); clear GB';
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 STK0 STK2 F0 F1' F8' F64 ALO LOS ACP ACV PP0 BUF0 PPAL APP APB DPB BUFC PPLO BP PE EB Hp2a Hp2e HeE;
                                    first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "BSN-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "BSN-LEFT:" g end.
    clear OLEN AB2.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (FB + 128) [C8 ?lw] |- _ => rename H into HL5; rename lw into L5 end.
    match goal with H : rw_cells _ m5 PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP5; rename qq into p5 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r5 end.
    match goal with H : r5 = 0 -> _ |- _ => rename H into HOK5 end.
    match goal with H : _ < r5 <= 0 |- _ => rename H into RR5 end.
    match goal with H : p2 <= p5 <= e1 |- _ => rename H into Hp5 end.
    pose proof (bv_unsigned_in_range 64 L5) as LR5. unfold bv_modulus in LR5. cbn [Z.pow Z.of_N Pos.pow] in LR5.
    (* [comment removed for export] *)
    zstep. if_cases KT5; zify_cond KT5.
    2:{ (* [comment removed for export] *)
      do 4 zstep.
      fin_epiq.
      all: first [ (exists (r5 + -15104), p5; split; [f_equal; change 18446744073709536512 with (2^64 + -15104); change 18446744073709551616 with (2^64); apply swrap32_mod64_addB; clear - RR5; lia|];
                    split; [clear - RR5 KT5; lia|]; split; [eassumption|]; split; [clear - Hp5 Hp2a Hp2e HeE; lia| eassumption])
                 | match goal with |- ?g => idtac "ERR5-LEFT:" g end ]. }
    assert (R50 : r5 = 0) by (clear - KT5 RR5; Z.div_mod_to_equations; lia). subst r5. destruct (HOK5 eq_refl) as [Hp5a HL5b]. clear HOK5 KT5.
    (* [comment removed for export] *)
    do 7 zstep.
    zstep. if_cases KEQ; zify_cond KEQ.
    2:{ (* [comment removed for export] *)
      zstep. zstep.
      fin_epiq.
      all: first [ (exists (-15206), p5; split; [reflexivity|]; split; [clear; lia|]; split; [eassumption|]; split; [clear - Hp5 Hp2a Hp2e HeE; lia| eassumption])
                 | match goal with |- ?g => idtac "ERR6-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ =>
      pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB3; pose proof (RTCL mx (hm_rtc asegs R HIA h1 _ _ mx HHc)) as RT3;
      pose proof (hm_img_shadow asegs R HIA h1 _ _ mx HHc) as ISH3 end end.
    pose proof (hcs_img_cs R HIA h1 IMG (proj2 (proj2 (proj2 IMG')))) as ICS.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      assert (OTBL : aobj asegs AL (hcs asegs R HIA h1) mx A_PK_INFO_TBL 32) by (eapply aobj_img; [exact ICS| exact ISH3| vm_compute; reflexivity]) end.
    pose proof (A_pk_info_from_type_spec AL IMG L) as PI'. unfold pk_info_from_type_stmtA, A_PK_INFO_FROM_TYPE in PI'.
    callxA_sp sp1 (eapply PI' with (CS := hcs asegs R HIA h1) (lo := lo); clear PI';
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 STK0 STK2 ALO LOS ACP ACV; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "INFO-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "INFO-LEFT:" g end.
    clear AB3 RT3 ISH3 OTBL.
    match goal with H : ?x = Z_to_bv 64 (pk_info_of _ _) |- _ => subst x end.
    fold (TVAL kv). remember (pk_info_of A_PK_INFOS (TVAL kv)) as info eqn:EINFO.
    assert (INFOB : info = 0 \/ In info A_PK_INFOS).
    { rewrite EINFO. unfold pk_info_of. destruct ((1 <=? TVAL kv) && (TVAL kv <=? 4)) eqn:EB4; [| left; reflexivity]. right.
      apply andb_true_iff in EB4. destruct EB4 as [E1 E4]. apply Z.leb_le in E1, E4.
      assert (CASES : TVAL kv = 1 \/ TVAL kv = 2 \/ TVAL kv = 3 \/ TVAL kv = 4) by (clear - E1 E4; revert E1 E4; generalize (TVAL kv); intros tv E1 E4; lia).
      destruct CASES as [E | [E | [E | E]]]; rewrite E; clear; cbn; tauto. }
    assert (INFOR : 0 <= info < 2^47).
    { destruct INFOB as [E0|HIN]; [rewrite E0; clear; lia|]. unfold A_PK_INFOS, A_RSA_INFO, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in HIN. cbn [In] in HIN. clear - HIN. lia. }
    (* [comment removed for export] *)
    zstep. if_cases KI; zify_cond KI.
    { (* [comment removed for export] *)
      zstep. zstep.
      fin_epiq.
      all: first [ (exists (-15488), p5; split; [reflexivity|]; split; [clear; lia|]; split; [eassumption|]; split; [clear - Hp5 Hp2a Hp2e HeE; lia| eassumption])
                 | match goal with |- ?g => idtac "ERR7-LEFT:" g end ]. }
    assert (INFO1 : In info A_PK_INFOS).
    { destruct INFOB as [E0|HIN]; [| exact HIN]. exfalso. rewrite E0 in KI. apply KI. reflexivity. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    apply evtA_done. right. unfold CALLQ_SETUP.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    do 13 eexists. exists kv, p5, e1, info.
    split; [reflexivity|]. split; [| split; [exact EINFO| exact INFO1]].
    unfold DINV. exists w0, w1, w2, pc0, pc1, L5, kpad, gv, gpad, pp, o0, o1, o2, o3, ptag, ppad, plen.
    repeat match goal with |- _ /\ _ => split end; first [ eassumption | idtac ].
    all: first [ (clear - Hp5 Hp2a Hp2e HeE; lia) | exact PPC | match goal with |- ?g => idtac "CQS-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "04@0@D10999193743.232D11014155534.216D12953353770.232D2236076691.231 D23021424555.216D44547585450.231D53006013040.216D57793146470.231D60109446735.216D60111543915.232D62151899352.216D62153996540.232D65048721748.232K12226132804.231K15433647418.216K29404953758.232K29577792773.232K32693134678.232K44164039966.231K51165101598.232K53758235425.216K55379086450.216K64113782398.231K9481672122.216 L1183019069.1   L12221849778.2  L12252132089.3  L13176305223.2  L14587613465.201L15421361836.3  L15822417165.1  L16626113666.3  L1685717371.0   L17252256177.2  L17454813295.1  L1747688473.24  L17611422932.42 L18359956405.6  L18892074935.1  L19131885611.1  L19684562151.1  L19979719403.42 L20491039612.198L20765759503.9  L21218866939.2  L21850448153.200L21850448153.217L21866712442.1  L22941438733.1  L23268210308.0  L24624535421.2  L24812681065.1  L26004870583.1  L27111942217.1  L27918872244.1  L27980923489.42 L28118495281.3  L28142564996.0  L28764923229.2  L29022582655.2  L29398824748.2  L29563340471.1  L30204481143.3  L30439224333.1  L30812569823.217L31168136491.1  L32039021495.1  L32378339725.42 L32508069537.0  L32687009508.2  L33314337069.42 L33985112333.1  L3482558654.42  L35176542020.42 L35530538413.3  L35595443383.1  L35653441506.11 L36189949245.1  L36314615039.2  L36463206329.4  L37353704346.202L37353704346.203L38200870584.42 L38235734261.1  L38331926573.42 L38334051855.2  L38551529394.0  L38948636245.0  L39188636933.0  L39332637397.0  L39631162845.3  L40870879649.0  L41409160545.3  L41898327682.3  L42710287031.1  L43188064477.2  L43300649301.0  L44168158952.3  L45455753602.3  L46938319508.42 L48602918719.7  L48603478104.42 L48849403412.42 L49695716705.42 L49833807665.2  L49902409492.42 L50370441005.42 L50372415759.2  L50444155144.3  L50496877661.2  L51158513068.3  L512883055.1    L51324313671.3  L52481905894.199L52941874306.3  L53009848806.1  L53770459319.1  L53838369457.2  L53940973981.216L54093066381.42 L54179040227.42 L55085943702.3  L55366666212.2  L5545697849.24  L55678034045.2  L56710798579.2  L58033257459.2  L58683913816.7  L589550697.1    L59272923917.1  L59308586248.2  L59472975334.12 L59915659704.42 L60056205954.3  L60098763854.3  L60881125047.1  L61147313713.2  L62253462701.3  L62342647223.1  L62918893459.6  L64118060424.2  L64240171697.2  L64704739633.3  L64850595401.0  L65058976486.1  L66151427842.16 L66939658253.207L66939906327.187L67170930818.3  L67993871543.1  L6850978225.2   L738030519.1    L7738195705.2   L7850760631.1   L8754660499.6   L881835912.0    L8846472116.1   L9080220944.4   L9356559676.13  L9465790413.42  L9494027820.2   L9915755099.2   P12255780986.232P12257878110.216P16610922021.215P16613019137.231P17256962866.232P18366707764.231P21212095580.215P21214192760.231P24617698778.214P28105433778.230P29008688568.231P29577792773.232P35519475466.215P36312780344.231P36465839390.216P36467936570.232P41419110342.215P41421207522.231P41903025153.231P41905122341.215P45461476133.216P48588551390.216P48590648570.232P49838513586.232P50438368175.216P50440465291.231P50440465291.232P51334230752.216P51336327876.232P52938159617.231P52940256805.215P53758235425.216P53853585430.216P55088519473.216P55090616597.232P55673336574.230P56721643329.232P58045542501.216P60050384933.215P60052482049.231P61140444310.216P62248756782.231P62923850838.232P64253323314.230P64698919830.214P67167306241.232P6856733462.214 P7750690063.231 P8745017202.216 Q15470341819.227Q15485021500.210Q15766564435.216Q15768661623.232Q19138405273.232Q19198323899.211Q19546636663.207Q19546884205.187Q27942454161.207Q31122772220.232Q31124869336.216Q31155392189.216Q31155766061.210Q31170445482.227Q32679510481.232Q32681607669.216Q32681824661.231Q34361068720.232Q34363165844.216Q34669143463.187Q34669522109.207Q34964382778.216Q34966479902.232Q35287842828.207Q35968101015.216Q36477868772.230Q36480143588.231Q38699473595.232Q45759487830.228Q4617814671.216 Q47158438559.216Q47989289395.232Q48117823211.231Q48118064779.216Q48120161967.232Q48358016498.232Q48360113622.216Q48606609525.207Q49698585326.229Q51739939498.211Q52744951088.230Q52747231024.231Q57753095321.213Q57753095326.212Q60214543256.216Q61315065771.232Q62076673598.231Q62378715631.232Q62380812747.216Q67592380552.213Q67592380559.212Q67634921660.232Q7759702014.207 Q7759752932.187 Q9122634134.231 Q9356887303.194 Q9356888455.210 Q9644499346.187 Q9644583048.207 Q9644583048.216 Q9646680236.232 00000100Q01101c01d01e02E03703`04I05Y06i07I08108K08e08f09?09h0:B0:C0:\0;E0;_0;c0;d0;e0;m0<P0<Q0<U0<V0<W0<X0<\0=D0>E0>F0>J0>N0>R0?T0@40@G0@H0@k0AN0AR0AV0AW0AX0A\0A`0Ad0Ah0B30B40B50B=0B>0B?0B@0BL0BP0C30C70C;0CN0CO0CP0C^0Cb0D_0Eg0Eh0El0FD0FH0FI0FJ0Fm0GP0I>0IB0IP0IW0IX0IY0IZ0I[0If0Ig0Ih0Ii0Im0J50J60J70J80K00K10LW0MX0Mc0Md0Ne0O30O:0O;0OC0OD0OH0OI0OJ0OK0OO0OP0OQ0OR0Oe0QK0QL0QM0R50R60R70R80RR0RV0RZ0R`0SM0U;0U<0UF0UJ0UK0UL0UP0UQ0UR0US0UT0UU0UY0V30VS0W30W40W80W90W=0W>0WB0WC0WD0WH0WW0XJ0X]0X^0Xh0YF0Yd0ZB0Z`0[Y0]00]10]20]k0^k0`30`40`R0aZ0bT0cN0cl0dJ0dh0eF0ed0g70hJ0iC0ia0j?0j]0k<0k[0l90lW0lX0mQ0mn0nK0oD10510f11D11b12[13914A15:16:16X17Q18Q19Y19k1:=1:Y1;51;G1;Y1<D1<o1=`1=a1=b1>41>F1>X1>Y1>Z1>[1>\1>]1>o1?A1@21@c1A@1AA1Ab1BC1BU1Bm1Bn1C@1CA1DD1E51Ef1FC1F`1Fa1G<1GN1Go1HP1Hb1I41IF1IG1IH1Ib1J<1JN1J`1K21KD1KV1KW1Ko1LG1L\1M11MF1M[FS2LF2sp2PP3PKA2bs3LFB2FB3sp13obsS2LF2sp2PP3PKA2bs3LFB2FB3sp13obsS2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r72HB5Ha_st5Hl_stFFS2LF2sp2PP3PKA2bs3LFB2FB3sp13obsS2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r72HB5Ha_st5Hl_stS1R2LF2sp2PP3PKA2lo2bs3LOS3LFB2FB3sp13obsS1R2LF2sp2PP3PKA2lo2bs3LOS3LFB2FB3sp13obsS1R3HIA1h2LF2sp2PP3PKA2lo2bs3TOP3LFB3PPB3PKB2FB3sp12h13SP15Ehtop3SPR4SP1R2F03obsS1R3HIA1h2LF2sp2PP3PKA2lo2bs3TOP3LFB3PPB3PKB2FB3sp12h13SP15Ehtop3SPR4SP1R2F03obsS2LF2sp2PP3PKA2bs3LFB2FB3sp13obsS2LF2PP2bs3LFB2FB3APP3obs2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB2FB3APB3obsS2LF3PKA2bs3LFB2FB3APK3obsFS2LF2PP2bs3LFB2FB3APP3obsS2LF3BUF2bs3LFB2FB3APB3obs2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB2FB3APB3obsFS2LF2PP2bs3LFB2FB3APP3obsS2LF3PKA2bs3LFB2FB3APK3obs2HB5Ha_st5Hl_stS2LF3PKA2bs3LFB2FB3APK3obsS2FBFFS2lo3sp1S2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r6FS2FBFSFS2FBS1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9S1R2sp2lo4STKk2bs3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F03F8'FS2FBS2FBS2FBS1R3HIA1h2sp2lo4STKk2bs3LOS3SLO3TOP3NB14STK22FB3sp13SP13ALO3ACV2F0S2LF2sp2PP3PKA2bs3LFB2FB3sp13obsS1P2p12p24Hp1a4Hp12FS2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r6S2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r7S2FBS2FBSFS2FBS2FBS2PPS2FBS2bs2FB3sp1FSS2lo3sp1FFFS3BUF2ap3AP1S2FBS2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r7S2FBS2FBS2lo2bs2FB3sp14FBLOSFS2bs2FB3sp12F0S2FBS1R2sp2lo4STKk2bs3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F0S1R2sp2lo4STKk3BUF2bs3LOS3SLO4BUF03NB14STK22FB3sp12ap3SP13AP13ALO3ACV2F0FS2FBS1R3HIA1h2sp2lo3TOP4HTOPS2FBFFS2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r6S2LF2sp2PP3PKA2bs3LFB2FB3sp13obs2r6S1R2sp3END2lo4STKk3BUF2bs3LOS3SLO2EB3NB14STK22FB3sp12Lw2p12p22ap4alen3SP14SP1M4Hp2e3HeE3AP13AP23ALO3ACV2F03APBS2loS2bs2FB3sp12F0S2FB2F0SSSSS2sp2lo3sp1SFFS2FBS2lo3sp1SFFS1R2sp2lo4STKk2bs3LOS3SLO3NB14STK22FB3sp13SP13ALO3ACV2F0FS1R2sp3END2lo4STKk3BUF2bs3LOS3SLO2EB3NB14STK22FB3sp12Lw2p12p22ap4alen3SP14Hp2e3HeE3AP23ALO3ACV2F04BUFCS1R2sp2lo4STKk2bs3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F03F8'S2bs2FB3sp1FS1R2sp2lo4STKk2bs3LOS3SLO3NB14STK22FB3sp13SP14SP1M3ALO3ACV2F03F8'S2bs2FB3sp12F0S2FB2F0FS2lo3sp1FS2FBFFFS2FBFFFS2lo2bs2FB3sp14FBLOS1R2sp3END2lo4STKk3BUF2bs3LOS3SLO2EB3NB14STK22FB3sp12Lw2p12p22ap4alen3SP14Hp2e3HeE3AP23ALO3ACV2F04BUFCFFS1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9FFFS2Lw2p12p22pp4plen4Hp2e2K2S2FBS2FBS1i2HiS3END3BUF2bs2EB2Lw2p12p22ap4alen4Hp2e3HeE3AP2S1R2sp3END2lo4STKk3BUF2bs3LOS3SLO2EB3NB14STK22FB3sp12Lw2p12p22ap4alen3SP14SP1M4Hp2e3HeE3AP13AP23ALO3ACV2F03APBFS1R2lo3LOSS2FBFFS2FBFFFFSS2FBS2FB2r03F641q1r1H2H02q02H4S2LF2sp2PP3PKA2bs3LFB2FB3sp13obsS2LF2sp2PP3PKA2bs3LFB2FB3sp13obsFS2FBFS2FBFS2FBFSS2FBS2sp2lo3sp13SP1S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS2lo2bs2FB3sp14FBLOFS4alen3ALRS2LF2PP2lo2bs3LFB4PPLO3sp13obsS2LF2PP2lo2bs3LFB4PPLO3sp13obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS2LF3END3BUF2bs3LFB2EB2FB2Lw2p12p22ap4alen4Hp2e3HeE3AP13AP23APB3obs4OLEN2HB5Ha_st5Hl_stFFS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3sp13SP13ALO3F1'3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obs2HB5Ha_st5Hl_stFS2LF2lo2bs3LFB2FB3sp14FBLO3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obs2HB5Ha_st5Hl_stS1R2LF2PP3PKA2lo3BUF2bs3LOS3LFB4PPLO4PKLO3sp13ALO4BUFC3obsS1R2LF2PP3PKA2lo3BUF2bs3LOS3LFB4PPLO4PKLO3sp13ALO4BUFC3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS1R2LF3END2lo3BUF2bs3LOS3LFB2EB3sp12Lw2p12p22ap4alen4Hp2e3HeE3AP23ALO4BUFC3obs4OLENS1R2LF3END2lo3BUF2bs3LOS3LFB2EB3sp12Lw2p12p22ap4alen4Hp2e3HeE3AP23ALO4BUFC3obs4OLENS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF3PKA2lo2bs3LFB4PKLO3sp13obsS2LF3PKA2lo2bs3LFB4PKLO3sp13obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsFS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS2LF2sp2lo2bs3LFB3sp13SP13obsS2LF2sp2lo2bs3LFB3sp13SP13obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB4FBLO3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB4FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS2LF3END3BUF2bs3LFB2EB2FB2Lw2p12p22ap4alen4Hp2e3HeE3AP13AP23APB3obs4OLENS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3sp13SP13ALO3F1'3obsS2LF2lo2bs3LFB2FB3sp14FBLO3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB3sp13SP14FBLO3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK22FB4FBLO3obs2HB5Ha_st5Hl_stS2LF3END3BUF2bs3LFB2EB2FB2Lw2p12p22ap4alen4Hp2e3HeE3AP13AP23APB3obs4OLENS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS1R2LF2lo2bs3LOS3LFB3ALO3obsS1R2LF2lo2bs3LOS3LFB3ALO3obsS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS2LF2sp2PP3PKA2bs3LFB2FB3sp13SPR2F03F8'3obsS2LF2sp2PP3PKA2bs3LFB2FB3sp13SPR2F03F8'3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK23sp13SP13obsFFS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsFFFFFS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK23sp13SP13obsS1R2LF2sp2lo4STKk2bs3SLO3LFB3NB14STK23sp13SP13obsS2LF2sp2lo2bs3LFB3sp13SP13obsFS2LF2bs3LFB2FB3obs2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3obs2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB2F03obs2HBFS2LF2bs3LFB2FB3obsFS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK22FB3ALO3obs2HB5Ha_st5Hl_stS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23ALO3obsS1R2LF2sp2lo4STKk2bs3LOS3SLO3LFB3NB14STK23ALO3obsS2LF2sp2lo2bs3LFB3sp13SP13obsS2LF2sp2lo2bs3LFB3sp13SP13obsFS2LF2bs3LFB2FB3obs2HB5Ha_stS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obs2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3obs2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsFFS2LF2PP2lo2bs3LFB4PPLO3obsS2LF2PP2lo2bs3LFB4PPLO3obsS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsS2LF2bs3LFB2FB3obsFS2LF2bs3LFB3sp14SP1R3obsS2LF2bs3LFB3sp14SP1R3obsS2LF2bs3LFB2FB2F03obsS2LF2bs3LFB2FB2F03obsS2LF2bs3LFB2FB2F03obsS2LF2bs3LFB2FB2F03obs". (* [comment removed for export] *)
  Lemma seg_A2 : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_D ()) "PFB,$0.Psp1,$0.Ph1,(24.$4.VR,VHIA,)Pmm,P,(1.&40.)(2.(1.&8.))Pxra,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pw0,(1.&40.)Pw1,(1.&40.)Pw2,(1.&40.)Ppc0,(1.&40.)Ppc1,(1.&40.)PLw,(1.&40.)Pkpad,(1.&40.)Pgpad,(1.&40.)Pp1,$0.Pp2,$0.Pap,$0.Ppp,$0.Patag,(1.&40.)Papad,(1.&40.)Palen,(1.&40.)Pptag,(1.&40.)Pppad,(1.&40.)Pplen,(1.&40.)P,(11.(10.(25.(1:.&40.Vsp,)+;0.)R25.)(10.R25.(25.(1:.&40.Vsp,)+:0.)))P,(>.$0.(?.R26.+20.)=)P,(>.P,$0.Sp(1=.$4.VR,VHIA,R26.)(1=.$4.VR,VHIA,Vh,))P,(>.$0.(26.$4.VR,VHIA,R27.)(26.$4.VR,VHIA,Vh,))P,(>.$0.(27.$4.VR,VHIA,R28.)(27.$4.VR,VHIA,Vh,))P,(>.$0.(?.R2;.+40.)=)P,(28.VR,VLB,VLF,R2<.+100.)P,(15.$4.VR,VHIA,R2;.VLB,(9.(16.$0.$0.)(17.$0.$0.R2=.+100.)VLF,)R2:.)P,(3.$4.R2;.R2>.(9.$:.(18.R1:.)(9.$:.(18.R19.)(9.$:.(18.R18.)(=.$:.)))))P,(3.$4.R2<.(5.R2?.+20.)(9.$:.(18.R18.)(9.$:.(18.R17.)(=.$:.))))P,(3.$4.R2=.(5.R30.+40.)(9.$:.(19.R10.)(9.$:.(19.R?.)(9.$:.(18.R>.)(9.$:.(18.(<.&40.R12.))(=.$:.))))))P,(3.$4.R2>.(5.R31.+80.)(9.$:.(18.R18.)(=.$:.)))P,(3.$4.R2?.(5.R32.+:0.)(9.$:.(19.R?.)(9.$:.(19.R>.)(9.$:.(18.R=.)(9.$:.(18.(<.&40.R13.))(=.$:.))))))P,(3.$4.R30.(5.R33.+>0.)(9.$:.(19.(<.&40.=))(9.$:.(19.R19.)(=.$:.))))P,(3.$4.R31.(5.R34.+?0.)(9.$:.(19.(<.&40.=))(9.$:.(19.R19.)(=.$:.))))P,(3.$4.R32.(5.(6.R35.+3.)(7.(8.VR,)))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?1.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?8.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.=))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?2.))(9.$:.(;.(<.&8.+4.))(9.$:.(;.(<.&8.+?3.))(=.$:.))))))))))))))))))))))))))))))))))P,(3.$4.R33.(5.(1:.&40.Vsp,)-68.)(9.$:.(18.Vs11,)(9.$:.(18.Vs10,)(9.$:.(18.Vs9,)(9.$:.(18.Vs8,)(9.$:.(18.Vs7,)(9.$:.(18.Vs6,)(9.$:.(18.Vs5,)(9.$:.(18.Vs4,)(9.$:.(18.Vs3,)(9.$:.(18.Vs2,)(9.$:.(18.Vs1,)(9.$:.(18.Vs0,)(9.$:.(18.Vra,)(=.$:.)))))))))))))))P,(3.$4.R34.(5.R36.+8.)(9.$:.(18.(<.&40.VPKA,))(9.$:.(18.(<.&40.(5.R37.+?0.)))(9.$:.(18.(<.&40.(5.(6.VPP,+3.)(7.(8.VR,)))))(=.$:.)))))P,(3.$4.R35.(5.R37.+30.)(9.$:.(18.(<.&40.R38.))(=.$:.)))P,(1;.$4.R36.R38.(5.R38.+8.))P,(1;.$4.R37.(5.R39.+20.)(5.R39.+30.))P,(1;.$4.R38.(5.R3:.+38.)(5.(1:.&40.Vsp,)-68.))P,(1;.$4.R39.Vlo,R3;.)P,(1<.$4.R3:.)P,(3.$4.R3;.VPP,(9.$:.(18.(<.&40.R21.))(=.$:.)))P,(13.$4.(8.VR,)(1=.$4.VR,VHIA,R3=.)R3<.VPP,+8.)P,(3.$4.R3=.VPKA,(9.$:.(18.(<.&40.=))(9.$:.(18.(<.&40.=))(=.$:.))))P,(13.$4.(8.VR,)(1=.$4.VR,VHIA,R3?.)R3>.VPKA,+10.)P,(1>.$4.R3?.VBUF,Vbs,)P,(13.$4.(8.VR,)(1=.$4.VR,VHIA,R41.)R40.VBUF,(1?.(20.(1.&8.)Vbs,)))P,(10.(5.VP,+2.)R28.)P,(10.R29.R28.)P,(10.R29.(5.R2:.(1:.&40.R2=.)))P,(10.(5.R2;.(1:.&40.R2>.))VEND,)P,(10.VBUF,R2:.)P,(10.(5.R2;.(1:.&40.R27.))R2<.)P,(21.(11.(>.$0.R2;.=)(11.(>.$0.(1:.&40.R25.)=)(>.(1.&40.)R27.(<.&40.=))))(11.(10.VBUF,R2;.)(11.(10.VP,R2;.)(>.$0.(5.R2;.(1:.&40.R25.))R2=.))))P,(22.$4.VR,VHIA,R49.VLB,VLF,(1:.&40.Vsp,)(23.VR,)(9.(16.$0.$0.)(17.$0.$0.VPP,(5.VPP,+8.))(9.(16.$0.$0.)(17.$0.$0.VPKA,(5.VPKA,+10.))(=.(16.$0.$0.))))Vm,R48.)(2=.$4.(8.VR,)(1=.$4.VR,VHIA,R4:.)Lms,$2>.(21.(14.(1.&40.)La0v,(1.&40.)(2?.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R4<.R4<.VLB,VLB,Vm,(9.(16.$0.$0.)(17.$0.$0.VPP,(5.VPP,+8.))(9.(16.$0.$0.)(17.$0.$0.VPKA,(5.VPKA,+10.))(=.(16.$0.$0.))))R4>.R4=.R1.(30.VPP,VEND,VPKA,VP,R1.)R2.))(3:.R4=.R4<.R4;.R1.))(31.(32.R48.(<.&40.R4;.)Vgp,Vtp,R47.R46.R45.Vsp,(<.&40.R4;.)R44.R43.R42.R41.R40.R3?.R3>.R3=.(<.&40.R4<.)(<.&40.R4<.)(<.&40.VPP,)(<.&40.(5.R30.(1:.&40.R33.)))(<.&40.(5.R4<.+80.))(<.&40.(5.R4<.+:0.))(<.&40.(7.(8.VR,)))(<.&40.(5.R4<.+>0.))(<.&40.(5.R4<.+40.))(<.&40.(5.(6.R4<.+3.)(7.(8.VR,))))R3<.R3;.R3:.R39.)VF,(<.&40.+:?394.)Vfc,(33.(1.&40.))R49.(34.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until plen. intros SP1 SP1M Ehcs Ehtop Estk F64 FRSH HH1 FHD LPKC LOID LLEN LPAR LALG LGID FSHX SAVE SLOTS SLOT48 STlo STmid SThi STbelow MI1
           HPP OPP HPKA OPKA HBS OBUF Hp1a Hp12 Hp2e HeE AP1 AP2 PPC PRES.
    rt_facts. rewrite <- Ehcs in CSOK, SCS0.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    assert (SCS : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STK0 NS1 TOP HTOP; lia]).
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h1) h1 LB LF mm FB 256 lo HH1 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (APB : FB + 256 <= BUF \/ BUF + BLEN <= FB) by (apply F3'; apply in_app_iff; left; exact BIN).
    destruct (hm_apart asegs R HIA h1 LB _ mm HH1) as [HBR1 _]. rewrite Forall_forall in HBR1.
    destruct (HBR1 _ ltac:(apply in_app_iff; left; exact BIN)) as (_ & _ & BUFC & _). cbn [fst snd] in BUFC.
    assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) PP 8).
    { eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCPP : wcover R LB LF (bv_unsigned sp) X00 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    pose proof (bv_unsigned_in_range 64 alen) as ALR. unfold bv_modulus in ALR. cbn [Z.pow Z.of_N Pos.pow] in ALR.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    destruct (sub_input asegs mm BUF bs ap (bv_unsigned alen) HBS AP1 ltac:(clear - ALR; lia) ltac:(clear - AP2 Hp2e HeE EB; lia)) as [HOB OLEN].
    set (obs := firstn (Z.to_nat (bv_unsigned alen)) (skipn (Z.to_nat (ap - BUF)) bs)) in HOB, OLEN.
    replace (C8 alen) with (C8 (Z_to_bv 64 (bv_unsigned alen))) in LOID by (rewrite Z_to_bv_bv_unsigned; reflexivity).
    change [C4 atag; C4 apad; C8 (Z_to_bv 64 (bv_unsigned alen)); C8 (Z_to_bv 64 ap)] with (buf_cells atag apad (bv_unsigned alen) ap) in LOID.
    lazymatch goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into FSH2 end.
    frame_aobj FSH2 (FB + 64) 3%nat as OOID. partial_aobj FSH2 28%nat (FB + 224) h1 as OALG0.
    chunk_split LALG 1%nat LALGa LALGb. chunk_split LGID 1%nat LGIDa LGIDb.
    assert (PPC' : (pp = 0 /\ bv_unsigned plen = 0 /\ ptag = Z_to_bv 64 0) \/ (BUF <= pp /\ P <= pp /\ pp + bv_unsigned plen <= p1 + bv_unsigned Lw))
      by (destruct PPC as [K|(K1 & K1' & K2)]; [left; exact K| right; split; [exact K1| split; [exact K1'| clear - K2 Hp2e; lia]]]).
    pose proof (hm_abase asegs R HIA h1 LB _ mm HH1) as AB1.
    pose proof OIDPK as OP'. unfold oid_lookup1_stmtA, A_OID_GET_PK_ALG in OP'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    callxA_sp sp1 (eapply OP' with (h := h1) (LB := LB) (LF := (FB, 256) :: LF) (OID := FB + 64) (EXT := FB + 224) (P := ap) (LEN := bv_unsigned alen) (lo := lo)
                                   (tg := atag) (pd := apad) (v0 := Z_to_bv 64 0) (xs := obs); clear OP';
                   rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehtop;
                   first [ exact LOS | exact LOID | exact HOB | exact OLEN | exact LALGa | exact OOID | exact OALG0 | reflexivity | eassumption
                         | lazymatch goal with
                           | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [exact IND| clear; lia| clear; lia]
                           | |- aobj _ _ _ _ ap _ => eapply aobj_sub; [exact OBUF| clear - AP1; lia| clear - AP2 Hp2e HeE EB; lia]
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 STK0 STK2 F0 F1' F8' F64 ALO LOS ACP ACV TOP FBLO APB BUFC BUF0 AP1 AP2 Hp2e HeE EB ALR;
                                    first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "OIDPK-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "OIDPK-LEFT:" g end.
    clear OOID OALG0 AB1.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : rw_cells _ m6 (FB + 224) [C4 ?v] |- _ => rename H into HKV; rename v into kv end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r6 end.
    match goal with H : r6 = 0 \/ r6 = _ |- _ => rename H into RR6 end.
    unfold buf_cells in LOID.
    (* [comment removed for export] *)
    Ltac to_tail kvx :=
      eapply evtA_eq; [| eapply (tail_114 _ _ _ _ kvx)]; [reflexivity|..];
      [eassumption|eassumption|eassumption|eassumption|eassumption|eassumption|eassumption|];
      unfold DINV; do 17 eexists; repeat match goal with |- _ /\ _ => split end; first [ eassumption | idtac ].
    Ltac to_err kvx rr :=
      eapply evtA_mono; [| intros msx Hx; left; exact Hx];
      eapply evtA_eq; [| eapply (err_c8 _ _ _ _ kvx _ _ rr)]; [reflexivity|..];
      [eassumption|eassumption|eassumption|eassumption|eassumption|eassumption|eassumption| |clear; lia];
      unfold DINV; do 17 eexists; repeat match goal with |- _ /\ _ => split end; first [ eassumption | idtac ].
    (* [comment removed for export] *)
    zstep. if_cases KFND; zify_cond KFND.
    - (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases KRSA; zify_cond KRSA.
      + to_tail kv. all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "T1-LEFT:" g end ].
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        zstep. if_cases KT5; zify_cond KT5.
        * (* [comment removed for export] *)
          zstep. zstep. if_cases KL; zify_cond KL.
          -- to_err kv (-14976). all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "E1-LEFT:" g end ].
          -- zstep. to_tail kv. all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "T2-LEFT:" g end ].
        * (* [comment removed for export] *)
          zstep. if_cases KT0; zify_cond KT0.
          -- to_err kv (-14976). all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "E2-LEFT:" g end ].
          -- zstep. zstep. if_cases KL; zify_cond KL.
             ++ to_err kv (-14976). all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "E3-LEFT:" g end ].
             ++ zstep. to_tail kv. all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "T3-LEFT:" g end ].
    - (* [comment removed for export] *)
      assert (R6 : r6 <> 0) by (intros E0; rewrite E0 in KFND; apply KFND; reflexivity).
      destruct RR6 as [E0|E6]; [exfalso; exact (R6 E0)|]. vm_compute in E6. subst r6. clear R6 KFND.
      zstep. zstep.
      try (if_cases KNF; zify_cond KNF; [exfalso; clear - KNF; first [apply KNF; reflexivity | lia]|]).
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into FSH3 end.
      frame_aobj FSH3 (FB + 64) 3%nat as OOID2. partial_aobj FSH3 30%nat (FB + 240) h1 as OGID.
      pose proof OIDGA as OG'. unfold oid_lookup1_stmtA, A_OID_GET_EC_GRP_ALGID in OG'.
      callxA_sp sp1 (eapply OG' with (h := h1) (LB := LB) (LF := (FB, 256) :: LF) (OID := FB + 64) (EXT := FB + 240) (P := ap) (LEN := bv_unsigned alen) (lo := lo)
                                     (tg := atag) (pd := apad) (v0 := Z_to_bv 64 0) (xs := obs); clear OG';
                     rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehtop;
                     first [ exact LOS | exact OOID2 | exact OGID | reflexivity | eassumption
                           | lazymatch goal with
                             | |- rw_cells _ _ (FB + 64) (buf_cells _ _ _ _) => unfold buf_cells; eassumption
                             | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [exact IND| clear; lia| clear; lia]
                             | |- aobj _ _ _ ?mx ap _ => lazymatch goal with OB : aobj _ _ _ mx BUF _ |- _ => eapply aobj_sub; [exact OB| clear - AP1; lia| clear - AP2 Hp2e HeE EB; lia] end
                             | |- _ => clear - SP1 SP1M SLO NS1 NB1 STK0 STK2 F0 F1' F8' F64 ALO LOS ACP ACV TOP FBLO APB BUFC BUF0 AP1 AP2 Hp2e HeE EB ALR;
                                      first [lia | Z.div_mod_to_equations; lia]
                             end
                           | match goal with |- ?g => idtac "OIDGA-PRE-LEFT:" g end ]).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "OIDGA-LEFT:" g end.
      clear OOID2 OGID.
      match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r7 end.
      match goal with H : r7 = 0 \/ r7 = _ |- _ => rename H into RR7 end.
      (* [comment removed for export] *)
      zstep. if_cases KGA; zify_cond KGA.
      + (* [comment removed for export] *)
        zstep. zstep.
        lazymatch goal with H : rw_cells _ _ (FB + 224) [C4 ?v] |- _ => to_tail v end.
        all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "T4-LEFT:" g end ].
      + (* [comment removed for export] *)
        zstep. zstep.
        to_err kv (-15488). all: first [ (clear - Hp1a Hp12 Hp2e HeE; lia) | exact PPC' | match goal with |- ?g => idtac "E4-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkPKD.
