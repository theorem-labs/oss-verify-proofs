(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Combined () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_of"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "ARUN_2.Combined.comb_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_2.Combined.combA_post"; "A_COMBINED"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "ARUN_2.Combined.comb_post"; "A_REFILL"; "A_LARGE_ALLOC"; "ARUN_2.Combined.combS_post"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

Definition A_COMBINED : Z := 0x4c008.      (* [comment removed for export] *)
Definition A_REFILL : Z := 0x4c758.        (* [comment removed for export] *)
Definition A_LARGE_ALLOC : Z := 0x4c2e0.   (* [comment removed for export] *)

(* [comment removed for export] *)
End ARUN_1.
Ltac show_vals :=
  match goal with |- evtA _ _ _ _ (MS ?R _ ?pc _ _ _ _) =>
    idtac "PC:" pc;
    let rec go t := lazymatch t with
      | TNode ?l (Some ?v) ?r => go l; (tryif is_var v then idtac else idtac "  REG:" v); go r
      | TNode ?l None ?r => go l; go r
      | TEmpty => idtac end in go R
  end.

(* [comment removed for export] *)
Ltac abbrev_by e v tac :=
  let HV := fresh "D" v in let HR := fresh "R" v in
  remember e as v eqn:HV in |- *;
  assert (HR : 0 <= v < 2^64) by (rewrite HV; tac).
Ltac abbrev e v := abbrev_by e v ltac:(change (inr64 e); zrange).
Ltac abb_lor v := lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => abbrev (Z.lor a b) v end.

Section ARUN_2. Context {hAR : arun}.
Section Combined.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0?L14946089560.79L15253791194.72L15254151642.71L15258154528.72L15258154528.73L22351964942.74L2537942390.76 L25875266104.68L26878554278.68L26882680664.69L27006251846.77L27468508909.79L28920986476.65L28921216760.79L29921300973.71L32457808536.75L34539781148.71L34540010524.72L34543774694.72L34543774694.73L34894458726.76L39659073912.79L40823377450.75L40823377515.53L40823606892.51L41417918856.69L41417918925.48L41418148300.50L44017203752.62L44017433129.60L44566935372.79L51266838984.79L52515836280.79L53516901336.79L5742541873.47 L5742901752.79 L5749041963.45 L59579268856.78L59579498232.79L63370226858.56L63370521771.54L64350097516.66L65499898154.57L65500127529.59L6751737895.45 L6753455968.66 L6753619773.47 L6758013062.69 L67644715620.78L8929201440.75 00000100900A00I00Q00Z00[00\00d00l01L01U01V01Z01j02202302402502602702;02<02=02>02?02@02A02B02C02D02K02O02S02Y02b02h02l03003103203303403503603703803903=03LFS2ev3RevS2ev3RevS2ev3RevS2ev3RevS2ev1H2H0SSS2en3RenS2en3RenS2ev2er3Der3Rer4Rer'2et3Det1H2H0S1x2Hx2etSS2etS2en3Ren1H2H02H1S2er3RerSSSSFS2etSSSSSSSSFS2et2lzS2etS2etS1x2HxS1x2Hx2etS1x2HxS2etS2etSSSSSSSSSS2etS2ev1H2H02H12H2". (* [comment removed for export] *)
  Lemma comb_cls_big : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Px,$3.P,(4.(5.+200.R1.)(6.R1.+10000.))P,(7.$8.R3.)(9.$8.VAL,VCS,Lms',$:.(;.(0.&40.)Lx5,(0.&40.)(;.(0.&40.)Lx6,(0.&40.)(;.(0.&40.)Lx12,(0.&40.)(;.(0.&40.)Lx14,(0.&40.)(;.(0.&40.)Lx15,(0.&40.)(;.(0.&40.)Lx16,(0.&40.)(;.(0.&40.)Lx17,(0.&40.)(<.$:.R8.(=.(>.R2<.R2;.R2:.R29.R7.R6.R26.(?.&40.(10.R;.))R24.R23.R22.R5.R20.R4.R3.R2.R1.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(?.&40.+4<19<.)R=.(11.(0.&40.))R<.(12.$8.))))))))))(=.(>.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(?.&40.R3.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(?.&40.+4<0<0.)R5.(11.(0.&40.))R4.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m x Hx MI. facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. abb_lor e1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. abb_lor e2.
    (* [comment removed for export] *)
    do 8 zstep. zstep. zstep. abb_lor e3.
    zstep. zstep. abb_lor e4.
    zstep. zstep. abb_lor e5.
    zstep. zstep. abb_lor e6.
    (* [comment removed for export] *)
    zstep.
    abbrev (Z.lxor e6 18446744073709551615) en.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    abbrev_by (en - Z.land (en ≫ 1) 6148914691236517205) ev
      ltac:(pose proof (Z_land_le_l (en ≫ 1) 6148914691236517205 ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia));
            pose proof (Z_shiftr_le en 1 ltac:(lia) ltac:(lia));
            pose proof (Z.land_nonneg (en ≫ 1) 6148914691236517205); lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    abbrev_by (Z.land ev 3689348814741910323 + Z.land (ev ≫ 2) 3689348814741910323) er
      ltac:(pose proof (Z_land_le_r ev 3689348814741910323 ltac:(lia) ltac:(lia));
            pose proof (Z_land_le_r (ev ≫ 2) 3689348814741910323 ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia));
            pose proof (Z.land_nonneg ev 3689348814741910323);
            pose proof (Z.land_nonneg (ev ≫ 2) 3689348814741910323); lia).
    assert (Rer' : er <= 2 * 3689348814741910323).
    { rewrite Der. pose proof (Z_land_le_r ev 3689348814741910323 ltac:(lia) ltac:(lia)).
      pose proof (Z_land_le_r (ev ≫ 2) 3689348814741910323 ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia)). lia. }
    (* [comment removed for export] *)
    zstep. zstep.
    abbrev_by (er + er ≫ 4) et ltac:(pose proof (Z_shiftr_le er 4 ltac:(lia) ltac:(lia)); pose proof (Z.shiftr_nonneg er 4); lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [Z_to_bv 64 (?v ≫ 56)] => abbrev (Z.shiftr v 56) lz end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. do 7 eexists.
    match goal with |- context [Z_to_bv 64 (?v + -2)] => replace (v + -2) with (class_of x); [reflexivity|] end.
    rewrite <- (classid_code_ok x) by lia. unfold classid_code.
    subst lz et er ev en e6 e5 e4 e3 e2 e1. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition comb_frame (m : mem) (SP : Z) (q4 q3 q2 q1 q0 qra : word) : Prop :=
    rw_cells asegs m (SP + -48) [C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra].

  (* [comment removed for export] *)
  Definition combA_post (SP : Z) (gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (x T lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Lms',$:.(;.(0.&40.)Lx5,(0.&40.)(;.(0.&40.)Lx6,(0.&40.)(;.(0.&40.)Lx12,(0.&40.)(;.(0.&40.)Lx14,(0.&40.)(;.(0.&40.)Lx15,(0.&40.)(;.(0.&40.)Lx16,(0.&40.)(;.(0.&40.)Lx17,(0.&40.)(;.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(4.(<.$:.R9.(=.(>.O7.(?.&40.(13.O1;.-30.))O1:.O19.R8.R7.O18.(?.&40.(10.O4.))(?.&40.(13.(13.O3.+=0.)(14.+50.(10.O4.))))(?.&40.$15.)(?.&40.(13.O3.+=0.))R6.(?.&40.+8.)R5.R4.R3.R2.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.)O6.(?.&40.+4<1;4.)O5.(11.(0.&40.))R1.(12.$8.)))(4.(16.(17.(18.$3.$3.)(19.$3.$3.O2.O1;.)(1:.(18.$3.$3.)))O1.R1.)(4.(1;.$8.O1.R1.)(4.(7.$8.R1.)(4.(1<.R1.O1;.O13.O14.O15.O16.O17.O7.)(1=.$8.R1.O2.(13.O1;.-30.)))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac combA_dead :=
    match goal with K : context [zlow 64 ((?x + 31) ≫ 5)], K2 : context [zlow 64 512 <? zlow 64 ?x], Ha : 1 <= ?x, Hb : ?x <= 65536 |- False =>
      rewrite (Z.shiftr_div_pow2 (x + 31) 5) in K by (clear; lia); change (2^5) with 32 in K; clear -K K2 Ha Hb; lx_klin; lia end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L27475295747.4 L29321836616.4 L40711950782.64L54494783937.4 L54592780436.71L5748959492.4  L5748959510.4  L67180998148.4 L67180998166.4 00000<00=00I00U00a00l01701801;S1x3Hxb4LXKTSS3hAR2SP1x1TS1x3Hxa4LXKFS3hAR2SP1x1TS1x3Hxa3HxbS1x3Hxa3HxbSS1x". (* [comment removed for export] *)
  Lemma comb_A : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Px,$3.PT,$3.Plo,$3.P,(4.(6.+1.R3.)(6.R3.+10000.))P,(6.=R3.)P,(6.(13.R4.+1000.)(1>.+2.+2?.))P,(1=.$8.R7.R4.R:.)P,(6.(1?.VhAR,)R5.)P,(6.R6.(20.R<.+30.))P,(6.R=.(1>.+2.+3?.))P,(<.$3.(21.R>.+10.)=)P,(22.VCS,R9.(20.R?.R9.))P,(7.$8.R=.)(9.$8.VAL,VCS,(23.R11.R2:.R29.R26.R25.R24.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R2;.R10.R?.R=.R<.R;.R>.)(=.(>.R2;.(?.&40.R11.)R2:.R29.R28.R27.R26.R25.R24.(?.&40.$15.)(?.&40.(13.R<.+=0.))(?.&40.R=.)(?.&40.+8.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R10.(?.&40.$24.)R?.(11.(0.&40.))R>.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m x T lo
      Hx T0 T1 ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_COMBINED, A_INSTANCE in *.
    pose proof (class_of_range x Hx) as [CRa CRb]. destruct Hx as [Hxa Hxb].
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x4c0c0; 0x4c1b4] [] 40%N).

    all: lazymatch goal with |- False => combA_dead | |- _ => idtac end.
    2: { (* [comment removed for export] *)
         replace ((x + 31) ≫ 5) with (class_of x) by (rewrite (Z.shiftr_div_pow2 (x + 31) 5), class_of_small by (clear -Hxa Hxb LXKF; try lx_klin; lia); reflexivity).
         apply evtA_done. unfold combA_post, comb_frame. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close. }
    (* [comment removed for export] *)
    eapply evtA_cut. { eapply comb_cls_big; [match goal with K : context [zlow 64 512 <? zlow 64 x] |- _ => clear -K Hxa Hxb; lx_klin; lia end | assumption]. }
    cbv beta. intros ms' (x5 & x6 & x12 & x14 & x15 & x16 & x17 & ->).
    lx_run (PLAN [0x4c1b4] [] 20%N). lx_same.
    apply evtA_done. unfold combA_post, comb_frame. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition comb_post (SP : Z) (gp tp t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 q4 qra mx : word)
      (F : bvmap 5 word) (fc : bv 32) (T SB c cnt csz lo : Z) (ws : list word) (pw : word) (W : list (Z * Z)) (m0 : mem)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Lms',$:.(;.(0.&40.)Lx5,(0.&40.)(;.(0.&40.)Lx6,(0.&40.)(;.(0.&40.)Lx11,(0.&40.)(;.(0.&40.)Lx12,(0.&40.)(;.(0.&40.)Lx14,(0.&40.)(;.(0.&40.)Lx15,(0.&40.)(;.(0.&40.)Lx16,(0.&40.)(;.(0.&40.)Lx17,(0.&40.)(;.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(;.(0.&40.)Lstw',(0.&40.)(4.(<.$:.R;.(=.(>.O>.(?.&40.O22.)O21.O20.R:.R9.O1?.O13.O12.(?.&40.(13.(13.O9.(14.O8.(1>.+2.+20.)))(14.+10.(21.(25.&40.O3.)(1>.+2.+20.)))))R8.R7.(?.&40.+8.)R6.R5.R4.R3.O11.O10.O?.O1>.O1=.O1<.O1;.O1:.O19.O18.O17.O16.O15.O14.)O<.(26.O>.)O;.(11.(0.&40.))R2.(12.$8.)))(4.(16.(17.(18.$3.$3.)(19.$3.$3.O5.O22.)(17.(18.$3.$3.)(19.$3.$3.(13.(13.O:.+=0.)(14.+50.O8.))(13.(13.(13.O:.+=0.)(14.+50.O8.))+4.))(17.(18.$3.$3.)(19.$3.$3.(13.O:.+:>0.)(13.O:.+:>8.))O2.)))O1.R2.)(4.(1;.$8.O1.R2.)(4.(7.$8.R2.)(4.(27.$8.R2.(13.(13.O:.+=0.)(14.+50.O8.))(17.$28.(29.(?.&40.(20.O7.+1.)))(17.$28.(29.O=.)(17.$28.(2:.(?.&40.O6.))(1:.$28.)))))(4.(2;.$8.R2.(13.(13.(13.O:.+=0.)(14.+50.O8.))+10.)O4.)(4.(27.$8.R2.(13.O:.+:>0.)(17.$28.(2:.R1.)(1:.$28.)))(1=.$8.R2.O5.O22.))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L18928849318.3  L23525600907.10 L26425050275.2  L31193373102.2  L39108636789.0  L48165528433.104L51489811883.76 L59470995410.104L8974479624.3   00000100M00R00[00\01501N01O01TSS3hAR2SP1T2lo1c3HCa3HCb4TSEPS1T1cS3cnt3HNaSS3hAR2SP1T2SB1c2ws2pw3LWSS3hAR2SP1T1c2ws3LWS1y3H17FS3cnt". (* [comment removed for export] *)
  Lemma comb_pop : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pqra,(0.&40.)Pmx,(0.&40.)Pstw,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))PT,$3.PSB,$3.Plo,$3.Pc,$3.Pcnt,$3.Pcsz,$3.Pws,(2<.(0.&40.))Ppw,(0.&40.)PW,(2<.(18.$3.$3.))P,(4.(6.+1000.R9.)(2=.(6.(13.R9.+1000.)+10000.)(6.+65?000.R9.)))P,(6.(13.R:.+1000.)(1>.+2.+2?.))P,(<.$3.(21.R;.+1000.)=)P,(22.VCS,R<.+1000.)P,(6.=R<.)P,(5.(13.R=.(1>.+2.+25.))(1>.+2.+2?.))P,(4.(6.+1.R<.)(6.R<.+1>.))P,(4.(6.+1.R<.)(6.R<.+10.))P,(4.(6.=R<.)(5.R<.(1>.+2.+40.)))P,(<.$2>.(2?.(0.&40.)R<.)#10.)P,(<.(2.(0.&40.))(30.(0.&40.)R=.(31.(20.R?.+1.)))(32.(0.&40.)R<.))P,(33.$8.R15.(13.$15.+20.)(17.$28.(2:.(?.&40.R13.))(1:.$28.)))P,(27.$8.R16.(13.(13.R15.+=0.)(14.+50.R12.))(17.$28.(29.(?.&40.R11.))(17.$28.(29.R1<.)(17.$28.(2:.(?.&40.R10.))(1:.$28.)))))P,(2;.$8.R17.(13.(13.(13.R16.+=0.)(14.+50.R13.))+10.)R10.)P,(27.$8.R18.(13.R17.+:>0.)(17.$28.(2:.R1=.)(1:.$28.)))P,(1<.R19.R1=.R21.R22.R23.R24.R25.R20.)P,(1=.$8.R1:.R17.(13.R1>.-30.))P,(6.(1?.VhAR,)R18.)P,(6.R19.(20.R20.+30.))P,(6.R21.(1>.+2.+3?.))P,(<.$3.(21.R22.+10.)=)P,(2=.(6.(13.R1>.+1000.)R1<.)(6.R23.R1>.))P,(22.VCS,R1=.(20.R24.R1=.))P,(16.(17.(18.$3.$3.)(19.$3.$3.R1>.R25.)(17.(18.$3.$3.)(19.$3.$3.(13.(13.R20.+=0.)(14.+50.R1=.))(13.(13.(13.R20.+=0.)(14.+50.R1=.))+4.))(17.(18.$3.$3.)(19.$3.$3.(13.R20.+:>0.)(13.R20.+:>8.))R18.)))R22.R21.)P,(1;.$8.R23.R22.)P,(7.$8.R23.)(9.$8.VAL,VCS,(34.R28.R47.R46.R43.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R27.R26.R23.R22.R20.R1?.R1>.R21.R1=.R1<.R1;.R25.)(=.(>.R48.(?.&40.(13.R28.-30.))R47.R46.R45.R44.R43.(?.&40.R20.)(?.&40.(13.(13.R23.+=0.)(14.+50.R20.)))(?.&40.$15.)(?.&40.(13.R23.+=0.))(?.&40.R1?.)(?.&40.+8.)R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)R27.(?.&40.+4<1;<.)R26.(11.(0.&40.))R24.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 q4 qra mx stw
      SP F fc m0 m T SB lo c cnt csz ws pw W
      T0 T1 TAL TCS SB0 SB1 HC HCNT HCSZ LWS NTH SBC PC ARR STC FR ST LOIMG SPL SPH SPA TSEP SCS MU WM MI.
    facts. unfold A_INSTANCE, comb_frame in *. change (1074072 + 32) with 1074104 in *.
    rewrite <- (Z_to_bv_bv_unsigned stw) in STC. rewrite <- (Z_to_bv_bv_unsigned mx) in PC.
    pose proof (bv_unsigned_in_range 64 pw) as PWR. unfold bv_modulus in PWR. cbn [Z.pow Z.of_N Pos.pow Pos.iter Z.mul Pos.mul] in PWR.
    destruct HC as [HCa HCb]. destruct HCNT as [HNa HNb]. destruct HCSZ as [HZa HZb]. lx_aceil.
    (* [comment removed for export] *)
    pose proof (lxw_u32arr_cell _ _ _ (cnt - 1) pw ARR NTH ltac:(clear -HNa; lia)) as CELL.
    rewrite <- (Z_to_bv_bv_unsigned pw) in CELL.
    lx_hide ARR. lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SP); (T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 2784, T + 2792)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    (* [comment removed for export] *)
    lx_run (PLAN [0x4c1d8] [] 20%N).
    match goal with |- context [Z_to_bv 64 (?e ≫ 30)] =>
      replace (e ≫ 30) with (4 * (cnt - 1)) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^30) with 1073741824; clear -HNa HNb;
        first [ replace e with (4 * (cnt - 1) * 1073741824) by lia; rewrite Z.div_mul by lia; reflexivity
              | unfold zlow; rewrite Z.mod_small by lia; replace (4294967296 * (cnt + -1)) with (4 * (cnt - 1) * 1073741824) by lia; rewrite Z.div_mul by lia; reflexivity ]) end.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N).
    lx_unhide. apply evtA_done. unfold comb_post. unfold zlow. lx_exs. lx_ands;
      [> lx_mseq
      | match goal with MUl : munch _ m ?mx |- _ => lx_munch MU MUl end
      | match goal with WMl : wmono _ m ?mx |- wmono _ _ ?mx' => lx_wmono WM WMl end
      | lx_close | lx_close
      | match goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx |- u32arr _ ?mx _ _ => eapply u32arr_transport; [exact ARR| exact MUl| exact WMl| rewrite LWS; cbn; clear -HCa HCb TSEP SPL LOIMG; lia] end
      | lx_close | lx_close ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L40607370799.80L41349968239.83L5327793275.83 L57325747188.83L59314923118.3 L6504741115.80 00000C00]01701J01V01iS3hAR1T1c2ws2HC3LWSS3hAR2SP1T3cnt2ws4HCNT3LWSS3hAR2SP1T3cnt2ws4HCNT3LWSS3hAR2SP1T1c2ws3LWSS3cnt4HCNT1KS3hAR1T1c2ws2HC3LWS". (* [comment removed for export] *)
  Lemma comb_hit : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pqra,(0.&40.)Pmx,(0.&40.)Pstw,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))PT,$3.PSB,$3.Plo,$3.Pc,$3.Pcnt,$3.Pcsz,$3.Pws,(2<.(0.&40.))Ppw,(0.&40.)PW,(2<.(18.$3.$3.))P,(4.(6.+1000.R9.)(2=.(6.(13.R9.+1000.)+10000.)(6.+65?000.R9.)))P,(6.(13.R:.+1000.)(1>.+2.+2?.))P,(<.$3.(21.R;.+1000.)=)P,(22.VCS,R<.+1000.)P,(6.=R<.)P,(5.(13.R=.(1>.+2.+25.))(1>.+2.+2?.))P,(4.(6.+1.R<.)(6.R<.+1>.))P,(4.(6.+1.R<.)(6.R<.+10.))P,(4.(6.=R<.)(5.R<.(1>.+2.+40.)))P,(<.$2>.(2?.(0.&40.)R<.)#10.)P,(<.(2.(0.&40.))(30.(0.&40.)R=.(31.(20.R?.+1.)))(32.(0.&40.)R<.))P,(33.$8.R15.(13.$15.+20.)(17.$28.(2:.(?.&40.R13.))(1:.$28.)))P,(27.$8.R16.(13.(13.R15.+=0.)(14.+50.R12.))(17.$28.(29.(?.&40.R11.))(17.$28.(29.R1<.)(17.$28.(2:.(?.&40.R10.))(1:.$28.)))))P,(2;.$8.R17.(13.(13.(13.R16.+=0.)(14.+50.R13.))+10.)R10.)P,(27.$8.R18.(13.R17.+:>0.)(17.$28.(2:.R1=.)(1:.$28.)))P,(1<.R19.R1=.R21.R22.R23.R24.R25.R20.)P,(1=.$8.R1:.R17.(13.R1>.-30.))P,(6.(1?.VhAR,)R18.)P,(6.R19.(20.R20.+30.))P,(6.R21.(1>.+2.+3?.))P,(<.$3.(21.R22.+10.)=)P,(2=.(6.(13.R1>.+1000.)R1<.)(6.R23.R1>.))P,(22.VCS,R1=.(20.R24.R1=.))P,(16.(17.(18.$3.$3.)(19.$3.$3.R1>.R25.)(17.(18.$3.$3.)(19.$3.$3.(13.(13.R20.+=0.)(14.+50.R1=.))(13.(13.(13.R20.+=0.)(14.+50.R1=.))+4.))(17.(18.$3.$3.)(19.$3.$3.(13.R20.+:>0.)(13.R20.+:>8.))R18.)))R22.R21.)P,(1;.$8.R23.R22.)P,(7.$8.R23.)(9.$8.VAL,VCS,(34.R28.R48.R47.R44.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R27.R26.R23.R22.R20.R1?.R1>.R21.R1=.R1<.R1;.R25.)(=.(>.R49.(?.&40.(13.R28.-30.))R48.R47.R46.R45.R44.(?.&40.R20.)(?.&40.(13.(13.R23.+=0.)(14.+50.R20.)))(?.&40.$15.)(?.&40.(13.R23.+=0.))R43.(?.&40.+8.)R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)R27.(?.&40.+4<1;4.)R26.(11.(0.&40.))R24.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 q4 qra mx stw
      SP F fc m0 m T SB lo c cnt csz ws pw W
      T0 T1 TAL TCS SB0 SB1 HC HCNT HCSZ LWS NTH SBC PC ARR STC FR ST LOIMG SPL SPH SPA TSEP SCS MU WM MI.
    facts. pose proof FR as FR'. unfold comb_frame in FR'.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small cnt) by lia.
    zstep. if_cases K; zify_cond K. { exfalso. clear - K HCNT. lia. }
    clear FR'. eapply comb_pop; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11336983832.85L22700267513.86L32747267358.85L39315178285.73L61817024193.85L66537803055.8500000e01B01`02802902:S3hAR2SP1x1T2lo2ws1c3LWS4TSEP2T03TAL5LOIMG3SPL3SPA2CRS3hAR2SP1x1T2lo2ws1c3LWS2x81HS3hAR2SP1x1T2lo2ws1c3LWS5LOIMGS3hAR2SP1x1T2ws1c2T03LWSFF". (* [comment removed for export] *)
  Lemma comb_hit_spec : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pmx,(0.&40.)Pstw,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Px,$3.PT,$3.PSB,$3.Plo,$3.Pcnt,$3.Pcsz,$3.Pws,(2<.(0.&40.))Ppw,(0.&40.)Zc,$3.(10.R8.)P,(4.(6.+1.R9.)(6.R9.+10000.))P,(4.(6.+1000.R9.)(2=.(6.(13.R9.+1000.)+10000.)(6.+65?000.R9.)))P,(6.(13.R:.+1000.)(1>.+2.+2?.))P,(<.$3.(21.R;.+1000.)=)P,(22.VCS,R<.+1000.)P,(6.=R<.)P,(5.(13.R=.(1>.+2.+25.))(1>.+2.+2?.))P,(4.(6.+1.R<.)(6.R<.+10.))P,(4.(6.=R<.)(5.R<.(1>.+2.+40.)))P,(<.$2>.(2?.(0.&40.)R<.)#10.)P,(<.(2.(0.&40.))(30.(0.&40.)R=.(31.(20.R?.+1.)))(32.(0.&40.)R<.))P,(33.$8.R15.(13.$15.+20.)(17.$28.(2:.(?.&40.R12.))(1:.$28.)))P,(27.$8.R16.(13.(13.R14.+=0.)(14.+50.R=.))(17.$28.(29.(?.&40.R11.))(17.$28.(29.R1;.)(17.$28.(2:.(?.&40.R10.))(1:.$28.)))))P,(2;.$8.R17.(13.(13.(13.R15.+=0.)(14.+50.R>.))+10.)R10.)P,(27.$8.R18.(13.R16.+:>0.)(17.$28.(2:.R1<.)(1:.$28.)))P,(1=.$8.R19.R15.R1<.)P,(6.(1?.VhAR,)R16.)P,(6.R17.(20.R1>.+30.))P,(6.R1?.(1>.+2.+3?.))P,(<.$3.(21.R20.+10.)=)P,(2=.(6.(13.R1<.+1000.)R1:.)(6.R21.R1<.))P,(22.VCS,R1;.(20.R22.R1;.))P,(7.$8.R20.)(9.$8.VAL,VCS,(34.R24.R3?.R3>.R3;.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R3:.R39.R34.R33.R32.R40.R26.R23.R22.R1?.R1>.R18.R1<.R1;.R1=.R1:.R19.(1:.(18.$3.$3.))R21.)(=.(>.R40.(?.&40.R24.)R3?.R3>.R3=.R3<.R3;.R3:.R39.(?.&40.$15.)(?.&40.(13.R1?.+=0.))(?.&40.R20.)(?.&40.+8.)R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R23.(?.&40.$24.)R22.(11.(0.&40.))R21.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mx stw SP F fc m x T SB lo cnt csz ws pw c
      Hx T0 T1 TAL TCS SB0 SB1 HCNT HCSZ LWS NTH SBC PC ARR STC ST LOIMG SPL SPH SPA TSEP SCS MI.
    pose proof (class_of_range x Hx) as CR. fold c in CR. unfold A_INSTANCE in SBC. change (1074072 + 32) with 1074104 in SBC.
    pose proof (munch_refl [(lo, SP); (T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 2784, T + 2792)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    callxA (eapply comb_A; try eassumption; lia).
    fold c. eapply comb_hit; try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L40609285039.52L57325747188.53L6498399611.52 L6632284219.53 00000<00E00Q00VS3hAR1T1c2HCS3hAR1T1cS3hAR1T1c2HCS3hAR". (* [comment removed for export] *)
  Lemma comb_miss : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pmx,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PT,$3.Plo,$3.Pc,$3.Pcsz,$3.P,(4.(6.+1000.R4.)(2=.(6.(13.R4.+1000.)+10000.)(6.+65?000.R4.)))P,(6.(13.R5.+1000.)(1>.+2.+2?.))P,(22.VCS,R6.+1000.)P,(4.(6.+1.R5.)(6.R5.+1>.))P,(27.$8.R9.(13.(13.R8.+=0.)(14.+50.R6.))(17.$28.(29.(?.&40.=))(17.$28.(29.R=.)(17.$28.(2:.(?.&40.R5.))(1:.$28.)))))P,(6.(1?.VhAR,)R8.)P,(6.R9.(20.R>.+30.))P,(6.R?.(1>.+2.+3?.))P,(2=.(6.(13.R<.+1000.)R;.)(6.R10.R<.))P,(7.$8.R>.)(9.$8.VAL,VCS,Lms',$:.(<.$:.R1.(=.(>.(?.&40.+4<2;8.)(?.&40.(13.R13.-30.))R2<.R2;.R2:.R29.R28.(?.&40.R=.)(?.&40.(13.(13.R?.+=0.)(14.+50.R=.)))(?.&40.(13.R?.+=0.))(?.&40.(13.(13.R?.+=0.)(14.+50.R=.)))(?.&40.$15.)(?.&40.R=.)R26.R25.R24.R23.(?.&40.+8.)(?.&40.(13.R?.+=0.))(?.&40.$15.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R12.(?.&40.$35.)R11.(11.(0.&40.))R10.(12.$8.)))(=.(>.R2<.(?.&40.(13.R12.-30.))R2;.R2:.R29.R28.R27.(?.&40.R<.)(?.&40.(13.(13.R>.+=0.)(14.+50.R<.)))(?.&40.$15.)(?.&40.(13.R>.+=0.))R26.(?.&40.+8.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R11.(?.&40.+4<1;4.)R10.(11.(0.&40.))R?.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mx SP F fc m T lo c csz
      T0 T1 TCS HC PC LOIMG SPL SPH TSEP MI.
    facts. unfold A_INSTANCE, A_REFILL in *.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small 0) by lia.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L29012665503.83L40602960267.81L5331805151.84 L57325747188.84L59314923118.3 L6508853087.81 00000F00Y01301F01N01aS3hAR2SP1T1r2ws2HR3LWSS3hAR1T1c2ws2HC3LWSS3hAR2SP1T3cnt2ws4HCNT3LWSS3hAR2SP1T1c2ws3LWSS1r2HR1KS3hAR1T1c2ws2HC3LWS". (* [comment removed for export] *)
  Lemma comb_refill_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pqra,(0.&40.)Pmx,(0.&40.)Pstw,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))PT,$3.PSB,$3.Plo,$3.Pc,$3.Pcnt,$3.Pcsz,$3.Pr,$3.Pws,(2<.(0.&40.))Ppw,(0.&40.)PW,(2<.(18.$3.$3.))P,(4.(6.+1000.R:.)(2=.(6.(13.R:.+1000.)+10000.)(6.+65?000.R:.)))P,(6.(13.R;.+1000.)(1>.+2.+2?.))P,(<.$3.(21.R<.+1000.)=)P,(22.VCS,R=.+1000.)P,(6.=R=.)P,(5.(13.R>.(1>.+2.+25.))(1>.+2.+2?.))P,(4.(6.+1.R=.)(6.R=.+1>.))P,(4.(6.+1.R=.)(6.R=.+10.))P,(4.(6.=R=.)(5.R=.(1>.+2.+40.)))P,(4.(5.=R=.)(5.R=.(1>.+2.+40.)))P,(<.$2>.(2?.(0.&40.)R=.)#10.)P,(<.(2.(0.&40.))(30.(0.&40.)R>.(31.(20.R11.+1.)))(32.(0.&40.)R=.))P,(33.$8.R17.(13.$15.+20.)(17.$28.(2:.(?.&40.R15.))(1:.$28.)))P,(27.$8.R18.(13.(13.R17.+=0.)(14.+50.R14.))(17.$28.(29.(?.&40.R13.))(17.$28.(29.R1>.)(17.$28.(2:.(?.&40.R12.))(1:.$28.)))))P,(2;.$8.R19.(13.(13.(13.R18.+=0.)(14.+50.R15.))+10.)R11.)P,(27.$8.R1:.(13.R19.+:>0.)(17.$28.(2:.R1?.)(1:.$28.)))P,(1<.R1;.R1?.R23.R24.R25.R26.R27.R22.)P,(1=.$8.R1<.R19.(13.R20.-30.))P,(6.(1?.VhAR,)R1:.)P,(6.R1;.(20.R22.+30.))P,(6.R23.(1>.+2.+3?.))P,(<.$3.(21.R24.+10.)=)P,(2=.(6.(13.R20.+1000.)R1>.)(6.R25.R20.))P,(22.VCS,R1?.(20.R26.R1?.))P,(16.(17.(18.$3.$3.)(19.$3.$3.R20.R27.)(17.(18.$3.$3.)(19.$3.$3.(13.(13.R22.+=0.)(14.+50.R1?.))(13.(13.(13.R22.+=0.)(14.+50.R1?.))+4.))(17.(18.$3.$3.)(19.$3.$3.(13.R22.+:>0.)(13.R22.+:>8.))R19.)))R24.R23.)P,(1;.$8.R25.R24.)P,(7.$8.R25.)(9.$8.VAL,VCS,(34.R2:.R49.R48.R45.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R29.R28.R25.R24.R22.R21.R20.R23.R1>.R1=.R1<.R27.)(=.(>.(?.&40.+4<2;8.)(?.&40.(13.R2:.-30.))R49.R48.R47.R46.R45.(?.&40.R22.)(?.&40.(13.(13.R25.+=0.)(14.+50.R22.)))(?.&40.R1?.)R44.R43.R42.R41.R40.R3?.R3>.(?.&40.+8.)(?.&40.(13.R25.+=0.))(?.&40.$15.)R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R29.(?.&40.+4<2;8.)R28.(11.(0.&40.))R26.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 q4 qra mx stw
      SP F fc m0 m T SB lo c cnt csz r ws pw W
      T0 T1 TAL TCS SB0 SB1 HC HCNT HCSZ HR LWS NTH SBC PC ARR STC FR ST LOIMG SPL SPH SPA TSEP SCS MU WM MI.
    facts. pose proof FR as FR'. unfold comb_frame in FR'.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { exfalso. clear - K HR. lia. }
    zstep. rewrite (sx32_small cnt) by lia.
    zstep. zstep. zstep. zstep.
    clear FR'. eapply comb_pop; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L63787280654.1L7872035019.5000000400CS2SPS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  Lemma comb_refill_no : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pqra,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))PT,$3.Plo,$3.Pc,$3.PW,(2<.(18.$3.$3.))P,(1<.R5.R9.R;.R<.R=.R>.R?.R:.)P,(1=.$8.R6.R4.(13.R:.-30.))P,(6.(1?.VhAR,)R5.)P,(6.R6.(20.R<.+30.))P,(6.R=.(1>.+2.+3?.))P,(<.$3.(21.R>.+10.)=)P,(22.VCS,R9.(20.R?.R9.))P,(16.(17.(18.$3.$3.)(19.$3.$3.R:.R10.)R8.)R=.R<.)P,(1;.$8.R>.R=.)P,(7.$8.R>.)(9.$8.VAL,VCS,Lms',$:.(;.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(4.(<.$:.R2.(=.(>.R16.(?.&40.R15.)R32.R31.R30.R2?.R2>.R1;.R1:.(?.&40.=)(?.&40.+9.)R2<.(?.&40.+8.)R2:.R29.R28.R27.R19.R18.R17.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R14.(26.R16.)R13.(11.(0.&40.))R1.(12.$8.)))(4.(16.(17.(18.$3.$3.)(19.$3.$3.R?.R15.)R=.)R12.R1.)(4.(1;.$8.R12.R1.)(4.(7.$8.R1.)(1=.$8.R1.R?.R15.))))))(=.(>.(?.&40.+4<2;8.)(?.&40.(13.R13.-30.))R30.R2?.R2>.R2=.R2<.(?.&40.R<.)(?.&40.(13.(13.R>.+=0.)(14.+50.R<.)))(?.&40.=)R2;.R2:.R29.R28.R27.R26.R25.(?.&40.+8.)(?.&40.(13.R>.+=0.))(?.&40.$15.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R12.(?.&40.+4<2;8.)R11.(11.(0.&40.))R?.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 q4 qra SP F fc m0 m T lo c W
      FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold comb_frame in FR.
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). lx_unhide. lx_stk_grow lo.
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | match goal with MUl : munch _ m ?mx |- _ => lx_munch MU MUl end
      | match goal with WMl : wmono _ m ?mx |- wmono _ _ ?mx' => lx_wmono WM WMl end | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition combS_post (SP : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (x lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Lms',$:.(;.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(4.(<.$:.R2.(=.(>.(?.&40.+4<0;0.)(?.&40.(13.O1>.-30.))O1=.O1<.O1;.O1:.O19.(?.&40.+8.)O17.(?.&40.(13.$15.+40.))(?.&40.(13.$15.+2;0.))(?.&40.O3.)(?.&40.+8.)(?.&40.(13.$15.+40.))(?.&40.+10000.)O8.O7.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.)O5.(?.&40.$36.)O4.(11.(0.&40.))R1.(12.$8.)))(4.(16.(17.(18.$3.$3.)(19.$3.$3.O2.O1>.)(1:.(18.$3.$3.)))O1.R1.)(4.(1;.$8.O1.R1.)(4.(7.$8.R1.)(4.(1<.R1.O1>.O14.O15.O16.O17.O18.O6.)(1=.$8.R1.O2.(13.O1>.-30.))))))))")
(* [comment removed for export] *).

  Lemma comb_sec_A : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Px,$3.Plo,$3.P,(4.(5.+10000.R2.)(5.R2.(1>.+2.+3?.)))P,(1=.$8.R4.R2.R7.)P,(6.(1?.VhAR,)R3.)P,(6.R4.(20.R9.+30.))P,(6.R:.(1>.+2.+3?.))P,(<.$3.(21.R;.+10.)=)P,(22.VCS,R7.(20.R<.R7.))P,(7.$8.R:.)(9.$8.VAL,VCS,(37.R>.R28.R27.R26.R25.R24.R23.R22.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R1>.R1=.R29.R=.R<.R:.R9.R;.)(=.(>.R29.(?.&40.R>.)R28.R27.R26.R25.R24.R23.R22.(?.&40.$15.)R21.(?.&40.R:.)(?.&40.+8.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R=.(?.&40.$24.)R<.(11.(0.&40.))R;.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m x lo
      Hx ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_COMBINED, A_INSTANCE, A_LARGE_ALLOC in *. destruct Hx as [Hxa Hxb].
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x4c2e0] [] 40%N).
    apply evtA_done. unfold combS_post, comb_frame. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L63787280654.1L7872035019.5300000400CS2SPS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  Lemma comb_sec_B : ltac2:(CDefT.buildp (gd_tbl_AW_Combined ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pr,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pqra,(0.&40.)PSP,$3.PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Plo,$3.PW,(2<.(18.$3.$3.))P,(1<.R3.R7.R9.R:.R;.R<.R=.R8.)P,(1=.$8.R4.R3.(13.R8.-30.))P,(6.(1?.VhAR,)R4.)P,(6.R5.(20.R:.+30.))P,(6.R;.(1>.+2.+3?.))P,(<.$3.(21.R<.+10.)=)P,(22.VCS,R8.(20.R=.R8.))P,(16.(17.(18.$3.$3.)(19.$3.$3.R9.R>.)R8.)R;.R:.)P,(1;.$8.R<.R;.)P,(7.$8.R<.)(9.$8.VAL,VCS,Lms',$:.(;.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(4.(<.$:.R2.(=.(>.R14.(?.&40.R13.)R35.R34.R33.R32.R31.R19.R18.R1:.(?.&40.+9.)R2>.(?.&40.+8.)R2<.R2;.R2:.R29.R17.R16.R15.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R12.(26.R14.)R11.(11.(0.&40.))R1.(12.$8.)))(4.(16.(17.(18.$3.$3.)(19.$3.$3.R>.R13.)R=.)R10.R1.)(4.(1;.$8.R10.R1.)(4.(7.$8.R1.)(1=.$8.R1.R>.R13.))))))(=.(>.(?.&40.+4<0;0.)(?.&40.(13.R11.-30.))R33.R32.R31.R30.R2?.(?.&40.+8.)R2>.R18.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R10.(?.&40.+4<0;0.)R?.(11.(0.&40.))R=.(12.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 r q0 q1 q2 q3 q4 qra SP F fc m0 m lo W
      FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold comb_frame in FR.
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). lx_unhide. lx_stk_grow lo.
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | match goal with MUl : munch _ m ?mx |- _ => lx_munch MU MUl end
      | match goal with WMl : wmono _ m ?mx |- wmono _ _ ?mx' => lx_wmono WM WMl end | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Combined.

End ARUN_2.
