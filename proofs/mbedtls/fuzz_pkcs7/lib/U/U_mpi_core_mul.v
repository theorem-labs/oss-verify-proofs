(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_mpi_core_mla.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsArr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_mul () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_MUL_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_mul_post"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].



Definition U_MPI_CORE_MUL : Z := 0x23d10.
Definition MPI_CORE_MUL_STACK : Z := 176.

Definition mpi_core_mul_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O17.O16.O15.O14.R11.R10.R?.O13.O12.R>.R=.R<.R;.R:.R9.R8.R7.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R6.R5.R4.R3.)O7.(9.O17.)O6.(:.(2.&40.))R2.(;.O18.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O5.(11.O5.(12.+4.O4.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O16.)$15.)(14.&40.O16.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O18.O1.R2.)(5.(18.O18.R2.)(5.(19.O18.R2.O5.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O4.)R1.)(1<.(2.&40.)(1=.O4.)O3.))(1>.O18.R2.O2.(14.&40.O16.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_mul_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.PA,$?.Pan,$?.PB,$?.Pbn,$?.Plo,$?.Pxs,(4.(2.&40.))Pys,(4.(2.&40.))Pzs,(4.(2.&40.))P,(19.O2.R:.R9.R3.)P,(20.O2.R;.R9.(21.R3.))P,(20.O2.R<.R8.(21.R3.))P,(22.=R:.)P,(22.=R9.)P,(22.(11.R<.R:.)+2710.)P,(22.(11.R=.R;.)(23.(1;.(2.&40.)R9.)))P,(22.R>.(23.(1;.(2.&40.)R9.)))P,(22.R=.(23.(1;.(2.&40.)R9.)))P,(24.(22.(11.R11.(12.+4.(23.(1;.(2.&40.)R;.))))R12.)(22.(11.R12.(12.+4.(23.(1;.(2.&40.)R<.))))R11.))P,(24.(22.(11.R10.(12.+4.(23.(1;.(2.&40.)R;.))))R13.)(22.(11.R13.(12.+4.(23.(1;.(2.&40.)R=.))))R10.))P,(6.$?.(25.R14.+4.)=)P,(6.$?.(25.R14.+4.)=)P,(6.$?.(25.R13.+4.)=)P,(26.=R17.)P,(24.(6.$?.R16.=)(26.=R17.))P,(24.(6.$?.R15.=)(26.=R16.))P,(26.(11.R1:.(12.+4.(23.(1;.(2.&40.)R14.))))(27.+2.+40.))P,(26.(11.R1:.(12.+4.(23.(1;.(2.&40.)R14.))))(27.+2.+40.))P,(26.(11.R19.(12.+4.(23.(1;.(2.&40.)R14.))))(27.+2.+40.))P,(1>.O2.R1>.R18.(14.&40.R3>.))P,(22.R19.(13.(14.&40.R3?.)$15.))P,(6.$?.(25.(14.&40.R40.)+10.)=)P,(24.(22.(11.R20.(12.+4.(23.(1;.(2.&40.)R1:.))))R1;.)(22.(14.&40.R41.)R20.))P,(24.(22.(11.R20.(12.+4.(23.(1;.(2.&40.)R1:.))))R1<.)(22.(14.&40.R42.)R20.))P,(24.(22.(11.R1?.(12.+4.(23.(1;.(2.&40.)R1:.))))R1=.)(22.(14.&40.R43.)R1?.))P,(18.O2.R24.)P,(6.$?.(25.(14.&40.R46.)+2.)=)P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))(29.O2.(2:.O2.R4<.R4;.R4:.R49.R45.R44.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R2=.R2<.R2:.(11.R28.R26.)R24.R25.R2;.)(7.(8.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)R2=.(28.&40.O1.)R2<.(:.(2.&40.))R2;.(;.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11066734223.13L17187524197.13L17412818593.13L24204441423.13L51288638096.13L67085962724.1300000M00j01G01d02A02^S1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3HgeS1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3Hge". (* [comment removed for export] *)
Lemma same_from_mla : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Pi,$1:.Pk,$1:.Pn,$1:.Pxs,(4.(2.&40.))Pds',(4.(2.&40.))Pxs0,(4.(2.&40.))P,(6.$1:.(1;.(2.&40.)R2.)(1;.(2.&40.)(1<.(2.&40.)R6.R3.)))P,(6.(4.(2.&40.))(1<.(2.&40.)R6.R3.)(1<.(2.&40.)R6.(1<.(2.&40.)R7.R4.)))P,(2;.(2<.R8.R7.)R6.)P,(2=.(2.&40.)R7.R6.R4.)(2=.(2.&40.)R8.(2>.(2.&40.)(2?.(2.&40.)R:.R7.)R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros i k n xs ds' xs0 L SK Hik FS q Hq.
  destruct (Nat.lt_ge_cases q (length xs)) as [Hlt|Hge].
  - rewrite nth_error_app2 by (rewrite firstn_length; lia). rewrite firstn_length, Nat.min_l by lia.
    rewrite <- (FS q Hq). transitivity (nth_error (skipn k ds') (q - i - k)).
    { rewrite nth_error_skipn. f_equal. lia. }
    rewrite SK, !nth_error_skipn. f_equal. lia.
  - rewrite <- (FS q Hq). rewrite (proj2 (nth_error_None xs q)) by lia. apply nth_error_None.
    rewrite app_length, firstn_length, L, skipn_length. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mul_dinv_tac X n m lo sp W :=
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
  lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
  lazymatch goal with Hm : munch _ m mx |- _ =>
  lazymatch goal with Hw : wmono _ m mx |- _ =>
  lazymatch goal with Hi' : mem_inv _ mx |- _ =>
  lazymatch goal with Hs : stk _ mx lo _ |- _ =>
    assert (DI' : u32arr usegs mx X l /\ Z.of_nat (length l) = n
                  /\ munch W m mx /\ wmono usegs m mx /\ mem_inv usegs mx /\ stk usegs mx lo (bv_unsigned sp + -128));
    [split; [exact Hu| split; [rewrite ?upd_length; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] | split; [first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | split; [exact Hw| split; [exact Hi'| exact Hs]]]]] |]
  end end end end end end.

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A an B bn lx la lb lo : Z) (xs0 ys zs : list word) (junk : list byte).
  Hypothesis Han : 0 <= an /\ 0 <= bn /\ an + bn <= 10000.
  Hypothesis Ln : an + bn <= lx /\ an <= la /\ bn <= lb.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LA : Z.of_nat (length ys) = la.
  Hypothesis LB : Z.of_nat (length zs) = lb.
  Hypothesis DA : A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis DB : B + 4 * lb <= X \/ X + 4 * lx <= B.
  Hypothesis XB : 0 < X /\ X + 4 * lx < 2^64.
  Hypothesis AB : 0 <= A /\ A + 4 * la < 2^64.
  Hypothesis BB : 0 <= B /\ B + 4 * lb < 2^64.
  Hypothesis NZA : an <= 0 \/ 1 <= A.
  Hypothesis NZB : bn <= 0 \/ 1 <= B.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis ALB : B mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 176.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= lo \/ bv_unsigned sp <= A.
  Hypothesis SBB : B + 4 * lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis HA0 : bytes_at usegs m A (u32s ys).
  Hypothesis HB0 : bytes_at usegs m B (u32s zs).
  (* [comment removed for export] *)
  Hypothesis HXhi : u32arr usegs m (X + 4 * (an + bn)) (skipn (Z.to_nat (an + bn)) xs0).

  Notation POST := (mpi_core_mul_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X (an + bn) xs0 lo m).
  Notation W := [(X, X + 4 * (an + bn)); (bv_unsigned sp - 176, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -128) [CB 8 junk; C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 an); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation DINV mm xs := (u32arr usegs mm X xs /\ Z.of_nat (length xs) = an + bn
                          /\ munch W m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -128)).

  Ltac mul_dinv := mul_dinv_tac X constr:(an + bn) m lo sp constr:(W).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L35876709422.5 L36962904668.11L58790393654.5 L59904178890.5 L6330159503.14 00000B00g01501E021S2an2bn3Han3xs'2LXS2an2bn2lx2la2lb3xs03Han2Ln2L03xs'2LXS2an2bn3xs'2LXS1X2an2bn3xs'2LXS2sp1X2an2bn2lx2la2lb2lo3xs03Han2Ln2L02LO2SX". (* [comment removed for export] *)
  Lemma fin_post : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Pm',P,(2.&40.)(3.(2.&8.))Pxs',(4.(2.&40.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya0,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.(11.Van,Vbn,))))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+;0.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R11.)P,(17.$30.Vm,R12.)P,(18.$30.R13.)P,(1>.$30.R14.Vlo,(14.&40.Vsp,))P,(19.$30.R15.VX,R14.)P,(6.$?.(23.(1;.(2.&40.)R15.))(11.Van,Vbn,))(2:.$30.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,(11.Van,Vbn,)Vxs0,Vlo,Vm,(7.(8.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,R12.R11.R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(9.Vra,)Vfc,(:.(2.&40.))R17.(;.$30.)))")
(* [comment removed for export] *).
  Proof.
    intros until yt6. intros MU WM MI ST HX LX.
    unfold mpi_core_mul_post, MPI_CORE_MUL_STACK.
    flexi 16%nat. exists (xs' ++ skipn (Z.to_nat (an + bn)) xs0). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split. { apply u32arr_app. split; [exact HX|]. replace (X + 4 * Z.of_nat (length xs')) with (X + 4 * (an + bn)) by xlia LX.
             eapply u32arr_transport; [exact HXhi | exact MU | exact WM |]. cbn [disjoint_from]. rewrite skipn_length. clear -Han Ln L0 SX LO. lia. }
    split. { rewrite app_length, skipn_length. xlia LX L0 Ln Han. }
    split. { rewrite skipn_app, skipn_all2 by xlia LX Han. replace (Z.to_nat (an + bn) - length xs')%nat with 0%nat by xlia LX Han. reflexivity. }
    exact ST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac mul_ret :=
    try rewrite (Z_to_bv_bv_unsigned sp); first [ apply evt_done | idtac ];
    let mx := lx_cur_mem in
    lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ m mx |- _ =>
    lazymatch goal with Hw : wmono _ m mx |- _ =>
    lazymatch goal with Hi' : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx lo (bv_unsigned sp) |- _ =>
      eapply (fin_post mx l);
      [ first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | exact Hw | exact Hi' | exact Hs | exact Hu
      | rewrite ?upd_length; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] ]
    end end end end end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i : Z) (xs : list word) (mm : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wb1 wx1 wx2 wi wb2 : word),
    Z.to_nat (bn - i) = k -> 0 <= i < bn ->
    wb1 = Z_to_bv 64 (B + 4 * i) -> wx1 = Z_to_bv 64 (X + 4 * i) -> wx2 = Z_to_bv 64 (X + 4 * i) ->
    wi = Z_to_bv 64 i -> wb2 = Z_to_bv 64 (B + 4 * i) ->
    DINV mm xs -> FRAME mm ->
    evt usegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 B) wb1
             xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 bn) (Z_to_bv 64 X) wx1 (Z_to_bv 64 (an + 1)) wx2 wi
             (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) wb2 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x23da4) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i xs mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wb1 wx1 wx2 wi wb2
      Hk Hi -> -> -> -> -> (HX & LX & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hi|].
    pose proof (u32ro_transport _ _ _ _ _ _ HB0 MU ltac:(cbn [disjoint_from]; rewrite LB; clear -Han Ln LB DB SBB LO; lia)) as HB.
    pose proof (u32ro_transport _ _ _ _ _ _ HA0 MU ltac:(cbn [disjoint_from]; rewrite LA; clear -Han Ln LA DA SA LO; lia)) as HA.
    pose proof (sumsarr_ok [X]) as LXSUMS.
    lx_run_tac (PLANS [0x23da4] [] 120%N SUMSARR); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23da4) _ _ _ _) =>
             mul_dinv; eapply (IH (i + 1)); [xlia Hk Hi | klia | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => mul_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma U_mpi_core_mul_spec : mpi_core_mul_stmt usegs U_MPI_CORE_MUL.
Proof.
  unfold mpi_core_mul_stmt, U_MPI_CORE_MUL.
  intros until zs. intros HX HA HB Han Hbn Hab LX LA LB DA DB ALX ALA ALB NZX NZA NZB XT AT BT ST LO SPA SX SA SB MI RA -> -> -> -> ->.
  unfold MPI_CORE_MUL_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB. pose proof (u32ro_bound _ _ _ _ HB) as BB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  assert (NZA' : an <= 0 \/ 1 <= A) by (clear -NZA Han; lia). assert (NZB' : bn <= 0 \/ 1 <= B) by (clear -NZB Hbn; lia). clear NZA NZB.
  pose proof (munch_refl [(X, X + 4 * (an + bn)); (bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn (Z.to_nat (an + bn)) xs) in HX. apply u32arr_app in HX. flat constr:(HX) 2%nat. flclear HX. intros HXlo HXhi.
  rewrite firstn_length in HXhi. replace (X + 4 * Z.of_nat (Nat.min (Z.to_nat (an + bn)) (length xs))) with (X + 4 * (an + bn)) in HXhi by xlia LX Han Hbn.
  assert (LXlo : Z.of_nat (length (firstn (Z.to_nat (an + bn)) xs)) = an + bn) by (rewrite firstn_length; xlia LX Han Hbn).
  pose proof (lock HXhi) as HXhi'. pose proof (lock HA) as HA'. pose proof (lock HB) as HB'. clear HXhi HA HB.
  carve_frame 128%nat ST. lxp_split_frame [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat.
  pose proof (sumsarr_ok [X]) as LXSUMS.
  lx_run_tac (PLANS [0x23da4] [] 100%N SUMSARR); lx_tree.
  all: lxp_unjunk.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23da4) _ _ _ _) =>
         mul_dinv_tac X constr:(an + bn) m lo sp constr:([(X, X + 4 * (an + bn)); (bv_unsigned sp - 176, bv_unsigned sp)]);
         eapply (@loop_walk) with (k := Z.to_nat bn) (i := 0) (A := A) (B := B) (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys))
             (lb := Z.of_nat (length zs)) (ys := ys) (zs := zs) (xs0 := xs);
           try eassumption; try reflexivity; try klia; try (f_equal; klia);
         first [exact (unlock _ HA') | exact (unlock _ HB') | exact (unlock _ HXhi') | idtac]
       | |- _ =>
         (* [comment removed for export] *)
         try rewrite (Z_to_bv_bv_unsigned sp); first [ apply evt_done | idtac ];
         let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
         lazymatch goal with Hu : u32arr _ mx xX ?l |- _ =>
         lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
         lazymatch goal with Hm : munch _ xm mx |- _ =>
         lazymatch goal with Hw : wmono _ xm mx |- _ =>
         lazymatch goal with Hi' : mem_inv _ mx |- _ =>
         lazymatch goal with Hs : stk _ mx xlo (bv_unsigned xsp) |- _ =>
           eapply fin_post with (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (lb := Z.of_nat (length zs)) (xs0 := xs);
           first [ exact Hw | exact Hi' | exact Hs | exact Hu | exact (unlock _ HXhi') | exact eq_refl
                 | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia
                 | rewrite Hl; exact LXlo | klia ]
         end end end end end end
       end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
