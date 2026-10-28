(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string.
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
Ltac2 gd_tbl_P_mpi_core_read_be () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_READ_BE_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_read_be_post"; "read_be_ret"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].


Definition U_MPI_CORE_READ_BE : Z := 0x23100.
Definition MPI_CORE_READ_BE_STACK : Z := 48.

(* [comment removed for export] *)
Definition chars_to_limbs4 (len : Z) : Z := (len + 3) / 4.
Definition read_be_ret (n len : Z) : Z := if n <? chars_to_limbs4 len then (-8) else 0.

Definition mpi_core_read_be_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n r : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O18.O17.O16.O15.R10.R?.R>.O14.O13.(9.&40.O4.)R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(:.O18.)O7.(;.(2.&40.))R2.(<.O19.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.O6.(12.O6.(13.+4.O5.)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.O17.)$16.)(15.&40.O17.))(17.(?.$10.$10.))))O1.R2.)(5.(18.O19.O1.R2.)(5.(19.O19.R2.)(5.(1:.O19.R2.O6.R1.)(5.(6.$1;.(1<.(2.&40.)R1.)(1<.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1=.(2.&40.)(1>.O5.)R1.)(1=.(2.&40.)(1>.O5.)O3.))(1?.O19.R2.O2.(15.&40.O17.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_read_be_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$10.Pn,$10.PB,$10.Pblen,$10.Plo,$10.Pxs,(4.(2.&40.))Pbs,(4.(2.&8.))P,(1:.O2.R8.R7.R2.)P,(21.O2.R9.R6.R2.)P,(5.(22.=R8.)(22.R8.+2710.))P,(22.R9.(23.(1<.(2.&40.)R5.)))P,(5.(22.=R8.)(22.R8.(23.(1<.(2.&8.)R5.))))P,(24.(22.(12.R:.(23.(1<.(2.&8.)R6.)))R<.)(22.(12.R<.(13.+4.(23.(1<.(2.&40.)R7.))))R:.))P,(6.$10.(25.R=.+4.)=)P,(24.(6.$10.R=.=)(26.+4.R>.))P,(24.(6.$10.R<.=)(26.=R=.))P,(26.(12.R10.(13.+4.(23.(1<.(2.&40.)R;.))))(27.+2.+40.))P,(26.(12.R?.(23.(1<.(2.&8.)R;.)))(27.+2.+40.))P,(1?.O2.R13.R>.(15.&40.R33.))P,(22.R?.(14.(15.&40.R34.)$16.))P,(6.$10.(25.(15.&40.R35.)+10.)=)P,(24.(22.(12.R15.(13.+4.(23.(1<.(2.&40.)R10.))))R11.)(22.(15.&40.R36.)R15.))P,(24.(22.(12.R14.(23.(1<.(2.&8.)R10.)))R12.)(22.(15.&40.R37.)R14.))P,(19.O2.R18.)P,(6.$10.(25.(15.&40.R3:.)+2.)=)P,(6.(2.&40.)R32.(9.&40.R19.))P,(6.(2.&40.)R32.(9.&40.R19.))P,(6.(2.&40.)R32.(9.&40.R19.))P,(6.(2.&40.)R32.(9.&40.R19.))(28.O2.(29.O2.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.R1=.R1<.(2:.R1<.R1:.)R18.R19.R1>.)(7.(8.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(9.&40.O1.)R1?.(;.(2.&40.))R1>.(<.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L22426354934.5L38189876470.5000004008S2ysS2xs". (* [comment removed for export] *)
Lemma u8arr_app : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Psegs,(4.$2;.)Pm,P,(2.&40.)(3.(2.&8.))PA,$10.Pxs,(4.(2.&8.))Pys,(4.(2.&8.))(2<.(2=.R5.R4.R3.(2>.(2.&8.)R2.R1.))(5.(2=.R5.R4.R3.R2.)(2=.R5.R4.(12.R3.(23.(1<.(2.&8.)R2.)))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A xs ys. unfold u8arr. rewrite app_length, bytes_at_app, Nat2Z.inj_add.
  rewrite (wr_at_app segs m A (Z.of_nat (length xs)) (Z.of_nat (length ys))) by lia. tauto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020=L7029460431.3L8857200067.300000900BS3len1H1ES3len1H1E". (* [comment removed for export] *)
Lemma chars_to_limbs4_eq : forall len, 0 <= len ->
  len / 4 + Z.b2z (0 <? Z.land len 3) = chars_to_limbs4 len.
Proof.
  intros len H. unfold chars_to_limbs4. rewrite land_3_mod'.
  destruct (0 <? len mod 4) eqn:E; cbn [Z.b2z]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n blen lx lo : Z) (xs0 : list word).
  Hypothesis Hn : 1 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 4 < X /\ X + 4 * lx < 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 48.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis OK : chars_to_limbs4 blen <= n.
  (* [comment removed for export] *)
  Hypothesis HXhi : u32arr usegs m (X + 4 * n) (skipn (Z.to_nat n) xs0).

  Notation POST := (mpi_core_read_be_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n (read_be_ret n blen) xs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation DINV mm xs := (u32arr usegs mm X xs /\ Z.of_nat (length xs) = n
                          /\ munch W m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -48)).
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2977899845.3800000IS2ra2sp1X1n4blen3xs02OK1E". (* [comment removed for export] *)
  Lemma ret_ok : read_be_ret n blen = 0.
  Proof. unfold read_be_ret. destruct (n <? chars_to_limbs4 blen) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma fin_post : forall (r : Z) (m' : mem) (xs' : list word) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
    munch W m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
    u32arr usegs m' X xs' -> Z.of_nat (length xs') = n ->
    mpi_core_read_be_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n r xs0 lo m
      (MS (mkR ra sp gp tp yt0 yt1 yt2 s0 s1 (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
          F (ret_pc ra) fc None m' (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until yt6. intros MU WM MI ST HX LX.
    assert (N0 : 0 <= n) by (clear -LX; lia).
    unfold mpi_core_read_be_post, MPI_CORE_READ_BE_STACK.
    flexi 15%nat. exists (xs' ++ skipn (Z.to_nat n) xs0). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split. { apply u32arr_app. split; [exact HX|]. replace (X + 4 * Z.of_nat (length xs')) with (X + 4 * n) by xlia LX.
             eapply u32arr_transport; [exact HXhi | exact MU | exact WM |]. cbn [disjoint_from]. rewrite skipn_length. clear -N0 Ln L0 SX LO. lia. }
    split. { rewrite app_length, skipn_length. xlia LX L0 Ln N0. }
    split. { rewrite skipn_app, skipn_all2 by xlia LX N0. replace (Z.to_nat n - length xs')%nat with 0%nat by xlia LX N0. reflexivity. }
    exact ST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac rdbe_ret :=
    try rewrite (Z_to_bv_bv_unsigned sp); first [ apply evt_done | idtac ]; rewrite ret_ok;
    let mx := lx_cur_mem in
    lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ m mx |- _ =>
    lazymatch goal with Hw : wmono _ m mx |- _ =>
    lazymatch goal with Hi' : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx lo (bv_unsigned sp) |- _ =>
      eapply (fin_post 0 mx l);
      [ first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | exact Hw | exact Hi' | exact Hs | exact Hu
      | rewrite ?upd_length; rewrite ?upd_length in Hl; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] ]
    end end end end end end.
  (* [comment removed for export] *)
  Ltac rdbe_dinv :=
    let mx := lx_cur_mem in
    lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ m mx |- _ =>
    lazymatch goal with Hw : wmono _ m mx |- _ =>
    lazymatch goal with Hi' : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx lo _ |- _ =>
      assert (DI' : DINV mx l);
      [ refine (conj Hu (conj _ (conj _ (conj Hw (conj Hi' Hs)))));
        [ rewrite ?upd_length; rewrite ?upd_length in Hl; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption]
        | first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx Hn; lia] ] | ]
    end end end end end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (l r : Z) (xs : list word) (mm : mem)
      (xra xt0 xt1 xt2 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 wl wr : word),
    r - l < 2 * Z.of_nat k -> 0 <= l <= r -> l + r = n - 1 ->
    wl = Z_to_bv 64 (X + 4 * l) -> wr = Z_to_bv 64 (X + 4 * r) ->
    DINV mm xs -> FRAME mm ->
    evt usegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 wl xs1 wr
             (Z_to_bv 64 (-5)) (Z_to_bv 64 65280) (Z_to_bv 64 5) xa4 xa5 xa6 xa7 xs2 xs3 xs4
             s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x231d0) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros l r xs mm xra xt0 xt1 xt2 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 wl wr Hk Hlr Hs -> ->
      (HX & LX & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hlr|].
    lx_run_tac (PLAN [0x231d0] [] 80%N); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x231d0) _ _ _ _) =>
             rdbe_dinv; eapply (IH (l + 1) (r - 1)); [xlia Hk Hlr | klia | klia | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => rdbe_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma conv_walk : forall (xs : list word) (mm : mem)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 : word),
    DINV mm xs -> FRAME mm ->
    evt usegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 X) xs1
             xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 n) xs4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x23188) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros (HX & LX & MU & WM & MI & ST) FR.
    lx_run_tac (PLAN [0x231d0] [] 40%N); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x231d0) _ _ _ _) =>
             try lx_same_mem; rdbe_dinv; eapply (loop_walk (Z.to_nat n) 0 (n - 1)); [klia | klia | klia | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => rdbe_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422282358.2000001S". (* [comment removed for export] *)
Lemma lxp_c2l_be : forall len, 0 <= len -> Z.shiftr len 2 + Z.b2z (0 <? Z.land len 3) = chars_to_limbs4 len.
Proof. intros len H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply chars_to_limbs4_eq. exact H. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma U_mpi_core_read_be_spec : mpi_core_read_be_stmt usegs U_MPI_CORE_READ_BE.
Proof.
  unfold mpi_core_read_be_stmt, U_MPI_CORE_READ_BE.
  intros until bs. intros HX HB Hn LX Hbl DB ALX NZX NZB XT BT ST LO SPA SX SB MI RA -> -> -> ->.
  unfold MPI_CORE_READ_BE_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (bytes_at_bound _ _ _ _ HB) as BB0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  assert (NZX' : n <= 0 \/ 5 <= X) by (clear -NZX Hn; lia). clear NZX.
  assert (NZB' : blen <= 0 \/ 1 <= B) by (clear -NZB Hbl; lia). clear NZB.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (lock HB) as HB0. pose proof (lock HX) as HX0.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn (Z.to_nat n) xs) in HX. apply u32arr_app in HX. flat constr:(HX) 2%nat. flclear HX. intros HXlo HXhi.
  rewrite firstn_length in HXhi. replace (X + 4 * Z.of_nat (Nat.min (Z.to_nat n) (length xs))) with (X + 4 * n) in HXhi by xlia LX Hn.
  assert (LXlo : Z.of_nat (length (firstn (Z.to_nat n) xs)) = n) by (rewrite firstn_length; xlia LX Hn).
  pose proof (lock HXhi) as HXhi'. clear HXhi HB.
  pose proof (sumsarr_ok [X]) as LXSUMS.
  (* [comment removed for export] *)
  lx_run_tac (PLANS [0x23138] [] 60%N SUMSARR); lx_tree.
  all: lxp_unjunk; try lx_same_mem; pose proof (lxp_c2l_be blen ltac:(xlia Hbl)) as C2L.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23138) _ _ _ _) =>
         assert (OK : chars_to_limbs4 blen <= n) by (rewrite <- C2L; klia);
         assert (BL4 : blen <= 4 * n) by (clear -OK Hbl; unfold chars_to_limbs4 in OK; lia);
         lx_run_tac (PLANS [0x46a40; 0x231d0] [] 120%N SUMSARR); lx_tree
       | |- _ => idtac
       end.
  all: lxp_unjunk; try lx_same_mem.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x231d0) _ _ _ _) =>
         (* [comment removed for export] *)
         let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
         lazymatch goal with Hu : u32arr _ mx xX ?lw0 |- _ =>
         lazymatch goal with Hl : Z.of_nat (length lw0) = _ |- _ =>
         lazymatch goal with Hm : munch _ xm mx |- _ =>
         lazymatch goal with Hw : wmono _ xm mx |- _ =>
         lazymatch goal with Hi' : mem_inv _ mx |- _ =>
         lazymatch goal with Hs : stk _ mx xlo _ |- _ =>
         lazymatch goal with Hf : rw_cells _ mx (bv_unsigned xsp + -48) _ |- _ =>
           eapply (@loop_walk) with (k := Z.to_nat n) (l := 0) (r := n - 1) (lx := Z.of_nat (length xs)) (xs0 := xs) (blen := blen);
           first [ exact Hf | exact (unlock _ HXhi') | refine (conj Hu (conj _ (conj _ (conj Hw (conj Hi' Hs))))); [rewrite Hl; exact LXlo | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx Hn; lia]
                 | reflexivity | klia | f_equal; klia ]
         end end end end end end end
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x46a40) _ _ _ ?mx) => idtac
       | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?xa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mf _) =>
           ((* [comment removed for export] *)
            try rewrite (Z_to_bv_bv_unsigned sp); apply evt_done;
            first [ replace (read_be_ret n blen) with (-8) by (unfold read_be_ret; rewrite (proj2 (Z.ltb_lt n (chars_to_limbs4 blen))) by klia; reflexivity)
                  | replace (read_be_ret n blen) with 0 by (unfold read_be_ret; rewrite (proj2 (Z.ltb_ge n (chars_to_limbs4 blen))) by klia; reflexivity) ];
            let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
            lazymatch goal with Hu : u32arr _ mx xX ?l |- _ =>
            lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
            lazymatch goal with Hm : munch _ xm mx |- _ =>
            lazymatch goal with Hw : wmono _ xm mx |- _ =>
            lazymatch goal with Hi' : mem_inv _ mx |- _ =>
            lazymatch goal with Hs : stk _ mx xlo (bv_unsigned xsp) |- _ =>
              eapply fin_post with (lx := Z.of_nat (length xs)) (xs0 := xs);
              first [ exact Hw | exact Hi' | exact Hs | exact Hu | exact (unlock _ HXhi') | exact eq_refl
                    | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia
                    | rewrite Hl; exact LXlo | klia ]
            end end end end end end)
       end.
  (* [comment removed for export] *)
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
  lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
  lazymatch goal with Hm : munch _ m mx |- _ =>
  lazymatch goal with Hw : wmono _ m mx |- _ =>
    rename Hu into RWu; rename Hm into MU1; rename Hw into WM1;
    assert (LL : Z.of_nat (length l) = n) by (rewrite Hl; exact LXlo); clear Hl;
    set (l0 := l) in RWu, LL; clearbody l0
  end end end end.
  try clear MU WM. rename MU1 into MU. rename WM1 into WM.
  assert (Hbl1 : 1 <= blen) by klia.
  lx_gc.
  pose proof (unlock _ HB0) as HB1. eapply (bytes_at_transport usegs _ _ _ _ _) in HB1; [| exact MU | cbn [disjoint_from]; clear -DB SB LO Hn LX Hbl BB0; lia].
  apply u32arr_cells in RWu. apply u8arr_of_rw_cells in RWu.
  rewrite <- (firstn_skipn (Z.to_nat (4 * n - blen)) (u32s l0)) in RWu. apply u8arr_app in RWu. flat constr:(RWu) 2%nat. flclear RWu. intros RW1 RW2.
  rewrite firstn_length, u32s_length in RW2. replace (Nat.min (Z.to_nat (4 * n - blen)) (4 * length l0)) with (Z.to_nat (4 * n - blen)) in RW2 by (clear -LL Hbl C2L OK Hn; unfold chars_to_limbs4 in OK; lia).
  apply rw_cells_of_u8arr in RW2. rewrite skipn_length, u32s_length in RW2.
  replace (X + Z.of_nat (Z.to_nat (4 * n - blen))) with (X + (4 * n - blen)) in RW2 by (clear -LL Hbl OK Hn; unfold chars_to_limbs4 in OK; lia).
  apply rw_cells_of_u8arr in RW1. rewrite firstn_length, u32s_length in RW1.
  rewrite <- (firstn_skipn (Z.to_nat blen) bs) in HB1. apply bytes_at_app in HB1. flat constr:(HB1) 2%nat. flclear HB1. intros HB1 _.
  pose proof U_memcpy_spec as SP. unfold memcpy_stmt in SP.
  eapply evt_cut.
  { eapply SP with (src := firstn (Z.to_nat blen) bs); rewrite ?unsigned_lit by (clear -XB XT BT LX Hn Hbl BB0 OK SPR; unfold chars_to_limbs4 in OK; lia);
      [ exact HB1 | rewrite firstn_length; clear -Hbl; lia
      | replace (Z.to_nat blen) with (4 * length l0 - Z.to_nat (4 * n - blen))%nat by (clear -LL Hbl OK Hn; unfold chars_to_limbs4 in OK; lia); exact RW2
      | clear -DB Hbl LX Hn OK; unfold chars_to_limbs4 in OK; lia | assumption ]. }
  clear SP HB1 RW2. unfold memcpy_post. rewrite !unsigned_lit by (clear -XB XT BT LX Hn Hbl BB0 OK SPR; unfold chars_to_limbs4 in OK; lia).
  match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
  match goal with H : rw_cells usegs ?m2 (X + (4 * n + - blen)) _ |- _ => rename H into RW2 end.
  apply u8arr_of_rw_cells in RW1. apply u8arr_of_rw_cells in RW2.
  lazymatch type of RW2 with u8arr _ ?m2 _ _ =>
    assert (U8 : u8arr usegs m2 X (firstn (Z.to_nat (4 * n - blen)) (u32s l0) ++ firstn (Z.to_nat blen) bs))
      by (apply u8arr_app; split; [exact RW1|]; rewrite firstn_length, u32s_length;
          replace (X + Z.of_nat (Nat.min (Z.to_nat (4 * n - blen)) (4 * length l0))) with (X + (4 * n - blen)) by (clear -LL Hbl OK Hn; unfold chars_to_limbs4 in OK; lia); exact RW2);
    clear RW1 RW2;
    destruct (u32arr_of_u8arr usegs m2 X _ (Z.to_nat n) U8 ltac:(rewrite app_length, !firstn_length, u32s_length; clear -LL Hbl OK Hn LX BB0; unfold chars_to_limbs4 in OK; lia)) as (ws & HXB & LW);
    clear U8
  end.
  lx_mkR.
  match goal with H4 : mem_inv usegs ?m2, H5 : stk usegs ?m2 lo _, Hf : rw_cells usegs ?m2 (bv_unsigned sp + -48) _ |- _ =>
    eapply (@conv_walk) with (lx := Z.of_nat (length xs)) (xs0 := xs) (blen := blen);
    first [ exact Hf | exact (unlock _ HXhi')
          | refine (conj HXB (conj _ (conj _ (conj _ (conj H4 H5)))));
            [ clear -LW Hn; lia
            | first [exact MU | eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
            | exact WM ]
          | f_equal; klia | klia ] end.
  all: match goal with |- ?g => idtac "LEFT" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
