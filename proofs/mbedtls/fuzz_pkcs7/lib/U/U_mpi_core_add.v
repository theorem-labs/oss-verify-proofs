(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_core_add () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_ADD_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_add_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.add_inv"].


Definition U_MPI_CORE_ADD : Z := 0x23698.

(* [comment removed for export] *)
Definition MPI_CORE_ADD_STACK : Z := 48.

Definition mpi_core_add_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n : Z) (xs ys zs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_add ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lc,$4.(1.(5.(2.&40.))Lxs',(5.(2.&40.))(6.(7.$0.R13.(8.(9.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(:.O19.)O8.(;.(2.&40.))R3.(<.O1:.)))(6.(=.(>.(?.$4.$4.)(10.$4.$4.O7.(11.O7.(12.+4.O6.)))(>.(?.$4.$4.)(10.$4.$4.(13.(14.&40.O18.)$15.)(14.&40.O18.))(16.(?.$4.$4.))))O1.R3.)(6.(17.O1:.O1.R3.)(6.(18.O1:.R3.)(6.(7.(2.&40.)R?.(19.&40.R2.))(6.(6.(1:.=R2.)(1:.R2.+1.))(6.(1;.O1:.R3.O7.R1.)(6.(7.$1<.(1=.(2.&40.)R1.)(1=.(2.&40.)O5.))(6.(7.(5.(2.&40.))(1>.(2.&40.)(1?.O6.)R1.)(1>.(2.&40.)(1?.O6.)O5.))(6.(7.$4.(11.(20.R1.O6.)(12.R2.(21.+2.(12.+20.O6.))))(11.(20.O4.O6.)(20.O3.O6.)))(22.O1:.R3.O2.(14.&40.O18.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_add_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_add ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$4.PA,$4.PB,$4.Pn,$4.Plo,$4.Pxs,(5.(2.&40.))Pys,(5.(2.&40.))Pzs,(5.(2.&40.))P,(1;.O2.R9.R8.R3.)P,(24.O2.R:.R8.(25.R3.))P,(24.O2.R;.R8.(25.R3.))P,(6.(1:.=R8.)(1:.R8.+2710.))P,(1:.R9.(26.(1=.(2.&40.)R7.)))P,(1:.R:.(26.(1=.(2.&40.)R7.)))P,(1:.R;.(26.(1=.(2.&40.)R7.)))P,(27.(6.(7.$4.R>.R?.)(7.(5.(2.&40.))R9.R:.))(27.(1:.(11.R>.(12.+4.(26.(1=.(2.&40.)R9.))))R?.)(1:.(11.R?.(12.+4.(26.(1=.(2.&40.)R:.))))R>.)))P,(27.(6.(7.$4.R>.R10.)(7.(5.(2.&40.))R9.R;.))(27.(1:.(11.R>.(12.+4.(26.(1=.(2.&40.)R9.))))R10.)(1:.(11.R10.(12.+4.(26.(1=.(2.&40.)R;.))))R>.)))P,(7.$4.(28.R11.+4.)=)P,(7.$4.(28.R11.+4.)=)P,(7.$4.(28.R11.+4.)=)P,(29.=R14.)P,(29.=R14.)P,(29.=R14.)P,(22.O2.R18.R13.(14.&40.R38.))P,(1:.R14.(13.(14.&40.R39.)$15.))P,(7.$4.(28.(14.&40.R3:.)+10.)=)P,(27.(1:.(11.R1:.(12.+4.(26.(1=.(2.&40.)R15.))))R16.)(1:.(14.&40.R3;.)R1:.))P,(27.(1:.(11.R1:.(12.+4.(26.(1=.(2.&40.)R15.))))R17.)(1:.(14.&40.R3<.)R1:.))P,(27.(1:.(11.R1:.(12.+4.(26.(1=.(2.&40.)R15.))))R18.)(1:.(14.&40.R3=.)R1:.))P,(18.O2.R1>.)P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1>.))(2:.O2.(2;.O2.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R22.R1?.R1=.R1<.R1;.R1>.R23.)(8.(9.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(19.&40.O1.)R24.(;.(2.&40.))R23.(<.O2.)))")
(* [comment removed for export] *).

Lemma lx_core_add_exact_u : forall (wa wb : word) (c c' : Z), 0 <= c <= 1 ->
  c' = Z.b2z (zlow 64 (zswrap 32 (zlow 32 (c + zswrap 32 (zlow 32 (bv_unsigned wa))))) <? zlow 64 (zswrap 32 (zlow 32 (bv_unsigned wa))))
     + Z.b2z (zlow 64 (zswrap 32 (zlow 32 (zswrap 32 (zlow 32 (bv_unsigned wb)) + zswrap 32 (zlow 32 (c + zswrap 32 (zlow 32 (bv_unsigned wa)))))))
              <? zlow 64 (zswrap 32 (zlow 32 (bv_unsigned wb)))) ->
  (0 <= c' <= 1) /\
  w32 (Z_to_bv 64 (zswrap 32 (zlow 32 (zswrap 32 (zlow 32 (bv_unsigned wb)) + zswrap 32 (zlow 32 (c + zswrap 32 (zlow 32 (bv_unsigned wa))))))))
    + 2 ^ 32 * c' = w32 wa + w32 wb + c.
Proof.
  intros wa wb c c' Hc ->.
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  unfold w32. change (zlow 32 (bv_unsigned wa)) with (bv_unsigned wa mod 2^32). change (zlow 32 (bv_unsigned wb)) with (bv_unsigned wb mod 2^32).
  set (ua := bv_unsigned wa mod 2^32) in *. set (ub := bv_unsigned wb mod 2^32) in *.
  destruct (lx_s32_cases ua ltac:(lia)) as [Ea Ua]. rewrite Ua.
  assert (Et : zlow 32 (c + zswrap 32 ua) = (c + ua) mod 2^32).
  { unfold zlow. rewrite Ea. destruct (ua <? 2^31); [reflexivity|]. rewrite <- (Z.mod_add _ 1) by lia. f_equal. lia. }
  rewrite Et. pose proof (Z.mod_pos_bound (c + ua) (2^32) ltac:(lia)) as Rt. set (tt := (c + ua) mod 2^32) in *.
  destruct (lx_s32_cases tt ltac:(lia)) as [Etz Ut]. rewrite Ut.
  destruct (lx_s32_cases ub ltac:(lia)) as [Eb Ub].
  assert (Et2 : zlow 32 (zswrap 32 ub + zswrap 32 tt) = (ub + tt) mod 2^32).
  { unfold zlow. rewrite Eb, Etz. destruct (ub <? 2^31); destruct (tt <? 2^31);
    first [reflexivity | rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia | rewrite <- (Z.mod_add _ 2) by lia; f_equal; lia]. }
  rewrite Et2. pose proof (Z.mod_pos_bound (ub + tt) (2^32) ltac:(lia)) as Rt2. set (tt2 := (ub + tt) mod 2^32) in *.
  destruct (lx_s32_cases tt2 ltac:(lia)) as [Et2z Ut2]. rewrite Ut2. rewrite Ub.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (zswrap 32 tt2)) with (zlow 64 (zswrap 32 tt2)). rewrite Ut2.
  assert (E1 : (if tt <? 2^31 then tt else tt + 2^64 - 2^32) <? (if ua <? 2^31 then ua else ua + 2^64 - 2^32) = (tt <? ua)).
  { clear - Rt Ra. destruct (Z.ltb_spec tt (2^31)); destruct (Z.ltb_spec ua (2^31)); destruct (Z.ltb_spec tt ua);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  assert (E2 : (if tt2 <? 2^31 then tt2 else tt2 + 2^64 - 2^32) <? (if ub <? 2^31 then ub else ub + 2^64 - 2^32) = (tt2 <? ub)).
  { clear - Rt2 Rb. destruct (Z.ltb_spec tt2 (2^31)); destruct (Z.ltb_spec ub (2^31)); destruct (Z.ltb_spec tt2 ub);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  rewrite E1, E2.
  assert (W : (if tt2 <? 2^31 then tt2 else tt2 + 2^64 - 2^32) mod 2^32 = tt2).
  { destruct (tt2 <? 2^31). apply Z.mod_small; lia. rewrite <- (Z.mod_add _ (1 - 2^32)) by lia. rewrite Z.mod_small; lia. }
  rewrite W.
  assert (Ett : tt = c + ua - (if c + ua <? 2^32 then 0 else 2^32)).
  { subst tt. destruct (Z.ltb_spec (c + ua) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (Ett2 : tt2 = ub + tt - (if ub + tt <? 2^32 then 0 else 2^32)).
  { subst tt2. destruct (Z.ltb_spec (ub + tt) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  clearbody ua ub tt tt2. clear - Hc Ra Rb Rt Rt2 Ett Ett2.
  destruct (Z.ltb_spec (c + ua) (2^32)); destruct (Z.ltb_spec (ub + tt) (2^32));
  destruct (Z.ltb_spec tt ua); destruct (Z.ltb_spec tt2 ub); cbn [Z.b2z]; lia.
Qed.

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A B n lx la lb lo : Z) (xs0 ys0 zs0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx /\ n <= la /\ n <= lb.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  (* [comment removed for export] *)
  Hypothesis DA : (A = X /\ la = lx /\ ys0 = xs0) \/ A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis DB : (B = X /\ lb = lx /\ zs0 = xs0) \/ B + 4 * lb <= X \/ X + 4 * lx <= B.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la <= 2^64.
  Hypothesis BB : 0 < B /\ B + 4 * lb <= 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis ALB : B mod 4 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - MPI_CORE_ADD_STACK.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= lo \/ bv_unsigned sp <= A.
  Hypothesis SB' : B + 4 * lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_add_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n xs0 ys0 zs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - MPI_CORE_ADD_STACK, bv_unsigned sp)].

  (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i c : Z) (xs ys zs : list word) (x3 x4 : word) (mm : mem) (j : list byte)
      (ex ea eb : Z),
    Z.to_nat (n - i) = k -> 0 <= i < n -> 0 <= c <= 1 ->
    ex = X + 4 * i -> ea = A + 4 * i -> eb = B + 4 * i ->
    u32arr usegs mm X xs -> bytes_at usegs mm A (u32s ys) -> bytes_at usegs mm B (u32s zs) ->
    Z.of_nat (length xs) = lx -> Z.of_nat (length ys) = la -> Z.of_nat (length zs) = lb ->
    same_from (Z.to_nat i) xs xs0 -> same_from (Z.to_nat i) ys ys0 -> same_from (Z.to_nat i) zs zs0 ->
    add_inv xs i c ys0 zs0 ->
    stk usegs mm lo (bv_unsigned sp + -48) -> length j = 8%nat ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 (le_bytes_to_word j); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
    munch [(X, X + 4 * n); (bv_unsigned sp + -48, bv_unsigned sp)] m mm -> wmono usegs m mm -> mem_inv usegs mm ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1)
             (Z_to_bv 64 ea) (Z_to_bv 64 eb) (Z_to_bv 64 X) (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 n)
             (Z_to_bv 64 c) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 ex) x3 x4
             s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 ex) (Z_to_bv 64 eb) (Z_to_bv 64 ea))
          F (Z_to_bv 64 0x23704) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    unfold MPI_CORE_ADD_STACK in *.
    induction k as [|k IH]; intros i c xs ys zs x3 x4 mm j ex ea eb Hk Hi Hc Ex Ea Eb HX HA HB LX LA LB FX FA FB INV
      ST LXJ FR MU WM MI; [exfalso; xlia Hk Hi|].
    (* [comment removed for export] *)
    lx_limb_ro HA FA i Ea (proj1 Hi) ltac:(xlia Hi LA Ln) wa VA. lx_limb_ro HB FB i Eb (proj1 Hi) ltac:(xlia Hi LB Ln) wb VB.
    lx_limb_rw HX i Ex (proj1 Hi) ltac:(xlia Hi LX Ln) wx NX.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. lx_hide HX.
    pose proof (munch_refl ([] : list ivl) mm) as MUl0. pose proof (wmono_refl usegs mm) as WMl0.
    lx_run_tac (PLAN [0x23704] [] 80%N); lx_tree.
    all: lx_unhide; lx_gc; try clear MUl0; try clear WMl0.
    (* [comment removed for export] *)
    all: lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?cv) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
           destruct (lx_core_add_exact_u wa wb c cv Hc eq_refl) as [Hc' V] end.
    all: lx_rn_rw ex CX'; lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'.
    all: try lx_rn_rw (bv_unsigned sp + -48) FR'.
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX (proj1 Hi) Ex MUl WMl CX') as HX';
         pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(xlia Ex Hi) ltac:(xlia Ex Hi)) as MU';
         pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23704) _ _ _ _) =>
      (* [comment removed for export] *)
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DA HX' LX FX HA LA FA ltac:(xlia Hi Ln) Ex MUl) as (ys' & HA' & LA' & FA');
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DB HX' LX FX HB LB FB ltac:(xlia Hi Ln) Ex MUl) as (zs' & HB'' & LB'' & FB');
      eapply (IH (i + 1)); [xlia Hk Hi | klia | exact Hc' | xlia Ex | xlia Ea | xlia Eb
        | exact HX' | exact HA' | exact HB''
        | exact (upd_length_Z _ _ _ _ LX) | exact LA' | exact LB''
        | exact (same_from_upd_Z _ _ _ _ FX (proj1 Hi)) | exact (same_from_S_Z _ _ _ FA' (proj1 Hi)) | exact (same_from_S_Z _ _ _ FB' (proj1 Hi))
        | exact (add_inv_next _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA VB V)
        | exact ST' | exact LXJ | exact FR' | exact MU' | exact WM' | exact MI' ]
    | |- _ =>
      (* [comment removed for export] *)
      lx_post;
      lazymatch goal with
           | |- munch _ _ _ => exact MU'
           | |- wmono _ _ _ => exact WM'
           | |- u32arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_length; xlia LX L0
           | |- skipn _ _ = skipn _ _ => eapply skipn_upd_Z; [exact FX | xlia Hi | klia | xlia LX L0]
           | |- lval _ ?nn + _ = _ => replace nn with (i + 1) by klia; exact (add_inv_next _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA VB V)
           | |- _ => first [reflexivity | assumption | xlia Hc']
           end
    end.
  Qed.
End Walk.

Lemma U_mpi_core_add_spec : mpi_core_add_stmt usegs U_MPI_CORE_ADD.
Proof.
  unfold mpi_core_add_stmt, U_MPI_CORE_ADD.
  intros until zs. intros HX HA HB Hn LX LA LB DA DB ALX ALA ALB NZX NZA NZB ST LO SPA SX SA SB MI -> -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  unfold MPI_CORE_ADD_STACK in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB. pose proof (u32ro_bound _ _ _ _ HB) as BB.
  pose proof (proj1 ST) as LO0.
  (* [comment removed for export] *)
  carve_frame 48%nat ST; lxp_split_frame [8;8;8;8;8;8]%nat.
  lx_run_tac (PLAN [0x23704] [] 80%N); lx_tree.
  all: lx_gc; try lx_same_mem.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23704) _ _ _ _) =>
    eapply (@loop_walk) with (X := X) (A := A) (B := B) (n := n) (lo := lo)
             (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (lb := Z.of_nat (length zs))
             (xs0 := xs) (ys0 := ys) (zs0 := zs) (k := Z.to_nat (n - 0)) (i := 0) (c := 0) (xs := xs) (ys := ys) (zs := zs) (j := j);
    try assumption;
    lazymatch goal with
         | |- _ \/ _ => first [ destruct DA as [[EA EY]|DA']; [left; subst; repeat split; reflexivity | right; exact DA']
                              | destruct DB as [[EB EZ]|DB']; [left; subst; repeat split; reflexivity | right; exact DB'] ]
         | |- same_from _ _ _ => apply same_from_refl
         | |- add_inv _ _ _ _ _ => apply add_inv_0
         | |- 0 <= 0 < _ => klia
         | |- _ /\ _ => first [xlia LX LA LB | xlia XB NZX | xlia AB NZA | xlia BB NZB | xlia0]
         | |- munch _ _ _ => first [eassumption | exact MU | apply munch_refl]
         | |- wmono _ _ _ => first [eassumption | exact WM | apply wmono_refl]
         | |- _ => first [ eassumption | reflexivity | xlia0 | klia ]
         end
  | |- _ =>
    (* [comment removed for export] *)
    (let xn := constr:(n) in match goal with K : (zlow 64 xn =? zlow 64 0) = true |- _ =>
       apply Z.eqb_eq in K; unfold zlow in K; rewrite (Z.mod_small n) in K by lia; assert (BR : 0 <= - n) by (rewrite K; reflexivity) end);
    lx_post; first [reflexivity | eassumption | apply munch_refl | apply wmono_refl | xlia Hn BR | rewrite !lval_nonpos by xlia Hn BR; xlia0 | idtac]
  end.
Qed.
