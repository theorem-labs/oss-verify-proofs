(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_sub_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P008963989194d0df 0 5 0 1 23 4 39 1 49 1 50 1P047c08721393eca7 0 5 0 1 26 4 42 1 52 1 53 1P0624a8633b184eb9 0 5 0 4 25 16 43 4 53 4 54 4P065a3059cc68add4 0 2 0 1 13 1P075cfac158b8a041 0 2 0 1 1 1P0940f5c0b5c2fe2e 0 2 0 1 1 1P0b7abd7f73545a35 0 2 0 1 10 1P0d20fd5ba745099f 0 2 0 1 11 1P0e5516a57c03668c 0 2 0 1 12 1P0f37f8a73c1b0ee8 0 2 0 1 1 1P105351ad60373a0f 0 5 0 4 25 16 43 4 53 4 54 4P10af68bec96a1ec1 0 2 0 1 11 1P10e14de2b79e93f6 0 4 0 1 24 1 35 1 36 1P152399bd2db0f45f 0 2 0 1 27 1P17ed8a8d2c027345 0 5 0 4 25 16 43 4 53 4 54 4P198d9b06dce3625f 0 2 0 1 1 1P19cdef7151929481 0 5 0 1 23 4 39 1 49 1 50 1P1b2ad48a1ed2fa06 0 2 0 1 11 1P1cea46782394b7a4 0 5 0 4 24 16 40 4 49 4 50 4P1df4702f3d36f3db 0 2 0 1 2 1P1ebe1163fb611e25 0 2 0 1 10 1P1f3959e914273e1b 0 2 0 1 2 1P1ff637e323cdbc59 0 3 0 1 25 1 40 1P2011b9a4c89c60eb 0 2 0 1 51 1P204e60d8434acc1e 0 2 0 1 2 1P204f9240fb5cf570 0 5 0 1 25 4 41 1 51 1 52 1P214a816f50aa37c7 0 4 0 1 13 1 26 1 39 1P21d1c5f219487e03 0 2 0 1 53 1P238f717f1098486a 0 3 0 1 25 1 40 1P288ee428b2290d28 0 2 0 1 2 1P2c01afade5f3a6ec 0 2 0 1 2 1P2c48f1aa647fe5ea 0 3 0 1 25 1 40 1P2ce70c8f586d7fcd 0 2 0 1 11 1P2dbefd1860e97dad 0 5 0 4 27 16 45 4 52 4 53 4P2dc37b008b4620c6 0 2 0 1 47 1P2e545b834a7e615b 0 5 0 4 26 16 44 4 53 4 54 4P30b3f7962be2fa69 2 46 0 5 0 1 1 1 20 4 27 4 45 1 0 4 0 1 2 1 28 4 46 1P326cf0d5c64c0269 0 4 0 1 13 1 26 1 39 1P32910371636559af 0 5 0 4 26 16 42 4 51 4 52 4P32e092e8a9481ee2 0 4 0 1 24 1 35 1 36 1P34008ad5b7e018ac 0 2 0 1 1 1P34afd0d914780a6e 0 2 0 1 11 1P3525e9835c0ea151 0 2 0 1 7 1P36e194dada37dfd2 0 2 0 1 51 1P376fa60359e626e3 0 5 0 4 26 16 44 4 53 4 54 4P38995a838be633d2 0 5 0 4 26 16 44 4 52 4 53 4P3bce65661eb2e1b6 0 2 0 1 1 1P3bfea43230abd65c 0 5 0 4 26 16 44 4 53 4 54 4P3c77d047fe13b46c 0 5 0 4 24 16 40 4 49 4 50 4P3ce5172ad3f802b1 0 2 0 1 28 1P3d199ba09f2338d2 0 4 0 1 23 1 34 1 35 1P3d73fef0777c0e51 0 5 0 4 27 16 43 4 52 4 53 4P3da92c116ccfa9e3 0 2 0 1 8 1P3e0196fd0799df42 0 2 0 1 2 1P3f9380538ca3424c 0 2 0 1 47 1N01e4a4d968e25924N033330b62bd150b6N0498c89702a20929N063ea498352422a8N0baec200bc2b40e5N0c106367ca161172N0e664a8ce75a7501N0f387445701b3c6eN0f54db13acc4b20dN0f71360404b8ea66N115e3f676b6699a4N11af39fa799cbd3dN120f8fceef09e6a8N127e8efaa9c1bdefN1316c364a986f0a4N139f00586b34eeb4N1436c718564cea8bN1475cf9aeb3c9436N149cae7af796209aN14bc1c856f2cc67fN153312fa82449298N15e883b6eb943ce3N17db341024270d29N19d50c74d27b6066N1a40fb4bc499c814N1ae39a89b415d6beN1b5fb4d1376b1693N1d790c605989957bN1e27d3502e7b57a7N20c0c134b9849382N20ee0d8110299752N22712b40546f12c5N22cd4703f775eef2N23aa4ecea612b314N23ec18728261871cN252862e853480f51N26bd7dfa2c60b07dN270c22710a21e1ecN273a243c37035cf0N291f3b041ade3e16N2a84428b3b532167N2a9c5147c3ca115cN2ab3ecac57e28911N2abc81dc2c20c91fN2bab9d01f94e4810N2cf85a480d2efdf5N2e8d284ffeb3f802N2e93301107987fa9N2edf204d5a822fabN31e6fab6d547f00eN3208c4619e719bdcN32388801520f9542N32c76086ce5d85bfN34aafb252fd7236cN35ace0afd14df632N35eb4b956f3b5117N36f0bb3ee4eaccbdN3a01b3b4c7f1958fN3a1a46c484ab74d4N3a5b530b0f2381c2N3a79209bb3582b7bN3cbaad65a5da4a17N3cf591f611e80c28N3db9879e5785ccddN3e85e3861d873aafN3efaaa6b7c9d7425N3f7ae9eadaf3d160"%lxh.
Ltac2 gd_tbl_A_mpi_core_sub_int () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_SUB_INT_STACK_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_sub_int_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sub_int_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"].


Definition A_MPI_CORE_SUB_INT : Z := 0xa64ec.
Definition MPI_CORE_SUB_INT_STACK_A : Z := 32.

Definition mpi_core_sub_int_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n c : Z) (xs ys : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_sub_int ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lc',$4.(1.(5.(2.&40.))Lxs',(5.(2.&40.))(6.(7.$0.R13.(8.(9.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(:.O19.)O8.(;.(2.&40.))R3.(<.O1:.)))(6.(=.(>.(?.$4.$4.)(10.$4.$4.O7.(11.O7.(12.+4.O6.)))(>.(?.$4.$4.)(10.$4.$4.(13.(14.&40.O18.)$15.)(14.&40.O18.))(16.(?.$4.$4.))))O1.R3.)(6.(17.O1:.O1.R3.)(6.(18.O1:.R3.)(6.(7.(2.&40.)R?.(19.&40.R2.))(6.(1:.=R2.)(6.(1;.(1:.R2.+1.)(7.$4.R2.O5.))(6.(1<.O1:.R3.O7.R1.)(6.(7.$1=.(1>.(2.&40.)R1.)(1>.(2.&40.)O4.))(6.(7.(5.(2.&40.))(1?.(2.&40.)(20.O6.)R1.)(1?.(2.&40.)(20.O6.)O4.))(6.(7.$4.(13.(21.R1.O6.)(12.R2.(22.+2.(12.+20.O6.))))(13.(21.O3.O6.)O5.))(23.O1:.R3.O2.(14.&40.O18.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_sub_int_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_sub_int ()) "PCS,P,$4.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(24.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$4.PA,$4.Pn,$4.Pc,$4.Plo,$4.Pxs,(5.(2.&40.))Pys,(5.(2.&40.))P,(1<.O3.R8.R7.R2.)P,(25.O3.R9.R7.(26.R2.))P,(6.(1:.=R7.)(1:.R7.+2710.))P,(6.(1:.=R7.)(27.R7.(22.+2.+1?.)))P,(1:.R9.(28.(1>.(2.&40.)R6.)))P,(1:.R:.(28.(1>.(2.&40.)R6.)))P,(1;.(6.(7.$4.R<.R=.)(7.(5.(2.&40.))R7.R8.))(1;.(1:.(11.R<.(12.+4.(28.(1>.(2.&40.)R7.))))R=.)(1:.(11.R=.(12.+4.(28.(1>.(2.&40.)R8.))))R<.)))P,(7.$4.(29.R>.+4.)=)P,(7.$4.(29.R>.+4.)=)P,(27.=R10.)P,(27.=R10.)P,(18.O3.R13.)P,(2:.O2.)P,(2;.O2.R37.)P,(2<.O3.O2.R16.)P,(2=.O3.O2.R39.R17.R16.(12.+4.R14.))P,(2=.O3.O2.R3:.R18.R16.(12.+4.R15.))P,(23.O3.R19.R14.(14.&40.R39.))P,(1:.R15.(13.(14.&40.R3:.)$15.))P,(7.$4.(29.(14.&40.R3;.)+10.)=)P,(2>.R3>.R17.(13.(14.&40.R3<.)R17.))P,(1;.(1:.(11.R1<.(12.+4.(28.(1>.(2.&40.)R17.))))(13.(14.&40.R3=.)$15.))(1:.(14.&40.R3=.)R1<.))P,(1;.(1:.(11.R1<.(12.+4.(28.(1>.(2.&40.)R17.))))(13.(14.&40.R3>.)$15.))(1:.(14.&40.R3>.)R1<.))P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1=.))P,(7.(2.&40.)R37.(19.&40.R1?.))(2?.O3.O2.R45.(30.O3.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R22.R20.R1?.R1=.R1<.R1>.R23.)(8.(9.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(19.&40.O1.)R24.(;.(2.&40.))R23.(<.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A n c lx la lo : Z) (xs0 ys0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Hc : 0 <= c < 2^31.
  Hypothesis Ln : n <= lx /\ n <= la.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis DA : (A = X /\ la = lx /\ ys0 = xs0) \/ A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la <= 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 32.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SX : X + 4 * lx <= bv_unsigned sp - 32 \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_sub_int_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n c xs0 ys0 lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - MPI_CORE_SUB_INT_STACK_A, bv_unsigned sp)].

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i ci : Z) (xs ys : list word) (r8 r9 r31 : word)
      (junk : list (bv 8)) (mm : mem) (ex ea : Z),
    Z.to_nat (n - i) = k -> 0 <= i < n -> 0 <= ci < 2 ^ 31 -> (ci <= 1 \/ ci = c) ->
    ex = X + 4 * i -> ea = A + 4 * i ->
    u32arr asegs mm X xs -> bytes_at asegs mm A (u32s ys) ->
    Z.of_nat (length xs) = lx -> Z.of_nat (length ys) = la ->
    same_from (Z.to_nat i) xs xs0 -> same_from (Z.to_nat i) ys ys0 ->
    sub_int_inv xs i ci ys0 c ->
    aobj asegs AL CS mm X (4 * n) -> aobj asegs AL CS mm A (4 * n) ->
    rw_cells asegs mm (bv_unsigned sp + -32) [CB 8%nat junk; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -32) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR ra SP' gp tp (Z_to_bv 64 1) SB (Z_to_bv 64 1) r8 r9 (Z_to_bv 64 X) (Z_to_bv 64 A) (Z_to_bv 64 ci)
               (Z_to_bv 64 n) (Z_to_bv 64 ea) (Z_to_bv 64 ex) (Z_to_bv 64 i) (Z_to_bv 64 1)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 ea) (Z_to_bv 64 ex) r31)
          F (Z_to_bv 64 0xa6540) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ci xs ys r8 r9 r31 junk mm ex ea Hk Hi Hci1 Hci2 Ex Ea HX HA LX LA FX FA INV
      OX OA FR ST MU WM MI; [exfalso; xlia Hk Hi|].
    pose proof (cs_ok_sb _ _ CSOK) as SB64. unfold MPI_CORE_SUB_INT_STACK_A in MU.
    lx_limb_ro HA FA i Ea (proj1 Hi) ltac:(xlia Hi LA Ln) wa VA. lx_limb_rw HX i Ex (proj1 Hi) ltac:(xlia Hi LX Ln) wx NX.
    lx_hide MU. lx_hide WM. lx_hide HX.
    lx_run_tac (PLAN [0xa6540] [(0xa6564, DJoin); (0xa658c, DJoin)] 120%N); lx_tree.
    all: lx_unhide; lx_gc.
    (* [comment removed for export] *)
    all: destruct (lx_core_sub_int_exact wa ci _ Hci1 eq_refl) as [Hc' V].
    all: lx_rn_rw ex CX'; lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'.
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX (proj1 Hi) Ex MUl WMl CX') as HX';
         pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(xlia Ex Hi) ltac:(xlia Ex Hi)) as MU';
         pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    - (* [comment removed for export] *)
      lx_rn_rw (bv_unsigned sp + -32) FR'. lx_rn_aobj X OX'. lx_rn_aobj A OA'.
      assert (BR : i + 2 <= n) by (match goal with K : _ |- _ => clear - K Hi; lia end).
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DA HX' LX FX HA LA FA ltac:(xlia Hi Ln) Ex MUl) as (ys' & HA' & LA' & FA').
      eapply (IH (i + 1)); [xlia Hk Hi | xlia Hi BR | xlia Hc' | left; xlia Hc' | xlia Ex | xlia Ea
        | exact HX' | exact HA' | exact (upd_length_Z _ _ _ _ LX) | exact LA'
        | exact (same_from_upd_Z _ _ _ _ FX (proj1 Hi)) | exact (same_from_S_Z _ _ _ FA' (proj1 Hi))
        | exact (sub_int_inv_next _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA V)
        | exact OX' | exact OA' | exact FR' | exact ST' | exact MU' | exact WM' | exact MI' ].
    - (* [comment removed for export] *)
      assert (BR : n <= i + 1) by (match goal with K : _ |- _ => clear - K Hi; lia end).
      lx_post.
      all: lazymatch goal with
           | |- munch _ _ _ => exact MU'
           | |- wmono _ _ _ => exact WM'
           | |- u32arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_length; xlia LX L0
           | |- skipn _ _ = skipn _ _ => eapply skipn_upd_Z; [exact FX | xlia Hi | xlia Hi BR | xlia LX L0]
           | |- lval _ ?nn - _ = _ => replace nn with (i + 1) by xlia Hi BR; exact (sub_int_inv_next _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA V)
           | |- _ <= 1 \/ _ = _ => left; xlia Hc'
           | |- _ => first [reflexivity | assumption | xlia Hc']
           end.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma A_mpi_core_sub_int_spec : forall AL, asan_img_ok AL -> mpi_core_sub_int_stmtA asegs AL A_MPI_CORE_SUB_INT.
Proof.
  intros AL IMG. unfold mpi_core_sub_int_stmtA, A_MPI_CORE_SUB_INT.
  intros until ys. intros HX HA Hn Hc LX LA DA ALX ALA NZX NZA MI ALWF CSOK ABS OX OA ST LO SPA SCS SX SA -> -> -> ->.
  pose (lxi := lxA_img AL IMG).
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_SUB_INT_STACK_A in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB.
  pose proof (proj1 ST) as LO0.
  carve_frame 32%nat ST.
  lx_run_tac (PLAN [0xa6540] [] 80%N); lx_tree.
  all: lx_gc.
  - (* [comment removed for export] *)
    match goal with K : 0 <= - n |- _ => rename K into BR end.
    lx_post. all: first [reflexivity | eassumption | right; reflexivity | xlia Hc
                        | replace n with 0 by xlia Hn BR; rewrite !lval_0; change (2 ^ (32 * 0)) with 1; xlia0 | idtac].
    all: match goal with |- ?g => idtac "N0-LEFT:" g end.
  - (* [comment removed for export] *)
    match goal with K : 0 <= n + _ |- _ => rename K into BR end.
    eapply (@loop_walk AL IMG ALWF CS CSOK) with (X := X) (A := A) (n := n) (c := c) (lo := lo)
             (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (xs0 := xs) (ys0 := ys)
             (k := Z.to_nat (n - 0)) (i := 0) (ci := c) (xs := xs) (ys := ys).
    all: try assumption.
    all: lazymatch goal with
         | |- (_ = _ /\ _) \/ _ => destruct DA as [[EA EY]|DA']; [left; subst; repeat split; reflexivity | right; exact DA']
         | |- _ <= 1 \/ _ = _ => right; reflexivity
         | |- same_from _ _ _ => apply same_from_refl
         | |- sub_int_inv _ _ _ _ _ => apply sub_int_inv_0
         | |- 0 <= 0 < _ => xlia BR
         | |- _ /\ _ => first [xlia LX LA | xlia XB NZX | xlia AB NZA | xlia0]
         | |- _ => first [ eassumption | reflexivity | xlia0 ]
         end.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
