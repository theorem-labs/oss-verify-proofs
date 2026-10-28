(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_add_if.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00223f456176bc47 0 2 0 1 2 1P0165394dfcd290ec 2 56 1 1 4 6 0 1 2 1 17 4 29 4 47 1 50 1 2 30 1 61 1 1 1 4 6 0 1 1 1 18 4 29 4 48 1 49 1 2 30 1 61 1P01a537e4137aeec0 0 5 0 4 26 16 44 4 55 4 56 4P01b5e65e4ce8d621 0 2 0 1 2 1P02636757aa759716 0 2 0 1 1 1P02849cff9e37cb4e 0 2 0 1 10 1P04591feac6c0610d 0 2 0 1 2 1P07618cae296420d4 0 3 0 1 27 1 44 1P08557aaba3bf8817 0 4 0 1 24 1 35 1 36 1P08a5267b7a506119 0 2 0 1 59 1P0a1d257d8dbcae1f 2 56 1 1 16 6 0 4 3 4 51 4 54 16 62 4 63 4 2 31 1 64 1 0 7 0 1 2 1 19 4 30 4 50 1 62 1 63 1P0af9153d838a029c 0 3 0 1 27 1 44 1P0c464316a0c63f9f 0 2 0 1 57 1P0e6d7bf5e8aa9a7c 0 5 0 1 27 4 45 1 57 1 58 1P0ec00157654e6694 1 1 4294967296 1 36 1 3 0 1 14 1 37 1P0f3644df36c8cfc5 0 5 0 4 28 16 48 4 59 4 60 4P0ff0d25503591532 0 2 0 1 2 1P10df121df97fe87c 0 5 0 4 26 16 44 4 55 4 56 4P112acaf05b6c265a 0 5 0 4 27 16 47 4 59 4 60 4P116d33c11bcc157c 0 2 0 1 11 1P12e1018efd3e56da 0 2 0 1 13 1P13105e70edcf48c1 0 2 0 1 51 1P1410af0e1efedcd6 0 3 0 1 59 1 61 1P14df7ecfae7f8225 0 5 0 1 28 4 46 1 58 1 59 1P14e2d20c534db469 0 2 0 1 7 1P1536d3609afde5d5 0 4 0 1 23 1 34 1 35 1P15b7db4e5e7423d9 0 3 0 1 30 1 59 1P19622cc3614385fb 0 5 0 1 25 4 43 1 55 1 56 1P1a09c5021a7b018d 0 2 0 1 1 1P1bc14b04fbbbef29 1 1 4294967296 1 0 1 2 13 1 34 1P1c47c756f59bf563 0 3 0 1 60 1 62 1P1d75f34c8391e8b7 0 5 0 4 29 16 47 4 58 4 59 4P1e26565c421f826b 0 2 0 1 1 1P1e9fae41a44384f2 0 2 0 1 59 1P1ec433cb4d75f5ec 0 2 0 1 1 1P1edcce6bf4a01c75 0 5 0 4 28 16 48 4 59 4 60 4P20145952d2e3890a 0 2 0 1 8 1P241b1be6503acb60 0 3 0 1 27 1 44 1P24a007090e22c0c4 0 4 0 1 13 1 28 1 43 1P261dca5bdb91047a 0 2 0 1 1 1P265a5f50c47e6778 0 5 0 1 25 4 43 1 55 1 56 1P273b84fb09a1aefb 0 2 0 1 59 1P29324d572ed3f0d5 0 2 0 1 57 1P2967822bb72d5191 0 2 0 1 11 1P2b245e1c52425d57 0 5 0 4 28 16 48 4 59 4 60 4P2bae7c4c15c8393e 0 5 0 4 28 16 46 4 57 4 58 4P2bd3abab4b522b5a 0 5 0 4 27 16 47 4 59 4 60 4P2bd547db7b828388 0 2 0 1 11 1P2cd69ae3087d823d 0 2 0 1 11 1P2d93ca83c91fe5bc 0 4 0 1 24 1 35 1 36 1P30834af18afabdcf 0 2 0 1 2 1P30b6b8f208672279 0 3 0 4294967296 13 4294967296 35 1P319a3ee40c036a89 0 2 0 1 11 1P326e15b78bbd115e 0 5 0 4 27 16 47 4 59 4 60 4P335bd8ac372366d3 0 2 0 1 12 4294967296P33685b9ed7e99944 0 2 0 1 12 1P340b21423d422331 0 2 0 1 1 1P3431dc257c7b5498 0 2 0 1 59 1P35dc14a9f0d25cb5 0 5 0 4 29 16 49 4 58 4 59 4P390c22b884f56138 0 2 0 1 51 1P39590d96540a46f9 0 4 0 1 13 1 28 1 43 1P3a476f09db29a6b8 0 2 0 1 10 1P3ae209ff70e84f75 0 5 0 4 28 16 48 4 58 4 59 4P3cef1a83e82363c8 2 50 0 5 0 1 1 1 18 4 29 4 49 1 0 4 0 1 2 1 30 4 50 1P3d608d28febc7244 0 2 0 1 2 1N00aa362dd2bde9e0N0214408a3f657a4cN022a8c89ef9837c7N0370cd266f4c0da9N0371657ae8919e44N050c53f49103cf07N0571313e5c34226cN063e517b90e633b1N06ea1db4fe25bed4N06f2fa0b4911de14N07fe3c436dfb3faeN089f7298d555c5faN094909b44b4e89b4N09dcb355f156d89fN09e235e38bffb75dN0c4c668c337280e3N0cf2119340929389N0dd18ec05065ae53N0e146ab7107ba474N0fd1d024f69a5920N1079a6c4997885dbN1311f8f3247b6eb1N146bbe108ff68940N148caa921afcbbb3N14d370ab7fcc2f47N15d8d6e6ea5e3815N17a052731df7dac4N18431841afb8972eN1859ea98b63ddf8fN1b3b1d8fc6967865N1c8139794c64494fN1cf4e1a5dbc1a074N1e94d0b26b47f65aN1f0b4d7e52d4a7deN203c9690ca74a9afN21c3b3d49722a955N221cb123c887d9a9N22346187640cc7e5N22378322af71c580N225227231e7100efN23e4fe13b0c41861N249fd92bbd9742f0N258fe88df3fc744bN26330b7249e2307cN26c7b76bb9358015N26ca3be31651e5e9N277016e94f46531dN2785a538db9020d2N27e4a9ae10624770N299490d0e550e0d7N29a8f95c5f9ab273N2b4ef80ec033c577N2ba7d7a70d232900N2bccaa69224365f1N2dfe4e70a66b569cN2e396ecb5b25615fN2e5088d517405c27N2e9d5684ba2a2473N2f2daaf012fc5657N302da736f3c7ccb6N3068da7712372f76N323ef3efaffe8471N3292f72adde8122eN32c174508ea5ecdbN338bffb45028f385N3419c020c4821e15N3487ae8a8020b83aN34b53081edcf4a81N34ebb85062105357N36393180e880fee1N366b0d0f78127084N3788d509c1ccb320N383d0f37d37b7658N38445d0395c8ec58N387dc525d654f35fN3a511b7ba682757fN3a52abcc7fe29ed1N3adabae5e44c9578N3b957901d4c2bf8aN3bab9c1f2eca458aN3bb986387195267aN3bc5bb2544b71ac1N3c9d7beaf8eb7e10N3ce2fc35812a98ddN3dd852250a8dd73fN3e1a536db0f0d838N3ea7b505f602e0e4N3edf8577b096ce4aN3f8baff9223157b2"%lxh.
Ltac2 gd_tbl_A_mpi_core_add_if () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_ADD_IF_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_add_if_postB"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Definition A_MPI_CORE_ADD_IF : Z := 0xa47ec.
Definition MPI_CORE_ADD_IF_STACK_A : Z := 32.

Definition mpi_core_add_if_postB (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n cond : Z) (xs ys : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (c : Z) (xs' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(X, X + 4 * n); (bv_unsigned sp - MPI_CORE_ADD_IF_STACK_A, bv_unsigned sp)] m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ a0 = Z_to_bv 64 c /\ 0 <= c <= 1
    /\ u32arr segs m' X xs' /\ length xs' = length xs
    /\ skipn (Z.to_nat n) xs' = skipn (Z.to_nat n) xs
    /\ lval xs' n + c * 2^(32 * n) = lval xs n + (if cond =? 0 then 0 else lval ys n)
    /\ stk segs m' lo (bv_unsigned sp).

Definition mpi_core_add_if_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_add_if ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))PX,$0.PA,$0.Pn,$0.Pcond,$0.Plo,$0.Pxs,(4.(1.&40.))Pys,(4.(1.&40.))P,(5.O3.R8.R7.R2.)P,(6.O3.R9.R7.(7.R2.))P,(8.(9.=R7.)(9.R7.+2710.))P,(9.R8.(:.(;.(1.&40.)R5.)))P,(9.R9.(:.(;.(1.&40.)R5.)))P,(8.(9.=R9.)(<.R9.(=.+2.+20.)))P,(>.(9.(?.R<.(10.+4.(:.(;.(1.&40.)R7.))))R=.)(9.(?.R=.(10.+4.(:.(;.(1.&40.)R8.))))R<.))P,(11.$0.(12.R>.+4.)=)P,(11.$0.(12.R>.+4.)=)P,(<.=R10.)P,(<.=R10.)P,(13.O3.R13.)P,(14.O2.)P,(15.O2.R37.)P,(16.O3.O2.R16.)P,(17.O3.O2.R39.R17.R16.(10.+4.R14.))P,(17.O3.O2.R3:.R18.R16.(10.+4.R15.))P,(18.O3.R19.R14.(19.&40.R39.))P,(9.R15.(1:.(19.&40.R3:.)$1;.))P,(11.$0.(12.(19.&40.R3;.)+10.)=)P,(1<.R3>.R17.(1:.(19.&40.R3<.)R17.))P,(>.(9.(?.R1<.(10.+4.(:.(;.(1.&40.)R17.))))(1:.(19.&40.R3=.)$1;.))(9.(19.&40.R3=.)R1<.))P,(>.(9.(?.R1<.(10.+4.(:.(;.(1.&40.)R17.))))(1:.(19.&40.R3>.)$1;.))(9.(19.&40.R3>.)R1<.))P,(11.(1.&40.)R37.(1=.&40.R1>.))P,(11.(1.&40.)R37.(1=.&40.R1>.))P,(11.(1.&40.)R37.(1=.&40.R1>.))P,(11.(1.&40.)R37.(1=.&40.R1>.))(1>.O3.O2.R45.(1?.O3.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R22.R20.R1?.R1=.R1<.R1>.R23.)(20.(21.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(1=.&40.O1.)R24.(22.(1.&40.))R23.(23.O3.)))")
(* [comment removed for export] *).

Lemma addif_inv_next : forall (l l0 ly : list word) (i c c' cnd : Z) (wx wa v : word),
  addif_inv l i c l0 ly cnd -> 0 <= i -> (Z.to_nat i < length l)%nat ->
  limb32 l0 (Z.to_nat i) = w32 wx -> limb32 ly (Z.to_nat i) = w32 wa ->
  w32 v + 2 ^ 32 * c' = w32 wx + (if cnd =? 0 then 0 else w32 wa) + c ->
  addif_inv (upd l (Z.to_nat i) v) (i + 1) c' l0 ly cnd.
Proof.
  intros l l0 ly i c c' cnd wx wa v INV Hi HL VX VA V.
  eapply addif_inv_step; [exact Hi | exact INV | apply lval_upd_ge; lia | rewrite (limb32_upd_same _ _ _ HL), VX, VA; exact V].
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A n cond lx la lo : Z) (xs0 ys0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx /\ n <= la.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LA : Z.of_nat (length ys0) = la.
  Hypothesis DA : A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la <= 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis HC : 0 <= cond < 2^32.
  Hypothesis MR : 0 <= ct_mask cond <= 18446744073709551615.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 32.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SX : X + 4 * lx <= bv_unsigned sp - 32 \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis HA0 : bytes_at asegs m A (u32s ys0).

  Notation POST := (mpi_core_add_if_postB asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cond xs0 ys0 lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - MPI_CORE_ADD_IF_STACK_A, bv_unsigned sp)].

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i c : Z) (xs : list word) (r8 r9 r18 : word) mm (ex ea mk : Z),
    Z.to_nat (n - i) = k -> 0 <= i < n -> 0 <= c <= 1 ->
    ex = X + 4 * i -> ea = A + 4 * i -> mk = (if cond =? 0 then 0 else -1) ->
    u32arr asegs mm X xs -> Z.of_nat (length xs) = lx -> same_from (Z.to_nat i) xs xs0 ->
    addif_inv xs i c xs0 ys0 cond ->
    bytes_at asegs mm A (u32s ys0) ->
    aobj asegs AL CS mm X (4 * n) -> aobj asegs AL CS mm A (4 * n) ->
    rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] -> stk asegs mm lo (bv_unsigned sp + -32) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR ra SP' gp tp (Z_to_bv 64 1) (Z_to_bv 64 mk) SB r8 r9 (Z_to_bv 64 X) (Z_to_bv 64 A) (Z_to_bv 64 n)
               (Z_to_bv 64 c) (Z_to_bv 64 ea) (Z_to_bv 64 ex) (Z_to_bv 64 i) (Z_to_bv 64 1)
               r18 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 ea) (Z_to_bv 64 ex))
          F (Z_to_bv 64 0xa4864) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros i c xs r8 r9 r18 mm ex ea mk Hk Hi Hc Ex Ea Emk HX LX FX INV HA OX OA FR ST MU WM MI;
      [exfalso; xlia Hk Hi|].
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    lx_limb_ro HA (same_from_refl (Z.to_nat i) ys0) i Ea (proj1 Hi) ltac:(xlia Hi LA Ln) wa VA.
    lx_limb_rw HX i Ex (proj1 Hi) ltac:(xlia Hi LX Ln) wx NX.
    pose proof (same_from_limb32 _ _ _ _ _ FX (PeanoNat.Nat.le_refl _) NX) as VX0.
    lx_hide MU. lx_hide WM. lx_hide HX.
    lx_run_tac (PLAN [0xa4864] [(0xa4888, DJoin); (0xa48b0, DJoin)] 120%N); lx_tree.
    all: lx_unhide; lx_gc.
    (* [comment removed for export] *)
    all: first [ lazymatch goal with DEF : ?cv = Z.b2z _ + Z.b2z _ |- _ =>
                   destruct (lx_core_addif_exact wx wa c cv mk cond Hc Emk DEF) as [Hc' V]; clear DEF end
               | lazymatch goal with |- context [Z_to_bv 64 (Z.b2z ?b1 + Z.b2z ?b2)] =>
                   destruct (lx_core_addif_exact wx wa c (Z.b2z b1 + Z.b2z b2) mk cond Hc Emk eq_refl) as [Hc' V] end ].
    all: lx_rn_rw ex CX'; lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_ro32 A HA'.
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX (proj1 Hi) Ex MUl WMl CX') as HX';
         pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(xlia Ex Hi) ltac:(xlia Ex Hi)) as MU';
         pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    - (* [comment removed for export] *)
      lx_rn_rw (bv_unsigned sp + -32) FR'. lx_rn_aobj X OX'. lx_rn_aobj A OA'.
      assert (BR : i + 2 <= n) by (match goal with K : _ |- _ => clear - K Hi; lia end).
      eapply (IH (i + 1)); [xlia Hk Hi | xlia Hi BR | exact Hc' | xlia Ex | xlia Ea | exact Emk
        | exact HX' | exact (upd_length_Z _ _ _ _ LX) | exact (same_from_upd_Z _ _ _ _ FX (proj1 Hi))
        | exact (addif_inv_next _ _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VX0 VA V)
        | exact HA' | exact OX' | exact OA' | exact FR' | exact ST' | exact MU' | exact WM' | exact MI' ].
    - (* [comment removed for export] *)
      assert (BR : n <= i + 1) by (match goal with K : _ |- _ => clear - K Hi; lia end).
      lx_post.
      all: lazymatch goal with
           | |- munch _ _ _ => exact MU'
           | |- wmono _ _ _ => exact WM'
           | |- u32arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_length; xlia LX L0
           | |- skipn _ _ = skipn _ _ => eapply skipn_upd_Z; [exact FX | xlia Hi | xlia Hi BR | xlia LX L0]
           | |- lval _ ?nn + _ = _ => replace nn with (i + 1) by xlia Hi BR; exact (addif_inv_next _ _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VX0 VA V)
           | |- _ => first [reflexivity | assumption | xlia Hc']
           end.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma A_mpi_core_add_if_spec : forall AL, asan_img_ok AL -> mpi_core_add_if_stmtA asegs AL A_MPI_CORE_ADD_IF.
Proof.
  intros AL IMG. unfold mpi_core_add_if_stmtA, A_MPI_CORE_ADD_IF.
  intros until ys. intros HX HA Hn LX LA HC DA ALX ALA NZX NZA MI ALWF CSOK ABS OX OA ST LO SPA SCS SX SA -> -> -> ->.
  pose (lxi := lxA_img AL IMG).
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_ADD_IF_STACK_A in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB.
  pose proof (proj1 ST) as LO0.
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  lx_run_tac (PLAN [0xa4864] [] 80%N); lx_tree.
  all: lx_gc.
  - (* [comment removed for export] *)
    match goal with K : 0 <= - n |- _ => rename K into BR end.
    lx_post. all: first [reflexivity | eassumption | xlia Hn BR | rewrite !lval_nonpos by xlia Hn BR; lazymatch goal with |- context [if ?cn =? 0 then _ else _] => destruct (cn =? 0); xlia0 end | idtac].
    all: match goal with |- ?g => idtac "N0-LEFT:" g end.
  - (* [comment removed for export] *)
    match goal with K : 0 <= n + _ |- _ => rename K into BR end.
    eapply (@loop_walk AL IMG ALWF CS CSOK) with (X := X) (A := A) (n := n) (cond := cond) (lo := lo)
             (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (xs0 := xs) (ys0 := ys)
             (k := Z.to_nat (n - 0)) (i := 0) (c := 0) (xs := xs).
    all: try assumption.
    all: lazymatch goal with
         | |- Z.shiftr _ 63 = _ => exact (lx_ct_mask_sra _ HC)
         | |- same_from _ _ _ => apply same_from_refl
         | |- addif_inv _ _ _ _ _ _ => apply addif_inv_0
         | |- 0 <= 0 < _ => xlia BR
         | |- 0 <= ct_mask ?cn <= _ => unfold ct_mask; destruct (cn =? 0); xlia0
         | |- _ /\ _ => first [xlia LX LA | xlia XB NZX | xlia AB NZA | xlia0]
         | |- _ => first [ eassumption | reflexivity | xlia0 ]
         end.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
