(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_check_zero_ct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0803c34233be2d6d 0 5 0 1 26 4 37 1 47 1 48 1P0cc61dc6be43577c 0 5 0 1 29 4 40 1 50 1 51 1P0efe417196c37829 0 2 0 1 28 1P1097a70bd80959af 0 5 0 1 25 4 36 1 47 1 48 1P14d5317a2af1cc3c 0 3 0 1 27 1 37 1P16b0f1f8b946b20b 0 2 0 1 1 1P18e425de4dc7f42f 0 2 0 1 20 1P19ee820f0d7a8d1f 0 2 0 1 2 1P1ac492761a6ecdcd 0 5 0 1 26 4 37 1 47 1 48 1P1b12615929855234 0 2 0 1 51 1P1c08617b3c596590 0 4 0 1 21 1 28 1 36 1P1d69b4739ccff114 0 5 0 1 28 4 39 1 51 1 52 1P220bf56006b87255 0 2 0 1 22 1P221ff450b904ec2c 0 2 0 1 28 1P225b49ff88a8bc17 0 4 0 1 32 1 41 1 42 1P237ed64f6fcbe4e5 0 2 0 1 2 1P24335d45523df39f 0 2 0 1 2 1P2a6f187f6d3c8826 0 2 0 1 10 1P2ac1e0fa2e5227ec 0 2 0 1 51 1P2bd0f20bc51a254b 0 2 0 1 21 1P2e96307753692377 0 2 0 1 21 1P2e971e78db434d0a 0 5 0 1 25 4 36 1 47 1 48 1P2f921b571086273a 0 3 0 1 27 1 37 1P3094d116766c7d6f 0 3 0 1 27 1 37 1P30ddd456de5446be 0 2 0 1 21 1P321bbf0dc32e0010 0 5 0 1 28 4 39 1 50 1 51 1P34b823656fdde1fd 0 2 0 1 1 1P37d6568f8def8dc5 0 2 0 1 21 1P3a81e6d091a74103 0 4 0 1 21 1 28 1 36 1P3c73bd549e862f58 0 2 0 1 1 1P3c8ea6f025778dfe 0 2 0 1 20 1P3e6551cd25659ab3 0 2 0 1 7 1P3e8014ecf625a1b7 0 2 0 1 6 1P3f98cf460de90804 0 5 0 1 27 4 38 1 51 1 52 1N00181c804efc4c8dN0241951b0209c2d6N051ffa6480d3e23fN061e891b7a301ab8N08fe833ffc88648fN0e6926b8b49dba27N0e78b3479709e4afN0ec29d20ff924ef9N10ace728e7603cbeN13e9927537429990N141d45b7031c2179N159de66541fc92e1N1ac5407156f21ee4N207b752b83ffc4b9N2272e298122b2977N2561ba90be04a551N264d568a4b4a7eb1N266a9b39f3c2dd98N2c66c1a13d28390fN2c750d03fe2ddac5N2de92478ad261cfdN2f9d8dde2c5c7b31N309dd9c7a482d21fN30f5ab723901cf36N35af38d41cf8e290N3bc1b26f7ed45e68N3c7809b6034101feN3d3516f7d07315fcN3ff5d069bbe3e01a"%lxh.
Ltac2 gd_tbl_A_mpi_core_check_zero_ct () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_CHECK_ZERO_CT_STACK_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.ct_mask"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limbs_zero"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_check_zero_ct_postA"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zswrap"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zlow"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"].


Definition A_MPI_CORE_CHECK_ZERO_CT : Z := 0xa6600.
Definition MPI_CORE_CHECK_ZERO_CT_STACK_A : Z := 16.

Definition mpi_core_check_zero_ct_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (xs : list word) (n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_check_zero_ct ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lz,$4.(5.(6.$0.R12.(7.(8.O16.O15.O14.O13.R11.R10.R?.O12.O11.R>.R=.R<.R;.R:.R9.R8.R7.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R6.R5.R4.R3.)O6.(9.O16.)O5.(:.(2.&40.))R2.(;.O17.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.(10.(11.&40.O15.)$12.)(11.&40.O15.))(13.(>.$4.$4.)))O1.R2.)(5.(14.O17.O1.R2.)(5.(15.O17.R2.)(5.(6.(2.&40.)R>.(16.&40.(17.R1.)))(5.(18.=R1.)(5.(19.(6.$4.R1.=)(1:.O4.O3.))(1;.O17.R2.O2.(11.&40.O15.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_check_zero_ct_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_check_zero_ct ()) "PCS,P,$4.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pn,$4.Plo,$4.Pxs,(1=.(2.&40.))P,(1>.O3.R5.R4.(1?.R1.))P,(5.(18.=R4.)(18.R4.+2710.))P,(18.R5.(20.(21.(2.&40.)R3.)))P,(6.$4.(22.R7.+4.)=)P,(23.=R8.)P,(15.O3.R:.)P,(24.O2.)P,(25.O2.R2>.)P,(26.O3.O2.R=.)P,(27.O3.O2.R30.R>.R=.(28.+4.R<.))P,(1;.O3.R?.R<.(11.&40.R2?.))P,(18.R=.(10.(11.&40.R30.)$12.))P,(6.$4.(22.(11.&40.R31.)+10.)=)P,(29.R34.R?.(10.(11.&40.R32.)R?.))P,(2:.(18.(2;.R12.(28.+4.(20.(21.(2.&40.)R?.))))(10.(11.&40.R33.)$12.))(18.(11.&40.R33.)R12.))P,(6.(2.&40.)R2<.(16.&40.R13.))P,(6.(2.&40.)R2<.(16.&40.R13.))(2<.O3.O2.R38.(2=.O3.R37.R36.R35.R34.R30.R2?.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R12.R14.R13.R16.)(7.(8.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(16.&40.O1.)R17.(:.(2.&40.))R16.(;.O3.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma lx_mod32_of_bv : forall L, bv_unsigned (Z_to_bv 64 L) mod 2 ^ 32 = L mod 2 ^ 32.
Proof.
  intros L. rewrite Z_to_bv_unsigned. change (bv_wrap 64 L) with (L mod (2 ^ 32 * 2 ^ 32)).
  apply Zaux.Zmod_mod_mult; lia.
Qed.
Lemma lx_zext32 : forall L, zlow 64 (4294967296 * L) ≫ 32 = L mod 2 ^ 32.
Proof.
  intros L. unfold zlow. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 64) with (4294967296 * 4294967296). change (2 ^ 32) with 4294967296.
  rewrite Zmult_mod_distr_l. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma lx_lor_sx32_mod32 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_check_zero_ct ()) "Pw,(2.&40.)Pa,$4.(6.$4.(22.(2>.(2?.+20.(30.+20.(11.&40.R2.)))R1.)(31.+2.+20.))(22.(2>.(11.&40.(32.R2.))R1.)(31.+2.+20.)))")
(* [comment removed for export] *).
Proof.
  intros w a. rewrite <- !LxSoundExpr.lor_mod_pow2 by lia. f_equal.
  change ((zswrap 32 (zlow 32 (bv_unsigned w))) mod 2 ^ 32) with (zlow 32 (zswrap 32 (zlow 32 (bv_unsigned w)))).
  rewrite lx_w32_eq, <- lx_wrap_sx32. reflexivity.
Qed.
Lemma lx_ct_tail_eq : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_check_zero_ct ()) "Pv,$4.P,(5.(18.=R1.)(23.R1.(31.+2.+20.)))(6.(2.&40.)(16.&40.(33.(2?.+40.(2>.(34.(33.R2.+1.))(34.R2.)))+3?.))(16.&40.(17.R2.)))")
(* [comment removed for export] *).
Proof.
  intros v Hv. unfold ct_mask. rewrite !Z.shiftr_div_pow2 by lia.
  destruct (Z.eqb_spec v 0) as [->|NE].
  - reflexivity.
  - assert (R : - 2 ^ 32 <= Z.lor (- (v / 2 ^ 1)) (- v) < 0).
    { destruct (Z.eq_dec (v / 2 ^ 1) 0) as [E|E].
      - rewrite E. cbn [Z.opp]. rewrite Z.lor_0_l. lia.
      - split; [| apply Z.lor_neg; right; lia].
        eapply Z.le_trans; [| apply lx_lor_neg_ge; lia]. lia. }
    set (x := Z.lor _ _) in *. unfold zswrap. change (2 ^ (64 - 1)) with (2 ^ 63).
    rewrite (Z.mod_small) by lia.
    replace ((x + 2 ^ 63 - 2 ^ 63) / 2 ^ 63) with (-1) by (clear - R; Z.div_mod_to_equations; lia).
    rewrite <- (Z_to_bv_mod64 (-1)). reflexivity.
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (A n lo : Z) (xs : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= Z.of_nat (length xs).
  Hypothesis XB : 0 < A /\ A + 4 * Z.of_nat (length xs) <= 2^64.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SA : A + 4 * Z.of_nat (length xs) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_check_zero_ct_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs n lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation W := [(bv_unsigned sp - 16, bv_unsigned sp)].

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Lemma tail_walk : forall (v : Z) (x5 x6 x11 x12 x13 x14 x15 x16 x17 : word) (junk : list (bv 8)) (mm : mem),
    0 <= v < 2 ^ 32 -> (v = 0 <-> limbs_zero xs n) ->
    rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -16) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST (MS (mkR ra SP' gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa6690) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros v x5 x6 x11 x12 x13 x14 x15 x16 x17 junk mm Hv Hz FR ST MU WM MI. al_facts.
    lx_spell. lx_run_tac (PLAN [] [] 20%N). lx_tree.
    all: lx_same_mem; lx_gc.
    rewrite (lx_ct_tail_eq v Hv).
    lx_post; [> reflexivity | clear - Hv; lia | exact Hz | .. ].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i : Z) (acc x5 x6 : word) (junk : list (bv 8)) (mm : mem) (ep ei : Z),
    Z.to_nat (n - i) = k -> 0 <= i < n -> ep = A + 4 * i -> ei = i ->
    (bv_unsigned acc mod 2 ^ 32 = 0 <-> limbs_zero xs i) ->
    bytes_at asegs mm A (u32s xs) -> aobj asegs AL CS mm A (4 * n) ->
    rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -16) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST (MS (mkR ra SP' gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 ep) acc
      (Z_to_bv 64 ei) SB (Z_to_bv 64 1) (Z_to_bv 64 ep) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0xa662c) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i acc x5 x6 junk mm ep ei Hk Hi Ep Ei Hacc HA OA FR ST MU WM MI; [exfalso; clear - Hk Hi; lia|]. al_facts.
    destruct (nth_error xs (Z.to_nat i)) as [w|] eqn:NX; [| exfalso; apply nth_error_None in NX; clear - NX Hi Ln; lia].
    pose proof (u32ro_cell_at mm A xs i ep w HA NX ltac:(clear - Hi; lia) Ep) as CSx.
    lx_spell. lx_run_tac (PLAN [0xa662c; 0xa6690] [(0xa664c, DJoin)] 40%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear CSx.
    all: pose proof (limbs_zero_step xs i w acc ltac:(clear - Hi; lia) NX Hacc) as Hacc'; rewrite <- lx_lor_sx32_mod32 in Hacc'.
    - (* [comment removed for export] *)
      eapply (IH (i + 1)); [clear - Hk Hi; lia | klia | clear - Ep; lia | clear - Ei; lia
        | rewrite lx_mod32_of_bv; exact Hacc' | exact HA | exact OA | exact FR | exact ST | exact MU | exact WM | exact MI].
    - (* [comment removed for export] *)
      assert (EI : i + 1 = n) by klia.
      rewrite lx_zext32.
      eapply tail_walk; [apply Z.mod_pos_bound; clear; lia | rewrite <- EI; exact Hacc' | exact FR | exact ST | exact MU | exact WM | exact MI].
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma A_mpi_core_check_zero_ct_spec : forall AL, asan_img_ok AL -> mpi_core_check_zero_ct_stmtA asegs AL A_MPI_CORE_CHECK_ZERO_CT.
Proof.
  intros AL IMG. unfold mpi_core_check_zero_ct_stmtA, A_MPI_CORE_CHECK_ZERO_CT.
  intros until xs. intros HA Hn LX ALA NZA MI ALWF CSOK ABS OA ST LO SPA SCS SA -> ->.
  pose (lxi := lxA_img AL IMG).
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_CHECK_ZERO_CT_STACK_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (u32ro_bound _ _ _ _ HA) as XB. pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  lx_spell. lx_run_tac (PLAN [0xa662c; 0xa6690] [] 40%N). lx_tree.
  all: lx_gc; lx_rn_munch MU'; lx_rn_wmono WM'; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_ro32 A HA'; lx_rn_aobj A OA'.
  all: lazymatch goal with
       | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa662c) _ _ _ _) =>
           eapply (loop_walk AL IMG ALWF CS CSOK) with (A := A) (n := n) (lo := lo) (xs := xs) (i := 0) (acc := Z_to_bv 64 0);
           first [ assumption | reflexivity | eassumption
                 | rewrite unsigned_lit by (clear; lia); split; [intros _; apply limbs_zero_0 | reflexivity]
                 | klia ]
       | |- _ =>
           match goal with K : 0 <= - ?nn |- _ => eapply tail_walk with (A := A) (n := nn) (lo := lo) (xs := xs) end;
           first [ assumption | eassumption
                 | match goal with K : 0 <= - ?nn |- _ => replace nn with 0 by (clear - K Hn; lia) end; split; [intros _; apply limbs_zero_0 | reflexivity]
                 | klia ]
       end.
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
