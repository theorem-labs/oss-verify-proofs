(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00346cb91e5fc6f4 0 5 0 1 25 1 26 1 33 1 34 1P0621ffcfb0dfeb69 2 26 1 1 8 3 1 1 46 1 47 1 6 0 1 33 1 34 1 45 1 48 1 49 8 1 1 8 3 2 1 45 1 48 1 4 0 2 46 2 47 2 49 16P093123a12a58a59e 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P0c7d601a86539057 0 2 0 1 8 1P0ebc972b26ae10cd 0 2 0 1 9 1P110e5e4a37806763 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P136a720246bd3985 2 34 1 1 8 3 1 1 52 1 53 1 6 0 1 39 1 40 1 51 1 54 1 55 8 1 1 8 3 2 1 51 1 54 1 4 0 2 52 2 53 2 55 16P15a42535358ad5b5 0 2 0 1 13 1P15bd4a0b71420974 0 2 0 1 1 1P175b64024f51e48b 0 2 0 1 13 1P188b0d37e6e16dc4 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P1dd9f6b7b520451f 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P1e0a152f812a4cd3 0 5 0 1 37 1 38 1 49 1 50 1P218d407274237262 0 2 0 1 14 1P22caca0cbef3908e 0 2 0 1 10 1P231051f836efade4 0 2 0 1 14 1P23e2a1426188cbd3 0 2 0 1 13 1P2c840fba9d6ddde9 0 5 0 1 31 1 32 1 43 1 44 1P2d500d85bf61028d 0 5 0 1 24 1 25 1 32 1 33 1P2daa4398c7c54cf8 1 1 64 9 0 16 10 16 16 16 28 16 29 16 30 16 36 16 39 16 40 16 3 13 1 21 1 41 1P30b932f3ba4c271d 2 26 1 1 8 3 1 1 46 1 47 1 6 0 1 33 1 34 1 45 1 48 1 49 8 1 1 8 3 2 1 45 1 48 1 4 0 2 46 2 47 2 49 16P340844ad3dc33f4a 0 5 0 1 27 1 28 1 35 1 36 1P35f68585e454b984 0 2 0 1 39 1P372993c8e591ad6b 2 34 1 1 8 3 1 1 52 1 53 1 6 0 1 39 1 40 1 51 1 54 1 55 8 1 1 8 3 2 1 51 1 54 1 4 0 2 52 2 53 2 55 16P39e2aaec9c047f83 1 2 16 2 0 1 39 1 16 2 17 1 40 1 2 41 1 42 1P3e12614dd21de348 1 1 16 2 17 1 40 1 3 0 1 39 1 41 16N01b870d4911e6f10N056a6decea69b980N087048007fdb5912N0f49dcf47574b8ffN0fcc382854ba112aN147aafbe7bd586e3N150727add60f0d0fN18244d2670ec3f36N1a75112dc79f6a57N1b59caa5cd920154N1c2630a65f53408fN1e38387b0bbd3157N1e4058199c54712cN1f1c15bd73513249N23eb95030df0fe66N279ec4fcb8b09abdN2888b6572cfa4730N28927d46837bab51N29bd5359af994aadN29d275bfe6f18d1dN2a23c9b32eeacbf1N2f1717e85513d952N2fa8b9d117d85431N30add60baaf062e3N34833a6a7af2a460N38237b50ad143965N38dff184a88f3f96N3a4c284f3b9774a7N3a5dadc8d2c28df3N3bf974a882183497"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_grow () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.max"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "grow_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].


Definition U_MPI_GROW : Z := 0x1f1bc.
Definition U_CALLOC : Z := 0x3f960.
Definition U_MEMCPY : Z := 0x46a40.

(* [comment removed for export] *)
Notation MPI_GROW_STACK := 64 (only parsing).

Definition grow_R (nb : Z) (dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_grow ()) "(0.(1.(0.(2.$3.O2.=)(0.(2.$3.(4.O1.)(4.O4.))(0.(2.$3.(5.O1.)(6.(5.O4.)O5.))(0.(2.(7.&40.)(8.O1.)(8.O4.))(0.(2.(9.(7.&40.))(:.O1.)(;.(7.&40.)(:.O4.)(<.(7.&40.)(=.&40.=)(>.(?.O5.(5.O4.))))))P,(10.O5.(5.O4.))(2.$11.O1.O4.))))))(0.(2.$3.O2.$12.)(2.$11.O1.O4.)))Pb,$13.P,(14.$13.R1.(15.O1.))(1.(14.$13.R2.(15.O4.))(16.(14.$13.R2.O3.))))")
(* [comment removed for export] *).

Definition mpi_grow_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_grow ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(17.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(18.(7.&8.))Pmo,$19.Ph,(1:.O5.O4.O3.)PLB,(9.$13.)PdX,$11.Pnb,$3.Plo,$3.P,(1;.O5.O4.O3.R5.R4.R7.R6.)P,(1<.O5.R8.R5.R4.)P,(16.(2.$1=.(1>.R5.)$1?.))P,(20.O4.R7.(21.&40.R2:.)(22.O5.O4.O3.R8.)R6.)P,(0.(10.=R6.)(23.R6.(24.+2.+40.)))P,(25.O5.R<.R6.(21.&40.R2<.))P,(10.R7.(?.(?.(21.&40.R2=.)+40.)(26.O4.)))P,(10.(27.O4.)R8.)P,(10.(21.&40.R2?.)(22.O5.O4.O3.R=.))P,(2.$3.(28.(21.&40.R30.)+10.)=)P,(10.(29.O4.)(27.O4.))P,(2.(7.&40.)R30.(=.&40.(2:.O4.)))P,(2;.O5.R13.)P,(2<.O5.O4.R14.)P,(2=.O4.O1.+8.)P,(2.(7.&40.)R2>.(=.&40.(2>.R12.)))P,(2.(7.&40.)R2>.(=.&40.R12.))(2?.O5.R17.(30.O5.O4.O3.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.(31.R13.R14.R15.)R12.R18.R17.)(32.(33.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(=.&40.O2.)R19.(34.(7.&40.))R18.(35.O5.)))")
(* [comment removed for export] *).

Lemma lor_align4 : forall a b, a mod 4 = 0 -> b mod 4 = 0 -> zlow 64 (Z.land (Z.lor a b) 3) = zlow 64 0.
Proof.
  intros a b Ha Hb. rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2).
  rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ha, Hb. reflexivity.
Qed.

Ltac lor_align_leaf :=
  lazymatch goal with
  | H : (if zlow 64 (Z.land (Z.lor ?a ?b) 3) =? zlow 64 0 then false else true) = true |- False =>
      rewrite (lor_align4 a b) in H by (first [clear_disj; lia | lia]); rewrite Z.eqb_refl in H; discriminate H
  end.

Section G.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).


  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.12L18926747689.12L18926759668.1200000:00;00@S1a1b1k2HkSS1a1b". (* [comment removed for export] *)
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fix_regs :=
    repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
      let z := constr:(Zpos p) in
      lazymatch eval compute in (Z.leb (2^63) z) with
      | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
      end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L34709347771.60L8746300367.60 00000:00DS2dX2nb2HnS2dX2nb2Hn". (* [comment removed for export] *)
  Lemma L_UNCH : ltac2:(CDefT.buildp (gd_tbl_P_mpi_grow ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)PF,(17.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(18.(7.&8.))Pmo,$19.Ph,(1:.$36.VL,VHI,)PLB,(9.$13.)PdX,$11.Pnb,$3.Plo,$3.Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pm',P,(7.&40.)(18.(7.&8.))Pmo',$19.Ph',(1:.$36.VL,VHI,)Pr,$3.P,(2;.$36.R4.)P,(25.$36.R5.R14.(21.&40.R2;.))P,(37.R1:.R5.)P,(2.$3.(22.$36.VL,VHI,R5.)(22.$36.VL,VHI,R1:.))P,(1;.$36.VL,VHI,R6.R1:.R8.R7.)P,(1<.$36.R9.R1;.R1:.)P,(16.(2.$1=.(1>.R1;.)$1?.))P,(38.$36.VL,R1=.(21.&40.R31.)(39.R1<.)R20.R;.)P,(2<.$36.VL,R<.)P,(1.(2.$3.R:.$12.)(0.(2.$3.R:.=)(10.R1=.(5.R1>.))))(2?.$36.R=.(30.$36.VL,VHI,R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R21.R20.R1?.(31.R1>.R1?.R20.)R1=.R23.R22.)(32.(33.R35.R34.R33.R32.R1<.R1;.R1:.R31.R30.(=.&40.R;.)R19.R18.R17.R16.R15.R14.R13.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R12.R11.R10.R?.)R25.(3:.R35.)R24.(34.(7.&40.))R>.(35.$36.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros MI' ST' MF' HT' HH' MA' NST HPX' SOK' Hr.
    apply aevtM_done. unfold mpi_binop_post. flexi 14%nat. exists m', mo', h', LB, dX, r.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MF'|]. split; [exact HT'|].
    split; [exact HH'|]. split; [exact MA'|]. split; [apply mpd_out_refl; exact NST|]. split; [exact HPX'|]. split; [exact SOK'|].
    split; [| intros b Hb; left; exact Hb].
    destruct Hr as [->|[-> Hn]]; [right; split; reflexivity| left].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
    replace (Z.to_nat (nb - md_n dX)) with 0%nat by lia. cbn [repeat]. rewrite app_nil_r. split; [reflexivity|]. intros _; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02L0@D1429363837.120 D29466597727.121D29471186428.120L11424325532.128L11424325532.179L11668620365.137L11669012089.127L11669012089.132L11670653863.138L12292857614.153L12292857614.154L12851051980.94 L12851051980.96 L12851051980.97 L15087643437.99 L17372839449.152L19730768531.120L21168528431.179L21323309894.100L21323309894.101L21323309894.98 L21365166618.180L21682003368.129L22613774103.128L22613774103.179L22706564033.155L22706593640.96 L22706593640.98 L22706593640.99 L23100341967.147L23139177294.125L23512662482.125L24503513358.125L2506416671.125 L25920923075.127L25920923075.132L26106415276.130L26405856937.98 L28573719472.179L28573719472.186L28573883312.177L28573883312.183L28573898934.175L28618480155.122L28812073579.138L28814103937.137L29093342756.153L29093342756.154L29638047992.176L29638086697.179L29644522319.180L32688990039.177L33085651873.132L33487813197.177L34160116234.100L34160116234.101L34160116234.95 L34160116234.97 L34160116234.98 L34290115814.86 L34464130877.128L35221870355.120L37867421857.0  L38221227230.152L38441453918.98 L38766759268.125L39409830041.179L39409836749.184L39409836878.157L39409837507.133L40081004225.178L40238812268.154L40297245962.125L40823233389.98 L41418088011.152L41930136202.120L43061758399.84 L43403828934.177L45290769777.152L45785754244.129L46288017421.158L46288019203.159L46288024153.179L47203009963.122L50249499534.152L51209632397.123L51209632397.127L51209632526.172L51209632526.178L52101720110.128L52101720110.129L52101720110.178L52101720239.178L52437720590.128L52437720590.129L52437720590.178L52437720719.178L5285886713.120 L53251959398.98 L53927500190.138L53933808495.154L54391891673.95 L54391891673.97 L54391891673.98 L54391984881.159L54391985276.157L54391985663.158L54398102733.130L54398102733.158L54398102733.181L5487331950.133 L55237439215.177L59308562897.183L59308579027.130L59308579543.128L59308579543.129L59308579543.130L59308579543.131L59308579543.177L59308579543.181L59308579543.182L59308579668.178L59308579930.129L59308977657.133L59315300849.181L59315300849.182L59315317366.126L59448302046.152L60199128149.128L61263218231.154L61931995297.132L62110619702.177L6329754031.172 L6329754031.178 L6384891599.98  L64638659.138   L64782995.152   L65502163868.83 L6624980440.180 L66797865.137   L67494351641.179L68108170489.127L68108170618.178L68238362254.152L68238445278.138L7190686615.116 L7190686615.171 L7193126325.98  L7193175859.152 L7227043232.135 L7269057982.179 L772750287.83   L8927230993.132 R14801101130.120R14813292009.121R22706563525.15800000?00@00A00Z01601o02003804104I05E05l06S07:07Q07R07a08G09509c0:Q0;90;Y0;o0<Z0=j0>Z0?J0@:0@M0@d0A>0Ae0B<0B=0CD0C`0D<0D=0Eh0Ei0GW0HU0Hh0Ig0Jf0Kg0Kh0L?0LW0M80NL0Nd0P>0Pn0Q^0Q_0Q`0RP0R_0S?0SN0SO0Sk0TF0TZ0U20UM0Uh0V@0WN0Xh0Y90YH0Y[0Yj0ZM0[C0\<0\\0]:0]X0^H0^Y0_L0_M0`L0`M0ag0b<0bQ0bi0cA0cV0ck0dC0d[0d\0e40fE0fF0g80gj0h\0j=0kW0m70mg0n]0oS10E10]11912J12b14914R15I15d16B17Q17l18D18]19m1;=1<:1<O1<o1=c1>;1>N1>O1?i1@>1@l1AZ1Ai1BX1CF1D11DD1DZ1EC1El1FW1GL1H71Hl1IR1J>1Ja1KC1KR1Ka1LbS2sp1X5limbs2XBFFS2sp1X2nb2NB2XB2H31A4LXKTS2sp1X1P5limbs2nb2NB2XB2H31AS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2N12P02P41A2A0FS1L3HLS2sp2LB1X1n1P5limbs3own2nb2lo3SLO3ACL3SPA3SPB2X02XB3OWF2H21A2A02A4S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2N12P02P41A2A0S2sp1X1n1P5limbs2nb2XB1AS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XB2P02H21A2A02A4S1L3HLS2sp1X5limbs2lo3SLO3ACL3SPB2X02XBS1L3HLS2sp1X5limbs2lo3SLO3ACL3SPB2X02XBS1L3HLS2sp1X5limbs2lo3SLO3ACL3SPB2X02XBS2sp1X1n5limbs2nb2XB2H1FS2sp1X5limbs2XBS2sp1X1n1P5limbs3SPB2X03LEN2XB2P01A2A0S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P4S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P4S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P4S2sp1X1n1P5limbs2nb3SPB2X02XB2P02H21A2A0S2sp1X2nb3SPB2X02XB2H21A2A04LXKTS2sp1X2nb2XB2H21A4LXKTS2sp1X1n1P5limbs2nb3SPB2X02XB2N12P02H21A2A0S1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB2P02P42H21A2A02A42XA3APA3x282H0S1L3HLS2sp1X5limbs2lo3SLO3ACL3DHI3SPB2X02XB1a2HaS1L3HLS2sp1X5limbs2lo3SLO3ACL3DHI3SPB2X02XB1a2HaS1L3HLS2sp1X5limbs2lo3SLO3ACL3DHI3SPB2X02XB1a2HaS2sp1X1P5limbs2XB1AS2sp1X5limbs2XB1A2H02H4S2sp1X5limbs2nb2XB1A2H02H4S2sp1X1n5limbs2nb3SPB2X03LEN2XB2H21A2A0S2sp1X5limbs2nb2XB1A2H4FS1L3HLS2sp2LB1X1n1P5limbs3own2nb2lo3SLO3ACL3SPB2X02XB3OWF2H21A2A02A42H5S2sp1X1b5limbs3LEN2XB1A4LXKTS2sp1X5limbs2nb3SPB2X02XB2H3FS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB2XS2N13PAL2P02P42H21A2A03A162A42XA3APA1a1B1k1R2O12O22H02B4FS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3DHI3SPB2X02XP2XB2XS2N13PAL2P02P42H21A2A03A162A42A52XA3APA1a1C2O12O22H02H4S1L3HLS2sp1X1P5limbs2nb2lo3SLO3ACL3SPB2X02XB2P01A2A02A41a1C2O1S2sp1X1n1P5limbs2XBS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XB2N12P02H21A2A02A4S1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XB2N12P02H21A2A02A4S2sp1X1n1P5limbs2nb3SPB2X03LEN2XP2XB3PAL2P02H21A2A03A162XA3APA2NNFS2sp1X1P5limbs2XB1A1a1CS2sp1X1P5limbs2XB1A1a2HaS1L2HI2sp1h1X1P5limbs2XB1A1a2Ha1CS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB2N13PAL2P02P42H21A2A03A162XA3APA2NNS2sp1X1n1P5limbs2NR2XB1AS1L3HLS2sp1X1n1P5limbs2nb2lo2NB3SLO3ACL3SPB2X02XP2XB2N13PAL2P02P42H21A2A03A162A42XA3APA2NNS1L3HLS2sp1X1P5limbs2lo3SLO3SPA3SPB3XAL2X02XB2XSS1L3HLS2sp1X1P5limbs2lo3SLO3SPA3SPB3XAL2X02XB2XSFFS1L3HLS2sp1X1P5limbs2lo3SLO3SPA3SPB3XAL2X02XB2XSS2sp1X5limbs2XBS2sp1X2nb3SPB2X02XB2H21A2A04LXKTS2sp1X5limbs2XBSS1L2sp1X1P5limbs2lo3SLO2XB1AS1L2HI2sp1h1X5limbs4HTOP2XBS2sp1X5limbs2XB1A2H4S2sp1X1P5limbs2XB1A1a2HaS2sp1X1P5limbs2XB1A1a2H42H5S2sp1X1P5limbs2XB1A1a2H02H4S2sp1X2XB1A4LXKT1a2H42H7S1L3HLS2sp2LB1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB2N12P02P42H21A2A02XA3APA1eS1L3HLS2sp1X1n1P5limbs2nb2lo2NB3SLO3ACL3SPB3XAL2X02XP2XB2N12P02P42H21A2A03A162A42XA3APA2NNS2sp1X5limbs2XB1AS2sp1X5limbs2XBS2sp1X1P5limbs2XB1AS2sp1X5limbs2XBS1L3HLS2sp1X5limbs2lo3SLO3SPB2X02XBS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P02P41A2A0S1L3HLS2sp1X1P5limbs2lo3SLO3ACL3SPA3ACP3SPB2X02XB2P01A2A0S2sp1X2nb3SPB2X02XB2H21A2A04LXKTS2sp1X1P5limbs2nb2XB1A1a2H42H5S2sp1X1P5limbs2nb2XB1A1a2H52H7S2sp1X1n1P5limbs2nb3SPB2X02XB2N12P02H21A2A01a2HaS2sp1X1P5limbs2XBS1L2HI2sp1h1X1P5limbs4HTOP3SPB2X02XB2P02h23HT21A2A0FS1L3HLS2sp1X2nb2lo3SLO3ACL3SPB3XAL2X02XB2H21A2A03A162A42XA4LXKTFS1L3HLS2sp1X1n1P5limbs2nb2lo2NB3SLO3ACL3SPB3XAL2X02XP2XB2N12P02P42H21A2A03A162A42XA3APA2NNS2sp1X2XB1A4LXKT1a2O1S2sp1X2XB1A4LXKT1a2O1S2sp1X1P5limbs2XB1A1a2O1S2sp1X1P5limbs2XB1A1a2O1S2sp1X2XB1A4LXKT1a2O1S2sp1X2XB1A4LXKT1a2O1S2sp1X1P5limbs2XB1A1a2O1S2sp1X1P5limbs2XB1A1a2O1FS1L2sp1X5limbs2lo3SLO2XBS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB3PAL2P02P42H21A2A03A162XA3APA2NNFS1L2HI3HLS2sp1h1X5limbs2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI3HLS2sp1h1X5limbs2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI3HLS2sp1h1X5limbs2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI3HLS2sp1h1X1n1P5limbs2nb2lo3SLO3ACL4HTOP3SPB2X02XP2XB2N12P02P42H21A2A02A42XA3APA1a2NO2H42H7S1L2HI3HLS2sp1h1X1n1P5limbs2nb2lo3SLO3ACL4HTOP3SPB2X02XB2XS2N12P02P42H21A2A02A41a2NO2H02H4S1L2HI3HLS2sp1h1X1n1P5limbs2nb2lo3SLO3ACL4HTOP3SPB2X02XP2XB2XS2N12P02P42H21A2A02A41a2NO2H42H52H0S1L2HI3HLS2sp1h1X2lo3SLO3SPB2X02XB1A2A04LXKT1a1CS1L2HI3HLS2sp1h1X1P5limbs2lo3SLO3SPB2X02XB2P01A2A01a1CS1L2HI3HLS2sp1h1X1P5limbs2lo3SLO3SPB2X02XB2P01A2A01a1CS2sp1X1n1P5limbs2nb3SPB2X03LEN2XB2N12P02H21A2A02NNS2sp1X1n1P5limbs2XP2XB1AS2sp1X1n1P5limbs2XB1A1a1R2O2S1L3HLS2sp2LB1X1n1P5limbs3own2nb2lo3SLO3ACL3SPB2X02XB3OWF1A2A02A41a2Ha1C1B1k1R2H0S2sp1X2XB1A4LXKT1a2NO2H4S1L3HLS2sp2LB1X1n1P5limbs3own2nb2lo3SLO3ACL3DHI3SPB2X02XB3OWF1A2A02A42A51a2Ha1C1D2H02H4S2sp1X2nb2XB2H21A4LXKT2H4S1L3HLS2sp1X2nb2lo3SLO3ACL3SPB2X02XB2H21A2A02A44LXKT2H4S2sp1X1P5limbs2XB1A1a2NO2H4S2sp1X1n1P5limbs2nb2XB2H21A2H4S1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB2N12P02P42H21A2A02A42XA3APA2H4S2sp1X1P5limbs2XB1A1a2NO2H5S2sp1X2XB1A4LXKT1a2NO2H7S2sp1X1P5limbs2XB2P01A2PZS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB2P02P42H21A2A02A42XA3APA1a2Ha1RS1L3HLS2sp1X1n1P5limbs2nb2lo3SLO3ACL3SPB2X02XP2XB2P02P42H21A2A02A42XA3APA1a2Ha1RS1L2HI3HLS2sp1h1X5limbs2nb2lo3SLO3ACL3SPB2X02XB1A2A02A41a1C1SS2sp1X1n1P5limbs2XB1AS2sp1X2nb3SPB2X02XB2H21A2A04LXKTS1L2sp1X1n1P5limbs2nb2lo3ACL3SPB2X02XB2P02H21A2A02A4S2sp1X1n1P5limbs2NR2XB1AS2sp1X1P5limbs2XB1AFS1L3HLS2sp1X1n1P5limbs2nb2lo2NB3SLO3ACL3SPB3XAL2X02XP2XB2N12P02P42H21A2A03A162A42XA3APA2NNS2sp1X5limbs2nb2NB2XBS2sp1X1n1P5limbs2nb3SPB2X02XB2N12P02H22H31A2A0S2sp1X1n1P5limbs2nb3SPB2X02XB2N12P02H22H31A2A0S2sp1X5limbs2XBS2sp1X2sg1n1P5limbs3pad2nb3SPB2X02XB2P02H21A2A0S2sp1X1n1P5limbs2nb3SPB2X02XB2N12P02H22H31A2A0S2sp1X1n1P5limbs2nb3SPB2X02XB2P02H21A2A02NNS2sp1X2nb2XB1A4LXKTS2sp1X1P5limbs2nb2XB1AS2sp1X1n1P5limbs3SPB2X03LEN2XB2N12P01A2A0S2sp1X1n1P5limbs3SPB2X03LEN2XB2N12P01A2A0S1L3HLS2sp1X5limbs2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp1X1P5limbs2lo3SLO3ACL3ACP3SPB2X02XB2P01A2A0S1L3HLS2sp1X5limbs2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp1X1P5limbs2lo3SLO3ACL3ACP3SPB2X02XB2P01A2A0S2sp1X1n1P5limbs3SPB2X03LEN2XB2P01A2A0S2sp1X1n1P5limbs2nb3SPB2X03LEN2XB2P02H21A2A0S1L3HLS2sp1X5limbs2lo3SLO3SPB2X02XBS2sp1X1n1P5limbs3SPB2X02XB2P01A2A0S2sp1X5limbs2XBS2sp1X5limbs2XBS1L4DIMG2sp1X1n1P5limbs2nb3SPB2X02XP2XB2P02H21A2A02A52XA3APA1a2H0". (* [comment removed for export] *)
  Lemma U_mpi_grow_spec : mpi_grow_stmt usegs L HI U_MPI_GROW U_MEMSET_FUNC.
  Proof.
    unfold mpi_grow_stmt, U_MPI_GROW. intros until lo. intros HH MA NST XW NB ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HH) as ND.
    pose proof MA as MA0.
    destruct dX as [X sg n P limbs pad own].
    flat constr:(MA) 2%nat. flclear MA. intros FLt1 SG. flat constr:(FLt1) 6%nat. flclear FLt1. intros CH XAL X0 LEN NR OWN. unfold mpi_cells in CH.
    flat constr:(XW) 3%nat. flclear XW. intros XCW XD XP. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    unfold MPI_MAX_LIMBS in NR. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    (* [comment removed for export] *)
    assert (OWF : (own = LNull /\ P = 0 /\ n = 0) \/ (own = LHeap /\ 1 <= n /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ 0 < P /\ P + 4 * n <= alloc_ceiling)).
    { destruct own as [| |]; [left| right| exfalso; exact (NST eq_refl)].
      - flat constr:(OWN) 2%nat. flclear OWN. intros P0 N0. (flsplit; repeat split); assumption.
      - flat constr:(OWN) 4%nat. flclear OWN. intros N1 PIN PAL PCH. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
        (flsplit; repeat split); try assumption; lia. }
    clear OWN. carve_frame 32%nat ST.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x3f960] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch ?W ?mA mx, Hw : wmono _ ?mA' mx |- _ =>
           pose proof (Asn1AuxA.HEAP_munch usegs L HI _ _ _ _ _ lo _ HH ACL Hm Hw ltac:(intros a Ha NO; cbn in NO; left; flia)) as HH1;
           pose proof (statics_ok_munch usegs L _ _ _ SOK Hm ltac:(intros a Ha NW; cbn; flia)) as SOK1;
           pose proof (heap_presx_frame usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad own)) _ _ _ Hm Hw HBR DHI ltac:(flia)) as HPX1;
           pose proof (mpd_at_munch usegs _ _ _ _ _ MA0 NST Hm Hw ltac:(cbn; split; [flia| exact I])
                         ltac:(cbn [md_own md_p md_n]; intros HO; cbn; split; [| exact I]; destruct OWF as [(E & _)|(_ & _ & _ & _ & P0 & P4)]; [congruence| flia])) as MA1;
           pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1
         end end.
    (* [comment removed for export] *)
    1: eapply L_UNCH; [eassumption| eassumption| apply mo_frame_refl| reflexivity| exact HH1| exact MA1| exact NST| exact HPX1| exact SOK1| left; reflexivity].
    1: eapply L_UNCH; [eassumption| eassumption| apply mo_frame_refl| reflexivity| exact HH1| exact MA1| exact NST| exact HPX1| exact SOK1| right; split; [reflexivity| cbn [md_n]; flia]].
    (* [comment removed for export] *)
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with Hm : munch _ ?mA m1, Hw : wmono _ ?mA' m1, STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ =>
      rename Hm into MU1; rename Hw into WM1; rename STx into ST1; rename MIx into MI1 end.
    clear ST MI CH FR MK.
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := nb) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ m1 m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame mo mo2 |- _ => rename H into MF2 end.
    heap_transport HPc.
    assert (SOK2 : statics_ok usegs L m2) by (eapply statics_ok_heap_pres; [exact SOK1| exact HPc| exact SW]).
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad own)) m m2).
    { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| lia| lia]. }
    assert (MA2 : mpd_at usegs m2 LB (mkMPD X sg n P limbs pad own)).
    { eapply mpd_at_heap_pres; [exact MA1| exact HPc| exact MI1| exact MI2| cbn [md_addr]; solve_client_range
        | cbn [md_own md_p md_n]; intros HO; destruct OWF as [(E & _)|(_ & _ & PIN & _)]; [congruence| eapply client_range_block; [exact PIN| lia| lia]]
        | cbn [mpd_blk md_own md_p md_n]; intros b Hb; destruct own; [destruct Hb| destruct OWF as [(E & _)|(_ & _ & PIN & _)]; [congruence| destruct Hb as [<-|[]]; exact PIN]| exfalso; exact (NST eq_refl)] ]. }
    clear HH SOK HH1 SOK1 HPX1 MA1 MK1 MU1 WM1 HPc MI1. try clear ST1. clear m1.
    destruct PO as (h2 & HT2 & [[-> HH2] | (A & -> & HBA & HH2 & HNEW)]); pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    { (* [comment removed for export] *)
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK2).
      lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
      eapply L_UNCH; [eassumption| eassumption| exact MF2| exact HT2| exact HH2| exact MA2| exact NST| exact HPX2| exact SOK2| left; reflexivity]. }
    (* [comment removed for export] *)
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2. pose proof (HND _ _ _ _ HH2) as ND2.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5.
    flat constr:(HAP2) 2%nat. flclear HAP2. intros HAPA _.
    assert (XA' : forall a, X <= a < X + 16 -> ~ (A <= a < A + nb * 4)).
    { intros a Ha C. destruct (XCW a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]. }
    assert (XA : X + 16 <= A \/ A + nb * 4 <= X).
    { destruct (Z.le_gt_cases X A); [left; destruct (Z.le_gt_cases (X+16) A); [lia| exfalso; apply (XA' A); lia] | right; destruct (Z.le_gt_cases (A + nb * 4) X); [lia| exfalso; apply (XA' X); lia]]. }
    clear XA'.
    (* [comment removed for export] *)
    assert (P4A : P mod 4 = 0) by (destruct OWF as [(_ & -> & _)|(_ & _ & _ & P16 & _)]; [reflexivity| flia]).
    assert (A4A : A mod 4 = 0) by flia.
    lazymatch type of HNEW with ?T => change (lx_hidden T) in HNEW end.
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK2).
    lx_run_tac (PLANS [0x46a40] [] 40%N (@nil summary)); lx_tree.
    all: try lor_align_leaf.
    all: try clear P4A A4A.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs; unfold lx_hidden in HNEW.
    all: lazymatch goal with Hz : 0 <= - zlow 64 ?Pz |- _ => assert (PZ : Pz = 0) by (unfold zlow in Hz; rewrite Z.mod_small in Hz by flia; flia)
                            | Hz : (zlow 64 ?Pz =? zlow 64 0) = false |- _ => assert (PNZ : Pz <> 0) by (intros EP; rewrite EP in Hz; discriminate Hz) end.
    { (* [comment removed for export] *)
      destruct OWF as [(-> & -> & ->)|(_ & _ & _ & _ & P0 & _)]; [| exfalso; lia].
      assert (limbs = []) as -> by (destruct limbs; [reflexivity| cbn in LEN; lia]). clear PZ.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      lazymatch goal with Hm : munch _ m2 m5, Hw : wmono _ m2 m5, Hc : rw_cells _ m5 X _ |- _ => rename Hm into MU; rename Hw into WM; rename Hc into CH end.
      lazymatch type of MU with munch ?W _ _ => apply (rw_cells_transport usegs W m2 m5) in HNEW; [| exact MU| exact WM| cbn; flia] end.
      replace (nb * 4) with (4 * nb) in * by lia.
      apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2.
      exists ((A, 4 * nb) :: LB), (mkMPD X sg nb A (repeat (Z_to_bv 64 0) (Z.to_nat nb)) pad LHeap), 0.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|].
      assert (XCW5 : forall a, X <= a < X + 16 -> client_waddr L ((A, 4 * nb) :: LB) lo (heap_top usegs L HI h) a).
      { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb|exact R]]. }
      split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU| exact WM|].
        intros a Ha NO. cbn in NO. rewrite HT2.
        destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [apply XCW5; lia|]|]; exfalso; flia. }
      split. { split; [|exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [exact CH|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite repeat_length; lia|]. split; [unfold MPI_MAX_LIMBS; lia|].
        split; [lia|]. split; [left; reflexivity|]. split; [exact A16|].
        eapply u32arr_of_cells; [exact HNEW|]. rewrite u32s_repeat0. f_equal. lia. }
      split. { cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
        split. { intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]. }
        split. { intros b Hb Hn. right. exact Hb. }
        intros b []. }
      assert (HPX5 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg 0 0 [] pad LNull)) m2 m5).
      { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _. (flsplit; repeat split); try exact I; flia. }
      split; [eapply heap_presx_trans; [exact HPX2| exact HPX5]|].
      split. { eapply statics_ok_munch; [exact SOK2| exact MU|]. intros a Ha NW. cbn.
               assert (O1 : ~ (X <= a < X + 16)) by (intros HX; exact (NW (XD a HX Ha))). (flsplit; repeat split); try exact I; flia. }
      split.
      - left. cbn [md_sg md_n md_pad md_limbs app]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [f_equal; lia|]. intros; exfalso; lia.
      - cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. intros Hin. pose proof (HAPA A (4 * nb) Hin). lia. }
    (* [comment removed for export] *)
    subst lxm. destruct OWF as [(_ & -> & _)|(-> & N1 & PIN & PAL & P0 & P4)]; [exfalso; exact (PNZ eq_refl)|]. clear PNZ.
    lazymatch goal with Hc : rw_cells _ m2 X _, Hf : rw_cells _ m2 (bv_unsigned sp + -32) _ |- _ => rename Hc into CH; rename Hf into FR end.
    repeat match goal with H : munch [] ?mx ?mx |- _ => clear H | H : wmono _ ?mx ?mx |- _ => clear H end.
    repeat match goal with H : stk _ m2 lo ?x, H' : stk _ m2 lo ?x |- _ => clear H' end.
    repeat match goal with H : mem_inv _ m2, H' : mem_inv _ m2 |- _ => clear H' end.
    pose proof MA2 as MA2c. flat constr:(MA2c) 2%nat. flclear MA2c. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ OWN2. cbn [md_own md_n md_p md_limbs] in OWN2. flat constr:(OWN2) 4%nat. flclear OWN2. intros _ _ _ PCH.
    specialize (XP eq_refl). pose proof (HAPA P (4 * n) PIN) as APA.
    assert (NN : bv_unsigned (zx16 (Z_to_bv 64 n)) = n) by (unfold zx16; rewrite !unsigned_lit by lia; apply Z.mod_small; lia).
    apply u32arr_cells in PCH.
    assert (HN2 : rw_cells usegs m2 A ([CB (4 * length limbs) (repeat (Z_to_bv 8 0) (4 * length limbs))] ++ [CB (Z.to_nat (4 * (nb - n))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (nb - n))))])).
    { eapply rw_cells_reshape; [exact HNEW| |].
      - cbn. rewrite !repeat_length; (flsplit; repeat split); reflexivity.
      - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. lia. }
    apply rw_cells_app in HN2. flat constr:(HN2) 2%nat. flclear HN2. intros HNA HNB. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
    pose proof (proj1 (u32arr_of_cells usegs m2 P _ _ limbs PCH eq_refl)) as PBA.
    replace (A + Z.of_nat (4 * length limbs + 0)) with (A + 4 * n) in HNB by lia.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 4 * nb); (X, X + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof U_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s limbs); rewrite ?unsigned_lit by lia; [ exact PBA | rewrite u32s_length; lia | replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia; exact HNA | lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post.
    rewrite !unsigned_lit by lia. post_call usegs m2.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
    match goal with H : rw_cells usegs m3 A _ |- _ => rename H into PA end.
    assert (HH3 : HEAP usegs L HI h2 ((A, nb * 4) :: LB) m3 mo2).
    { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. rewrite HT2.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(lia)) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb| exact R]] |] |].
      all: destruct (Z.le_gt_cases A a); [destruct (Z.lt_ge_cases a (A + 4 * nb)); [right; right; exists (A, nb * 4); split; [left; reflexivity| cbn; lia] |] |].
      all: left; lia. }
    clear HH2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (bv_unsigned (zx16 (Z_to_bv 64 n)) ≪ 2) with (4 * n) by (rewrite NN, Z.shiftl_mul_pow2 by lia; lia).
    eapply aevtM_cut.
    { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := P) (len := 4 * n) (lo := lo) (junk := u32s limbs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia.
      right. split; [right; exact PIN|]. replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia. exact PCH. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m4 mo4 h4 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    flat constr:(PO) 7%nat. flclear PO. intros MI4 ST4 MF4 HT4 HH4 PX4 SOK4.
    replace (ret_pc (Z_to_bv 64 127568)) with (Z_to_bv 64 127568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LBR : lb_remove P ((A, nb * 4) :: LB) = (A, nb * 4) :: lb_remove P LB) by (cbn; destruct (Z.eqb_spec A P); [lia| reflexivity]).
    rewrite LBR in HH4, PX4. clear LBR.
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in FR; [| cbn [cells_size csize Nat.add]; intros a Ha; left; lia | cbn; split; [lia| exact I] ].
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in PA; [| cbn [cells_size csize Nat.add]; intros a Ha; right; right; exists (A, nb * 4); split; [left; reflexivity| cbn; lia] | cbn; split; [lia| exact I] ].
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in HNB; [| cbn [cells_size csize Nat.add]; intros a Ha; right; right; exists (A, nb * 4); split; [left; reflexivity| cbn; lia] | cbn; split; [lia| exact I] ].
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in CH;
      [| cbn [cells_size csize Nat.add]; intros a Ha;
         destruct (XCW a ltac:(lia)) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [|exact R]];
         right; apply In_lb_remove_keep; [exact Hb|];
         intros ->; cbn in R; destruct (Z.eq_dec k (4 * n)) as [->|NE]; [lia| exact (nodup_fst_neq LB P (4 * n) P k ND PIN Hb ltac:(congruence) eq_refl)]
       | cbn; split; [lia| exact I] ].
    clear PCH.
    assert (HPX3 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m m3).
    { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
      destruct Hc as [C|[C|([B k] & Hb & R)]]; [first [clear_disj; lia | lia]| destruct DIMG; first [clear_disj; lia | lia]| pose proof (HAPA B k Hb); pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _); cbn in R, B4; first [clear_disj; lia | lia]]. }
    assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m m4).
    { eapply heap_presx_trans; [exact HPX3|]. intros a Ha Hc Ho. cbn in Ho. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
      apply PX4; [exact Ha| | cbn; split; [exact O2| exact I]].
      destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; first [clear_disj; lia | lia]| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
      right. apply In_lb_remove_keep; [exact Hb|]. intros ->. cbn in R.
      destruct (Z.eq_dec k (4 * n)) as [->|NE]; [lia| exact (nodup_fst_neq LB P (4 * n) P k ND PIN Hb ltac:(congruence) eq_refl)]. }
    clear HPX2 HPX3 PX4 MU WM MA2.
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo4 _ _ MK4).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lazymatch goal with Hm : munch _ m4 m5, Hw : wmono _ m4 m5, Hc : rw_cells _ m5 X _ |- _ => rename Hm into MU; rename Hw into WM; clear CH; rename Hc into CH end.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport usegs W m4 m5) in PA; [| exact MU| exact WM| cbn; flia];
      apply (rw_cells_transport usegs W m4 m5) in HNB; [| exact MU| exact WM| cbn; flia] end.
    replace (nb * 4) with (4 * nb) in * by lia.
    apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h4.
    exists ((A, 4 * nb) :: lb_remove P LB), (mkMPD X sg nb A (limbs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nb - n))) pad LHeap), 0.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [eapply mo_frame_trans; [exact MF2| exact MF4]|]. split; [rewrite HT4; exact HT2|].
    assert (XCW5 : forall a, X <= a < X + 16 -> client_waddr L ((A, 4 * nb) :: lb_remove P LB) lo (heap_top usegs L HI h) a).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
      right. apply In_lb_remove_keep; [exact Hb|]. intros ->. cbn in R.
      destruct (Z.eq_dec k (4 * n)) as [->|NE]; [lia| exact (nodup_fst_neq LB P (4 * n) P k ND PIN Hb ltac:(congruence) eq_refl)]. }
    split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH4| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. rewrite HT4, HT2.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [apply XCW5; lia|]|]; exfalso; flia. }
    split. { split; [|exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CH|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite length_app, repeat_length; lia|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [lia|]. split; [left; reflexivity|]. split; [exact A16|].
      apply u32arr_app. split; [eapply u32arr_of_cells; [exact PA| reflexivity]|].
      replace (A + 4 * Z.of_nat (length limbs)) with (A + 4 * n) by lia.
      eapply u32arr_of_cells; [exact HNB|]. rewrite u32s_repeat0. f_equal. lia. }
    split. { cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split. { intros b [<-|Hb]; [right; left; reflexivity| left; eapply In_lb_remove; exact Hb]. }
      split. { intros [B k] Hb Hn. right. apply In_lb_remove_keep; [exact Hb|]. intros ->.
               destruct (Z.eq_dec k (4 * n)) as [->|NE]; [apply Hn; left; reflexivity| exact (nodup_fst_neq LB P (4 * n) P k ND PIN Hb ltac:(congruence) eq_refl)]. }
      intros b [<-|[]] [E|Hin]; [injection E; lia| exfalso; exact (lb_remove_notin LB P (4 * n) ND Hin)]. }
    assert (HPX5 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m4 m5).
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _. (flsplit; repeat split); try exact I; flia. }
    split; [eapply heap_presx_trans; [exact HPX4| exact HPX5]|].
    split. { eapply statics_ok_munch; [exact SOK4| exact MU|]. intros a Ha NW. cbn.
             assert (O1 : ~ (X <= a < X + 16)) by (intros HX; exact (NW (XD a HX Ha))). (flsplit; repeat split); try exact I; flia. }
    split.
    - left. cbn [md_sg md_n md_pad md_limbs]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. intros; exfalso; lia.
    - cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. intros Hin. pose proof (HAPA A (4 * nb) Hin). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End G.
