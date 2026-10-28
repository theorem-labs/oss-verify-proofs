(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_pkcs7_nextlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00205f4017d33cc9 0 4 0 8 22 8 41 8 42 8P00c114de31327203 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P00f00f3a9084dd03 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P01955ed4beb95410 0 4 0 1 22 1 32 1 33 1P02924f0f734fe47e 0 4 0 1 22 1 32 1 33 1P03be7bcbc96813bf 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P0401b1068c29d45f 0 4 0 1 22 1 32 1 33 1P044ca273ca0cf85c 1 1 8 3 0 1 35 1 36 1 5 2 2 24 2 34 2 37 2 38 16P05bbf8edc29c9126 1 1 8 3 1 1 34 1 37 1 4 2 2 35 2 36 2 38 16P05faaf1c01e18d81 0 4 0 1 29 1 39 1 40 1P08ad8eaca090039b 0 4 0 1 32 1 44 1 45 1P09a194f8d1c3d4e2 0 4 0 1 32 1 44 1 45 1P09b0964d9ca29a6b 0 4 0 1 32 1 44 1 45 1P09ba36a367ad790b 0 4 0 1 32 1 44 1 45 1P0a6c1510c6f7ca8c 0 4 0 1 3 1 35 1 36 1P0b1bfb4ec51c2cdb 1 1 8 2 0 1 41 1 3 23 1 42 1 43 8P0bc6f29e28b366f1 0 2 0 1 7 1P0dae1b60f4dd2d21 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P0fa3a2b0cba9cf14 0 4 0 1 29 1 39 1 40 1P0fbc93e5d0c6f2f8 0 4 0 1 32 1 44 1 45 1P1091ba865fce658d 1 1 8 3 1 1 34 1 37 1 4 2 2 35 2 36 2 38 16P12234c3c19a736e5 0 2 0 1 5 1P1226f73d9aa1540d 0 2 0 1 1 1P129dbfe2862f1b4c 0 4 0 1 32 1 44 1 45 1P13099e435d2b0ddb 1 1 8 3 1 1 34 1 37 1 4 2 2 35 2 36 2 38 16P136505b3e195dfb4 0 4 0 1 22 1 32 1 33 1P1463354b86caf8ac 0 4 0 1 2 1 36 1 37 1P14bdac4ed4ac6b56 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P15f3bdb0c2cd7059 1 1 8 2 24 1 33 1 3 0 1 32 1 34 8P1913f3fe1732e276 1 1 8 3 0 1 35 1 36 1 5 2 2 24 2 34 2 37 2 38 16P1945f830973bf67b 0 4 0 1 1 1 33 1 34 1P1a748229e9430c92 0 4 0 1 29 1 39 1 40 1P1a75eb0a4c7496a1 0 4 0 1 32 1 44 1 45 1P1bf815a1702388ab 0 5 0 1 1 1 23 1 33 1 34 1P1c82373026441bb7 0 2 0 1 1 1P1cc5898270756f88 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P1d83f36920d2d274 0 4 1 1 3 1 35 1 36 1P1dbe67abcb2583c6 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P1e63f68eb05aafcb 1 1 8 3 1 1 34 1 37 1 4 2 2 35 2 36 2 38 16P1f3196295d7db1d2 1 1 16 2 17 1 32 1 3 0 1 33 1 34 16P1f72308f932efd3d 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P2011af99a04de109 0 2 0 1 29 1P202680f78c07fd89 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P20a3500892ebd174 0 2 0 1 5 1P2124cf58fc4a12e7 0 2 2 1 4 1P219ff72b09e275dd 1 1 8 3 0 1 35 1 36 1 5 2 2 24 2 34 2 37 2 38 16P21ec745616ca5dd6 0 4 0 1 32 1 44 1 45 1P226d570a3f50a42b 0 4 0 1 3 1 35 1 36 1P251d0ebc3ce80722 0 4 0 1 32 1 44 1 45 1P25d50fadb18809ab 0 4 0 1 32 1 44 1 45 1P277d26fd5640be9c 0 4 0 1 2 1 36 1 37 1P28efc8abc372d819 0 4 0 1 32 1 44 1 45 1P295b1f5dec632329 0 4 0 8 24 8 41 8 42 8P2a2e48919209adde 0 2 0 1 1 1P2a542edaef7420ea 0 4 0 1 22 1 32 1 33 1P2c13a3e673b3f470 1 1 16 2 0 1 32 1 3 6 1 33 1 34 16P2d2aa6056320d2f4 0 2 2 1 4 1P2dbc1d5ff0d9650e 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P2dbcff9abe377d3e 0 4 0 1 3 1 35 1 36 1P2e76083d9a4dbd0d 0 4 1 1 3 1 35 1 36 1P2ed6b86fdcd4fef0 1 1 8 3 1 1 35 1 36 1 4 2 2 34 2 37 2 38 16P31e4208a184cc43c 0 4 0 1 22 1 32 1 33 1P32026bd32672a41f 0 4 0 1 22 1 32 1 33 1P321651997b7281a1 1 1 8 2 0 1 41 1 3 25 1 42 1 43 8P326720477f0006f7 1 1 8 3 1 1 35 1 36 1 4 2 2 34 2 37 2 38 16P328d986ed4ac2543 0 2 0 1 2 1P32dc3b2d3d164e42 0 4 0 1 29 1 39 1 40 1P33d4191f42fa5277 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P348c4c8cd6201ddf 0 2 0 1 27 1P358cf9c65c8644d8 0 4 0 1 22 1 32 1 33 1P3591e4218ad731af 0 4 0 1 29 1 39 1 40 1P35ff2f2faf8565fe 0 2 0 1 6 1P36fb042faed7e02e 0 4 0 1 32 1 44 1 45 1P3763e9e9e6531fa5 0 2 0 1 5 1P37f4fb8ee9cbac06 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P38d48b119d83f01d 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P3a2f395a44bc44f3 0 4 0 1 29 1 39 1 40 1P3ab1027e4042acbf 0 2 0 1 26 1P3ad3926ce8f753a3 0 5 1 1 3 1 25 1 35 1 36 1P3b27874ffad88a34 0 2 0 1 25 1P3c364cf5bac76112 0 2 2 1 4 1P3c449ea51996397f 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P3d7a17589e90593a 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P3d867081a5029dd6 0 2 0 1 28 1P3f0eb7503443e564 1 1 8 2 23 1 33 1 3 0 1 32 1 34 8P3fa16020b55d3e7e 1 1 8 3 0 1 35 1 36 1 5 2 2 24 2 34 2 37 2 38 16N0236790c47c72dbeN045be90b9232c5b3N0499019af333499cN05eb4c5c8dfa158cN076362bd64b690e3N0809ebb537b07d49N09d2b260a9de65f6N0a3c0584c0f735d6N0d41e7fd817d9569N0db712939b59e33aN0e434d4f8aa15070N0e517ecc7d0d7af0N0f24f05202c31e34N0fe5fca718853492N10efb1ebcdc64782N14a0c2f8a59714f6N182038e184b82516N1887a908524d4545N18b4452406e81585N1932befa015ef9b7N19dabd0312878232N19eb7d372c74692aN1bdef884779ca521N1c837eafc45c854cN1ccc24fb3116784cN1d4d1ee9f86a2d44N1f1adad5d32be756N1f3849af06ea47acN2002dafda73f528dN2116775c909dbbafN22064cb8590a518fN225fe420c60d3abdN25a3458aee2e3435N25f69475508f5f62N2740d4e6c7a6b7eaN29f87aaff9ca65e7N2b085dc3b1f17b7fN2b62711c1454ce5aN2bd301f303534b07N2bd895d719a1e39aN2d74b3a2cb813226N2d82080481983153N2da3192dd9e7a3e0N2e214c9cd3c69293N2fac1046eaef4e79N2fd23593639b60a3N309b06655c2b84e2N30a8fb85d53b5812N31956352af8b3cd1N31f7c539cc698cb4N3266688f7556bb0fN33f8ce9b9d1eeee2N342f5737b8db6b31N38b01133396371fbN39ee1a10904de68fN3a36055562493905N3a6e16616fa50430N3b0098fbbeb90e28N3b3a09fbdbecde0dN3c23f0be14db9c71N3cd95b9862f23011N3e5a189a4fe43a00N3ea53ce6813c6e82N3eaa9919c3958d91"%lxh.
Ltac2 gd_tbl_A_pkcs7_nextlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "pkcs7_nextlen_postA"].


Definition A_PKCS7_NEXTLEN : Z := 0x0980b4.
Notation PKCS7_NEXTLEN_STACK_A := 64 (only parsing).   (* [comment removed for export] *)

Definition pkcs7_nextlen_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_nextlen ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+40.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-5600.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1;.R1.)(13.$1:.)))(5.(1<.O19.R4.O2.(12.&40.O17.))(5.(5.(18.O4.R2.)(18.R2.O3.))P,(6.$4.R3.=)(5.(18.(10.O4.+2.)R3.)(6.$4.(10.R3.(12.&40.R2.))O3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pkcs7_nextlen_stmtA {L : heap_layout} (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP LENP P END BUF lo : Z) (bs : list byte) (lenv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m LENP [C8 lenv] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= LENP \/ LENP + 8 <= PP) ->
  (Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (Z.of_nat (length bs) = 0 \/ LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP) ->
  PP mod 8 = 0 -> LENP mod 8 = 0 -> 0 < PP -> 0 < LENP -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PKCS7_NEXTLEN_STACK_A -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (LENP + 8 <= lo \/ bv_unsigned sp <= LENP) ->
  (Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  (* [comment removed for export] *)
  al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m PP 8 -> aobj segs AL CS m LENP 8 -> aobj segs AL CS m BUF (Z.of_nat (length bs)) ->
  crange CS lo (bv_unsigned sp - lo) ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 LENP ->
  evtA segs AL CS (pkcs7_nextlen_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Context {L : heap_layout}.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : LENP mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < LENP.
  Hypothesis SPL : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : LENP + 8 <= lo \/ bv_unsigned sp <= LENP.
  Hypothesis DS3 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation W := [(PP, PP + 8); (LENP, LENP + 8); (bv_unsigned sp - 64, bv_unsigned sp)].
  Notation POST := (pkcs7_nextlen_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).

  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_nextlen ()) "Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Plenv,(2.&40.)P,(19.$1=.Vm,VPP,(=.$1:.(1;.(16.&40.VP,))(13.$1:.)))P,(19.$1=.Vm,VLENP,(=.$1:.(1;.R2.)(13.$1:.)))P,(1>.$1=.Vm,VBUF,Vbs,)P,(15.$1=.Vm,)P,(1?.$1=.VAL,Vm,)P,(20.$1=.VAL,VCS,Vm,VPP,+8.)P,(20.$1=.VAL,VCS,Vm,VLENP,+8.)P,(20.$1=.VAL,VCS,Vm,VBUF,(21.(22.(2.&8.)Vbs,)))P,(1<.$1=.Vm,Vlo,(12.&40.Vsp,))(23.$1=.VAL,VCS,(24.$1=.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VPP,)(16.&40.VEND,)(16.&40.VLENP,)R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+980;4.)Vfc,(:.(2.&40.))Vm,(;.$1=.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros a3 a4 a5 a6 a7 lenv HPP HLEN HBUF MI AB OPP OLEN OBUF ST.
  pose proof (munch_refl W m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn [Z.pow Z.of_N Pos.pow] in SPR.
  carve_frame 48%nat ST.
  pose proof (sums_asn1_ok AL IMG) as LXSUMS.
  lx_pre. lx_run_tac (PLANS [0x98178] [(0x9814c, DSplit)] 88%N [SUM_getlenA; SUM_gettagA]).
  lx_tree.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
  all: lxu_chk_leaves 0x98178.
  all: match goal with |- ?g => idtac "lx END FORM main_walk: unexpected leaf left:" g end.
  Qed.
End Walk.

Lemma A_pkcs7_nextlen_spec {L : heap_layout} : forall AL, asan_img_ok AL -> pkcs7_nextlen_stmtA asegs AL A_PKCS7_NEXTLEN.
Proof.
  intros AL IMG. unfold pkcs7_nextlen_stmtA, A_PKCS7_NEXTLEN.
  intros until lenv. intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI ALWF CSOK AB OPP OLEN OBUF SCS -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0. pose proof (proj1 ST) as LO0.
  eapply main_walk; try eassumption; try lia.
Qed.
