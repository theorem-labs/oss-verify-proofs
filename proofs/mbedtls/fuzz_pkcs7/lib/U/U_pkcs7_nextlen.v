(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux X509Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0055e9b07d58db43 1 1 8 3 1 1 29 1 30 1 4 2 2 28 2 31 2 32 16P009cb0f7083ef592 0 4 0 1 2 1 30 1 31 1P0342033d2d6e4670 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P035e5967a340855d 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P059258eecc9d68bc 1 1 8 2 18 1 27 1 3 0 1 26 1 28 8P059d7c593970c9cf 0 4 0 1 2 1 30 1 31 1P07028cdcc3f252d1 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P08ce5065c3be02a6 0 2 0 1 1 1P090fade406e79f30 0 2 0 1 7 1P0adcbeff3e9d89eb 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P0b2571bd1e0245e1 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P0e0a34254285bc14 0 4 0 1 25 1 35 1 36 1P0f0afbe678f51ad9 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P1036c94828b83c9a 0 2 0 1 21 1P114fcb625e43cb2f 0 4 0 1 23 1 33 1 34 1P140b640215d5540e 0 2 0 1 17 1P17d33b26b27ca44b 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1f837e2c645ec5a0 1 1 8 3 1 1 29 1 30 1 4 2 2 28 2 31 2 32 16P206619ccf17f752f 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P231edbc0a0e39176 0 2 0 1 5 1P23dec634dbcc37ec 0 2 0 1 1 1P254b86de846029a5 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P270ada0d4aae52b1 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P28b4e23073585d52 1 1 8 2 19 1 27 1 3 0 1 26 1 28 8P290f6af0e687c997 0 2 0 1 5 1P2a96796ef471ea29 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P2ac76ec70578a321 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P2b1c5366b0e20b1b 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P2d1366dd21459d4a 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P2d685c8df486bd50 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P2ef0306a47f507f8 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P30fa30059d0b9483 0 2 0 1 5 1P332ac3ce34f9b878 0 2 0 1 23 1P332efbee82d00a48 0 2 0 1 6 1P3e0b2c99790d075b 0 2 0 1 20 1P3f9bd89fa2a0a0ea 0 2 0 1 22 1N010a9543a06bb2ccN017d55ff7bb41dbcN03292d211d0990c5N047f14470cdf2c94N0485f966224d4659N050897789a828840N055b4397fca011e6N05dcea52b4e5d35cN0ab55564792511ddN0b0004feacc3d411N0e8bf32255797d58N0fa3fed1e863796aN12ac8d21609a28e6N13c4f0c06fbe62cdN1635a2ab0c4c4571N17c5ae82082de7afN18021dd38d6a8002N196c393a3d9cc2b9N19bbdb4e28c8933eN1c4a21f6c0b9f3e0N1c71fa10406a2f11N1c7b7518b239c755N1dc0cd2d2dc3c637N1fa0fee8f3e03039N21289618517949faN22606eeab195cfebN22ea8b217bd52368N231595a111510930N239246f49893bf4fN23eb7e8afc6b8415N25236486643d0c62N2b147f268f5f1d25N2c4b7f84b9edec11N2d851bb5c23734deN2f4d3bac6d5ce75bN2f541c89599dd65fN30d75462c9b79e5bN30e86dc8e3249593N30fbdbdba02bed4cN3202414c74517f78N32bf1cf0eb78c115N345a49e4968fc13dN34979c1b47b19c7eN34e31cadffdbe533N3623d6f9457ad619N362759b31b46ab36N378c0736a6393bc1N37cc01bd1f8658e9N3ab904f27d2c55aaN3eccec43622bbf20N3f5718d706fad106"%lxh.
Ltac2 gd_tbl_P_pkcs7_nextlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Definition U_PKCS7_NEXTLEN : Z := 0x1dc2c.
Notation PKCS7_NEXTLEN_STACK := 32 (only parsing).

Definition pkcs7_nextlen_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pkcs7_nextlen ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+20.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-5600.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1;.R1.)(13.$1:.)))(5.(1<.O19.R4.O2.(12.&40.O17.))(5.(5.(18.O4.R2.)(18.R2.O3.))P,(6.$4.R3.=)(5.(18.(10.O4.+2.)R3.)(6.$4.(10.R3.(12.&40.R2.))O3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pkcs7_nextlen_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP LENP P END BUF lo : Z) (bs : list byte) (lenv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m LENP [C8 lenv] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= LENP \/ LENP + 8 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP) ->
  PP mod 8 = 0 -> LENP mod 8 = 0 -> 0 < PP -> 0 < LENP -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PKCS7_NEXTLEN_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (LENP + 8 <= lo \/ bv_unsigned sp <= LENP) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 LENP ->
  evt segs (pkcs7_nextlen_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Lemma U_pkcs7_nextlen_spec {L : heap_layout} : pkcs7_nextlen_stmt usegs U_PKCS7_NEXTLEN.
Proof.
  unfold pkcs7_nextlen_stmt, U_PKCS7_NEXTLEN.
  intros until lenv.
  intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LENB.
  change (Z.of_nat 8) with 8 in LENB.
  pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 32%nat ST.
  lxp_split_frame [8;8;8;8]%nat. lxp_seps 32.
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [] [] 103%N SUMS1).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
