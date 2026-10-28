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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000babe38ee12b16 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P00310dae59564dc3 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P025ccc91f5d4408f 0 5 1 1 3 1 19 1 29 1 30 1P03725e97a8baf60d 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P05e319ae30c8e403 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P0678f6625f092369 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P068079aa85d44484 0 2 0 1 5 1P0b51a98c2c49fe98 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P0bdb764f145d01b8 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P0cf7e184ec48e56a 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P0d0c71de57e8a76e 1 1 8 3 1 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P0dd5f967d0b6ad95 0 4 0 1 2 1 28 1 29 1P0f082b5af1146618 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P0f4503a2493cef8b 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P103639d34f534372 0 2 0 1 17 1P10fda9b9a0c811a9 0 2 0 1 20 1P12a2b0a8f7e69646 0 2 0 1 23 1P146d76760532e78c 0 4 0 1 3 1 29 1 30 1P14b612b5727308f0 2 25 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P15c8aca43cad01eb 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P191bfcc13aa4de55 0 2 0 1 5 1P1af8fe9d8e1b825e 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1d925b46144deb01 0 2 0 1 5 1P1dfbdeab9ab6b82f 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P1f7fd927d1be23df 0 4 0 1 25 1 35 1 36 1P207c6ca115cbcbcb 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P2238ba8fee7d0732 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P23d8050b2bdad899 1 1 8 3 0 1 28 1 31 1 4 2 2 29 2 30 2 32 16P246db72bec289637 0 4 0 1 25 1 35 1 36 1P24c5ef29dccbb7b5 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P25b71546e130fb71 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P276c9139d10ff4bb 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P27f07d403c9babf8 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P2c1e1b287a02eb1a 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P2c846de83be2e29b 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P2d2d645765c610d3 0 4 0 1 2 1 30 1 31 1P2d54e8d56a81457b 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P2da94cee562761cd 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P2fb7dda8b9be4d0a 1 1 16 2 0 1 26 1 3 7 1 27 1 28 16P3109d00e90e8dd01 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P318dec03651e112b 0 2 0 1 22 1P32102dee5f5da53d 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P348751c7455121b2 0 1 1 1P351bb4162b2a5170 0 4 0 1 23 1 33 1 34 1P36e2b3bf11e686f2 1 1 8 3 1 1 29 1 30 1 4 2 2 28 2 31 2 32 16P36eba8a58a13a02b 0 2 0 1 6 1P37525919bb51a1de 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P37672496d82753db 2 25 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P390bacefae3e1d14 0 2 0 1 21 1P39191fc52d010b44 0 4 0 1 25 1 35 1 36 1P39b4f28a8169a6f1 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P39bb7674ac22fbff 1 1 8 2 19 1 27 1 3 0 1 26 1 28 8P39cb1e8ada1d55a8 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P3b5c93bf95d86bce 0 2 0 1 1 1P3c6df7d7f4e5753c 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P3d0c8fedcc4f1980 0 5 1 1 2 1 18 1 28 1 29 1P3d93d37ebaf9f3f2 2 25 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P3e5f22b73b8a2dde 0 4 0 1 23 1 33 1 34 1P3fa8d5c81e964d5f 0 4 0 1 23 1 33 1 34 1N00e1a0a805186181N01ee22091b62452bN01f1e3aca716318cN03de6dd56267eddaN04f05131fae3a72fN051a7061739eff0bN0570041866fc2e72N05cb897b1b662e95N07783ab8ab147c2eN089724dd80e2ae5eN08b3b7e530bfff5bN0df4efa73ed0d5dfN0e4d6efc8b64ac42N0f3263777cce2b08N13146b6abcf1c6b9N13df4d18eaf46509N143ebb3a7eaf6657N1711f23bee143d63N180afd04639ae56aN18890223d1a9ea2cN1c13bc294c883f94N1ce79dbc2da5beeaN1d2ee48895e499eeN1f3cfb657a8d00b0N202cee34b35b3014N2084d1506d46f4bbN211ffbc5ffac6c04N2206272c4757b07dN26edf38977a70247N27d35bfd6a413b6fN2808819b52bc1b91N2ab04f35b79398e5N2acbf6f3ea5f1470N2ba16bed960b88fdN2bbc73169cbcfe97N2c89b6591b62e584N2ca9c762156242e9N2e7537ef61f171c0N2f9a879b09a09fe4N31ae8548f8608826N334cb26bd07160a9N33d6e5f2bd3cb3f8N34f0d32c13e7d6d8N35129eb42b6c7e86N35cd256803ce6e7cN3702e1f3b9c04c6bN3784fc22cb1439c2N388619cc2195b055N38c7d03a0a1e9247N39a937ca0c982409N39cc12042d3f6bd3N3bde015f149554f0N3d3bebfd726a9bc2N3dd719224a49ea48N3e2f6cb49443f124N3eef6327135f1369N3f63e7f06c92286dN3f6c5749ec21e79e"%lxh.
Ltac2 gd_tbl_P_pkcs7_getsig () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Lemma land64_zero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 (2^64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.

Definition U_PKCS7_GETSIG : Z := 0x1e45c.
Notation PKCS7_GETSIG_STACK := 48 (only parsing).

Definition pkcs7_getsig_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP SIGB P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pkcs7_getsig ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Ltg,(2.&40.)(1.(2.&40.)Lpad,(2.&40.)(1.$4.Llen,$4.(1.$4.Lq,$4.(5.(6.$0.R17.(7.(8.O18.O17.O16.O15.R16.R15.R14.O14.O13.R13.R12.R11.R10.R?.R>.R=.R<.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R;.R:.R9.R8.)O8.(9.O18.)O7.(:.(2.&40.))R7.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+30.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R7.)(5.(14.O19.O1.R7.)(5.(15.O19.R7.)(5.(6.(2.&40.)R13.(16.&40.R6.))(5.(5.(17.-7?.R6.)(18.R6.=))(5.(19.O19.R7.O6.(=.$1:.(1;.(16.&40.R5.))(13.$1:.)))(5.(19.O19.R7.O5.(1<.R4.R3.R2.R1.))(5.(1=.O19.R7.O2.(12.&40.O17.))(5.(5.(18.O4.R5.)(18.R5.O3.))P,(6.$4.R6.=)(5.(6.(2.&40.)R5.(16.&40.+4.))(5.(18.(10.O4.+2.)R2.)(5.(18.=R3.)(6.$4.(10.R2.R3.)R6.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pkcs7_getsig_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP SIGB P END BUF lo : Z) (bs : list byte) (tg0 pad : word) (len0 q0 : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m SIGB (buf_cells tg0 pad len0 q0) ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= SIGB \/ SIGB + 24 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (SIGB + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SIGB) ->
  PP mod 8 = 0 -> SIGB mod 8 = 0 -> 0 < PP -> 0 < SIGB -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PKCS7_GETSIG_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (SIGB + 24 <= lo \/ bv_unsigned sp <= SIGB) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 SIGB ->
  evt segs (pkcs7_getsig_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SIGB P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac spine_firstn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
  | Datatypes.S ?k' => lazymatch cs with
             | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
             | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
             end
  end.
Ltac spine_skipn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => cs
  | Datatypes.S ?k' => lazymatch cs with
             | _ :: ?cs' => spine_skipn k' cs'
             | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
             end
  end.
Ltac joinr H1 H2 :=
  lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn; lia);
    let Hj := fresh "J" in
    pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
    cbn [app] in H1
  end end.

Lemma U_pkcs7_getsig_spec {L : heap_layout} : pkcs7_getsig_stmt usegs U_PKCS7_GETSIG.
Proof.
  unfold pkcs7_getsig_stmt, U_PKCS7_GETSIG.
  intros until q0.
  intros HPP HSIG HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HSIG) as SIGBB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in SIGBB.
  change (Z.of_nat 24) with 24 in SIGBB.
  pose proof (munch_refl [(PP, PP + 8); (SIGB, SIGB + 24); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold buf_cells in HSIG.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [] [] 46%N SUMS1).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
