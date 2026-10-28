(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002a13fd8c35b85f 0 4 0 1 2 1 37 1 38 1P00fb7b3c46f01c21 1 1 16 2 0 1 35 1 3 16 1 36 1 37 16P01cf3db84aa4f481 0 4 0 1 34 1 44 1 45 1P01f71e96519217a5 1 1 8 3 0 1 38 1 39 1 5 2 2 27 2 37 2 40 2 41 16P0229337cc331a464 0 2 0 1 1 1P028972d2e4668472 1 1 8 3 1 1 37 1 40 1 4 2 2 38 2 39 2 41 16P046afae294ddeb84 0 3 0 1 4 1 30 1P053839cba5d6b008 0 4 0 1 34 1 44 1 45 1P061a72607f5422a3 0 2 0 1 5 1P066254317c016a7a 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P07e5a9925787683a 1 1 8 3 0 1 38 1 39 1 5 2 2 27 2 37 2 40 2 41 16P09b61c31c2d2ca43 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P09b6dfb740dd8ff0 2 24 1 1 8 3 1 1 38 1 39 1 5 0 2 27 2 37 2 40 2 41 16 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P0b0f662868b7119f 0 2 0 1 6 1P0cf27bf559bf0880 0 4 0 1 32 1 42 1 43 1P0e98c0ab9ce4a2f1 1 1 8 3 1 1 37 1 40 1 4 2 2 38 2 39 2 41 16P0fefd668c10bd384 0 2 0 1 29 1P10f3c4c46019bd85 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P11574f350bba58bd 0 2 0 1 1 1P126acfaad787adaa 1 1 8 3 0 1 38 1 39 1 5 2 2 27 2 37 2 40 2 41 16P126aefa6f78df20a 0 2 0 1 3 1P146a177b278c8f27 0 2 0 1 17 1P1488ed9cd260157b 1 1 8 3 1 1 28 1 31 1 4 2 2 29 2 30 2 32 16P15362cad06d0f587 0 2 0 1 5 1P16c00e357036b64f 0 2 0 1 6 1P174c44eb6d958fc5 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1817c64bd2a75afb 0 4 0 1 2 1 30 1 31 1P1821952ba81c4b2a 0 5 1 1 3 1 28 1 38 1 39 1P18897f8b79ef5f59 1 1 8 3 1 1 29 1 30 1 4 2 2 28 2 31 2 32 16P19478d2316b55d23 0 4 0 1 2 1 28 1 29 1P196290f6266987c3 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P1a39b3b5cffbe412 1 1 8 3 0 1 29 1 30 1 4 2 1 28 1 31 1 32 8P1aa78881f22bd342 1 1 8 3 1 1 37 1 40 1 4 2 2 38 2 39 2 41 16P1dc3b60958fec4ad 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1eebec34eb2a4df0 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1fa72c32be0df447 0 4 0 1 3 1 38 1 39 1P21484a4961a9b57c 0 4 0 1 23 1 33 1 34 1P22469f958b2fd8fe 0 2 0 1 5 1P2500cbd2ba078e41 0 1 1 1P25f9e692447980e3 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P260e89fbef1a4a39 0 4 1 1 2 1 28 1 29 1P2647d69dd27a04d2 1 1 8 3 1 1 38 1 39 1 4 2 2 37 2 40 2 41 16P2790896572c28b7f 0 2 0 1 23 1P2800514c95f864eb 0 2 0 1 5 1P297adee055d397e1 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P29a605591a648f92 0 4 0 1 32 1 42 1 43 1P2a18e26a2f223292 1 1 8 3 1 1 28 1 31 1 4 2 1 29 1 30 1 32 8P2a65d3ce5de996ad 0 4 0 1 2 1 39 1 40 1P2a873b85e4ee803e 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P2bc75233f1f203cc 1 1 8 3 0 1 37 1 40 1 4 2 2 38 2 39 2 41 16P2c4b9e0ab051d16c 1 1 8 2 28 1 36 1 3 0 1 35 1 37 8P2c5e526b15cacea2 0 2 0 1 7 1P2c7c77dde660e83f 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P2c89f452abcc6216 0 2 0 1 5 1P2d03c78cfe223937 0 4 0 1 2 1 30 1 31 1P2d605042720bc3ab 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P2e94ed57db86edcf 0 2 0 1 21 1P2f36dbd10b4303d5 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P3269a8e51a892556 1 1 8 3 1 1 38 1 39 1 5 2 2 27 2 37 2 40 2 41 16P328cc5e5a9a92d90 0 4 0 1 34 1 44 1 45 1P32fbea1dd1f7b3f7 0 4 0 8 13 8 26 8 27 8P3369eb3e84aa186c 0 2 0 1 22 1P337e9364d93a7386 0 2 0 1 20 1P340bcca7bde6a4e8 0 4 0 1 32 1 42 1 43 1P34f8f155dcf05f3c 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P35ce31f59ad9ecb2 0 5 1 1 2 1 27 1 37 1 38 1P36adbe82e29c9dea 0 2 0 1 5 1P38a03b87a2701104 0 3 0 1 5 1 32 1P38ac3db99b819df9 0 2 0 1 26 1P391646ab5ce018d8 1 1 8 3 1 1 29 1 30 1 4 2 2 28 2 31 2 32 16P39bf242b40282452 1 1 8 2 19 1 27 1 3 0 1 26 1 28 8P39d2394894193aa4 0 2 0 1 7 1P3c61c91eef728a57 1 1 8 3 0 1 29 1 30 1 5 2 2 18 2 28 2 31 2 32 16P3e6800b358ac35bc 0 2 0 1 1 1P3e8de7819db09de7 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P3f921fce8bd6b30d 0 2 0 1 1 1N0060348d2246ba13N01f6c9ee79e9554aN05c662c9dd76fc5cN064c93b9101878e3N075023dc4f83c665N07f4ce4a53a11bb3N090caa7334950395N093de0ad506d9543N099231d6e3de6dc6N099d27fc1f7f80f9N09ea9bcf8fdfec2dN0a988ee26cbebc90N0b6eb9775ed6f7feN0bd745ae61b07805N0bffc24eaf348cdbN0c237e8939cc054aN0ce6b1b6b63d5d96N0dc5b11cfd526153N0f381998db4a53b3N0fb9c35bf089be9bN0ff2807c66b73f4aN0ffed8c74eea6526N103a462825df445fN10503452924d4f15N111e1cee63a42c25N1234f4e1cf8e2858N1269d504062fc718N12f9c3d526caeb28N135eba87e725bcfcN138ebc197e8d8d16N14a711b2f2620937N16cff0019cbdece3N16f5de2227623201N17bfce6e935b9a14N17d5e538d351118cN18b57abac6575d47N18db413d24d97b3bN1a209a4b1e2447b4N1a6e30383605c530N1aedf0664363b5bcN1c2b1069b73edea5N1ccf4c738f7f622eN1e08b8e791319f13N1e6527d40cb08197N1fe67f8f27b2beb6N2023a179f2e6e486N2092b970e4f3fc40N20b81abce7002559N22ad3ea7ad760726N22d87bd99cab763cN23e1033fe0e96e85N2482c396ba74c9d0N24aa33f5ebd35dc9N25643e0bf2a626e0N25a73348040c4194N25e204a8fe6ee8c4N26fd299ac9ed9aa2N2834d4c3bbbd00c5N29f3d25454f5caaeN2a3e219d1786d4baN2ae43da9a76b7b0eN2ba65128663955b2N2bb5aa456af907b6N2bfebfc50c63c523N2c99c5d76aec5104N2d1fcb9e60156a5fN2e5e6e432bf96c2fN2ebf1d930b8c05f9N2f1e1af7e720a5ccN2f971baee61221d2N2fb4804e278cbda1N311c1a5071acd302N32cfa9fc78c80309N33194206515fb6c4N335a6a9606e04fddN33a77a0353319abcN3487f9b7588ea7c6N34f398924908415dN35bc4a1be08d1544N35ce4824b861cb4dN36c656fdf5ad54bfN36ceda8c8de179ecN36eeebcc8f2ae02cN36ffafc8d986dbbcN37738149460eeaf7N3802dc968de32a85N3802ed1990508f8aN38291ba8bb36091cN38b9adbc23e50ff5N396d14b791a43a0fN3a1a6023034a9422N3a548db4b237bf16N3a75ac1c5be27e65N3ac1db6a646bbaeaN3b379358bb97476eN3b49f2ba10ab39e0N3bf6e77089061190N3c37b361a410e3a5N3c442b77353bf4f4N3cdc732bb997bfedN3dbbf41f0fe1c5e1N3e28fbcc2abe9117N3e3a871907a5629bN3eef10b0f5560acb"%lxh.
Ltac2 gd_tbl_P_x509_get_ext () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Definition U_X509_GET_EXT : Z := 0x28698.
Notation X509_GET_EXT_STACK := 48 (only parsing).

Definition x509_get_ext_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP EXT P END lo : Z) (pad : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_ext ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Ltg,(2.&40.)(1.$4.Llen,$4.(1.$4.Lq,$4.(5.(6.$0.R16.(7.(8.O19.O18.O17.O16.R15.R14.R13.O15.O14.R12.R11.R10.R?.R>.R=.R<.R;.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R:.R9.R8.R7.)O9.(9.O19.)O8.(:.(2.&40.))R6.(;.O1:.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+8.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O18.)+30.)(12.&40.O18.))(13.(>.$4.$4.)))))O1.R6.)(5.(14.O1:.O1.R6.)(5.(15.O1:.R6.)(5.(6.(2.&40.)R12.(16.&40.R5.))(5.(5.(17.-3000.R5.)(18.R5.=))(5.(19.O1:.R6.O7.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1:.R6.O6.(=.$1:.(1<.R3.)(=.$1:.(1<.O2.)(=.$1:.(1;.(16.&40.R2.))(=.$1:.(1;.(16.&40.R1.))(13.$1:.))))))(5.(1=.O1:.R6.O3.(12.&40.O18.))(5.(5.(18.O5.R4.)(18.R4.O4.))P,(6.$4.R5.=)(5.(18.(10.O5.+2.)R2.)(5.(18.=R3.)(5.(18.(10.R2.R3.)O4.)(5.(18.(10.R2.+2.)R5.)(18.R5.(10.R2.R3.)))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_ext_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP EXT P END BUF lo tag : Z) (bs : list byte) (tg0 pad : word) (len0 q0 : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m EXT [C4 tg0; C4 pad; C8 (Z_to_bv 64 len0); C8 (Z_to_bv 64 q0)] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= EXT \/ EXT + 24 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (EXT + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= EXT) ->
  PP mod 8 = 0 -> EXT mod 8 = 0 -> 0 < PP -> 0 < EXT -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_GET_EXT_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (EXT + 24 <= lo \/ bv_unsigned sp <= EXT) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 EXT -> a3 = Z_to_bv 64 tag ->
  evt segs (x509_get_ext_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP EXT P END lo pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Lemma U_x509_get_ext_spec {L : heap_layout} : x509_get_ext_stmt usegs U_X509_GET_EXT.
Proof.
  unfold x509_get_ext_stmt, U_X509_GET_EXT.
  intros until q0.
  intros HPP HEXT HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HEXT) as EXTB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in EXTB.
  change (Z.of_nat 24) with 24 in EXTB.
  pose proof (munch_refl [(PP, PP + 8); (EXT, EXT + 24); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  (* [comment removed for export] *)
  pose proof (@sums2_ok _) as LXSUMS.
  lxp_run (PLANS [] [] 62%N SUMS2).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
