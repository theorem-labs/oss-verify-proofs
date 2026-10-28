(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux X509Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_bitstring.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P015228dbc1e692e1 0 2 0 1 21 1P02d8a70c63cb3558 0 4 0 1 32 1 44 1 45 1P041044ac48d06a85 2 15 0 5 0 1 2 1 18 1 28 1 29 1 0 4 0 1 1 1 28 1 29 1P05205b136b77bf97 0 2 0 1 21 1P05b34af6e210f1ca 2 15 0 5 0 1 2 1 18 1 28 1 29 1 0 4 0 1 1 1 28 1 29 1P067a91f0cc55c9e6 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P088d73b6bc265389 2 15 0 5 0 1 2 1 18 1 28 1 29 1 0 4 0 1 1 1 28 1 29 1P0ace016029725299 0 5 0 1 2 1 24 1 26 1 37 1P0aeb2a0871c01a5c 2 33 0 5 0 1 1 1 36 1 48 1 49 1 0 4 0 1 2 1 48 1 49 1P0bbd48d6a7297a04 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P10effe3d5ebcd0aa 2 15 0 5 0 1 2 1 18 1 28 1 29 1 0 4 0 1 1 1 28 1 29 1P126970d71d2c3580 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P13f898ff876ce211 2 31 0 5 0 1 1 1 34 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P166694a5a5d059a8 0 4 0 1 28 1 40 1 41 1P16b1d17bbc3a5b98 0 4 0 1 31 1 43 1 44 1P1783e3a2c03ceb05 2 15 0 5 0 1 2 1 18 1 28 1 29 1 0 4 0 1 1 1 28 1 29 1P17e98e73a265f116 0 2 0 1 21 1P1897ece2c02d784b 0 4 0 1 31 1 43 1 44 1P18c73eb8b01df61e 0 2 0 1 19 1P1a0a1826ab256816 0 4 0 1 32 1 44 1 45 1P1a0ac39ea077f44e 0 4 0 1 34 1 46 1 47 1P1a25f3fe06bf3c5f 0 2 0 1 1 1P1b4f1042fb7b0ab7 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1d9397e0bbf68e7b 0 3 0 1 28 1 39 1P1dbe233cee04bd6a 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1ed339197a735994 0 2 0 1 20 1P1efdd906ab628efb 2 33 0 5 0 1 1 1 36 1 48 1 49 1 0 4 0 1 2 1 48 1 49 1P1f414d3005668d27 0 4 0 1 28 1 40 1 41 1P1f5982d627570fc3 0 2 0 1 18 1P1f91dcda27a5109c 0 2 0 1 21 1P211dc5cdb6a22993 2 33 0 5 0 1 1 1 36 1 48 1 49 1 0 4 0 1 2 1 48 1 49 1P22fc54da3b4ce73c 0 8 0 1 22 1 24 1 26 1 31 1 34 1 35 1 37 1P23ff32fb07e4ad57 0 4 0 1 28 1 40 1 41 1P25c494fadbc2ab6f 0 2 0 1 18 1P277ecb416660d3eb 0 4 0 1 34 1 46 1 47 1P287aa793033963a8 0 2 0 1 20 1P28a0790c8397d601 0 4 0 1 34 1 46 1 47 1P2a048e8702fd846a 2 31 0 5 0 1 1 1 34 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P2ab4918392b687bc 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P2b4509eba1fe0425 0 2 0 1 18 1P2fbb08a17da37483 0 4 0 1 32 1 44 1 45 1P2fd35e960ef4707d 0 4 0 1 31 1 43 1 44 1P31ded8c783f3b10f 0 2 0 1 20 1P3269ed9f28c39322 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P38a70c8f483aa37c 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P3c0f3d1a98cddc7b 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P3d90c222d8415993 0 2 0 1 1 1P3e4978b326f38060 0 2 0 1 21 1P3e8d2d30fc91a6f0 2 31 0 5 0 1 1 1 34 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P3eb09fb4c053d398 0 8 0 1 22 1 24 1 26 1 31 1 34 1 35 1 37 1P3f4142f965129cf4 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1N005e9fdea50340d2N00fda6afa93047afN0111beafefd74dd8N015b4152bd41e8f9N01a513bfbd8b6ba1N027925aee91d8b66N033e56502df86ae2N04434599414be8ffN05ca05f072fb4f91N0606b1fec83f5cccN070dcf9d12f807beN0790a6a8bff30623N07be5475104c475aN085ab23db6a6d9daN08fd6fe0ab7f5a10N0a5cdf531e8125dfN0b2fe551065613ffN0bafbbcac4ab30f6N0bfee4801206e817N0c0a28d21c9cf741N0cb58fda20d424eeN0cdcc2dd9e440b7bN0db852829c5ab42bN0e1a1e0b6b2dda6dN0e6f65107eea5c20N109c976d883847d4N11031f88524543e2N11bc566dfcbc01b2N12ac3687b52048feN13205e1fa3919d9dN13459745f018cb48N13d958061d985f9fN146fbfd8fbbdcc14N15c69c93a9327ab3N163c71b08d6092baN1648189fa8299976N167ba54e50fd72c8N173ecb4f61b1edc9N178057aa5b30109fN186a791a0a238adaN1a9dca25953149daN1aa80262d8f06f87N1ada543c088bc188N1cee8b5492502cadN1e2254140cf0b70cN1f267355d8e76fa3N1ff8d80d6bbed5b6N205532c599572214N20569ce32bbb45e3N224052d531567b2fN228195b0460dd648N22b9e7389c5ce770N246fcfa3b76cf087N268e5dcbcaf34a09N26989c4ae67f66d5N26a47a474d6aa6d4N27838b8c89311abaN290cec40a02aceebN297ac945c503e6efN29930002347493b5N299cf83c6f98841aN29d87703c8717719N2abd5e34e046cd6eN2ac6c7ea8c76bf0cN2bb3ab4a188a7d69N2c099efd88d3c061N2c5c23375fb07413N2f88eb90409409ccN2f9c09615c4b44edN30228e860d354e5aN31763d3f11d3211fN31a4a368c23b75f4N324630f58d1b8c39N328e0c4ca0e1fad4N331e516d4f5066f4N33bf6e6d2d902326N350c4fc2ccc93ca0N3566d2de02d59975N35daddb1b1f321fbN363204ed84793895N36320d81e5fd28faN3704cf8c4c55f7d5N387667053ccfc373N39a3c72e6752a4c0N39b3b6101b431f68N3aa69423d8936333N3b386ab345b42d07N3b8ecb3b9369ccbcN3bb120f2c9050474N3be4c7a619879c6aN3c4adc5b877219dbN3c7479ec09caec66N3cb5ed6debbe3566N3cf0a64a329e1313N3d2f4c89adeef616N3df7b50b935abde8N3f621258d3c8c646"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_ns_cert_type () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Definition U_X509_GET_NS_CERT_TYPE : Z := 0x28ea8.
Notation X509_GET_NS_CERT_TYPE_STACK := 80 (only parsing).

Definition x509_get_ns_cert_type_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP NS P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_ns_cert_type ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&8.)Lv,(2.&8.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+1.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+50.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-3000.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1<.R1.)(13.$1:.)))(5.(1=.O19.R4.O2.(12.&40.O17.))(5.(18.O4.R2.)(18.R2.O3.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_ns_cert_type_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP NS P END BUF lo : Z) (bs : list byte) (v0 : byte),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m NS [C1 v0] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= NS \/ NS + 1 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (NS + 1 <= BUF \/ BUF + Z.of_nat (length bs) <= NS) ->
  PP mod 8 = 0 -> 0 < PP -> 0 < NS -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_GET_NS_CERT_TYPE_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (NS + 1 <= lo \/ bv_unsigned sp <= NS) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 NS ->
  evt segs (x509_get_ns_cert_type_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP NS P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Local Ltac2 Set LiaOrc.tbl := fun () => "01<0@D11388703609.117D12428150072.116D1486160726.116 D21222177849.117D23189910102.117D25076071819.117D28556370513.117D30993319891.117D32699890468.117D34335414293.116D41549539716.117D41777267137.117D42456594038.117D42941640505.117D44454707256.116D44484923210.116D44926152022.117D50093495118.117D50452373632.117D50671478649.116D53850538065.116D55356914756.116D64645357113.116D67081454617.117L11388703609.112L12428150072.111L12428150072.113L1486160726.111 L20763668797.94 L20763668797.99 L20763668924.100L20763670321.103L22700267513.5  L23189910102.112L24417571617.0  L25076071819.112L25076071819.114L30993319891.112L31378308326.70 L31958642652.103L32699890468.112L32699890468.116L34335414293.111L34335414293.115L35103052813.100L37379186772.94 L3914178817.94  L3914178817.99  L3914178944.100 L3914180365.103 L41549539716.112L42456594038.112L42941640505.112L42941640505.114L43059266230.68 L44484923210.111L44484923210.113L44926152022.112L50093495118.112L50452373632.112L50671478649.111L52920467968.99 L55356914756.111L55356914756.113L59314873579.5  L66151426060.94 R11513106564.87 R14792943382.87 R17275046973.87 R23233893396.87 R39181178313.87 R54240564377.87 R60939260030.87 R64207379304.87 R68280421716.87 R806312532.87   00000100200300k00l00m01e01f01g01h01i02j02k02l03g03h03i03j03k03l04d04e05]06^07\07]07^08i09n0;30<80==0=K0>V0>W0>X0>Y0?X0?b0@Z0@[0@\0@]0@^0A_0B]0Cb0Dg0El0G10H?0IN0IO0IP0Ia0Ib0Ic0Jn0L=0MK0NJ0OB0OC0OD0OE0PF0R50SF0TE0UH0VY0WT0XS0ZJ0[_0]4FFFS2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFS2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFFFS2sp2PP2NS2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ43x201HFFS2sp2PP2lo2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFFFFS2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FS2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2NS2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ43x201HS2sp2PP2NS2bs2D11j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFS2sp2PP2lo2bs3NZ13SLO3DS13SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP2NS1x1HS2sp2PP2lo2bs3NZ13SLO3DS13SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4SFFS2sp2PP3BUF2bs2D21j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2bsS2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFFFS2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42Lw2LR2H4S2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ41r3PC0S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42p23PC4S2sp2PP2NS2lo2bs3NZ13SLO3DS23SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3BUF2lo2bs3NZ13SLO3DS33SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFS2sp2PP2lo2bs3SLOFFS2sp2PP2lo2bs3NZ13SLO3DS13SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3BUF2lo2bs3NZ13SLO3DS33SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2NS2lo2bs3NZ13SLO3DS23SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2lo2bs3DS11j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFSS2sp2PP2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ41r3PC02H6S2sp2PP2NS1P3END3BUF2lo2bs2B12B22B32D22D33NZ13SLO3DS13DS23DS33SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S1L2sp2PP2lo2bs3NZ13SLO3ACL3ACP3SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2lo2bs3SLO1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3BUF2lo2bs3DS31j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S1L2sp2PP2lo2bs3NZ13SLO3ACL3ACP3SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2lo2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2lo2bs3DS11j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP2NS1P3END3BUF2lo2bs2B12B22B32D12D23AL13NZ13SLO3SPA3DS13DS23DS33SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S1L2sp2PP2lo2bs3NZ13SLO3ACL3SPA3ACP3SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S1L2sp2PP2lo2bs3NZ13SLO3ACL3SPA3ACP3SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4". (* [comment removed for export] *)
Lemma U_x509_get_ns_cert_type_spec {L : heap_layout} : x509_get_ns_cert_type_stmt usegs U_X509_GET_NS_CERT_TYPE.
Proof.
  unfold x509_get_ns_cert_type_stmt, U_X509_GET_NS_CERT_TYPE.
  intros until v0.
  intros HPP HNS HBUF B1 B2 B3 B4 D1 D2 D3 AL1 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HNS) as NSB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in NSB.
  change (Z.of_nat 1) with 1 in NSB.
  pose proof (munch_refl [(PP, PP + 8); (NS, NS + 1); (bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  lxp_run (PLAN [0x1e90c; 0x28ef4] [] 51%N).
  (* [comment removed for export] *)
  lxp_gc. try lxp_statics.
  lxp_frame_cut (bv_unsigned sp + -48) [8; 16].
  try clear FRB.
  pose proof U_asn1_get_bitstring_spec as SP.
  unfold asn1_get_bitstring_stmt, U_ASN1_GET_BITSTRING in SP.
  callx_sp (bv_unsigned sp + -48)
    (eapply SP with (PP := PP) (BSP := bv_unsigned sp + -40) (P := P) (END := END) (BUF := BUF) (bs := bs) (lo := lo);
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by plia; try eassumption; try reflexivity; try plia).
  try clear SP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -40) (bitstring_cells ?lw _ _ ?pw) |- _ => rename H into FRB; rename lw into Lw; rename pw into Pw end.
  match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP; rename qq into p2 end.
  match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
  match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST' end.
  pose proof (bv_unsigned_in_range 64 Lw) as LR.
  unfold bv_modulus in LR.
  cbn in LR.
  lxp_gc.
  lxp_run (PLAN [0x1e90c; 0x28ef4] [] 51%N).
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_r0 r.
    subst r.
    destruct (HL0 eq_refl) as (q & -> & Hq1 & Hq2 & Hq3).
    try clear HL0. try clear Kr.
    lxp_gc.
    lxp_run (PLAN [0x1e90c; 0x28ef4] [] 51%N).
    { (* [comment removed for export] *)
      lxp_ret.
    }
    { (* [comment removed for export] *)
      lxp_ret.
    }
    { (* [comment removed for export] *)
      lxp_ret.
    }
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
