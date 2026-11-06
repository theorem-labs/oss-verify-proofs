(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0132df590fc9900e 0 2 0 1 1 1P01a6632b6cba4908 0 4 0 1 1 1 2 1 24 1P01aa5098e2d157cd 0 2 0 1 28 1P027a2add292c134d 0 2 0 1 19 1P027efd334f3ad48d 0 3 0 1 15 1 20 1P03a991db8de691ef 0 5 0 1 14 1 17 1 18 1 20 1P03ac986f22a19770 0 3 0 1 12 1 14 1P0691dd86ddf8ead2 0 2 0 1 3 1P07c76e0aba0a40fd 0 4 0 1 9 1 11 1 14 1P07ddff11c955ac87 0 4 0 1 13 1 15 1 16 1P096fa10fd83728e5 0 2 0 1 1 1P0a4dcc4d20cd28c6 0 2 0 1 1 1P0df6ad4c617fce37 0 2 0 1 2 1P0ef9b575f8fccf6d 0 3 0 1 1 1 19 1P1101d9a32629dc50 0 2 0 1 2 1P116fa8b8365133ee 0 2 0 1 31 1P1250246b780ed022 0 5 0 1 19 1 22 1 23 1 25 1P1276e34aaeecf7e0 0 2 0 1 3 1P130e632d89238aa8 0 4 0 1 13 1 15 1 16 1P15989c8f0b8ca85d 0 2 0 1 21 1P16b1c050874fe536 0 2 0 1 1 1P17c47329ce9c82b0 0 2 0 1 26 1P18b63bf322dbe4ed 0 3 0 1 20 1 26 1P191283e7b486c402 0 2 0 1 22 1P1931403ee2d18723 0 2 0 1 11 1P19ac0bb8d4406293 0 3 0 1 10 1 15 1P19b76b2ac09ceab7 0 2 0 1 33 1P1b21314cfaf27cc5 0 2 0 1 32 1P1b7e219662d32776 0 2 0 1 2 1P1e73342140ead570 0 5 0 1 20 1 23 1 24 1 26 1P1e9a082b7fd2bcf8 0 4 0 1 1 1 2 1 19 1P1ef93bff8985a8c5 0 2 0 1 2 1P1f0b0ca40c0f1d26 0 5 0 1 11 1 12 1 14 1 17 1P20072aa7fceb10b1 0 2 0 1 5 1P219318aac6191acd 0 6 0 1 13 1 15 1 16 1 17 1 18 1P219d4f5d96d0693b 0 2 0 1 1 1P225a91464b6452f8 0 2 0 1 2 1P22cfd9a5429aa4b8 0 2 0 1 3 1P2472eff0c1963f3e 0 5 0 1 18 1 21 1 22 1 24 1P24b195113ac92ab2 0 2 0 1 2 1P25cc1195eeafd4eb 0 2 0 1 2 1P2762eae7917aeca2 0 2 0 1 2 1P290a1689c0edfd74 0 2 0 1 1 1P2933f59e6e2ace1b 0 3 0 1 1 1 24 1P295ee36d49e142c1 0 2 0 1 1 1P2a313ab4b68eaf62 0 4 0 1 12 1 14 1 17 1P2a68443be08af2a2 0 2 0 1 3 1P2cd68bfc61d085c3 0 2 0 1 11 1P2daeb056c159fcee 0 2 0 1 2 1P2e40af1925daaf62 0 2 0 1 2 1P308c7e797bd65a3d 0 2 0 1 32 1P30b74d1d15ad9369 0 5 0 1 11 1 13 1 15 1 16 1P3156fd68beb3d2d6 0 2 0 1 26 1P33135f2b7c3cf20c 0 2 0 1 25 1P34df3f36cbde07c6 0 5 0 1 11 1 12 1 14 1 17 1P377edd23b1505633 0 3 0 1 4 1 23 1P382881e53ba67ca6 0 5 0 1 11 1 13 1 15 1 16 1P3893544aac94aac3 0 2 0 1 1 1P39bc37e051a3679d 0 2 0 1 2 1P3cc1945830fee0ef 0 2 0 1 5 1P3d1e588a484a3afe 0 4 0 1 12 1 14 1 17 1P3d7ba2daedc78188 0 2 0 1 2 1P3fead412096a053d 0 4 0 1 6 1 23 1 24 1N0017f396d1c63809N005d1442c61376eaN009e383af8330694N0100baa1cd1f562cN01254f63f2acbf0fN016e64a41568f215N018410d2905a55f5N01a9f18fbf095f71N01e52dfa511138b1N01f52ff8019a412dN021c951110a11f0dN030787a9da64b661N031b8c726e592fdbN032af7340b8f552bN033d3600caef51ddN0364efa3941b32b6N036e64bd1d7fcbfeN038d5bc3c97ccf52N03935f43861fcff5N0395df69a761f443N039a54f4fe6ca8b9N04d74a502d43cbeeN04ef8307448780c3N04fec22a8ab6eb32N058cf79e80b81a0dN0593cc35368b87acN0597ffc4c095906eN05e39f6edea3461cN060327dcc8370f50N060547f5f6b46969N07c451a2767591e5N07db2f93a6302265N0802c2cf41bbd6fbN080ae5dfc6621149N0832808e30971e7cN08935652c7e609e7N08d05d81751ed15cN08d96b021a77d0deN091125c677b8766cN092bc0da973bf9c6N099c4edc7eefc9f4N0a0310531bb9efa9N0a699f2d7f5d13bcN0ac48792aa74b453N0acebf6450603194N0b93120a28a93cc7N0bd9bf4137bcbf8aN0bf26876082f736eN0c934ba8ab9465b1N0cb99299409e68beN0cdcade13e9e0cd4N0d0491b4aa00171bN0d92a9b4961f1676N0da62571b8f5825aN0db5a0ef2cfb0791N0dfc20837e749714N0e07945f7bd0fd5cN0e13408e4be1d283N0e5a31342f59fa38N0ede58dc85571516N0f38d37a4a593e8dN0f566977eb9a0887N0f6c79d26d2a7f74N0f7e1a8d44f08700N0f8940f5582c95c9N0fa5e9a6b63925bdN0fdd22d1e67131d3N1009eba0690c98dfN100d874b7515d1eaN1019e9d2ab1ece2fN102c47db660c9c50N1049be419464a578N1052a9b38ee63265N1055929da4d115b7N1105e2763717e3d5N114130f4934b5dfeN114fec6e2195a07fN118191bbd9002720N11b2bc1468446566N11cbe7db41048c53N125928b1456cab22N12730f951d5b544cN12784b9f48d319f4N12bc5fa10eb5e999N12d4f6a8cb520f88N12db25317ae75653N12ef6d56fd184c3cN12fe323e294ff2bbN13909144d54ed9cfN13d3d74a29cf1b56N13e08e85567e7423N13e1f3cf5bc68fe5N13e5987d34ad0738N13ff7c5404dc8ee0N14c567d9b18e8ca1N14e0e4b273672b32N152375a9a26a4709N1535615e168049d5N1610871af86cbc96N1678d6ecd58a5071N16840a1fef6754b7N17b6b5be6c32fe3cN17e587f17364c8a7N17e6463ed2e658feN18279978e0461689N185330fa2f46fa1dN18699e14f749bc44N186ea92a52103979N1871c5b5fe01cf02N189e4b86dd7e2bffN18b46f0ab100f94eN18be7ca0e2828360N18da2b1f701d64ccN197c54f4ac0f148bN197f9915d0bed67fN1985d0534d92e0feN19b3f88a5875eb34N19cf3591c8bc925fN1a3555eae224a9c8N1a5824033c15ecf8N1a7b80e972ab6f8aN1a88445b1f5e3936N1ab3b4bd679e846fN1ad0e3f8c8ed7833N1b08a52b7854339fN1b12a65646f36ad7N1b1bfb10d5ab9b33N1b378db3e7963979N1b9eab430bce9f44N1ba189eeb091c578N1ba1a0e0332d2a3bN1bdbe05560a9b048N1c28cefdb28c5563N1c4736405ff4c578N1c579436222588e9N1c947bf48227cf51N1cb82d58549eeed8N1d13db8a2be6bdcfN1d56c88f0db5fb39N1d58c9b092ff7a23N1d8c237c7d16938dN1da5e77d67e39ad2N1ddf3417ecc1ca7eN1e40f69208ddab48N1e969d0449e7dc6dN1e9785ba9c71957cN1e98d627e4792608N1f749aef08766f43N1f8f113c44b4f3a0N1fcb890e70cf48d2N1ffaad46d2cb3d8fN20540645a327b76eN20c8c85f90b1bcb6N20fb45e5cb8dc3a6N2125b28fb0fa34e9N213c9b27cc609c92N218523c52a23aebfN21f74190bf28a78dN223c839488bd5484N225746f2c93da611N228082ac77afe58aN22c8d596c12dca78N22dfe4333dc9909dN22e6ccccde9ad641N232ee71201c611d4N2348f143f0dc7b00N2359543ba3d4c734N23729985598a3c08N23d06e9476444934N23da12601e8d8a54N23e782972259da73N24034edd33399569N245dcc9c9dbbc947N247ba030fa5131d4N24a1f16593ed0d0dN25141da101bec301N2542646e87f61c87N2573c41db546d5c3N25bc3d66077401f9N25e023514f1ecc58N2668311f4c66a1d0N269f2054c83c2e2dN26d0e8d964da74b9N26e40bab109ce09aN27050acfd86c76e1N27082d446384ecafN2708d343df33eeefN2733a47cf6ee731dN27fae841472691a2N2827b505c2e0845aN282bac997e1d0e55N288a0e8abc248f19N28b488360830f5c0N2901050fa3731823N2902fc128b8ba83eN2938184bed1e630fN294f966c4e3ec1c8N29545fbcf10ea825N2962194315c02353N29b627549890d815N29ff19c7b7f05238N2a452a9a9cc7308aN2a54b2c91a7f70b3N2aa98dafa95d651fN2ac0d4e58161de0bN2af7816bc1d1855dN2b23b64293cbd683N2b67e8a2af52bdc8N2b897fc8b1c16c8dN2bb30b1a18e64cbaN2be0b0496a93c196N2c3014133f8a7e8fN2c552068bfee0fe5N2c5d1b42f30c040cN2c8c06512ebd0373N2ceaff6a002940f8N2d033855938953a9N2d331d58ab3f3310N2d52ff224ea242dbN2d579e3312d8b361N2dd4c8d70877d2ecN2dfa862deaa06f5cN2e04e470d95915efN2e1c6fecb7f5688bN2ed96fb2f8651031N2ef139df94317c64N2ef144d345310852N2f491ababa2c0e64N2f6b4b231c1e1685N2f6f898e6769a193N305bbd78bc7ad9deN306d3c5f71a617ffN309c9e6a63b980a4N315c0947052d6f4fN318474394706cd7cN3197d0d0c7e154b0N327a2eff50090182N32a3f1cfff71061fN32b8c3de59728ed9N331042b61c749952N331b73518bc6b8e2N3327ea8665dacf35N3362b59ba0b96c97N3388db00055b7c62N338ba4ff825db343N33b0170f0e1552afN34481a82fc8a6871N344d2519fed16b73N345e7f7ad209da71N34609bc9f60747b0N34c2b78833140a5fN34d50bbd7acb8b63N351e4eb741ee20e7N354e17a0e3203ac0N3574faf9394ae719N35c2ca67c509e2a3N35db4e3f4ec341ceN35e6d0e1d786fb8eN35ee857749215313N362ec3b72a15f205N36510e7af43bf478N366eeb033f1fa6ebN3698dc2cbf212ed8N36e312b39ce2f678N37528e6615216bf7N3775fb439b4f7c8cN37961c9ca6021e9fN37f8e96b953ad4c4N3885faa24707c323N38d9f069acd07608N3988a2b98c7416ecN399fa62caec93565N39b3d42310a16931N39e7326da203444dN3a16fa3bb98b0755N3a17c5dd630aa7e2N3a5a7fb9fcd4240fN3a6974b4aa856de3N3a917914d05e3306N3ad98ddca46fee23N3adc02d6cca6807cN3b66d19cd2fb63a7N3b6ee65dac73fd1fN3b7b19ca2d8614f1N3b86f2de32dcd05bN3b9b2efec87a8c1aN3b9f4866bf12f472N3ba3e2c4cf354d24N3bc20742e90bc2e6N3bcedd0abcb80809N3bf05dc6df2b68a3N3c232a0f7b6e3518N3c7406cb36f0a2b4N3c96e5d931651663N3cb4f7ee9a2eb35aN3cf50e40b3b2129aN3d56041281e5a6b3N3da2c7470f605d33N3ddf0b23d95e69e3N3df0968d11a9535dN3e583477362de8d7N3e5942a85a40109aN3e6b74454911bcdcN3ef5a834c8f7794cN3f14c5e5f606e604N3f1910bc6a7d5879N3f22978cd830f9ddN3f4e7405578ae91aN3f7984c9669bebaaN3f80d7b6ddcd3fc2N3f8937a6bb4bd020N3fb8a55fa7742508N3ff4dc65179f3194"%lxh.
Ltac2 gd_tbl_P_asn1_get_bitstring_null () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Frame.stk"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Exec.evt"; "asn1_get_bitstring_null_post"].


Definition P_ASN1_GET_BITSTRING_NULL : Z := 0x1e5c0.

(* [comment removed for export] *)
Notation ASN1_GET_BITSTRING_NULL_STACK := 32 (only parsing).

Definition asn1_get_bitstring_null_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bitstring_null ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+20.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-7?.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1;.R1.)(13.$1:.)))(5.(1<.O19.R4.O2.(12.&40.O17.))(5.(5.(18.O4.R2.)(18.R2.O3.))P,(6.$4.R3.=)(5.(18.(10.O4.+3.)R3.)(18.(12.&40.R2.)(11.O3.R3.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_bitstring_null_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
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
  (* [comment removed for export] *)
  PP mod 8 = 0 -> LENP mod 8 = 0 -> 0 < PP -> 0 < LENP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_BITSTRING_NULL_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (LENP + 8 <= lo \/ bv_unsigned sp <= LENP) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 LENP ->
  evt segs (asn1_get_bitstring_null_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.

  Notation W := [(PP, PP + 8); (LENP, LENP + 8); (bv_unsigned sp - ASN1_GET_BITSTRING_NULL_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_bitstring_null_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END lo m).


  (* [comment removed for export] *)
  Lemma loop1_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bitstring_null ()) "Pk,$1=.Pcur,$4.Pstop,$4.PL,(2.&40.)Px5,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(6.$1=.(1>.(11.R5.R6.))R7.)P,(5.(18.(10.VP,+2.)R7.)(17.R7.R6.))P,(18.R7.VEND,)P,(19.$1?.R4.VPP,(=.$1:.(1;.(16.&40.R9.))(13.$1:.)))P,(19.$1?.R5.VLENP,(=.$1:.(1;.R8.)(13.$1:.)))P,(20.$1?.R6.VBUF,Vbs,)P,(1<.$1?.R7.Vlo,(12.&40.Vsp,))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VLENP,(10.VLENP,+8.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+20.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R8.)P,(14.$1?.Vm,R9.)P,(15.$1?.R:.)(21.$1?.(22.$1?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,R=.Vt1,Vt2,Vs0,Vs1,(16.&40.-60.)(16.&40.VEND,)(16.&40.VLENP,)(16.&40.VPP,)(16.&40.R10.)R>.(16.&40.R?.)R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>684.)Vfc,(:.(2.&40.))R;.(;.$1?.)))")
(* [comment removed for export] *).
  Proof.
  induction k as [|k IH]; intros cur stop L x5 x17 mm Hk Hcur Hstop HPP HLEN HBUF ST MU WM MI; [lia|].
  destruct (nth_error bs (Z.to_nat (cur - BUF))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  read_at HBUF NB (cur - BUF) RD.
  lxp_run (PLAN [0x1e5c0; 0x1e684] [(0x1e6a4, DMerge 10)] 78%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 124548; (lxp_apply (IH (cur + 1) stop)) | lxp_ret ].
Qed.

End Walk.

Lemma P_asn1_get_bitstring_null_spec {L : heap_layout} : asn1_get_bitstring_null_stmt psegs P_ASN1_GET_BITSTRING_NULL.
Proof.
  unfold asn1_get_bitstring_null_stmt, P_ASN1_GET_BITSTRING_NULL.
  intros until lenv.
  intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0.
  pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8); (bv_unsigned sp - ASN1_GET_BITSTRING_NULL_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  lxp_run (PLAN [0x1e684] [(0x1e6a4, DMerge 10)] 78%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 124548; lxp_longform nn; lxp_apply loop1_walk | lxp_ret ].
Qed.
