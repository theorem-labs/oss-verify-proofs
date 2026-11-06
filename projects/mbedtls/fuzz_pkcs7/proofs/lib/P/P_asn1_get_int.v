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
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02c7d2b6d4f5a8e0 0 2 0 1 11 1P02cb06e36b6fcdbe 0 7 0 1 9 1 10 1 12 1 13 1 14 1 15 1P03a78d4a0604f547 0 5 0 1 10 1 11 1 12 1 13 1P054bf683ef237487 0 3 0 1 1 1 13 1P0683331b00e48691 0 2 0 1 1 1P0737ef21dca508e6 0 2 0 1 11 1P074a98e1fafb13ef 0 2 0 1 11 1P08b53b6afc5427ba 0 4 0 1 13 1 15 1 16 1P09abcb60587972e7 0 2 0 1 30 1P09bdbb9093c9b1f0 0 5 0 1 11 1 13 1 15 1 16 1P0af9400cf6b01407 0 2 0 1 19 1P0cc3fe3b020ddcaf 0 3 0 1 12 1 18 1P1007e06fef23cff9 0 2 0 1 13 1P11bbc7a8981d5603 0 2 0 1 2 1P12a8df56c754dcba 0 2 0 1 1 1P1366647c6c9454a4 0 2 0 1 1 1P1498dd37ba7134e5 0 4 0 1 13 1 15 1 16 1P153765483f105913 0 4 0 1 13 1 15 1 16 1P15e41a1850f44924 0 5 0 1 20 1 21 1 22 1 23 1P177d7ace7fd92619 0 3 0 1 1 1 18 1P18f7914b3c6ba540 0 2 0 1 23 1P18fe00d9d8e62076 0 4 0 1 13 1 15 1 16 1P195ad457e5525a4b 0 5 0 1 15 1 16 1 17 1 18 1P196d1c2b33b51564 0 2 0 1 14 1P1979e4f3d60ecd4c 0 2 0 1 2 1P19d5b8ab95da9a91 0 4 0 1 9 1 11 1 14 1P1b4a91ac4fc0c3ad 0 3 0 1 4 1 21 1P1d483c4861e38c09 0 6 0 1 10 1 13 1 14 1 15 1 16 1P1d92dde9c76143ca 0 2 0 1 25 1P1e4ce189e8b878a0 0 2 0 1 1 1P1f1c70ccca30c319 0 3 0 1 10 1 15 1P20528749470470a7 0 2 0 1 13 1P21d716053019b697 0 2 0 1 11 1P2295dd472d87f248 0 5 0 1 11 1 12 1 14 1 17 1P22ec973e945ff012 0 2 0 1 11 1P23855327aa755814 0 2 0 1 1 1P24f8b39a77ef0a0e 0 5 0 1 11 1 12 1 14 1 17 1P25da0a41b7567aa4 0 2 0 1 2 1P260d158a3b63e125 0 3 0 1 11 1 16 1P26ada8450a958432 0 2 0 1 11 1P29dba3c07bf62b53 0 2 0 1 27 1P2a2c8d00ca7b1cae 0 2 0 1 9 1P2c5ec11374f04bc2 0 7 0 1 1 1 11 1 14 1 15 1 16 1 17 1P2d7d6d3fb584f64e 0 2 0 1 2 1P2de3afbca84c35d2 0 2 0 1 1 1P2ed5dcc267976977 0 5 0 1 11 1 13 1 15 1 16 1P2fe369000dd5f4e0 0 4 0 1 12 1 14 1 17 1P30bfc80efa21ad77 0 2 0 1 13 1P31084b2a96d40ddf 0 4 0 1 12 1 14 1 17 1P32075870e2a0a564 0 4 0 1 1 1 10 1 15 1P320df7933e477de5 0 2 0 1 20 1P3274a5604bd099c0 0 2 0 1 13 1P327e13b44a656f66 0 4 0 1 12 1 14 1 17 1P32ea8b22787dfdf2 0 2 0 1 21 1P3404a3acb4d79e82 0 5 0 1 11 1 13 1 15 1 16 1P348af6bef9efabb2 0 2 0 1 5 1P34baf49bb9293627 0 4 0 1 9 1 11 1 14 1P3679eeadeb553f20 0 2 0 1 1 1P36d6b5966da9580e 0 4 0 1 12 1 14 1 17 1P379de9c9ff775877 0 7 0 1 9 1 10 1 12 1 13 1 14 1 15 1P37bd00f6daa8eab8 0 3 0 1 10 1 15 1P3836a473524525c7 0 2 0 1 11 1P3841dce136788279 0 4 0 1 1 1 2 1 17 1P386c07bb3cb5d416 0 2 0 1 31 1P39463ebf426090f8 0 2 0 1 2 1P3a90c00be3c18178 0 2 0 1 22 1P3a91326f80a21176 0 2 0 1 1 1P3b728bc020ea2542 0 2 0 1 9 1P3b88f4d382c36e95 0 5 0 1 11 1 12 1 14 1 17 1P3b8b79fbae13751a 0 5 0 1 11 1 13 1 15 1 16 1P3c3d868903cd40a2 0 4 0 1 12 1 14 1 17 1P3cc48234ca067eb0 0 2 0 1 5 1P3dbd3570f762864a 0 2 0 1 2 1P3e77f1d5db32f4c1 0 2 0 1 12 1P3eed019fd281ee10 0 2 0 1 2 1P3fe227ba0b00944d 0 5 0 1 11 1 12 1 14 1 17 1N0003d0dd67ef4687N002ac21413b2bf33N00314d9a96703c43N005aa69be8f5d67cN00727f3353043002N00926c36087de37fN0182bad65f2e678aN01c216056c7de033N023e622d73f2e2e0N029d36ea302684eeN02c34a71b39df0bcN02ca562078a4d132N02db21bd943beb45N02e2e59f657bf8d5N03982e024610afe8N043207695b97668eN046123208d917c98N04621565c03cbd57N0470e9d8b43db386N0481355c9f9e2791N04c8f92f46f2532dN04dcff0ae81eb57cN05108f35d909001cN054223162d75d01fN055297f3c7131d80N055928e5551d65f9N0561c55f209fdfc1N057eefe8d36052f5N05bcd7d0cfeb931cN066e195139225b46N074fc5cae66d67c4N076b4179de24fbc0N07943f284adb913aN07b5adcdb891cc11N07deda76faad263bN081d7ac99f20b9b7N084732e42f3289cfN084a97f8aedfa368N08c473a600f1214bN08e74e18294cd82fN08f00c8d7997bc7eN091fea5afa3e82e3N0930dadb67bf6cd2N09fa2c2d4b9eb3a5N0a56a3676f9ae385N0a60aa2d9b77eee2N0b554d71b0fd7db7N0b909d2cbb8fc001N0bc1da7fba25fa78N0c47462970a00026N0c9b5536801fd9adN0cc64041cf00bd14N0ce7c0dd9a076542N0d545bcb07b831c9N0d864aed22feb4fbN0d9b94983bacc9b6N0e086e1ea17b2fcfN0e5040cc3f1b41bcN0f0e5bdbc600f4c8N0f1df96ce782c50cN0fa405c648881b16N0fefd267fb082099N1011a867267467b6N103d1436701ed41cN104299e173bd5d90N104e389c784f49c1N1091e10a7a3c43daN10d953959ab12dc3N11cb66801e26f30dN12317e1379705caeN123fb10ddc64cf0eN12666f411076f9aeN12a63e7a3c1b7a58N12c3c5bf06453bdaN12f9a2e81e6f8c53N136ae8375c3aea95N137471fa70221542N139d904394f2d56aN14294890a3fa64f5N142a91b2ede0f704N143fab3c542e0bf8N14477679514451bfN147c583f91fa8c14N148ffecaba89841fN1490b2dbe67b36afN14c1a011362c17d7N14edec060e3f7b8dN1579403f976aaed8N15b8c7a68e7e1923N15eff6b8c708f49aN15fd047fb64d4324N167f0f329a53e215N168b92c5c3668780N16d6ab2592d6332cN16fdb5f0b393f416N170dc099dd008342N17520dc5ebcde2f3N1770b769a2003577N181432a2ee7e1623N184a70fb78536c82N18b3973e605b194dN18d6d7eef90c1c31N193b9ac4108dfc9fN195bbd0b3738a421N195ef5f2a6c89940N19868bb716f231c0N198fcedd4425e931N19a661b2e1c37814N1a242eadd6ed690bN1a6a156f12772e10N1a77d7e792723746N1a928eedfe1f341eN1b19b50e992774ecN1b200329d98006ecN1b41426df8b718b3N1b5f930c9627af36N1bb47a1ee1b892eeN1bd926aa9a0424d0N1c3140a94ac42a5eN1c94e6973b357b5bN1cb4771cecb6bfd3N1d1d40d171bb7cb3N1d4318437377b072N1d899862a0dbc03dN1d936fdb44fd6ff3N1dc28a6a523ba51cN1ddc2916f8f8d596N1e84bc432d6f1189N1ea0789a5f0c904cN1ecc8c163f7cbbacN1f7fea85ac257609N202835d9e6f1637cN215b0d7296d60f08N221eeae1cfcb4abfN22eb8ef744ad0190N22ece25421d90f8cN22fa0289ad1f4bf5N23158663c065ac04N2356f772b5f4129dN235cfe3ddaaf1deeN238370d6dcd434efN23b3c8e7fca2072bN23ba5d8e99b2b77fN23cfc01d490f671fN23fda3dedc5f63c8N2422feb572031f87N2442d80bd4632d5fN247e6d03e817fce3N24809dac3180d46dN24f05d9bb4428835N258114f4f46f3f42N25bb72db70b0ebf1N25c86322f3e39db9N26664c031e0fbfa2N2714348b9a6eb06bN2739c3071188cbdfN278d9f860e4a1608N27c9cd152f86d59aN27ce4da8a97611f9N27dbb0fbba702f14N27fc8d3f80720accN2858f5410f9c3582N28eabf9d51a266e3N29644712d212310fN2992eba4c18a3bdfN29aa9deee22f16d9N29ff0a77a5626ddcN2a5a8d96716ce975N2a819a6023a89a5cN2ace5d374317adb7N2b22c50be0bcd357N2b43ed5ce716e95bN2b67e98c852a917fN2b8312ef3c285ae9N2b88517b80e6ff15N2b8feb4b90196a7dN2c1365dc3fc9ac7bN2c4b8280afaf13e0N2c4b98f601e0a3b4N2c638f415f1b7d53N2c69ad9215e26e40N2c90a332c819756fN2c9aaa8fce054543N2cb5a2cbf5acf238N2d544b4aa852583aN2d9feb08179a8778N2dbf5154d76e6f49N2ddcb2d21d3b8b1cN2e32deeeeedccea3N2e3e47fd6f24f81cN2eaece91dc39c47dN2ec8e1d22a387101N2fa9bcc08b120ea4N2fc63c7adecbf300N2fe4069edf7fccabN30042c75ac83fee0N301e60a6d2249ef7N3025c2061a1f49f8N30411af5b5a90e42N3070032618dae771N30d387f45e5d76e7N30f39c4d37066a56N30fa54b1f1e4265cN316abf32365bf709N318ce55ba305c334N31d94cee323925ffN31e282ceb9f6f1bcN32108f15c36d79ccN325b0ac8ebf44fb8N328485f85d625e99N328bc07adcdfb01eN3295939f9b88129cN329e53da28cd6383N32cb3d8b03da6206N3310bd9df5fe35ccN3330252329c03eabN33351cf7bb681ab5N3398c8479ac09380N33c081bf97a06d60N341082b31c3a0ff3N349395db6c0c3233N34d49fc5aea91013N3562991598f9be12N363e7b51ce3731f5N36be733b89247671N372c87c5ee19f5f8N37c4f6f63ee0a166N38703e7d4c2d7d8bN3899a531f22aab26N38a1b1e521392ecfN395c699858e58fd7N3967cd66e3078169N396dffb1988b026bN39a894290c6b5988N39a9953dce25992aN39c039f3df7f6df7N39c8c1f190e98e85N3a51b4078ad56f65N3a991a4fb417990fN3abd7932ab7f1c39N3b924ae1e63fcd3bN3b9878b91e680abfN3c58d5a731db2f2eN3c7742140f42ccf6N3c77c653bf9b9106N3c82719d4874eeafN3c91b2033f114542N3ca14f0b2c9fb0fdN3ceca9af32e9d6feN3d5edfdfb7d5cb1eN3d629179e5c54dcdN3e1e0fd57d4b09dfN3e4bceac148b892eN3ea005a1e2c6f2d3N3ec702db79bdf768N3f04c828525b4e59"%lxh.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition P_ASN1_GET_INT : Z := 0x1e02c.

(* [comment removed for export] *)
Notation ASN1_GET_INT_STACK := 32 (only parsing).

Definition asn1_get_int_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP VALP P END lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r p' : Z) (v : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_INT_STACK, bv_unsigned sp)] m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ a0 = Z_to_bv 64 r /\ (-0x7f < r <= 0)
    /\ rw_cells segs m' PP [C8 (Z_to_bv 64 p')]
    /\ rw_cells segs m' VALP [C4 v]
    /\ stk segs m' lo (bv_unsigned sp)
    /\ P <= p' <= END
    /\ (r = 0 -> P + 3 <= p').

Definition asn1_get_int_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP VALP P END BUF lo : Z) (bs : list byte) (valv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m VALP [C4 valv] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= VALP \/ VALP + 4 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP) ->
  (* [comment removed for export] *)
  PP mod 8 = 0 -> VALP mod 4 = 0 -> 0 < PP -> 0 < VALP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_INT_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (VALP + 4 <= lo \/ bv_unsigned sp <= VALP) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 VALP ->
  evt segs (asn1_get_int_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP VALP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= VALP \/ VALP + 4 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis VALB : 0 <= VALP /\ VALP + 4 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.

  Notation W := [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_INT_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_int_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m).

  (* [comment removed for export] *)
  Lemma loop3_walk : forall (k : nat) (c stop : Z) (val curw valw : word) x5 x16 x17 mm,
    Z.to_nat (stop - c) = k -> P + 3 <= c < stop -> stop <= END + 1 ->
    rw_cells psegs mm PP [C8 curw] -> rw_cells psegs mm VALP [C4 valw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp) ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 0) val (Z_to_bv 64 stop) (Z_to_bv 64 VALP) (Z_to_bv 64 PP)
              (Z_to_bv 64 c) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e154) fc None mm (seg_rom psegs)).
  Proof.
  induction k as [|k IH]; intros c stop val curw valw x5 x16 x17 mm Hk Hc Hstop HPP HVAL HBUF ST MU WM MI; [lia|].
  destruct (nth_error bs (Z.to_nat (c - 1 - BUF))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  read_at HBUF NB (c - 1 - BUF) RD.
  lxp_run (PLAN [0x1e02c; 0x1e038; 0x1e078; 0x1e0e4; 0x1e104; 0x1e128; 0x1e154] [] 105%N).
  { (* [comment removed for export] *)
    lxp_apply (IH (c + 1) stop).  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.

  (* [comment removed for export] *)
  Lemma j2_walk : forall (cur len : Z) (lenw fl valw : word) x5 x16 x17 mm,
    bv_unsigned lenw = len -> 1 <= len -> P + 2 <= cur -> cur + len <= END ->
    rw_cells psegs mm PP [C8 (Z_to_bv 64 cur)] -> rw_cells psegs mm VALP [C4 valw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp) ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (-100)) fl lenw (Z_to_bv 64 VALP) (Z_to_bv 64 PP)
              (Z_to_bv 64 cur) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e128) fc None mm (seg_rom psegs)).
  Proof.
  intros cur len lenw fl valw x5 x16 x17 mm HLc Hlen Hcur HE HPP HVAL HBUF ST MU WM MI.
  subst len.
  pose proof (bv_unsigned_in_range 64 fl) as FR_.
  unfold bv_modulus in FR_.
  lxp_run (PLAN [0x1e02c; 0x1e038; 0x1e078; 0x1e0e4; 0x1e104; 0x1e154] [] 105%N).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply loop3_walk ] | solve [ eapply loop3_walk with (c := cur + 1) (stop := cur + 1 + bv_unsigned lenw); lxp_apply_post ] | lxp_apply loop3_walk ].  (* [comment removed for export] *)
  }
Qed.

  (* [comment removed for export] *)
  Lemma loop2_walk : forall (k : nat) (cur rem : Z) (remw curw valw : word) x5 x11 x16 x17 mm,
    Z.to_nat rem = k -> 1 <= rem -> P + 3 <= cur -> cur + rem <= END + 1 -> remw = Z_to_bv 64 rem ->
    rw_cells psegs mm PP [C8 curw] -> rw_cells psegs mm VALP [C4 valw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp) ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (-100)) x11 remw (Z_to_bv 64 VALP) (Z_to_bv 64 PP)
              (Z_to_bv 64 cur) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e104) fc None mm (seg_rom psegs)).
  Proof.
  induction k as [|k IH]; intros cur rem remw curw valw x5 x11 x16 x17 mm Hk Hrem Hcur HE -> HPP HVAL HBUF ST MU WM MI; [lia|].
  lxp_run (PLAN [0x1e02c; 0x1e038; 0x1e078; 0x1e0e4; 0x1e104; 0x1e128; 0x1e154] [] 105%N).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_apply (IH (cur + 1) (rem - 1)).  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply j2_walk ] | solve [ eapply j2_walk with (cur := cur) (len := rem - 1); lxp_apply_post ] | lxp_apply j2_walk ].  (* [comment removed for export] *)
  }
Qed.

  (* [comment removed for export] *)
  Lemma j1_walk : forall (p1 : Z) (L valw : word) x5 x16 x17 mm,
    P + 2 <= p1 <= END ->
    rw_cells psegs mm PP [C8 (Z_to_bv 64 p1)] -> rw_cells psegs mm VALP [C4 valw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp) ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (-96)) (Z_to_bv 64 END) L (Z_to_bv 64 VALP) (Z_to_bv 64 PP)
              (Z_to_bv 64 p1) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e078) fc None mm (seg_rom psegs)).
  Proof.
  intros p1 L valw x5 x16 x17 mm Hp HPP HVAL HBUF ST MU WM MI.
  pose proof (bv_unsigned_in_range 64 L) as LR.
  unfold bv_modulus in LR.
  lxp_run (PLAN [0x1e02c; 0x1e038; 0x1e0e4; 0x1e104; 0x1e128; 0x1e154] [] 105%N).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply loop2_walk ] | solve [ eapply loop2_walk with (cur := p1 + 1) (rem := bv_unsigned L); lxp_apply_post ] | lxp_apply loop2_walk ].  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply j2_walk ] | solve [ eapply j2_walk with (cur := p1) (len := bv_unsigned L); lxp_apply_post ] | lxp_apply j2_walk ].  (* [comment removed for export] *)
  }
Qed.

  (* [comment removed for export] *)
  Lemma loop1_walk : forall (k : nat) (cur stop : Z) (L valw : word) x5 x17 mm,
    Z.to_nat (stop - cur) = k -> P + 2 <= cur < stop -> stop <= END ->
    rw_cells psegs mm PP [C8 (Z_to_bv 64 cur)] -> rw_cells psegs mm VALP [C4 valw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp) ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (-96)) (Z_to_bv 64 END) L (Z_to_bv 64 VALP) (Z_to_bv 64 PP)
              (Z_to_bv 64 cur) (Z_to_bv 64 stop) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e0e4) fc None mm (seg_rom psegs)).
  Proof.
  induction k as [|k IH]; intros cur stop L valw x5 x17 mm Hk Hcur Hstop HPP HVAL HBUF ST MU WM MI; [lia|].
  destruct (nth_error bs (Z.to_nat (cur - BUF))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  read_at HBUF NB (cur - BUF) RD.
  lxp_run (PLAN [0x1e02c; 0x1e038; 0x1e078; 0x1e0e4; 0x1e104; 0x1e128; 0x1e154] [] 105%N).
  { (* [comment removed for export] *)
    lxp_apply (IH (cur + 1) stop).  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply j1_walk ] | solve [ eapply j1_walk with (p1 := cur + 1); lxp_apply_post ] | lxp_apply j1_walk ].  (* [comment removed for export] *)
  }
Qed.

  Lemma loop1_entry : forall (nn : Z) (stopw : word) valw x5 x17 mm,
    1 <= nn <= 4 -> P + 2 + nn <= END -> stopw = Z_to_bv 64 (P + 2 + nn) ->
    rw_cells psegs mm PP [C8 (Z_to_bv 64 (P + 2))] -> rw_cells psegs mm VALP [C4 valw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp) ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (-96)) (Z_to_bv 64 END) (Z_to_bv 64 0) (Z_to_bv 64 VALP) (Z_to_bv 64 PP)
              (Z_to_bv 64 (P + 2)) stopw x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e0e4) fc None mm (seg_rom psegs)).
  Proof.
    intros nn stopw valw x5 x17 mm HN HE -> HPP HVAL HBUF ST MU WM MI.
    eapply loop1_walk with (k := Z.to_nat nn) (cur := P + 2) (stop := P + 2 + nn); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tagged_int_walk : forall (tag : Z) (valw : word) x5 x14 x15 x16 x17 mm,
    P <= END ->
    rw_cells psegs mm PP [C8 (Z_to_bv 64 P)] -> rw_cells psegs mm VALP [C4 valw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp) ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 tag) (Z_to_bv 64 VALP) x14
              x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e038) fc None mm (seg_rom psegs)).
  Proof.
  (* [comment removed for export] *)
  intros tag valw x5 x14 x15 x16 x17 mm B2 HPP HVAL HBUF ST MU WM MI.
  lxp_run (PLAN [0x1e02c; 0x1e078; 0x1e0e4; 0x1e104; 0x1e128; 0x1e154] [] 105%N).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_longform nn.
    first [ solve [ lxp_apply loop1_entry ] | solve [ eapply loop1_entry with (nn := nn); lxp_apply_post ] | lxp_apply loop1_entry ].  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply j1_walk ] | solve [ eapply j1_walk with (p1 := P + 2); lxp_apply_post ] | lxp_apply j1_walk ].  (* [comment removed for export] *)
  }
Qed.
End Walk.

Lemma P_asn1_get_int_spec {L : heap_layout} : asn1_get_int_stmt psegs P_ASN1_GET_INT.
Proof.
  unfold asn1_get_int_stmt, P_ASN1_GET_INT.
  intros until valv.
  intros HPP HVAL HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HVAL) as VALB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, VALB.
  pose proof (proj1 HBUF) as BUF0.
  lxp_run (PLAN [0x1e038; 0x1e078; 0x1e0e4; 0x1e104; 0x1e128; 0x1e154] [] 105%N).
  first [ solve [ lxp_apply tagged_int_walk ] | solve [ eapply tagged_int_walk with (BUF := BUF) (bs := bs); lxp_apply_post ] | lxp_apply tagged_int_walk ].  (* [comment removed for export] *)
Qed.

