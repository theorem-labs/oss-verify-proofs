(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux X509Aux X509AuxB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_platform_zeroize P_asn1_get_alg_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0056a3f73adce88f 0 2 0 1 5 1P01613391e89d35aa 0 2 0 1 2 1P034bd1efe89d6f3b 0 6 0 1 15 1 19 1 21 1 28 1 31 1P04d1ae1354a6e614 0 5 0 1 19 1 23 1 25 1 35 1P060ae87cc1190f51 0 6 0 1 15 1 19 1 21 1 28 1 31 1P076a82638a75017e 0 2 0 1 1 1P0bd81341530b92cd 0 7 0 1 1 1 15 1 19 1 21 1 28 1 31 1P0c0ff38887a8d5c3 0 4 0 1 28 1 40 1 41 1P1373d3805dd02ba0 0 2 0 1 45 1P176c292b9a1ef413 0 2 0 1 13 1P1a2df14cd695122e 2 28 0 5 0 1 1 1 28 1 40 1 41 1 0 4 0 1 2 1 40 1 41 1P1d881debc3a1e197 0 4 0 1 35 1 51 1 52 1P1e11ef4a15ee24c9 0 4 0 1 1 1 21 1 31 1P202159ce13c14bc5 0 2 0 1 1 1P208f02a2b7b1c709 0 5 0 1 22 1 26 1 28 1 38 1P21cad8a854cd1a9d 0 2 0 1 3 1P25985660f6d299de 0 7 0 1 1 1 15 1 19 1 21 1 28 1 31 1P279d9a28e6f8a215 0 2 0 1 48 1P28b73b26d66be25b 0 5 0 1 1 1 20 1 29 1 30 1P29e520cd487f1934 0 4 0 1 30 1 42 1 43 1P2b6a33ed5543195e 0 4 0 1 23 1 24 1 27 1P2c19ca736bf01c61 0 2 0 1 1 1P2ea62134369c3887 0 2 0 1 49 1P2f0e303820247fb7 2 38 0 5 0 1 1 1 37 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P2fc229f6317e8930 0 4 0 1 34 1 48 1 49 1P309620af3ea654b6 0 9 0 1 18 1 22 1 23 1 24 1 31 1 32 1 33 1 34 1P30c7b7c6f1f9b267 0 5 0 1 1 1 20 1 29 1 30 1P318922d57b734679 2 29 0 5 0 1 1 1 28 1 40 1 41 1 0 4 0 1 2 1 40 1 41 1P327fbe3e0ec6582c 2 36 0 5 0 1 1 1 37 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P340140f04adad999 0 4 0 1 20 1 29 1 30 1P341ca02773636a93 0 4 0 1 26 1 38 1 39 1P35cd0407c6e17ca7 2 36 0 5 0 1 1 1 35 1 47 1 48 1 0 4 0 1 2 1 47 1 48 1P370099aafcdbf2c2 0 4 0 1 4 1 27 1 37 1P3864b68a26534d57 0 2 0 1 17 1P38a5dcb57af6357b 2 30 0 5 0 1 1 1 31 1 43 1 44 1 0 4 0 1 2 1 43 1 44 1P3911a3d6a5c1e740 0 4 0 1 1 1 24 1 34 1P392e968ebff61503 0 2 0 1 18 1P3b33bd073b19d9b6 0 3 0 1 14 1 15 1P3c399bcb28dfbcf7 2 36 0 5 0 1 1 1 37 1 49 1 50 1 0 4 0 1 2 1 49 1 50 1P3f719a090bb17c5b 0 4 0 1 20 1 29 1 30 1P3f7b4abe456c6810 0 5 0 1 16 1 20 1 22 1 32 1P3f91f7d0ab0880f0 2 32 0 5 0 1 1 1 31 1 43 1 44 1 0 4 0 1 2 1 43 1 44 1N003f27d899ea0e30N00d36e90b0fcf523N010add0705e9e5baN019410525df7b142N01bf08df4f574b53N0245b8473080f04dN025d119ed33cf817N02603f0711a9afdaN02900544879b3b7dN02c4a6a5097bc53bN030165d9f1897f94N032e63c98459d601N038bc4121e8dafc3N039ce748e06d86d7N03d4d8365624035bN03ef824a78c90c45N03f87e023a346234N041f6b123c6b848cN0428dfb94ffa9cfdN0449d9986684bbd6N046fa5f770bd183cN0488cb6eeecd371bN04d0f557158d1b57N04d86829ccd65e21N0518e7a3e7b26b5eN05496a563fb23b67N0552baa7cbcd2ec9N055d86916d01425fN0568ba41b9888878N05969b1e8ed0aecbN065fc5bf5dd77996N0669d3abfe3cadf5N067127832966597fN068df9a5b03a82f4N06c07ac08d85e0b0N0729393cd54a3163N074e0108eeb556b4N07ae2893092cc9c0N07ca16020f566fd4N07f2fe6607650c36N084473a629fb84f4N0848b6a27f0d713dN08553c451e9280d2N08be259ce74136a8N08c0974d34cc8d72N08e9918134db5e8dN0957ae88e60744faN09a2b6a52e1353c9N0a2b63dabfc94fa4N0a48b07eace4bbf6N0a633fb8f2302a41N0a79d580de442eb1N0ab569d3cec03537N0ad87d967b6516ecN0afc3936faf03617N0b14995b83888440N0b1c1fef4dfaa1b2N0b46295fab85f054N0b6fa574bc94004dN0bafcb6d481aa90cN0bd57434468ff4daN0c0895a52cc1ea00N0c70873d98a90813N0cade997a861b340N0cbe46a6ce0d5d33N0cd92aa8a8f83298N0cf002253860f2c5N0d1b4793ac16053cN0e1b0d0f2feb4190N0e804bf1304978a0N0ed6df55de8a1942N0eea47125d9aff6dN0f301e38cc110a8dN0f3cfa152d444089N0f5818b04ae5a707N0fa45584e914f291N1031306dae6b82f8N106cf47ca6d510c2N106d803fd4ae1de6N1077e42066c6009cN1093999715c9246fN10bb43b96e2f44fcN10f9806a6bb42d40N113c79d638582e94N1168579923de3a74N1240c23c9698c395N12431cd07f309266N125aede2da8fc20eN126ff8cd47d05e80N1277164a2652e858N128cb334e04657dfN12d9f36e643a892dN130ae9fa4510623aN136b4b20c8f0a3c6N139fcd12eb8d2b7eN13a4a0e8e719a098N13d14cdf78d211c8N13ec1a5ff8e2a8faN1417b436d27708a0N141b239fbbd8269bN147103bf5fb61bd8N14ff8781c49175c3N150ec286100c19aeN151a254ff4086db0N1521d24bacd67cedN1525faaafcf79eb0N15e018d726280ac8N1639ff17cb6b2666N1650397af493674fN16630318d2a61cc6N1670897830c9e9a2N16785841095994ffN170dbc3ce6b2797dN1717b5c764d70b55N172531c7221488a7N175a74d48aae4b9eN175e079986c0f703N177046fdcd9a143bN1797349697d4b7e5N179ad66c7d276669N17f01850b6b1aeaaN17f2030795715345N181e2016a97d5ee8N18203d48aae1bb83N18228adba76b06a0N1871df8761158ed4N18b3c16ca4713b3aN18dd34420ada83fcN1903b3ced3b4ce37N19095d24d2bf786cN191649fa3b4f27a1N19b26179949a7ebcN19cdd03fa0c972ddN19d2a882f3ba75bdN1a15c4851e31217fN1a26650b58826041N1a3507139985f4dfN1a54aef94099ba4fN1a673d88ba8f248aN1a6776a58144766fN1aab1f5606a147a5N1b0d98733d4df00aN1b2fd3da90150148N1b973663896901e0N1b99e4ce7562ccbdN1bca460aa8aa56bbN1bf3692c3a6f2d16N1c176fff2fd1febbN1c2af9cbb8f2b613N1c60ff09e4047162N1c945c1de0845ba3N1c9a8edfc8e18606N1ca101fade39f8e4N1cf8071a2dc3cc67N1d0f30836f52a6e7N1d3f9244ef2e3217N1d53a72230393ddaN1d7191931c52eb8dN1d7f8dce12806439N1dd355467161021bN1e008030c00973abN1e6738a4cbbcc665N1e68ef7c4682707cN1e90faaf7ba54867N1eafcd43f2ca96a7N1f29d7dad5d2fb2cN1f54dcb35ac7a1edN1f6693e8fa99fd4cN1f79d1f922dd1bb1N1fef6e438bfe702dN2012fbd3e01919ecN202047f286cc5a9cN20706e4f97a78bdaN20939ccd7f7417bdN20b01c3b4a797827N20d7518adac84cb6N210cee593802d083N21484a58f367c806N21654166d38e51f4N219f777830c563d9N21bb86b414a99171N221a46ff300da9a2N2271e4f99878dd86N227c2ccf09d0be3eN22cb0df026f4c6baN23234db78ec0704dN233738c3f605a8adN233db6822048b35bN23789d98f0dba7cfN239e3ca00768eba4N23a15d701c878f34N23fdb1ec55687434N24382b317e9bac9aN2457b36361dc239cN2462acece09de1b8N24635be5d8f33459N247530db6a5736a4N248ad21576769dd3N248d7bb675e53651N2516c55df635199aN2554b636480cbfa5N255d524993768badN25d60f1adf2aae89N25f958d4b394912fN2651f70a8efe09f1N275ca21ae3d564c5N27d011527f013b0cN27d0374728db2236N27e16001da2bea9fN28082dfd4b28c0c7N2816ec6301265c7fN28815fe352d871c8N28919a31f628a31aN290eeab6e2b66156N295f766ea1252522N29b40e6c0e6ace66N29bd1e3acd78a4eaN29e26d9a5495f46dN29e3a23de468a9bbN2a55bcfa988623e0N2a5c293f2c2427c1N2aec4c176df10f77N2afe1c1d62808a2bN2b197fabb68b0d74N2b39e4762f5240ffN2b3b9ea98875e415N2b7c7a0aa348a3a1N2ba9889a96acfcbeN2bae56c84723f9eeN2bb4e20217083c5eN2c1b84d35526912bN2c778702df4d5909N2ca06753d78588b5N2cb7c87109345d03N2d010c913a7dda0fN2d065ba63dcd508cN2d868a957e314c5bN2de7b68ceb6f3f87N2e2f16858508d2f7N2e4a2890a5e9b0e9N2e7c4a3e17333a36N2ed39b72614db8a0N2f01bcfa00f2f271N2f4222cfaf074412N2f63dcf2c363ab00N2f654bcdb42e80fbN2f71df5f6e67e718N2fb3ef1bb6f7edbcN2fbdeb98cda4c9f2N2fe4ba338e35c302N2fec8e6f402f297eN30519eba2f02e62aN306b522557b77b7aN307316b75ca2ded0N30eecfb00bb9d8a0N30fb7a24aa227f81N31385fd25735904eN3190ebfd1dd8aa19N319fe02bb58c004aN31a1c537f9f182e2N31aa794c9b9a35f5N31fae42f0fe1f227N323a772e28bd2deaN32f22366837dbccaN330839e08cedf014N330dadba2807bfffN33672b63d90a543bN3371b061d7cb72abN33b08a4096dd7dc9N33d2bde6f1a59e16N340876fd7f8fcbeaN3413ca44ee53e815N3433be162f0e40dfN34513305a1742d18N345570cc488bddaeN34676c6a81061400N348716921bf96206N34fd5857e82929acN350ec08567d0ed9cN35858622e5ede021N35bbc92c0137cc28N35e7b5914ba89f2dN360529c4492cc3e4N36338713e4abe366N36df75a9846bf5e2N3708b752007c9185N371ec5718f906301N375fc0dc13abe4a8N376639c0a58c6ef3N37aa715aed236bd4N37aacf0f33407df5N37acb9cde18b6fceN37c032311ab143fcN37c81b557ae11c9eN37d1eba584d34f2aN37d2d9718fb7d238N38461311a23dbcfaN3848052660a0f8caN3852b05788a0e825N385c17be5535e4bfN389903354525e446N38b203033aae5300N38c30ca163bf379fN38daa4c5297168faN392ab6a99b1d02b0N3936adcd637d23ebN3982de13785fb4e9N39b0f0e5e5b42a0cN39ba5b7f12756997N39cf064b86fe9fbeN39effc272c1e9464N39f546623ef91ca9N3a0779f8f1fa05c2N3a1a6c7ddcc5f060N3a1be85788d39387N3a1d69fd54817d62N3b38d708ed7d8f69N3b6575920b3d6d99N3b6c6990435a3ba2N3bf20439aa297409N3c2883765050dcc7N3c709341da144bcfN3c7669f5108307ffN3c7dac0605167ec2N3c8ea3d0e9010c85N3cb6f6fe67be03afN3cc52c339e000097N3cd3420d38723f3fN3cf6dce2f44af962N3d2cbaac78d4b604N3d38b6c3726ab73eN3d9f7017eb2dda63N3dae34693b0fa233N3e30c5d379421330N3ebb52b2edd2285bN3ec5048bdde8b357N3eff41d40986725cN3f5749cabe3aadf6N3f577afe26e36fb5N3f826477258dca6dN3fae2132ade295a4"%lxh.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Walk.
  Variable L : heap_layout.
  Hypothesis HZ : platform_zeroize_stmt psegs L P_PLATFORM_ZEROIZE P_MEMSET_FUNC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP ALG PAR P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= ALG \/ ALG + 24 <= PP.
  Hypothesis D1b : PP + 8 <= PAR \/ PAR + 24 <= PP.
  Hypothesis D1c : ALG + 24 <= PAR \/ PAR + 24 <= ALG.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : ALG + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= ALG.
  Hypothesis D3b : PAR + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= PAR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis ALGB : 0 <= ALG /\ ALG + 24 <= 2^64.
  Hypothesis PARB : 0 <= PAR /\ PAR + 24 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis NZ3 : 0 < PAR.
  Hypothesis SLO : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : ALG + 24 <= lo \/ bv_unsigned sp <= ALG.
  Hypothesis DS3 : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS4 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CA : const_at L P_MEMSET_FUNC 8.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis OD1 : PP + 8 <= hl_data_lo L \/ hl_data_hi L <= PP.
  Hypothesis OD2 : ALG + 24 <= hl_data_lo L \/ hl_data_hi L <= ALG.
  Hypothesis OD3 : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis SPB : bv_unsigned sp < 2^64.

  Notation W := [(PP, PP + 8); (ALG, ALG + 24); (PAR, PAR + 24); (bv_unsigned sp - ASN1_GET_ALG_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_alg_post psegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP ALG PAR P END BUF lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HZ => idtac | B1 => idtac | B3 => idtac | B4 => idtac | D1 => idtac | D1b => idtac | D1c => idtac | D2 => idtac | D3 => idtac | D3b => idtac | PPB => idtac | ALGB => idtac | PARB => idtac | BUF0 => idtac | NZ3 => idtac | SLO => idtac | ACL => idtac | ACP => idtac | SPA => idtac | DS1 => idtac | DS2 => idtac | DS3 => idtac | DS4 => idtac | CA => idtac | DHI => idtac | OD1 => idtac | OD2 => idtac | OD3 => idtac | SPB => idtac end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0@D13071307342.129D19725246676.129D25046979674.129D31857500821.130D35717332817.129D42966123332.129D44484923210.129D45023094893.129D45500963550.129D46364619679.131D52101704109.131D63103926631.130D63341238054.129D67295449239.129D8072571891.129 D8743105197.129 L13083761374.117L13499136167.101L1687956686.3   L17076861729.0  L19720661060.117L20102134622.101L25034529994.117L28573888615.29 L28573888615.30 L28575982988.6  L30766065397.97 L36171020123.101L37857181118.5  L38394746501.96 L39448980882.100L39457292826.88 L39457293334.80 L39459391376.95 L39459391383.97 L42148661401.2  L42812834608.93 L42814931121.76 L42814932669.84 L42953673684.117L44246070758.101L44316660252.3  L44480858074.117L45018767613.117L45513937486.117L46364608939.119L46885401511.76 L47834411191.91 L53792479276.4  L57622410744.6  L57628696595.28 L58921266196.97 L59314873579.6  L63345041334.117L67226672827.101L67307640839.117L8085545827.117 L8208580904.3   L8756083261.117 L8796498103.84  L8798596410.93  L8798596413.91  L8800126135.6   L8804812607.96  L8806420828.31  R15446641981.109R20104312001.124R2221556538.119 R3525480214.109 R37861583968.123R41872992514.109R41891184142.109R44243892857.124R44256442206.119R44256442206.123R44321041695.123R5231659496.119 R5231659496.123 R53519107637.124R58914923403.124R67436144724.109R8212643371.119 R8212643371.123 00000100200300R00`00a00b00c00d00e01L01k01l01m01n01o02U02V02`02a03G03H03n04o06006C06D06E06F06T06U07:07d08I08n09509C09Q09_09`0:Y0:Z0:[0;40;Y0<C0==0=K0=W0=j0>k0??0?@0?A0?B0?[0@30@40@L0AP0BT0CX0Ck0Do0F00FE0FF0GC0Gf0HF0H_0Hm0If0J_0K[0LW0Lk0MB0MP0Md0NG0NH0NIFFFS2sp2PP3ALG3PAR2bs2jk3LXJ3x191HS2sp2bs2jk3LXJFFFFFS1L2sp2lo2bs3SLO3ACL3ACP3DHI2jk3LXJ1a1HS2sp2PP3ALG3PAR2bs2jk3LXJ3x191HFFFFS1L2sp3BUF2lo2bs3SLO3ACL3ACP2jk3LXJ2HDFS2p22L12nnSS1L2sp3ALG2lo2bs3SLO3ACL3ACP2jk3LXJ2HDFS1L2sp3PAR2lo2bs3SLO3ACL3ACP2jk3LXJ2HDS1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS2sp2PP3ALG3PAR1x1HFFFS2sp2bs2jk3LXJFS2sp3BUF2bs2p22L14plen3ppw2jk3LXJ3lxvS2sp3BUF2bs2p22L13apw4ptag4plen3ppw2jk3LXJS2sp3BUF2bs2p22L14plen3ppw2jk3LXJ3lxvS2sp3BUF2bs2p22L14plen3ppw2jk3LXJ3lxvS2nn2HNS2sp2bs2jk3LXJS2sp2bs2jk3LXJS2sp2bs2jk3LXJFS1L2sp1P3BUF2lo2bs2B13SLO3ACL3ACP2p12p22L02jk3Hp13Hp23LXJFFS2sp3ALG3PAR2bs2jk3LXJ2HDS1L2sp2PP2lo2bs3SLO3ACL3ACP2jk3LXJ2HDS1L2sp3PAR2lo2bs3SLO3ACL3ACP2jk3LXJ1a1H2HDS1L2sp1P3END2lo2bs3SLO3ACL3ACP2p12p22L02jk3Hp13Hp23He23LXJS2sp2bs2jk3LXJS4lxv02nn2H6S2sp2PP3ALG3PAR1x1HS1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS2sp2bs2p22L12jk3LXJSFFS2sp3PAR3BUF2bs2jk3LXJ2HDS2sp2PP3PAR2bs2jk3LXJ2HDFS2sp3PAR2lo2bs2jk3LXJ2HDS1L2sp1P3END2lo2bs3SLO3ACL3ACP2p12p22L02L12jk3Hp13Hp23He23LR13LXJ2H7S1L2sp1P3END2lo2bs3SLO3ACL3ACP2p12p22L02L12jk3Hp13Hp23He23LR13LXJ2H9S1L2sp1P3END2lo2bs3SLO3ACL3ACP2p12p22L02L12jk3Hp13Hp23He23LR13LXJ2H8S2sp2PP3ALG3PAR1x1HS1L2sp1P3END2lo2bs3SLO3ACL3ACP2p12p22L02L12jk3Hp13Hp23He23LR13LXJ2H6S1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS2sp2lo2bs3SLO2jk3LXJFS1L2sp1P2lo2bs3SLO3ACL3ACP2p12p22L02L12jk3Hp13Hp23LR13LXJ3H10S1L2sp2lo2bs3SLO3ACL3ACP3SPB2jk3LXJS2sp2bs2p12p22L02L12jk3LXJ2nn2H5S2sp3PAR2lo2bs3DS32jk3LXJS2sp2bs2jk3LXJS1L2sp1P3BUF2lo2bs2B13SLO3ACL3ACP2p12p22L02jk3Hp13Hp23LXJS1L2sp1P3BUF2lo2bs2B13SLO3ACL3ACP2p12p22L02jk3Hp13Hp23LXJS1L2sp1P3BUF2lo2bs2B13SLO3ACL3ACP2p12p22L02jk3Hp13Hp23LXJ2nnS1L2sp1P2lo2bs3SLO3ACL3ACP2p12p22L02L12jk3Hp13Hp23LR13LXJ2nnS2sp2bs2p22L12jk3LXJS2sp2bs2p22L12jk3LXJ2nnS2sp2bs2jk3LXJS2sp2bs2p22L12jk3LXJS1L2sp2lo2bs3SLO3ACL3ACP3SPA2jk3LXJFF". (* [comment removed for export] *)
  Lemma j2_walk : forall (p1 p2 : Z) (L0 L1 atag apad apw ptag ppad plen ppw x5 x6 x7 x17 : word) (jk : list byte) mm,
    P + 2 <= p1 -> p1 + 2 <= p2 <= p1 + bv_unsigned L0 -> p1 + bv_unsigned L0 <= END ->
    rw_cells psegs mm PP [C8 (Z_to_bv 64 p2)] ->
    rw_cells psegs mm ALG [C4 atag; C4 apad; C8 L1; C8 apw] ->
    rw_cells psegs mm PAR [C4 ptag; C4 ppad; C8 plen; C8 ppw] ->
    bytes_at psegs mm BUF bs -> stk psegs mm lo (bv_unsigned sp + -16) ->
    rw_cells psegs mm (bv_unsigned sp + -16) [CB 8 jk; C8 ra] -> statics_ok psegs L mm ->
    munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
    evt psegs POST
      (MS (mkR ra SP' gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 PP) L1 (Z_to_bv 64 ALG) (Z_to_bv 64 PAR) (Z_to_bv 64 p2)
              L0 (Z_to_bv 64 p1) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e848) fc None mm (seg_rom psegs)).
  Proof.
  (* [comment removed for export] *)
  intros p1 p2 L0 L1 atag apad apw ptag ppad plen ppw x5 x6 x7 x17 jk mm Hp1 Hp2 He2 HPP HALG HPAR HBUF ST FR SOK MU WM MI.
  pose proof (bv_unsigned_in_range 64 L0) as LR0.
  try (unfold bv_modulus in LR0).
  try (cbn in LR0).
  pose proof (bv_unsigned_in_range 64 L1) as LR1.
  try (unfold bv_modulus in LR1).
  try (cbn in LR1).
  lxp_run (PLAN [0x1e898; 0x1e9dc; 0x242bc] [] 171%N).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_gc. try lxp_statics.
    try (rewrite ?unsigned_lit in KE by plia).
    destruct (rw_cells_forget _ _ _ _ HPAR) as [junk HPAR'].
    (* [comment removed for export] *)
    cbn [cells_size csize Nat.add] in HPAR'.
    pose proof HZ as SP.
    try (unfold platform_zeroize_stmt, P_PLATFORM_ZEROIZE in SP).
    callx_sp (bv_unsigned sp + -16)
      (eapply SP with (A := PAR) (n := 24) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by plia;
      try eassumption; try reflexivity; try plia).
    try clear SP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells _ _ PAR _ |- _ => rename H into HPAR end.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul repeat] in HPAR.
    apply (rw_cells_zeros psegs m3 PAR 24 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in HPAR;
      [| cbn; repeat split; reflexivity | reflexivity].
    lxp_gc.
    lxp_run (PLAN [0x1e898; 0x1e9dc; 0x242bc] [] 171%N).
    lxp_ret.
    intros _. exists p2, 0. repeat split; try plia. left. rewrite unsigned_lit by plia. repeat split; first [plia| reflexivity].
  }
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_longform nn.
    lxp_gc. try lxp_statics.
    eapply loop3_entry with (nn := nn) (cur := p2 + (bv_unsigned L1 + 2)) (e2 := p1 + bv_unsigned L0).
    all: try eassumption. all: try (f_equal; clear; lia). all: try plia. all: try (exists p2; repeat split; plia).
  }
  { (* [comment removed for export] *)
    lxp_gc. try lxp_statics.
    eapply j3_walk with (p4 := p2 + (bv_unsigned L1 + 2)) (e2 := p1 + bv_unsigned L0).
    all: try eassumption. all: try plia. all: try (exists p2; repeat split; plia).
  }
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
