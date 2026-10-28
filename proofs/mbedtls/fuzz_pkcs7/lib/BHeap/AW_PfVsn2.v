(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr Frame Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SeqExec EnframeArith.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib A_imsetv A_vsnp_num.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfNum AW_PfVsn.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0009eaa4c137dadd 0 3 0 1 63 1 65 1P00318ebbcecc7f4b 0 2 0 1 44 1P00be1b157fd82686 0 2 0 1 36 1P0131f3ae49249e22 0 3 1 1 37 1 38 1P013d1868078954f4 0 3 1 1 53 1 54 1P0163da6aa499cd22 0 2 0 1 26 1P017120babbb21943 0 3 1 1 37 1 38 1P01c35311da0b9a6e 0 2 0 1 52 1P01c54461bada7b7f 0 2 0 1 52 1P01c652ce3a2170ab 0 2 1 1 37 1P01cb6c72dbfebf44 0 3 1 1 53 1 54 1P01e9b2ef877e712c 0 2 0 1 52 1P0216ed97ea710b6e 0 2 0 1 50 1P02dc1e435fe52422 0 3 1 1 37 1 38 1P02fb61efe53bd8a9 0 3 1 1 53 1 54 1P03252d0260360ba1 0 2 0 1 36 1P036f82fc086765f0 0 2 0 1 52 1P03d80450ecd38bbd 0 3 1 1 53 1 54 1P0406122993817667 0 2 0 1 52 1P0410c8f6e11babef 0 2 0 1 52 1P0490260636054a5a 0 2 0 1 52 1P04a7085208e1e247 0 3 1 1 53 1 54 1P04d5320222b60e80 0 3 1 1 53 1 54 1P05084abdf409af85 0 2 0 1 52 1P053d7dca212cae74 0 3 1 1 37 1 38 1P0563b8ee96e8aa48 0 2 0 1 50 1P057dbb2adb91b600 0 3 1 1 53 1 54 1P058513ccba5cf7fd 0 3 1 1 53 1 54 1P0589edb92c972268 0 2 1 1 53 1P059b5a5df90e8f3d 0 3 1 1 53 1 54 1P05d3f11c487fee22 0 2 0 1 78 1P060c251959645f53 0 3 1 1 53 1 54 1P06121c31ed688d66 0 3 1 1 53 1 54 1P06123dd537a60144 0 2 0 1 78 1P06344abbd4923454 0 2 0 1 52 1P0682194e8cd7fca0 0 2 0 1 52 1P0693ca9b0fc8c128 0 2 0 1 36 1P06da4c6c7eec5c8b 0 2 0 1 50 1P06f4f84b44c78f5a 0 3 1 1 53 1 54 1P0711c13a0620a6a1 0 3 1 1 53 1 54 1P07b72606bc758714 0 3 1 1 53 1 54 1P0804fc00a24bd951 0 3 1 1 37 1 38 1P083a47e1748e0266 0 2 0 1 36 1P084e62dac72d9286 0 3 1 1 37 1 38 1P084ec54711448ab7 0 2 0 1 78 1P0868f1c03817bc69 0 3 1 1 37 1 38 1P088fd18536d71b90 0 2 0 1 52 1P08b6fe5e5a0b5a94 0 2 0 1 36 1P08d3ba8719d71e7e 0 2 0 1 34 1P09123cf3880c1564 0 2 0 1 52 1P091ab920db4e2d34 0 2 0 1 36 1P093996d58864b8d2 0 2 0 1 46 1P09fdfa5392236894 0 2 0 1 34 1P0a0239a04d6204d2 0 3 1 1 37 1 38 1P0a082428a29e0afa 0 3 1 1 37 1 38 1P0a4f309dd69deb31 0 2 0 1 36 1P0a91a0abdab57eea 0 2 0 1 36 1P0b5c949707824361 0 2 0 1 78 1P0b7e48c96be22cac 0 3 1 1 53 1 54 1P0b921f4e8467c3d2 0 2 0 1 50 1P0bb837a55fffd043 0 3 1 1 37 1 38 1P0bd431570e4590af 0 2 1 1 53 1P0c08c499e388db92 0 3 0 1 26 1 34 1P0c1fcec71804aa6c 0 2 0 1 50 1P0c892285fa59e45b 0 3 1 1 37 1 38 1P0ca9ee24d26122e7 0 2 0 1 36 1P0cd2cb60ef310922 0 3 1 1 53 1 54 1P0cda5f405106d49d 0 2 0 1 36 1P0d2ebb358f682c5c 0 2 0 1 52 1P0d7163e636beca47 0 3 1 1 53 1 54 1P0d796788b68d4cd3 0 3 1 1 53 1 54 1P0d884370122d5c40 0 2 0 1 36 1P0daecd5c27e818f6 0 2 0 1 36 1P0db9256d4fbcaac0 0 2 0 1 34 1P0dc83a0aa8ef8836 0 2 0 1 52 1P0dc86adf8465c563 0 3 1 1 37 1 38 1P0ded811feb134cd7 0 2 0 1 36 1P0e19650d63734c60 0 2 0 1 76 1P0e26830f3f131267 0 2 0 1 52 1P0e3638ed573d6e77 0 2 0 1 50 1P0ea589eae4117e9f 0 2 0 1 36 1P0eac095c83904941 0 2 0 1 52 1P0eaf15fb63fb458e 0 2 0 1 52 1P0f0cefe635d858cb 0 2 0 1 34 1P101e902fb3d20da9 0 2 0 1 46 1P1026a0b98b815d78 0 2 0 1 46 1P1041bf14c2378a5c 0 2 0 1 52 1P105533bfce5c8274 0 2 0 1 26 1P10b9c81616e11922 0 2 0 1 36 1P1154a11c7fede2f8 0 3 1 1 37 1 38 1P118b9b7621d9c42e 0 2 0 1 34 1P11a94b6e5df7f360 0 2 1 1 53 1P11b4fd8180f8df6b 0 2 0 1 59 1P11d030dfd0eb47b6 0 3 1 1 53 1 54 1P1200259ec42c0024 0 2 0 1 52 1P12202ef729ea7366 0 2 0 1 36 1P122a4b25b0ed5fc9 0 3 1 1 53 1 54 1P12d6a2c67f3e11f0 0 5 0 1 23 1 69 1 71 1 73 1P130a90ef6e73ac7f 0 3 0 1 19 1 32 1P13fc7e63fad7761c 0 2 0 1 36 1P1404e1888e829fed 0 3 0 1 62 1 64 1P141989e08240be96 0 2 1 1 37 1P142b647c7623f13d 0 2 1 1 37 1P1443caee1107fcbf 0 2 0 1 78 1P1446f679a5733ea6 0 3 1 1 53 1 54 1P14743ebaca9384c6 0 2 0 1 78 1P14820c815df5f874 0 2 1 1 37 1P148856a43d026493 0 5 0 1 42 1 68 1 70 1 72 1P14bafdb55fca6b6a 0 2 0 1 46 1P14ee1cfc2806e253 0 2 0 1 34 1P1504ae8b0e88b308 0 3 1 1 53 1 54 1P150f74b069899131 0 3 1 1 53 1 54 1P155767e39eb2da45 0 2 0 1 50 1P1571abf2670ad679 0 2 0 1 52 1P1574eb6a12670e6a 0 3 1 1 37 1 38 1P15bd0b03d66d2c9e 0 2 0 1 34 1P16035ceaa01cc0ed 0 2 0 1 34 1P1662bd934b9560eb 0 3 1 1 37 1 38 1P16aa04b7e885208e 0 3 1 1 53 1 54 1P16d73ddf15a06bc5 0 2 1 1 53 1P171db77d693a5e8d 0 2 0 1 52 1P176401b95dea4e78 0 2 0 1 52 1P1782811999364df9 0 2 0 1 50 1P179aba6d3cfa31e5 0 3 1 1 53 1 54 1P17de2124597437fb 0 3 1 1 53 1 54 1P17ed701a1204bbcb 0 2 0 1 36 1P1889a8b9b5484369 0 2 1 1 53 1P189046ef6f1c6f14 0 3 1 1 53 1 54 1P18b6eec7e63c22bd 0 3 1 1 53 1 54 1P18c975b82c7761fa 0 3 1 1 53 1 54 1P18f18dc07e13939a 0 3 1 1 37 1 38 1P19032534cff7b62e 0 2 0 1 46 1P192d940b554a6aa9 0 2 1 1 37 1P1965f2c8a075f2b6 0 3 1 1 37 1 38 1P19a075615fe68a04 0 3 1 1 53 1 54 1P19a18c812c035d8d 0 2 1 1 37 1P19b71a5f6efb9545 0 2 0 1 44 1P19b8177dcc40c394 0 2 0 1 35 1P1a0217ce813cfd37 0 3 1 1 53 1 54 1P1a39fc3ebac60942 0 3 1 1 37 1 38 1P1a86c5b36a128ce1 0 2 0 1 46 1P1ada0184f818edc4 0 2 0 1 36 1P1adf240da4029f9b 0 3 1 1 53 1 54 1P1b04d57a2c67a5bc 0 2 1 1 37 1P1b13e36f5084692d 0 2 0 1 78 1P1b1a0c581ab4a150 0 2 1 1 37 1P1b4c2c1667d01bbc 0 3 1 1 53 1 54 1P1bbad5b283442394 0 2 0 1 52 1P1bcb8aa37675a3ff 0 2 0 1 19 1P1bd8cacf6a49cd5b 0 3 1 1 37 1 38 1P1c18e7c9229fad46 0 2 0 1 36 1P1c21ba10094c1d8f 0 3 1 1 37 1 38 1P1c9cdf42e107d996 0 3 1 1 37 1 38 1P1d9e447cfef9c50f 0 2 0 1 34 1P1dd3bc903d35ffbe 0 2 0 1 78 1P1ddb72f207614a0b 0 2 0 1 46 1P1de0277cec58afc2 0 2 0 1 58 1P1df98218c8dfbb33 0 2 0 1 36 1P1e169a11baa399d8 0 6 0 1 42 1 68 1 70 1 72 1 76 1P1e2ceb2a303502b9 0 2 0 1 36 1P1e369a9e26ee56ca 0 2 0 1 50 1P1e3b86018a5e1c2e 0 3 1 1 53 1 54 1P1e7e5dbc6ec0e731 0 3 1 1 53 1 54 1P1ed9e6019327f4fb 0 2 1 1 37 1P1ee61c4746efdc27 0 2 0 1 78 1P1f436fe4d641eead 0 3 1 1 37 1 38 1P1f493d75a008489e 0 3 1 1 53 1 54 1P1f5d85c5c4711c72 0 2 1 1 37 1P1f75226bd28a80b6 0 2 0 1 36 1P1fc7787350e51e17 0 3 1 1 53 1 54 1P1ff3765e6a001dbf 0 2 0 1 36 1P20015c416cb594ed 0 2 0 1 50 1P201da85698bb90dd 0 2 0 1 46 1P20343e928d929dfc 0 2 0 1 26 1P203d3e0910ce70ab 0 2 0 1 46 1P207d43e927e19c92 0 2 0 1 36 1P207d9928b3b584ac 0 2 0 1 50 1P208367bd14e7b0c2 0 3 1 1 53 1 54 1P2088bd60ed3ae3e5 0 3 0 1 5 1 26 1P20b63955eea79496 0 2 1 1 53 1P20c8065c4384760c 0 3 1 1 53 1 54 1P20f44dfedbe6a918 0 2 0 1 46 1P21315cd8881530d8 0 2 0 1 36 1P215ebcbe20251300 0 3 1 1 53 1 54 1P2166a228cae388df 0 2 0 1 36 1P21761923cea52228 0 2 0 1 52 1P2195a86d71719fa9 0 2 0 1 36 1P21c0cb2330012c8a 0 2 0 1 36 1P21c57ba5879f5255 0 2 0 1 78 1P21cc41bc29d1eba5 0 2 0 1 36 1P21cf98d091419251 0 2 0 1 34 1P21ed29a935d33747 0 2 0 1 36 1P2200d476c0193196 0 2 0 1 36 1P2206245ac7286a66 0 2 0 1 52 1P221fc3f4cf89060f 0 3 1 1 53 1 54 1P226369d9569f0d4b 0 2 0 1 78 1P226eeccfff8306fd 0 2 1 1 37 1P22e8a7cd5060e743 0 3 1 1 53 1 54 1P22ff4dc7213f38d8 0 2 0 1 36 1P2304365abcb662cc 0 2 0 1 52 1P23a35c05d7e9e966 0 2 1 1 53 1P23aa6fdcb8da1d01 0 2 0 1 52 1P2404d12958011d99 0 2 0 1 50 1P24363f46cf9094dd 0 3 1 1 53 1 54 1P24708cee73b7c819 0 3 1 1 37 1 38 1P248b255c6db4d038 0 2 0 1 52 1P249a6549ddedf38b 0 3 0 1 23 1 42 1P24bb59c591e39aae 0 3 1 1 53 1 54 1P24e4561bd795baad 0 3 1 1 37 1 38 1P24fce13afe6d9cb9 0 3 1 1 37 1 38 1P25187f5139b9bcfc 0 3 0 1 32 1 44 1P25b2fd174489e36c 0 3 1 1 53 1 54 1P25d033da8617999a 0 2 0 1 25 1P25d3522e4cc1470f 0 2 1 1 53 1P2603810d261def89 0 2 0 1 78 1P269f99eef34180d1 0 2 0 1 78 1P27004a22dc7ffb07 0 3 1 1 53 1 54 1P277de12b9baef7a3 0 3 1 1 37 1 38 1P27b3a83aadb13b55 0 2 0 1 52 1P2815ab98845a46d9 0 3 1 1 53 1 54 1P2819883db8bc3979 0 3 1 1 37 1 38 1P282100ad8b524f83 0 2 0 1 46 1P2826a813226f5bae 0 3 1 1 53 1 54 1P28a8ead6da2bf899 0 2 1 1 53 1P28d4452989b35d87 0 2 0 1 52 1P28eab4dbc39383be 0 4 0 1 67 1 69 1 71 1P29235d12ed9ec36e 0 3 1 1 37 1 38 1P295b09706ec2caa7 0 3 1 1 53 1 54 1P29d6152b7fda434b 0 3 1 1 53 1 54 1P2a012714ce5a555d 0 2 0 1 36 1P2a280b8f2b8073b8 0 3 1 1 37 1 38 1P2a2b716981d4f70b 0 2 0 1 36 1P2a360cc5856ac810 0 2 1 1 37 1P2a39bc92c121cfe2 0 2 1 1 37 1P2a4263cbcf51663f 0 3 1 1 37 1 38 1P2a7c050fa9e09146 0 2 0 1 34 1P2a7dda1ce221ae52 0 3 1 1 37 1 38 1P2a8aa785f6304566 0 2 0 1 34 1P2aaad6235924f31b 0 2 0 1 46 1P2ac1d2503d02f09b 0 2 0 1 32 1P2ae2366be5ebbb75 0 2 0 1 78 1P2b0230dbb296fcc7 0 3 1 1 53 1 54 1P2b2150281ed0e680 0 2 1 1 37 1P2b5b40a4dcd3397c 0 2 0 1 52 1P2bd499c2e323a126 0 2 0 1 36 1P2bdb8b672921fa1e 0 2 0 1 36 1P2bec4cea6da94b9d 0 3 1 1 53 1 54 1P2c0fc1fb9e9a17f4 0 2 0 1 36 1P2c3ce0d1349ac464 0 3 1 1 37 1 38 1P2caa4cf27de14b08 0 2 0 1 50 1P2d15bcbcb3aa5443 0 2 0 1 34 1P2d2a87dc6013246c 0 3 1 1 53 1 54 1P2d3c9a1f56cd843b 0 2 0 1 52 1P2d8bfcd6f8f1f785 0 2 1 1 53 1P2e0838fd3901ccea 0 3 1 1 37 1 38 1P2e158c56782370d0 0 3 1 1 37 1 38 1P2e2aacce68f87452 0 3 1 1 53 1 54 1P2e654fda63681268 0 3 0 1 19 1 32 1P2e69ff77cd708d44 0 3 1 1 53 1 54 1P2f25bf648082f0c2 0 3 1 1 53 1 54 1P2f428b77bbad705d 0 3 1 1 37 1 38 1P2f9507c4c077c5ea 0 2 0 1 52 1P2fa4bb4d83837a6a 0 2 1 1 53 1P2fb760c36d0ceb2d 0 2 0 1 50 1P2fe9ab3eb5a7e295 0 2 0 1 36 1P302cda63ce4f2000 0 2 0 1 78 1P302f925aa7624762 0 3 1 1 53 1 54 1P304181c37e2ed286 0 3 1 1 53 1 54 1P30541399f6689d5f 0 3 1 1 53 1 54 1P308615a2d7519a89 0 2 1 1 53 1P309412522c1a4751 0 2 0 1 5 1P30d44b7fc69cd532 0 3 1 1 53 1 54 1P3169d8f98a116ff4 0 2 0 1 36 1P31aa867dd7a6bb78 0 3 1 1 37 1 38 1P31ba0f4289a3a6e9 0 2 0 1 34 1P31c8ad28f27e9134 0 2 0 1 36 1P31dbfc9c6dc184a2 0 3 1 1 53 1 54 1P320a1e8e2613fb2c 0 2 0 1 52 1P321af5b0109ebc30 0 3 1 1 37 1 38 1P3255ae09b87499e6 0 2 1 1 53 1P32898d14f67cb377 0 2 0 1 36 1P331f0e2bfb53be23 0 3 1 1 37 1 38 1P334268a50780dc87 0 2 0 1 46 1P334db4ac0d4a88b3 0 2 0 1 36 1P336a42c50992872d 0 2 0 1 36 1P336c77a2c6a1aa52 0 2 0 1 36 1P3374bfad9dee1cf0 0 2 0 1 36 1P33759d0a2bec683d 0 2 0 1 36 1P33a5134ee7cddc09 0 3 1 1 37 1 38 1P33cf2bb815e85bdf 0 2 0 1 52 1P33e1d058af7c9af6 0 2 0 1 78 1P33e905d5135001b2 0 3 1 1 53 1 54 1P3468102e32ab4ab6 0 2 0 1 76 1P34a6224d308092c6 0 2 0 1 34 1P34ab8bc90c6e1ec7 0 3 1 1 53 1 54 1P353d6183838d7889 0 2 0 1 52 1P35840acb07810b53 0 3 1 1 53 1 54 1P3588192acf88f84a 0 3 1 1 53 1 54 1P359a177e117daa64 0 2 1 1 37 1P35b87e3b1aff1640 0 3 1 1 53 1 54 1P35f99230983b2dff 0 3 1 1 53 1 54 1P36f344dfff5a73c2 0 2 0 1 50 1P3719c2a530cdbaaa 0 3 1 1 53 1 54 1P372ca1704b365a14 0 2 0 1 50 1P3749683ef6d73c1e 0 2 0 1 52 1P3794e062eee52389 0 3 1 1 53 1 54 1P3797469d5487aeb6 0 2 0 1 52 1P37c8d61b7a565783 0 2 0 1 46 1P38059c1c2d15840a 0 2 0 1 52 1P384a8f2feb02f78d 0 2 0 1 52 1P38893ff9de22bf1f 0 3 1 1 53 1 54 1P38e208d343771c6e 0 2 0 1 52 1P38fcb224fd77bc32 0 3 1 1 53 1 54 1P39046cf4ad829019 0 2 0 1 52 1P3989862bfdd8a724 0 2 0 1 36 1P39abb6e2578d5e40 0 2 1 1 37 1P39b7162ef8082101 0 2 1 1 53 1P39b8256456c85e64 0 3 0 1 23 1 42 1P3a1dae59a98e47e5 0 3 1 1 53 1 54 1P3a35ecc02d2b35e3 0 2 0 1 52 1P3a52ab39ed01c6b2 0 3 1 1 37 1 38 1P3a74ef735fe68c3a 0 2 0 1 52 1P3a84fa7fa296350b 0 2 0 1 34 1P3a99f39ce2af343d 0 3 1 1 53 1 54 1P3aa339b67b3996c3 0 2 0 1 52 1P3aade72a6f2b2fc9 0 3 1 1 37 1 38 1P3aadeb989a830c97 0 3 1 1 53 1 54 1P3aae5702b63f5487 0 3 1 1 37 1 38 1P3ab27ba3b5a81fc4 0 2 0 1 36 1P3af00fb08dedb373 0 2 0 1 78 1P3b02e69d5c2844d0 0 3 1 1 37 1 38 1P3b32a17614729e32 0 2 0 1 36 1P3bfc0815e6ba1738 0 2 0 1 34 1P3c08f2c04ee54213 0 3 1 1 37 1 38 1P3c4deef723b7ef65 0 2 0 1 46 1P3ca015a057af1446 0 2 0 1 52 1P3cb05b5be8687fe5 0 2 0 1 46 1P3d1d93b6fcbbda63 0 3 1 1 53 1 54 1P3d27eb91cf1fcea3 0 2 0 1 46 1P3d8e84da0af0657e 0 3 1 1 53 1 54 1P3d917fabefc28404 0 4 0 1 66 1 68 1 70 1P3dd6501521e8adec 0 3 1 1 53 1 54 1P3e0f4a7e03793ecb 0 3 1 1 53 1 54 1P3e1d97c9a45c813d 0 3 1 1 53 1 54 1P3ecaacc02070cbe3 0 3 1 1 37 1 38 1P3ed2a93348c191d9 0 3 1 1 53 1 54 1P3efbcf852ad96b55 0 3 1 1 37 1 38 1P3f58ebbd99a39a78 0 2 1 1 53 1P3f887137a414e759 0 3 1 1 37 1 38 1P3fbb60e8ce185156 0 2 0 1 52 1P3fbfc93a79b37771 0 3 1 1 37 1 38 1P3fe2c35b0880f5aa 0 2 1 1 53 1N0010b9180095ac9cN003d0adf5fdcc2b4N00da68c78ed3c02aN011e76048613ed56N0174fc094cc63c53N02099781b92a920fN03f156599aa53140N0419d29ab88a005dN0518e13b23b1cd50N06a2bcb1bfd6136cN06d68b8f391c665fN08e7e078157a9c7aN08f1ceaf7b1b17d6N0a61a8631bf9c859N0a946ddaf6699f9eN0aa9bd10f20a5018N0bfe6bc8d9d493ebN0c689031fad800e3N0c89c80410bb9811N0d68753300b3be91N0e31de01c24d1315N0e6d62608b052226N0f63a191b0ba0ce7N10180d30afb9a313N11ff758c6813734bN12124139329e9d41N1272a5ad9ae49880N12c19b4046d81c9bN1303ce2fab0222a2N1327223a4e074009N138fab72de9fe9a5N13c640dc540c8f1bN13cdfbb4236c74faN13eb49eda48920e6N14f4fb1f544892ebN153580d0f04ae7d5N153aee68c36cea5cN15f424fb60d33a50N16c5beb5f2767cb4N172ed013f86c753cN17b4932a28a24cb7N17db756e94358d74N1821c8e1d2bc2846N1946fc613f070269N1980a30120483311N1b168e2fa01142e6N1b5f068be3052c66N1bcbad7e9d55247bN1c2da6f1f481cf3dN1cfb1fb47d2239bcN1d2c7639a1bafa56N1d50f54f6b97b948N1db11bdc87d375caN1dc154481796d1a6N1e336d0a95468c23N1f2724976b638ca0N20114b399513d559N20c6c18a82e02bc1N2143cb3149e92a19N215cf12457a2c3b0N2178352ead178cd8N21a6479399ff5cebN220bde87438ded31N22729aadc9834942N22760a4f0ea04b66N22f6c5100c91e4b9N234e69b675995fbaN235e0ae875ea1d24N236ca0e960638bb3N23846598627480c9N23a3a3f114976255N23fe69dd64e4ad24N24d1441e6e75f460N2531244831c6e80eN25aaf3a90bf187bdN25d40d26cd1fc90cN2638e2de89076678N263980c8161eb9caN2683576f2b4e112bN26cc9cde311fa866N2706ad5ecc7c6ca7N270c663581be236cN2796c14f7a358185N27c76cdd38868256N2845eb267d1fcbd5N286dd2c11b3a9bd5N28839ed96a9c2bc8N29e699bdc8243eeeN2a33b2e21007b620N2beecb9b2dfff5faN2c099bcdf09ec63dN2ccdd8f868651ab0N2dba2ee0c046cc41N2dd75b2553174a41N2dfde8a4e5c3f68bN2f490c1dc0e6dabdN2f613d86f1078e00N2f8cb3fd6abaffe0N2fb6ff50049ad207N303a47fa5f88d8c1N309f3034f6f41a60N31e3495936420b1aN32a9a28824ce036eN3372b3f4e9f45213N33cf60540271359bN33f12d6b29c0954bN35702f4dd4d29ac6N35a6f5a8471ed8d2N35b8aa72fa84f928N366f8d733f07605dN367f124f0d29c9f1N36c43b6ed1f21be7N39257603a74cb11bN39ddf63fe11a8bd6N3a5cc92d0caaf2e5N3d92ce0f5ecd8297N3e2185026c0b784aN3ed5fc665692a124N3f41ec29da8dbb29N3fba20ca39a19ea8"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_PfVsn2 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_bytes"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.pr"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.prefix_eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.pr_range"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zxb"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.B.A_vsnp_num.ndig"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01<0?L24142750981.93L25632405863.73L25632405863.76L26429915884.83L27130107066.76L27130107066.79L28002517558.73L28002517558.76L28208847179.83L28589588364.96L2927256661.68 L2927256661.71 L29396766551.94L31193536511.83L35148397023.93L35331060674.73L35331060674.76L3642410729.83 L36981668545.75L36981668545.78L39413017952.93L42512125815.83L43068215915.68L43068215915.71L43443422639.73L43443422639.76L43527503652.83L46270112731.73L46270112731.76L49927808798.68L49927808798.71L53103466515.68L53103466515.71L53517157520.83L53698772173.68L53698772173.71L55604753157.3 L60176911727.83L60431159072.83L6410694970.83 L65382697107.83L66423778277.94L66915692106.83L6848026864.93 L7075230642.76 L7075230642.79 L8798718121.73 L8798718121.76 P55608439556.76P55608439556.79Q17696774327.74Q17696774327.77Q23506379178.74Q23506379178.77Q25075822059.76Q25075822059.79Q29008194145.74Q29008194145.77Q30331531331.75Q30331531331.78Q34509719024.73Q34509719024.76Q39170186397.74Q39170186397.77Q44708747979.75Q44708747979.78Q49698585326.74Q49698585326.77Q53211001503.73Q53211001503.76Q53522260663.74Q53522260663.77Q53994776842.73Q53994776842.76Q7291830719.74 Q7291830719.77 00000Q01901W02;02g03I04704T05105f06_07N07k08H08i09\0:>0:V0;?0;S0<20<Q0=@0=Z0>@0>M0>g0?P0?o0@X0A70AY0B10BE0C>0Cm0Cn0Co0DG0Da0Db0EC0E^0F;0Fh0G@0Gf0H30Hl0IT0IU0IV0IW0IX0JM0K10K[0L20Lg0MK0N10NF0Nl0O;0P00PT0QC0QY0R>0RY0SD0SV0TD0TY0UG0U^S4rest1b3cnt3off2bs4LEN13bs'4LEN'S1q3cnt3BUF3off1E2bs3QHI2BH4ROOM2EH4CNTHS4rest3BUF3off1E2bs2BH4ROOM2EHS2b24rest1b3off2bs4LEN13B204B2273BR2S1b1q3cnt3BUF3off1E2bs3QHI4ROOM2EH4CNTH4LEN1S4rest1b3BUF3off1E2bs4ROOM2EH4LEN1S1q3cnt3SPV3BUF3off1E2bs3QHI3CCB3OFF4ROOM4CNTHS4rest3SPV3BUF3off2bs3CCB3OFFS4rest1b3cnt3off2bs4CNTH4LEN1S2b24rest1b3off2bs4LEN13B204B2273BR23bs'4LEN'1k2Hk2NES1q3cnt3SPV3BUF3off1E2bs3QHI4SPLO3CCB2BH3OFF4ROOM2EH4CNTHS4rest3SPV3BUF3off1E2bs4SPLO3CCB2BH3OFF4ROOM2EHS4rest1b3off2bs4LEN13bs'4LEN'S4rest1b3cnt3off2bs4CNT04LEN1S4rest1b3BUF3off2bs4LEN13bs'4LEN'S1q3cnt3SPV3BUF3off1E2bs3QHI4SPLO3CCB3OFF4ROOM4CNTHS4rest3SPV3BUF3off2bs4SPLO3CCB3OFFS4rest1b3off2bs3OFF4LEN1S1b1q3cnt3BUF3off1E2bs3QHI4ROOM4CNTH4LEN1S4rest1b3off2bs4LEN1S4rest1b1q3off2bs4LEN13bs'4LEN'S4rest1b3BUF3off1E2bs4ROOM4LEN1S1q3cnt3SPV3BUF3off1E2bs3QHI4SPLO3CCB4ROOM4CNTHS4rest3SPV3BUF2bs4SPLO3CCBS1q3cnt3SPV3BUF3off1E2bs3QHI4ROOM4CNTHS4rest3SPV2bsS4rest1b1q3off2bs3QLO4LEN1S1q3cnt3BUF3off1E2bs3QHI3OFF4ROOM2EH4CNTHS4rest3BUF3off1E2bs3OFF4ROOM2EHS1q3cnt3BUF3off1E2bs3QHI3OFF4ROOM2EH4CNTHS4rest3BUF3off1E2bs3OFF4ROOM2EHS1q3cnt3BUF3off1E2bs3QHI4ROOM4CNTHS4rest3BUF3off1E2bs4ROOMS4rest1b3off2bs4LEN1S1q3cnt3SPV3BUF3off1E2bs3QHI4SPLO3CCB2BH3OFF4ROOM2EH4CNTHS4rest3SPV3BUF3off1E2bs4SPLO3CCB2BH3OFF4ROOM2EHFFS4rest1b3BUF3off2bs4LEN1S4rest1b1q3off2bs3QHI4LEN1FS4rest1b3off2bs3OFF4LEN13bs'4LEN'S2b24rest1b3off2bs4LEN13BR2S4rest1b3off2bs4LEN13bs'4LEN'S1b1q3cnt3BUF3off1E2bs3QHI3OFF4ROOM4CNTH4LEN1S4rest1b3off2bs3OFF4LEN1S1q3cnt3SPV3BUF3off1E2bs3QHI4ROOM4CNTHS4rest3SPV2bsS1q3cnt3SPV3BUF3off1E2bs3QHI3CCB4ROOM4CNTH2HB5Ha_st5Hl_stS4rest3SPV3BUF3off2bs3CCB2HB5Ha_st5Hl_stFFFFS1q3cnt3SPV3BUF3off1E2bs3QHI4ROOM4CNTH2HB5Ha_st5Hl_stS4rest3SPV3BUF3off2bs2HB5Ha_st5Hl_stS2AL1q3cnt3BUF3off1E2bs3QHI4ROOM4CNTH4IMG'S2AL4rest1q2bs3QHI4IMG'S1q3cnt3SPV3BUF3off1E2bs3QHI4ROOM4CNTH2HB5Ha_st5Hl_stS4rest3SPV3BUF3off2bs2HB5Ha_st5Hl_stS1q3cnt3BUF3off1E2bs3QHI3OFF4ROOM4CNTHS4rest3BUF3off2bs3OFFS1q3cnt3BUF3off1E2bs3QLO3QHI4ROOM4CNTHS4rest1q2bs3QLOS1q3cnt3SPV3BUF3off1E2bs3QHI4ROOM4CNTH2HB5Ha_st5Hl_stS4rest3SPV3BUF3off2bs2HB5Ha_st5Hl_stS1q3cnt3SPV3BUF3off1E2bs3QHI4ROOM4CNTH2HB5Ha_stS4rest3SPV2bs2HB5Ha_stS1q3cnt3BUF3off1E2bs3QHI4ROOM2EH4CNTHS4rest3BUF3off1E2bs4ROOM2EHS2AL1q3cnt3BUF3off1E2bs3QHI4ROOM4CNTH5ALWF'S2AL4rest2bs5ALWF'S1q3cnt3SPV3BUF3off1E2bs3QHI4SPLO4ROOM4CNTH2HBS4rest3SPV2bs4SPLO2HBS2AL1q3cnt3BUF3off1E2bs3QLO3QHI4ROOM4CNTH4IMG'S2AL4rest1q2bs3QLO4IMG'". (* [comment removed for export] *)
  Lemma vsn_strloop : ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn2 ()) "Prest,(0.(1.&8.))Pb,(1.&8.)Pq,$2.Pcnt,$2.PSPV,$2.PBUF,$2.Poff,$2.PE,$2.Pbs,(0.(1.&8.))Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(4.(1.&8.))Pm,P,(1.&40.)(4.(1.&8.))P,(5.$6.R24.(7.(1.&8.)R26.(8.(1.&8.)(9.&8.=)(:.(1.&8.)))))P,(;.R26.)P,Px,(1.&8.)P,(<.(1.&8.)R1.R29.)(;.R2.)P,(=.+10000.R27.)P,(=.(>.(>.R28.(?.(10.(1.&8.)R2:.)))+1.)+65?000.)P,(=.+65?000.R27.)P,(11.$6.R7.(>.R28.+10.)(8.$12.(13.(9.&40.(>.R27.R26.)))(:.$12.)))P,(14.VCS,(>.R29.+10.)+8.)P,(=.(>.R2:.+18.)R29.)P,(15.$6.R:.R2:.R27.)P,(14.VCS,R2;.(?.(10.(1.&8.)R28.)))P,(16.(>.R2<.(?.(10.(1.&8.)R29.)))(17.+2.+3?.))P,(=.=R2<.)P,(=.(>.(>.(>.R2>.R2=.)+1.)(?.(10.(1.&8.)R33.)))R2<.)P,(=.R2=.(>.R2?.(?.(10.(1.&8.)R2<.))))P,(=.=R32.)P,(16.(>.(>.R33.+1.)(?.(10.(1.&8.)R36.)))(17.+2.+1?.))P,(18.(8.(19.$2.$2.)(1:.$2.$2.(>.R33.+10.)(>.R33.+18.))(8.(19.$2.$2.)(1:.$2.$2.R32.(>.R32.(?.(10.(1.&8.)R2?.))))(:.(19.$2.$2.))))R13.R12.)P,(1;.$6.R14.R13.)P,(1<.$6.R14.)(1=.$6.VAL,VCS,Lms',$1>.(1?.(0.(1.&8.))Lbs',(0.(1.&8.))(1?.P,(1.&40.)(4.(1.&8.))Lm',P,(1.&40.)(4.(1.&8.))(20.(21.$1>.R3.(22.(23.R34.(9.&40.R39.)R33.R32.R31.R30.R2?.R2>.R2=.R2<.(9.&40.(>.(>.R3:.+1.)(?.(10.(1.&8.)R3=.))))(9.&40.(>.(>.R3;.(?.(10.(1.&8.)R3=.)))+1.))(9.&40.(>.(>.(>.R38.R37.)+1.)(?.(10.(1.&8.)R3=.))))(9.&40.=)R2;.R2:.R29.R28.(9.&40.R36.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(9.&40.+7=:=<.)R1:.(24.(1.&40.))R1.(25.$6.)))(20.(11.$6.R1.(>.R39.+10.)(8.$12.(13.(9.&40.(>.(>.(>.R38.R37.)+1.)(?.(10.(1.&8.)R3=.)))))(:.$12.)))(20.(15.$6.R1.R38.R2.)(20.(21.$26.(10.(1.&8.)R2.)(10.(1.&8.)R35.))(20.(27.R35.R2.R37.)(20.(28.R2.R37.(>.(>.R37.+1.)(?.(10.(1.&8.)R3=.))))(20.(18.(8.(19.$2.$2.)(1:.$2.$2.(>.R39.+10.)(>.R39.+18.))(8.(19.$2.$2.)(1:.$2.$2.R38.(>.R38.(?.(10.(1.&8.)R35.))))(:.(19.$2.$2.))))R19.R1.)(20.(1;.$6.R19.R1.)(1<.$6.R1.)))))))))))(22.(23.R31.(9.&40.R36.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(9.&40.R37.)(9.&40.R38.)(9.&40.(>.R35.R34.))(29.R39.)R28.R27.R26.R25.(9.&40.R33.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(9.&40.+7=::4.)R17.(24.(1.&40.))R15.(25.$6.)))")
(* [comment removed for export] *).
  Proof.
    induction rest as [|b2 rest IH]; intros until m; intros RO PB PRS QLO QHI SPLO CCH CRC CCB OUT CRB BH OFF ROOM EH CNT0 CNTH MU WM MI; al_facts.
    all: cbn [length] in *; rewrite ?Nat2Z.inj_succ in *.
    all: pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn [Z.pow Z.of_N Pos.pow] in BR.
    all: cbn [app] in RO; destruct RO as [ROB RO].
    all: pose proof (mem_inv_ro_read asegs m q _ MI ROB) as RD1.
    all: zstep; if_falseU.
    all: destruct (out_store m BUF off bs b OUT ltac:(lia) ltac:(lia) BH MI) as (SOK & OUT1 & MI1 & WM1 & MU1).
    all: zstep.
    all: change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)); rewrite le1_zxb.
    all: specialize (MU1 _ _ MU ltac:(cbn [inside]; right; left; lia)).
    all: apply (wmono_trans asegs _ _ _ WM) in WM1.
    all: apply (rw_cells_frame asegs m (SPV + 16) _ (BUF + off) [b]) in CCH; [| lia | cbn [length]; lia | cbn; lia].
    all: change (wa (BUF + off)) with (Z_to_bv 64 (BUF + off)) in *.
    all: set (m1 := write_to_mem m (Z_to_bv 64 (BUF + off)) [b]) in *; clearbody m1.
    all: clear SOK RD1.
    all: zstep; zstep; zstep; zstep.
    all: match goal with MIx : mem_inv asegs ?mx |- _ (MS _ _ _ _ _ ?mx _) => pose proof (mem_inv_ro_read asegs mx q _ MIx ROB) as RD1;
           assert (RD : ov_read_bytes asegs mx (Z_to_bv 64 q) 1 = Some [_]) by (rewrite ov_rdn, rdn_unfold; change (Z_to_bv 64 q) with (wa q); rewrite RD1; reflexivity) end.
    all: zstep; zstep; zstep; zstep.
    all: assert (LEN1 : length (upd bs (Z.to_nat off) b) = length bs) by apply upd_length.
    all: assert (PE1 : prefix_eq bs (upd bs (Z.to_nat off) b) off) by (apply prefix_eq_upd; lia).
    all: assert (PR1 : pr_range (upd bs (Z.to_nat off) b) off (off + 1)) by (apply pr_range_snoc; [apply pr_range_empty| lia| lia| exact PB]).
    - apply evtA_done. cbn [Z.of_nat]. rewrite !Z.add_0_r. eexists _, m2. split; [reflexivity|].
      split; [exact CCH|]. split; [exact OUT1|]. split; [exact LEN1|]. split; [exact PE1|]. split; [exact PR1|].
      split; [exact MU1|]. split; [exact WM1| exact MI1].
    - destruct (PRS b2 (or_introl eq_refl)) as [B20 B227].
      pose proof (bv_unsigned_in_range 8 b2) as BR2; unfold bv_modulus in BR2; cbn [Z.pow Z.of_N Pos.pow] in BR2.
      if_falseU.
      replace (BUF + off + 1) with (BUF + (off + 1)) in * by lia. change (Z_to_bv 64 (bv_unsigned b2)) with (zxb b2).
      eapply (evtA_mono asegs AL CS).
      { eapply (IH b2 (q + 1) (cnt + 1) SPV BUF (off + 1) E (upd bs (Z.to_nat off) b)); try rewrite LEN1; try eassumption; try lia.
        - split; assumption.
        - intros x Hx. apply PRS. right. exact Hx. }
      cbn beta. intros ms' (bs' & m' & -> & CCH' & OUT' & LEN' & PE' & PR' & MU' & WM' & MI').
      eexists bs', m'.
      replace (cnt + 1 + 1 + Z.of_nat (length rest)) with (cnt + 1 + Z.succ (Z.of_nat (length rest))) by lia.
      replace (q + 1 + Z.of_nat (length rest) + 1) with (q + Z.succ (Z.of_nat (length rest)) + 1) by lia.
      replace (BUF + (off + 1) + 1 + Z.of_nat (length rest)) with (BUF + (off + 1) + Z.succ (Z.of_nat (length rest))) in * by lia.
      split; [reflexivity|]. split; [exact CCH'|].
      split; [exact OUT'|]. split; [rewrite LEN'; exact LEN1|].
      split; [eapply prefix_eq_trans; [exact PE1| exact PE'| lia]|].
      split; [|split; [rewrite <- LEN1; exact MU'|split; [exact WM'| exact MI']]].
      intros k Hk; destruct (Z.eq_dec k off) as [->|NE]; [rewrite PE' by lia; apply PR1; lia| apply PR'; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition str_asan_tail : list byte := map (Z_to_bv 8) [100;100;114;101;115;115;83;97;110;105;116;105;122;101;114].
  Definition fmt_oom1_lit : list byte := map (Z_to_bv 8) [58;32;79;117;116;32;111;102;32;109;101;109;111;114;121;46;32].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@C7735802038.105 C7735802038.106 C7735802038.107 K44164039966.106K51568474198.105K57502636100.105K57502636100.106K57502636100.107L12918770360.2  L13271016587.11 L13272883632.11 L13931612467.1  L15045032506.11 L15045194790.3  L15121082681.2  L18677440057.2  L20578020426.11 L20579887473.11 L20765300874.1  L21084722684.1  L23370930316.3  L2472639188.3   L2488439402.1   L25851734559.11 L26220523669.1  L27692218474.2  L29232893998.3  L29544327097.2  L29820868625.1  L32027975233.0  L33077831927.2  L36225192527.4  L44166645080.2  L46256578908.0  L46509758831.1  L46728936358.11 L48178441532.0  L48947786748.1  L49396667621.0  L49448063295.4  L50070528111.2  L51564585761.2  L52014379532.3  L52112781644.0  L53880390231.1  L53912167311.1  L54105727247.1  L5478825391.2   L54868683973.0  L54971080283.11 L54973406048.11 L56982188541.11 L57504225282.2  L58234243953.4  L58972629835.11 L58974629488.11 L60230008169.2  L60900702101.0  L61369582905.11 L62575142762.1  L63496200470.11 L6364778611.7   L64514878738.11 L65500263341.11 L65852717012.11 L66566358642.5  L67214993615.2  L9768996348.1   N21855282908.107N21855282908.87 N39208679943.107N39208679943.87 N7920831721.107 N7920831721.87  O26678291594.85 O26688781277.105O28456226397.105O28470909194.85 O28472746265.85 O28487431758.105O28814377356.105O28816479963.85 O36326070192.105O36336550119.85 O36407143180.85 O36421827675.105O4571592027.85  O4573684236.105 O49633738830.105O49635841817.85 O51593762169.85 O51604242990.105O9671024925.105 O9673127498.85  P15127361611.105P18683744075.105P20758989304.105P21080100702.105P21082200073.85 P23375694343.85 P23381990736.105P2494743320.105 P29529667275.105P44164039966.106P48943622494.105P48949919241.85 P50065797860.85 P50076280243.105P52009672839.85 P52024358864.105P5473106035.105 P5483589412.85  P57502636100.105P57502636100.106P57502636100.107P58237966842.85 P58244255405.105P60217241176.105P60227729679.85 P62564644376.105P67211344452.85 P67226021139.105P9770663945.85  P9772767070.105 Q43326511339.101Q43330355346.105Q57524744393.103Q58463610890.104Q66219132086.104Q6851534445.105 Q6855902740.101 00000100200300400Z00[00\00]00d01801M01Q01U01V01W01X01g02702802902:02C02D02Q02U02[02\02]02a02b02i03703803903>03C03D03E03F03T03U03V03W03X03]03a03e03f03g04504D04I04J04K04]04n04o05005505605:05G05K05P05^05n05o06006T06o07L07`07a07b07c07d07e07f07g07h07i07j07k07l07m07n07o08008108208308408508608W09809f0:L0:i0;C0;f0<T0=50=60=\0>90>`0?P0?j0@M0A=0Ad0Ae0Af0Ag0BD0Bj0CK0Cc0DQ0E80Eh0FE0Fk0GJ0Gi0HI0Hn0IP0Ij0JDFFFFS3BUF1n2VA2bs2Hn3VAB3bs14LEN13bs24LEN2FFFS3BUF1nS2SP2lo2bs5LOIMG3SPLS2SP2lo5LOIMG3SPL3bs1S2SPS2bsSFFS2SP3BUF2bs3SPBS2SP3BUF3SPB3bs1FFFS1i2Hi2GEFS3BUF1n2bs2HnS2SPS1i2HiSFS2SPSS2SP2loS1n2Hn3bs23LB2FSS3BUFS3bs1SFSS1n2Hn3bs23LB2FFFSS3BUFS2SPS2SPFSS3BUF1n2bs3LENS3BUF1n3bs13LB1S3bs1FFS3BUF1n2BH3bs13LB1S3BUF1n2bs3LEN2BHFSS3bs1FS2bsS3bs11i2Hi2LTS2bsS3bs1S3BUF1n2Hn3bs1S2SP2lo3SPL1x2HxFFS2SP2lo2bs3SPL3bs14LEN13bs24LEN21x1CS2SP2lo2bs3SPL3bs14LEN11x1CS2SP2bs3bs14LEN13bs24LEN21x1CS2SP2bs3bs14LEN11x1CFFFFFFFFFFFFFFFFFFFFFFS2SP3BUF2bs3SPB3bs14LEN13bs24LEN2S2SP3BUF2bs3SPB3bs14LEN13bs24LEN2S2SP2lo3BUF2bs5LOIMG3SPL3SPB3bs14LEN13bs24LEN2S2SP2lo2bs5LOIMG3SPL3bs14LEN13bs24LEN2S2SP2lo2bs5LOIMG3SPL3bs14LEN1S2SP3BUF1n2bs3SPB3bs14LEN1S2SP3BUF1n2bs3SPB3bs14LEN13bs24LEN2S2SP2lo3BUF2bs5LOIMG3SPL3SPB3bs14LEN13bs24LEN2S2SP3BUF2bs3SPB3bs14LEN13bs24LEN2FS2SP2lo2bs5LOIMG3SPL3bs14LEN13bs24LEN2S2SP2lo2bs5LOIMG3SPL3bs14LEN1S2SP2lo3BUF1n2bs5LOIMG3SPL3SPB3bs14LEN1S2SP2lo3BUF1n2bs5LOIMG3SPL3SPB3bs14LEN13bs24LEN2S2SP3BUF1n2bs3SPB3bs14LEN1S2SP3BUF1n2bs3SPB3bs14LEN13bs24LEN2S2SP2lo3BUF1n2bs5LOIMG3SPL3SPB3bs14LEN13bs24LEN2S2SP2lo3BUF1n2bs5LOIMG3SPL3SPB3bs14LEN1FFFS2SP2lo3BUF1n2bs3SPB3bs14LEN1S2SP2lo3BUF1n2bs3SPB3bs14LEN13bs24LEN2S2SP2VA2bs4SPVA3bs14LEN13bs24LEN2S2SP2VA2bs4SPVA3bs14LEN1S2SP2lo3BUF2bs5LOIMG3SPL3SPB3bs14LEN13bs24LEN2S2SP2lo3BUF1n2bs5LOIMG3SPL3SPB3bs14LEN1S2SP2lo3BUF1n2bs5LOIMG3SPL3SPB3bs14LEN13bs24LEN2S2SP2lo2bs5LOIMG3SPL3bs14LEN1S2SP2lo2bs5LOIMG3SPL3bs14LEN13bs24LEN2S3BUF1n2bs2Hn3bs14LEN13bs24LEN2S3BUF1n2bs2Hn3bs14LEN13bs24LEN2S3BUF2bs3bs14LEN13bs24LEN25HBarrS2SP2lo3BUF1n2bs2Hn3bs14LEN13bs24LEN2S3BUF1n2bs2Hn2BH3bs14LEN13bs24LEN2S3BUF2bs3bs14LEN13bs24LEN2S3BUF2bs3bs14LEN13bs24LEN2". (* [comment removed for export] *)
  Theorem vsn_f1_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn2 ()) "PSP,$2.Plo,$2.PBUF,$2.Pn,$2.PVA,$2.Pbs,(0.(1.&8.))Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(4.(1.&8.))P,(20.(=.+23.R20.)(16.R20.(17.+2.+1?.)))P,(21.$2.(?.(10.(1.&8.)R1?.))R21.)P,(2:.$6.R3.R24.R25.)P,(=.+65?000.R25.)P,(=.R26.(2;.R27.+80.))P,(14.VCS,R27.(2;.R28.R27.))P,(=.R29.R27.)P,(15.$6.R8.R28.R25.)P,(14.VCS,R29.R28.)P,(16.(>.R2:.R29.)(17.+2.+3?.))P,(11.$6.R;.R29.(8.$12.(13.(9.&40.+240?>.))(:.$12.)))P,(14.VCS,R2:.+8.)P,(=.R2?.R2;.)P,(2<.(=.(>.R2<.+8.)R2>.)(=.(>.R2>.R2=.)R2<.))P,(16.(>.R2=.+8.)(17.+2.+3?.))P,(1<.$6.R10.)(1=.$6.VAL,VCS,Lms',$1>.(1?.(1.&40.)La1',(1.&40.)(1?.(1.&40.)La2',(1.&40.)(1?.(1.&40.)La3',(1.&40.)(1?.(1.&40.)La4',(1.&40.)(1?.(1.&40.)La5',(1.&40.)(1?.(1.&40.)La6',(1.&40.)(1?.(1.&40.)La7',(1.&40.)(1?.(1.&40.)Lt0',(1.&40.)(1?.(1.&40.)Lt1',(1.&40.)(1?.(1.&40.)Lt2',(1.&40.)(1?.(1.&40.)Lt3',(1.&40.)(1?.(1.&40.)Lt4',(1.&40.)(1?.(0.(1.&8.))Lbs',(0.(1.&8.))(1?.P,(1.&40.)(4.(1.&8.))Lm',P,(1.&40.)(4.(1.&8.))(20.(21.$1>.R?.(22.(23.R3<.(9.&40.R42.)R3;.R3:.R7.R6.R5.R36.R35.(9.&40.+21.)R>.R=.R<.R;.R:.R9.R8.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R4.R3.R24.R23.)R22.(2=.R3<.)R21.(24.(1.&40.))R1.(25.$6.)))(20.(2:.$6.R1.R41.R42.)(20.(15.$6.R1.R40.R2.)(20.(21.$26.(10.(1.&8.)R2.)(10.(1.&8.)R3=.))(20.(28.R2.=+21.)(20.(21.(4.(1.&8.))(2>.(1.&8.)R2.(2?.+21.))(30.(1.&8.)(9.&8.=)))(20.(11.$6.R1.R3>.(8.$12.(13.(9.&40.+240?>.))(:.$12.)))(20.(18.(8.(19.$2.$2.)(1:.$2.$2.R41.R42.)(8.(19.$2.$2.)(1:.$2.$2.R40.(>.R40.R3?.))(:.(19.$2.$2.))))R20.R1.)(20.(1;.$6.R20.R1.)(1<.$6.R1.))))))))))))))))))))))))(22.(23.R2=.(9.&40.R33.)R2<.R2;.R2:.R29.R28.R27.R26.(9.&40.R31.)(9.&40.R30.)(9.&40.+221;8.)(9.&40.R2?.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(9.&40.+7=810.)R12.(24.(1.&40.))R11.(25.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros Hn LEN ST LOIMG SPL SCS SPB OUT CRB BH VAC CRV SPVA VAB VAH MI. al_facts.
    pose proof (munch_refl [(lo, SP); (BUF, BUF + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct OUT as [OUTb OUTw].
    (* [comment removed for export] *)
    assert (FMTC : ro_cells asegs m 139704 [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 58); C1 (Z_to_bv 8 32); C1 (Z_to_bv 8 79); C1 (Z_to_bv 8 117); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 32); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 102); C1 (Z_to_bv 8 32); C1 (Z_to_bv 8 109); C1 (Z_to_bv 8 101); C1 (Z_to_bv 8 109); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 114); C1 (Z_to_bv 8 121); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 32); C1 (Z_to_bv 8 0)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (STRC : ro_cells asegs m 147710 [C1 (Z_to_bv 8 65); C1 (Z_to_bv 8 100); C1 (Z_to_bv 8 100); C1 (Z_to_bv 8 114); C1 (Z_to_bv 8 101); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 83); C1 (Z_to_bv 8 97); C1 (Z_to_bv 8 110); C1 (Z_to_bv 8 105); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 105); C1 (Z_to_bv 8 122); C1 (Z_to_bv 8 101); C1 (Z_to_bv 8 114); C1 (Z_to_bv 8 0)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (JTC : ro_cells asegs m 150188 [C4 (Z_to_bv 64 364492)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    (* [comment removed for export] *)
    lx_run (PLAN [0x7daa4] [] 200%N).
    (* [comment removed for export] *)
    lazymatch goal with FRl : rw_cells _ ?mx (SP + -128) _, BYl : bytes_at _ _ BUF bs, WMl : wmono _ m _ |- _ =>
      chunk_split FRl 2%nat FRa FRr; chunk_split FRr 1%nat CCH FRb;
      replace (SP + -128 + 16 + 8) with (SP + -104) in FRb by (clear; lia);
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw WMl) : u8arr asegs mx BUF bs) as OUTl; clear BYl; try clear LXlen end.
    replace (BUF + (n + -1)) with (BUF + n + -1) by (clear; lia).
    change (Z_to_bv 64 65) with (zxb (Z_to_bv 8 65)). replace (Z_to_bv 64 BUF) with (Z_to_bv 64 (BUF + 0)) in CCH |- * by (f_equal; clear; lia).
    assert (ROS : ro_bytes asegs 147711 (str_asan_tail ++ [Z_to_bv 8 0])) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
    assert (CRC : crange CS (SP + -128 + 16) 8) by (intros x Hx; apply SCS; clear -Hx SPL; lia).
    eapply (evtA_cut asegs AL CS).
    { eapply (vsn_strloop str_asan_tail (Z_to_bv 8 65) 147711 0 (SP + -128) BUF 0 (BUF + n + -1) bs);
        first [ exact ROS | exact CCH | exact CRC | exact OUTl | apply munch_refl | apply wmono_refl | assumption
              | split; vm_compute; discriminate
              | intros x Hx; apply (litok_all str_asan_tail); [vm_compute; reflexivity| exact Hx]
              | rewrite LEN; exact CRB
              | cbn [length str_asan_tail map]; clear -Hn LEN SPL SPB LOIMG BH; lia ]. }
    cbn beta. intros ms' (bs1 & m2 & -> & CCH1 & OUT1 & LEN1 & PE1 & PR1 & MUc & WMc & MIc).
    rewrite LEN in MUc. clear CCH OUTl ROS.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx m2 MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    change (Z.of_nat (length str_asan_tail)) with 15 in *. change (0 + 1 + 15) with 16 in *. change (147711 + 15 + 1) with 147727.
    replace (BUF + 0 + 1 + 15) with (BUF + 16) in CCH1 |- * by (clear; lia). replace (SP + -128 + 16) with (SP + -112) in CCH1 by (clear; lia).
    assert (LB1 : Z.of_nat (length bs1) = n) by (rewrite LEN1; exact LEN).
    destruct OUT1 as [OUT1b OUT1w].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7d8a0] [] 20%N).
    (* [comment removed for export] *)
    assert (OUTw1 : wr_at asegs m BUF (Z.of_nat (length bs1))) by (rewrite LB1, <- LEN; exact OUTw).
    first [ lazymatch goal with CCl : rw_cells _ _ (SP + -112) (_ :: _) |- _ => rename CCl into CCH end
          | lazymatch goal with FRl : rw_cells _ _ (SP + -128) (_ :: _ :: _ :: _) |- _ =>
              chunk_split FRl 2%nat FRa2 FRr; chunk_split FRr 1%nat CCH FRb2; replace (SP + -128 + 16 + 8) with (SP + -104) in FRb2 by (clear; lia);
              replace (SP + -128 + 16) with (SP + -112) in CCH by (clear; lia) end ].
    replace (SP + -112) with (SP + -128 + 16) in CCH by (clear; lia).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bs1, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw1 WMl) : u8arr asegs mx BUF bs1) as OUT2; clear BYl OUTw1; try clear LXlen end.
    replace (BUF + (n + -1)) with (BUF + n + -1) by (clear; lia).
    assert (ROF : ro_bytes asegs 139706 (fmt_oom1_lit ++ [Z_to_bv 8 0])) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
    eapply (evtA_cut asegs AL CS).
    { eapply (vsn_litloop AL IMG ALWF CS CSOK fmt_oom1_lit (Z_to_bv 8 0) 139706 16 (SP + -128) BUF 16 (BUF + n + -1) bs1);
        first [ exact ROF | exact CCH | exact CRC | exact OUT2 | apply munch_refl | apply wmono_refl | assumption
              | apply litok_all; vm_compute; reflexivity
              | rewrite LB1; exact CRB
              | cbn [length fmt_oom1_lit map]; clear -Hn LB1 SPL SPB LOIMG BH; lia ]. }
    cbn beta. intros ms' (a0l & a1l & bs2 & m3 & -> & CCH2 & OUT3 & LEN2 & PE2 & PR2 & MUc & WMc & MIc2).
    rewrite LB1 in MUc. clear CCH OUT2 ROF.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx m3 MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    change (Z.of_nat (length fmt_oom1_lit)) with 17 in *. change (16 + 17) with 33 in *. change (139706 + 17) with 139723.
    replace (SP + -128 + 16) with (SP + -112) in CCH2 by (clear; lia).
    assert (LB2 : Z.of_nat (length bs2) = n) by (rewrite LEN2; exact LB1).
    destruct OUT3 as [OUT3b OUT3w].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7dc60] [] 30%N).
    try subst lxm. lx_clear_mem m2.
    (* [comment removed for export] *)
    assert (OUTw2 : wr_at asegs m BUF (Z.of_nat (length bs2))) by (rewrite LB2, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bs2, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw2 WMl) : u8arr asegs mx BUF bs2) as OUT4; clear BYl OUTw2; try clear LXlen;
      pose proof (u8arr_store_ok asegs mx BUF bs2 33 (Z_to_bv 64 (BUF + 33)) OUT4 ltac:(clear -LB2 Hn; lia) eq_refl) as SOK end.
    zstep. rewrite (le1_lit 0) by (clear; lia).
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u8arr_write asegs mx BUF bs2 33 (Z_to_bv 8 0) OUT4 ltac:(clear -LB2 Hn; lia)) as OUT5 end.
    store_done. try clear SOK.
    destruct OUT5 as [OUT5b OUT5w].
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 30%N).
    assert (OUTw5 : wr_at asegs m BUF (Z.of_nat (length (upd bs2 (Z.to_nat 33) (Z_to_bv 8 0))))) by (rewrite upd_length, LB2, <- LEN; exact OUTw).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, BYl : bytes_at _ _ BUF _ |- _ =>
      apply evtA_done; lx_exs; lx_ands;
      [ lx_mseq
      | assumption
      | exact (conj BYl (wr_at_transport _ _ _ _ _ OUTw5 WMl))
      | rewrite upd_length, LEN2; exact LEN1
      | intros i Hi; rewrite nth_error_upd_other by (clear -Hi; lia); destruct (Z_lt_le_dec i 16) as [LT|GE];
          [ eapply pr_range_prefix; [exact PR1| exact PE2| clear -Hi LT; lia| clear -Hi LT; lia| clear -Hi LT LB1 Hn; lia]
          | apply PR2; clear -Hi GE; lia ]
      | apply nth_error_upd_same; clear -LB2 Hn; lia
      | assumption | exact MUl | exact WMl | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition fmt_oom2_l1 : list byte := ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn2 ()) "(31.$2.(1.&8.)(9.&8.)(8.$2.+54.(8.$2.+68.(8.$2.+65.(8.$2.+20.(8.$2.+70.(8.$2.+72.(8.$2.+6?.(8.$2.+63.(8.$2.+65.(8.$2.+73.(8.$2.+73.(8.$2.+20.(8.$2.+68.(8.$2.+61.(8.$2.+73.(8.$2.+20.(8.$2.+65.(8.$2.+78.(8.$2.+68.(8.$2.+61.(8.$2.+75.(8.$2.+73.(8.$2.+74.(8.$2.+65.(8.$2.+64.(8.$2.+20.(:.$2.))))))))))))))))))))))))))))")
(* [comment removed for export] *).
  Definition fmt_oom2_l2 : list byte := map (Z_to_bv 8) [32;77;66;32;102;111;114;32;115;105;122;101;32;99;108;97;115;115;32].
  Definition fmt_oom2_l3 : list byte := map (Z_to_bv 8) [32;40].
  Definition fmt_oom2_l4 : list byte := map (Z_to_bv 8) [32;98;121;116;101;115;41;46;10].

  Ltac fold_closed_z :=
    repeat match goal with
    | |- context [Z.b2z (?a <? ?b)] => let v := eval vm_compute in (Z.b2z (a <? b)) in change (Z.b2z (a <? b)) with v
    end;
    repeat match goal with
    | |- context [Z_to_bv 64 (?x - ?y)] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (x - y) in change (x - y) with v
    | |- context [Z_to_bv 64 (?x + ?y)] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (x + y) in change (x + y) with v
    end.
  Ltac zstepf := first [ zstep | (fold_closed_z; zstep) ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L15045194790.16L21415495027.16L32974222010.16L38972254420.1600000100>00K00NSS1a1b1i2Hi2GES1a1b1i2Hi2LTS1a". (* [comment removed for export] *)
  Lemma pr_range_extend : ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn2 ()) "Pxs,(0.(1.&8.))Pxs',(0.(1.&8.))Pa,$2.Pb,$2.P,(28.R4.=R2.)P,(27.R5.R4.R3.)P,(28.R5.R4.R3.)P,(=.=R5.)(28.R7.=R5.)")
(* [comment removed for export] *).
  Proof. intros xs xs' a b H1 H2 H3 Ha i Hi. destruct (Z_lt_le_dec i a) as [LT|GE]; [eapply pr_range_prefix; [exact H1| exact H2| lia| lia| lia] | apply H3; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06f0@C13764637640.152C13764637642.136C13764637644.120C17014926024.151C17014926026.135C17014926028.119L10618413726.3  L11756639497.22 L11756639753.14 L12113396597.7  L12918770360.2  L13271016587.11 L13272883584.15 L13272883588.23 L13272883590.23 L13661641124.7  L13931612467.1  L14149232373.1  L1419338836.22  L14330209397.1  L14811944510.2  L15045032506.11 L15172795127.15 L15172878871.3  L15920300924.1  L16669576992.9  L16669576993.22 L16806171132.1  L17885720845.16 L17903019543.8  L1828508571.22  L18536215029.23 L18536215285.15 L19101061691.23 L19209173186.1  L19236364733.22 L19236364989.14 L19274831102.14 L19274831870.22 L195118956.0    L19755737389.2  L2031876783.2   L20578020426.11 L20579887425.15 L20579887429.23 L20579887431.23 L20584916343.14 L2312959868.0   L23283958317.2  L23319080389.14 L23370930316.3  L23384764189.15 L23464192230.14 L23464192998.22 L23715241049.70 L23715241177.68 L23715241945.72 L25159285657.70 L25924156977.3  L26220523669.1  L26559125860.7  L27294482733.2  L28111658535.8  L2958118052.7   L29820868625.1  L29886112823.22 L31839127518.22 L31839127519.9  L31950456780.23 L32027975233.0  L33077831927.2  L33414278631.2  L33473186477.68 L34764881284.23 L34764881540.15 L34862854693.3  L35046729807.2  L35685890861.2  L36032598652.1  L36109843872.14 L36109844128.22 L37352693208.23 L37352693210.23 L38072217075.11 L38452488413.2  L39044636597.0  L3949604542.2   L39784994434.1  L41435685113.22 L41435685881.14 L42137636273.15 L43186549017.15 L43325479547.9  L43325579677.23 L44608643791.2  L45060654645.0  L4531812619.11  L45364655525.0  L45380655605.0  L45890636139.1  L45906304563.5  L46443948538.15 L46509758831.1  L46911241205.1  L47645080066.1  L47706155461.72 L48020663429.0  L48065838564.7  L49273267842.1  L49485674697.23 L49530372422.11 L51425135484.1  L51523651672.23 L51523651674.23 L51523651678.15 L52014379532.3  L52880649725.7  L53427981929.11 L53690782884.3  L53806113228.0  L53912167311.1  L53981202600.3  L54105727247.1  L54398614572.0  L54554180237.16 L54611292832.3  L54879612862.2  L54971080283.11 L57122632560.8  L58234243953.4  L58713211983.2  L58972629883.15 L58972629885.23 L58972629887.23 L58974629488.11 L5937668621.23  L59565979266.11 L59726336417.0  L60230008169.2  L60516700949.0  L60693205159.8  L62051727448.8  L62522128194.1  L63082623084.23 L63268789266.3  L63674199992.23 L63674199994.23 L63674199998.15 L6396841767.8   L64072613375.23 L64236967981.2  L64317360284.0  L65029254940.14 L65319781658.9  L65319829246.23 L65374700796.1  L6623085637.5   L66566358642.5  L6860841066.165 L8768825252.7   L9158076143.2   N21855282908.108N21855282908.120N21855282908.125N21855282908.136N21855282908.141N21855282908.152N21855282908.157N39208679943.108N39208679943.120N39208679943.125N39208679943.136N39208679943.141N39208679943.152N39208679943.157N7920831721.108 N7920831721.120 N7920831721.125 N7920831721.136 N7920831721.141 N7920831721.152 N7920831721.157 O12005851168.135O12005851170.151O12005851174.119O13472660009.119O13472660013.151O13472660015.135O17014926024.151O17014926026.135O17014926028.119O23207863247.106O23207863288.139O23207863290.155O23207863294.123O24186381600.135O24186381602.151O24186381606.119O24447821340.106O24447821352.151O24447821353.155O24447821354.135O24447821355.139O24447821356.119O24447821357.123O26923684352.135O26923684354.151O26923684358.119O28223626089.119O28223626093.151O28223626095.135O28816479885.106O28816479928.155O28816479929.152O28816479930.139O28816479931.136O28816479932.123O28816479933.120O36336550016.123O36336550020.155O36336550022.139O36336550065.106O36407143258.106O36407143275.123O36407143277.139O36407143279.155O43308370972.106O43308370984.151O43308370985.155O43308370986.135O43308370987.139O43308370988.119O43308370989.123O43452743384.139O43452743386.155O43452743390.123O43452743407.106O43472198876.106O43472198888.151O43472198889.155O43472198890.135O43472198891.139O43472198892.119O43472198893.123O4571591949.106 O4571591992.155 O4571591993.152 O4571591994.139 O4571591995.136 O4571591996.123 O4571591997.120 O46104344860.106O46104344872.151O46104344873.155O46104344874.135O46104344875.139O46104344876.119O46104344877.123O48916995401.119O48916995405.151O48916995407.135O53723584201.119O53723584205.151O53723584207.135O55626484480.120O55626484484.152O55626484486.136O58814920288.135O58814920290.151O58814920294.119O59856760408.139O59856760410.155O59856760414.123O59856760431.106O62362011612.106O62362011624.151O62362011625.155O62362011626.135O62362011627.139O62362011628.119O62362011629.123O6441113763.120 O6441113765.136 O6441113767.152 O65605440585.119O65605440589.151O65605440591.135O67353074712.139O67353074714.155O67353074718.123O67353074735.106O7917776591.106 O7917776632.139 O7917776634.155 O7917776638.123 O9351601792.135 O9351601794.151 O9351601798.119 P13665991141.156P15918108383.106P15918108392.139P15918108394.155P15918108398.123P16804371551.106P16804371560.139P16804371562.155P16804371566.123P17917159013.156P19206976849.119P19206976853.151P19206976855.135P19757333593.135P19757333595.151P19757333599.119P2035492930.119 P2035492931.123 P2035492932.135 P2035492933.139 P2035492934.151 P2035492935.155 P2035492978.106 P23286603609.135P23286603611.151P23286603615.119P23375694417.106P23375694432.123P23375694433.120P23375694436.155P23375694437.152P23375694438.139P23375694439.136P25922239025.120P25922239029.152P25922239031.136P26571864357.156P27292900441.135P27292900443.151P27292900447.119P28107587174.156P2962435301.156 P35043048082.106P35043048098.119P35043048099.123P35043048100.135P35043048101.139P35043048102.151P35043048103.155P35687442009.135P35687442011.151P35687442015.119P36030275551.106P36030275560.139P36030275562.155P36030275566.123P38450539737.152P38450539739.136P38450539741.120P39786732305.119P39786732309.151P39786732311.135P44604928018.106P44604928034.119P44604928035.123P44604928036.135P44604928037.139P44604928038.151P44604928039.155P47646881681.119P47646881685.151P47646881687.135P48053099941.156P49271401233.119P49271401237.151P49271401239.135P51422873311.106P51422873320.139P51422873322.155P51422873326.123P52009672913.106P52009672928.123P52009672929.120P52009672932.155P52009672933.152P52009672934.139P52009672935.136P58237966745.155P58237966747.139P58237966749.123P58237966764.106P58717918866.106P58717918882.119P58717918883.123P58717918884.135P58717918885.139P58717918886.151P58717918887.155P60227729753.106P60227729768.123P60227729772.155P60227729774.139P60689133798.156P62047410201.156P62524259025.119P62524259029.151P62524259031.135P6401191782.156 P64239568217.135P64239568219.151P64239568223.119P65372768607.106P65372768616.139P65372768618.155P65372768622.123P8764770277.156 P9153410050.119 P9153410051.123 P9153410052.135 P9153410053.139 P9153410054.151 P9153410055.155 P9153410098.106 Q22908537960.155Q22912586769.152Q27841045884.152Q27845098757.155Q31952571586.153Q31961136359.152Q31974155422.155Q42588614267.155Q42592925186.152Q53790155573.155Q53802597196.152Q58463610890.155Q60251772067.152Q60256406746.155Q8338307705.152 Q8351293952.155 Q8915256987.154 00000400800<00=00>00?00J00]00d01;01B01V02102X03?03@03D03H03l04004704;04J04U04V04m05D05E06=06>06W06X06Y07007107N07_07i08?08@08A08B08Q08g09I09k0:?0:@0:A0:N0:O0:Z0:j0;F0;J0;N0;R0;]0;^0;b0;c0;d0;e0;f0;j0<R0<m0=H0=k0=l0>30>40>?0>@0>A0>L0>M0>N0>O0>a0??0?b0@A0@N0@O0@P0@W0@X0@k0A20AA0AL0Ag0BF0BG0BH0B`0Ba0Bb0Bg0C80CG0CL0CM0CN0CY0CZ0C[0C\0D30D70D80D`0EL0Ed0Ee0F<0F@0FK0FL0FP0F[0F_0F`0GL0GW0G^0Gl0HD0HE0HF0H^0IB0If0J70JN0JR0JS0JT0JU0JV0JW0JX0K70KB0Kc0LD0LY0LZ0M10M20M30M:0MY0N<0N=0NN0N^0PC0PD0PE0Q20Ql0Ro0T?0UX0W>0Xm0YS0ZE0[=0\A0]K0^a0`=0`>0`?0`@0`A0`B0`C0`D0`E0`F0`G0`H0`I0`J0`g0aD0aa0ab0ac0ad0ae0af0ag0ah0ai0aj0ak0al0am0an0ao0b00b10b20b30b40b50b60b70b80b90b:0b;0b<0b=0b>0b?0b@0bA0bB0bC0bD0bE0bF0bG0bH0bI0bJ0bK0bL0bM0bN0bO0bP0bQ0bR0bS0bT0bU0bV0bW0bX0bY0bZ0b[0b\0b]0b^0b_0b`0ba0bb0bc0bd0be0bf0bg0bh0bi0bj0bk0bl0bm0bn0bo0c00c10c20c30c40c50c60c70c80c90c:0c;0c<0c=0c>0c?0c@0cA0cB0cC0cD0cE0cF0cG0cH0cI0cJ0cK0cL0eI0f80gS0iD0jI0k80lS0nD0oI0oJ10F11n13@14F15^16R17X18g1:C1;h1=Z1?U1@N1AT1Bl1C`1DL1EJ1F?1Ga1I:1JJ1KQ1LG1Ma1Ni1Pf1Ql1SD1T81Uh1We1X^1Yd1[31\O1^41_f1aa1bg1d?1e31eb1g=1hn1j31kJ1lO1mB1n>1of21822123724F25b27G2992;42<02=X2>j2@g2Ac2CK2D]2EL2Fg2HX2I]2JI2KG2L<2M^2O72PG2QN2S32TF2UG2V62Vo2X52YD2Z`2\E2^72`22`\2aX2c82dF2f62h72i32j[2km2m]2nc30;30o31^33934j35o37l3923:A3;]3=B3?43@o3Ah3Ai3Aj3CZ3EJ3GG3GH3GI3IC3K=3Lf3NO3PW3RN3TE3TF3TG3VDS2SPS2SPS2SPFFFS2v13BUF2J1S2v12v22v32J12J22J3S2v12J1S2v12v22v33BUF2J12J22J3S3BUF1nS2SP2lo2bs5LOIMG3SPLS2v12SP2lo5LOIMG3SPL2J13bsAS2v12v22v32SP2lo5LOIMG3SPL2J12J22J33bsES2v12v22v32SP2lo5LOIMG3SPL2J12J22J33bsCFS2SPS2SPS2v12v22v33BUF1n2Hn2J13J1b2J23J2b2J3S2SPS2SP2loS2bsS2v12J13J1a3bsAS2v12J13J1aFS2v12v22v32J13J1a2J22J3S2v12v22v32J13J1a2J22J3FS2v12v22v31n2Hn2J13J1a3J1b2J23J2a3J2b2J33J3a3J3b3bsF3LBFFS2v12v22v33BUF1n2J12J22J3FFS2v12v22v32J12J22J33bsCFS2v12v22v32SP2lo3SPL2J12J22J3S2v12SP2lo3SPL2J1S2v12SP2J1S2v12v22v32SP2J12J22J3SFFS2SP3BUF2bs3SPBS2v12SP3BUF3SPB2J13bsAS2v12v22v32SP3BUF3SPB2J12J22J33bsES2v12v22v32SP3BUF3SPB2J12J22J33bsCS2v13BUF1n2Hn2J13J1bSFS2v13BUF1n2J1FS2v12J13bsAS2v13BUF1n2BH2J1S2v12v22v33BUF1n2BH2J12J22J3S2bsS2bsS2bsS2v22bs3Hv2FS2SPFFFFS2SPS2v12v22v33BUF1n2Hn2J13J1b2J23J2b2J33J3bS2v12v22v32J13J1a2J23J2a2J3S2v12v22v32J13J1a2J23J2a2J3S2v12v22v32J13J1a2J23J2a2J33J3a3bsESS2SP2loFS2v12bs3Hv1FFS2v13BUF2J1FFFS2v12SP3BUF3SPB2J1S2v12v22v32SP3BUF3SPB2J12J22J3S2v12v22v32J13J1b2J23J2b2J33J3b3bsES2v12v22v32J13J1b2J23J2b2J33bsCS3BUF1n2bs2HnFSS2SP2loFS2v12v22v32J12J22J3S2v12J1S2v12J13J1a3bsAS2v12J13bsAS2v12v22v32J13J1a2J23J2a2J3S2v12v22v32J13J1a2J23J2a2J33bsCFSS2v12v22v32J12J22J31i2HiSSS3BUFS2v12v23BUF2J12J2S2v12J13J1b3bsAS3BUFFFS2v32bs3Hv3SFFS2v12v22v32J12J22J33bsES2bsFS2v12v22v33BUF1n2Hn2J13J1b2J23J2b2J33bsCS2v12v22v33BUF1n2Hn2J13J1b2J23J2b2J33J3b3bsES2v13BUF1n2Hn2J13J1b3bsAFS2v12v22v33BUF2J12J22J3S2bsS2v32J33J3aSS2SPS2v12J13J1aS2SPSS2v12v22v31n2Hn2J13J1b2J23J2b2J33J3b3bsF3LBFS2v13BUF2J1S2SP2loS3BUF1n2bs3LENS2v12v22v32J12J22J31i2HiFFS2v13BUF1n2BH2J13bsA3LBAS2v12v22v33BUF1n2BH2J12J22J33bsC3LBCS2v12v22v33BUF1n2BH2J12J22J33bsE3LBES3BUF1n2bs3LEN2BHS2v12v22v32J12J22J33bsES2bsSFSFFFS2v12v22v32J13J1a2J23J2a2J33bsCS2v22J23J2aS2v12v22v33BUF1n2J12J22J33bsC3LBCS2v12v22v33BUF1n2J12J22J33bsE3LBES2v13BUF1n2J13bsA3LBAFS2v12v22v32J12J22J33bsCFSS2v12J1S2v12v22v32J13J1a2J23J2a2J33J3aS2v12v22v32J13J1a2J23J2a2J33J3a3bsEFS2v12v23BUF2J12J2S2SP2lo3SPL1x2HxS2v12v22v32bs2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenFFS2v12v22v32SP2lo2bs3SPL2J12J22J33bs14LEN11x1CS2v12v22v32SP2lo2bs2J12J22J33bs14LEN13bsA4LENA1x1C3SPL3J1aS2v12v22v32SP2lo2bs3SPL2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENB1x1CS2v12v22v32SP2lo2bs2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC1x1C3SPL3J1a3J2aS2v12v22v32SP2lo2bs3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND1x1CS2v12v22v32SP2lo2bs2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE1x1C3SPL3J1a3J2a3J3aS2v12v22v32SP2lo2bs3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF1x1CS2v12v22v32SP2bs2J12J22J33bs14LEN11x1CS2v12v22v32SP2lo2bs2J12J22J33bs14LEN13bsA4LENA1x1CS2v12v22v32SP2bs2J12J22J33bs14LEN13bsA4LENA3bsB4LENB1x1CS2v12v22v32SP2lo2bs2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC1x1CS2v12v22v32SP2bs2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND1x1CS2v12v22v32SP2lo2bs2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE1x1CS2v12v22v32SP2bs2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF1x1CFFFFFFFFFFFFFS2v12v22v32SP2lo3SPL2J12J22J3S2v12v22v32SP2lo3SPL2J12J22J3S2v12v22v32SP2lo3SPL2J12J22J3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2v12v22v32SP2lo3BUF2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo2bs5LOIMG3SPL2J12J22J33bs14LEN1S2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo2bs5LOIMG3SPL2J12J22J33bs14LEN1S2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBFS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J12J22J33bs14LEN1S2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN1S2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP3BUF2bs3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo3BUF2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J12J22J33bs14LEN1S2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J12J22J33bs14LEN1S2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J12J22J33bs14LEN1S2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2bs5LOIMG3SPL2J12J22J33bs14LEN1S2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN1S2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo3BUF1n2bs3SPB2J12J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo3BUF1n2bs3SPB2J12J22J33bs14LEN1S2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J12J22J33bs14LEN1S2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2VA2bs4SPVA2J12J22J33bs14LEN1S2v12v22v32SP2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2VA2bs4SPVA2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP3BUF2bs3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v33BUF1n2VA2bs2Hn3VAB2J13J1a3J1b2J23J2a3J2b2J33J3a3J3b3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP3BUF2bs3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo2bs5LOIMG2J12J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo2bs5LOIMG3SPL2J12J22J33bs14LEN1S2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo2bs5LOIMG3SPL2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo3BUF2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENAS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J22J33bs14LEN13bsA4LENA3bsB4LENBS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENCS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LENDS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENES2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENFS2v12v22v32SP2lo3BUF1n2bs5LOIMG3SPL3SPB2J12J22J33bs14LEN1FFS2v12v22v32SP3BUF2bs3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP3BUF2bs3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo3BUF2bs5LOIMG3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenFFS2v12v22v33BUF1n2bs2Hn2J13J1a3J1b2J23J2a3J2b2J33J3a3J3b3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v33BUF1n2bs2Hn2J13J1a3J1b2J23J2a3J2b2J33J3a3J3b3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v33BUF2bs2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v33BUF2bs2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo3BUF1n2bs2Hn3SPL3SPB2J13J1a3J1b2J23J2a3J2b2J33J3a3J3b3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo3BUF2bs3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenS2v12v22v32SP2lo3BUF2bs3SPL3SPB2J13J1a2J23J2a2J33J3a3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3lenFFS2v12v22v33BUF1n2bs2Hn2BH2J13J1a3J1b2J23J2a3J2b2J33J3a3J3b3bs14LEN13bsA4LENA3bsB4LENB3bsC4LENC3bsD4LEND3bsE4LENE3bsF4LENF3len". (* [comment removed for export] *)
  Theorem vsn_f2_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn2 ()) "Pv1,$2.Pv2,$2.Pv3,$2.PSP,$2.Plo,$2.PBUF,$2.Pn,$2.PVA,$2.Pbs,(0.(1.&8.))Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(4.(1.&8.))P,(20.(=.=R26.)(16.R26.(17.+2.+40.)))P,(20.(=.=R26.)(16.R26.(17.+2.+40.)))P,(20.(=.=R26.)(16.R26.(17.+2.+40.)))P,(20.(=.+78.R23.)(16.R23.(17.+2.+1?.)))P,(21.$2.(?.(10.(1.&8.)R22.))R24.)P,(2:.$6.R6.R27.R28.)P,(=.+65?000.R28.)P,(=.R29.(2;.R2:.+1=0.))P,(14.VCS,R2:.(2;.R2;.R2:.))P,(=.R2<.R2:.)P,(15.$6.R;.R2;.R28.)P,(14.VCS,R2<.R2;.)P,(16.(>.R2=.R2<.)(17.+2.+3?.))P,(11.$6.R>.R2<.(8.$12.(13.(9.&40.R33.))(8.$12.(13.(9.&40.R32.))(8.$12.(13.(9.&40.R31.))(:.$12.)))))P,(14.VCS,R2=.+18.)P,(=.R32.R2>.)P,(2<.(=.(>.R2?.+18.)R31.)(=.(>.R31.R30.)R2?.))P,(16.(>.R30.+18.)(17.+2.+3?.))P,(1<.$6.R13.)(1=.$6.VAL,VCS,Lms',$1>.(1?.(1.&40.)La1',(1.&40.)(1?.(1.&40.)La2',(1.&40.)(1?.(1.&40.)La3',(1.&40.)(1?.(1.&40.)La4',(1.&40.)(1?.(1.&40.)La5',(1.&40.)(1?.(1.&40.)La6',(1.&40.)(1?.(1.&40.)La7',(1.&40.)(1?.(1.&40.)Lt0',(1.&40.)(1?.(1.&40.)Lt1',(1.&40.)(1?.(1.&40.)Lt2',(1.&40.)(1?.(1.&40.)Lt3',(1.&40.)(1?.(1.&40.)Lt4',(1.&40.)(1?.(0.(1.&8.))Lbs',(0.(1.&8.))(1?.P,(1.&40.)(4.(1.&8.))Lm',P,(1.&40.)(4.(1.&8.))Zlen,$2.(>.(>.(>.+38.(32.+:.#14.R48.))(32.+:.#14.R47.))(32.+:.#14.R46.))(20.(21.$1>.R10.(22.(23.R40.(9.&40.R46.)R3?.R3>.R8.R7.R6.R3:.R39.(9.&40.R1.)R?.R>.R=.R<.R;.R:.R9.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R5.R4.R28.R27.)R26.(2=.R40.)R25.(24.(1.&40.))R2.(25.$6.)))(20.(2:.$6.R2.R45.R46.)(20.(15.$6.R2.R44.R3.)(20.(21.$26.(10.(1.&8.)R3.)(10.(1.&8.)R41.))(20.(28.R3.=R1.)(20.(21.(4.(1.&8.))(2>.(1.&8.)R3.(2?.R1.))(30.(1.&8.)(9.&8.=)))(20.(11.$6.R2.R42.(8.$12.(13.(9.&40.R49.))(8.$12.(13.(9.&40.R48.))(8.$12.(13.(9.&40.R47.))(:.$12.)))))(20.(18.(8.(19.$2.$2.)(1:.$2.$2.R45.R46.)(8.(19.$2.$2.)(1:.$2.$2.R44.(>.R44.R43.))(:.(19.$2.$2.))))R24.R2.)(20.(1;.$6.R24.R2.)(1<.$6.R2.))))))))))))))))))))))))(22.(23.R30.(9.&40.R36.)R2?.R2>.R2=.R2<.R2;.R2:.R29.(9.&40.R34.)(9.&40.R33.)(9.&40.+23?;2.)(9.&40.R32.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(9.&40.+7=810.)R15.(24.(1.&40.))R14.(25.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros Hv1 Hv2 Hv3 Hn LEN ST LOIMG SPL SCS SPB OUT CRB BH VAC CRV SPVA VAB VAH MI. al_facts.
    pose proof (munch_refl [(lo, SP); (BUF, BUF + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ndig_ge1 10 20 v1) as J1a. pose proof (ndig_le 10 20 v1 ltac:(lia) ltac:(lia)) as J1b. change (Z.max 1 (Z.of_nat 20)) with 20 in J1b.
    pose proof (ndig_ge1 10 20 v2) as J2a. pose proof (ndig_le 10 20 v2 ltac:(lia) ltac:(lia)) as J2b. change (Z.max 1 (Z.of_nat 20)) with 20 in J2b.
    pose proof (ndig_ge1 10 20 v3) as J3a. pose proof (ndig_le 10 20 v3 ltac:(lia) ltac:(lia)) as J3b. change (Z.max 1 (Z.of_nat 20)) with 20 in J3b.
    set (J1 := ndig 10 20 v1) in *. set (J2 := ndig 10 20 v2) in *. set (J3 := ndig 10 20 v3) in *.
    destruct OUT as [OUTb OUTw].
    (* [comment removed for export] *)
    assert (D1C : ro_cells asegs m 147404 [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 122); C1 (Z_to_bv 8 117)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (D2C : ro_cells asegs m 147426 [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 122); C1 (Z_to_bv 8 117)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (D3C : ro_cells asegs m 147431 [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 122); C1 (Z_to_bv 8 117)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (NULC : ro_cells asegs m 147443 [C1 (Z_to_bv 8 0)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (JTC : ro_cells asegs m 150196 [C4 (Z_to_bv 64 364452)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (CRC : crange CS (SP + -128 + 16) 8) by (intros x Hx; apply SCS; clear -Hx SPL; lia).
    (* [comment removed for export] *)
    lx_run (PLAN [0x7d8a0] [] 60%N).
    (* [comment removed for export] *)
    first [ lazymatch goal with CCl : rw_cells _ _ (SP + -112) (_ :: _) |- _ => rename CCl into CCH end
          | lazymatch goal with FRl : rw_cells _ _ (SP + -128) (_ :: _ :: _ :: _) |- _ =>
              chunk_split FRl 2%nat FRa FRr; chunk_split FRr 1%nat CCH FRb; replace (SP + -128 + 16 + 8) with (SP + -104) in FRb by (clear; lia);
              replace (SP + -128 + 16) with (SP + -112) in CCH by (clear; lia) end ].
    replace (SP + -112) with (SP + -128 + 16) in CCH by (clear; lia).
    replace (Z_to_bv 64 BUF) with (Z_to_bv 64 (BUF + 0)) in CCH by (f_equal; clear; lia).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bs, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw WMl) : u8arr asegs mx BUF bs) as OUT0; clear BYl; try clear LXlen end.
    replace (BUF + (n + -1)) with (BUF + n + -1) by (clear; lia).
    assert (ROF : ro_bytes asegs 147378 (fmt_oom2_l1 ++ [Z_to_bv 8 37])) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
    eapply (evtA_cut asegs AL CS).
    { eapply (vsn_litloop AL IMG ALWF CS CSOK fmt_oom2_l1 (Z_to_bv 8 37) 147378 0 (SP + -128) BUF 0 (BUF + n + -1) bs);
        first [ exact ROF | exact CCH | exact CRC | exact OUT0 | apply munch_refl | apply wmono_refl | assumption
              | apply litok_all; vm_compute; reflexivity
              | rewrite LEN; exact CRB
              | cbn [length fmt_oom2_l1 map]; clear -Hn LEN SPL SPB LOIMG BH; lia ]. }
    cbn beta. intros ms' (a0l & a1l & bs1 & m2 & -> & CCH1 & OUT1 & LEN1 & PE1 & PR1 & MUc & WMc & MI1).
    rewrite LEN in MUc. clear CCH OUT0 ROF.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx m2 MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    change (Z.of_nat (length fmt_oom2_l1)) with 26 in *. change (0 + 26) with 26 in *. change (147378 + 26) with 147404.
    replace (SP + -128 + 16) with (SP + -112) in CCH1 by (clear; lia). replace (BUF + 0 + 26) with (BUF + 26) in CCH1 by (clear; lia).
    assert (LB1 : Z.of_nat (length bs1) = n) by (rewrite LEN1; exact LEN).
    pose proof PR1 as PRALL1. clear PR1 PE1.
    destruct OUT1 as [OUT1b OUT1w].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7e118] [] 80%N). try clear LXSAME. lx_clear_mem m2.
    (* [comment removed for export] *)
    assert (OUTw1 : wr_at asegs m BUF (Z.of_nat (length bs1))) by (rewrite LB1, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bs1, WMl : wmono _ m ?mx', STl : stk _ _ lo (SP + -128), CCl : rw_cells _ _ (SP + -112) _ |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw1 WMl) : u8arr asegs mx BUF bs1) as OUT2; clear BYl OUTw1; try clear LXlen;
      replace (BUF + (n + -1)) with (BUF + n + -1) by (clear; lia);
      assert (LL1 : Z.max J1 0 = J1) by (clear -J1a; lia);
      eapply (evtA_cut asegs AL CS);
      [ eapply (apn_spec AL IMG ALWF CS CSOK v1 10 0 0 0 (SP + -128) lo (SP + -112) BUF 26 (BUF + n + -1) bs1);
          first [ exact STl | exact CCl | exact OUT2 | exact CRC | assumption
                | rewrite LB1; exact CRB
                | left; reflexivity
                | fold J1; rewrite ?LL1, ?LB1; clear -Hv1 Hn SPL SPB LOIMG BH J1a J1b; lia
                | intros x Hx; apply SCS; clear -Hx SPL; lia ]
      | ] end.
    cbn beta. intros ms' (a1A & a2A & a3A & a4A & a5A & a6A & a7A & bsA & mA & -> & STA & CCHA & OUTA & LENA & PEA & PRA & MUc & WMc & MIA).
    fold J1. fold J1 in CCHA, PRA, MUc. rewrite LL1 in *. rewrite LB1 in MUc. clear OUT2.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx mA MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    ret_lit.
    assert (LBA : Z.of_nat (length bsA) = n) by (rewrite LENA; exact LB1).
    pose proof (pr_range_extend _ _ _ _ PRALL1 PEA PRA ltac:(clear; lia)) as PRALLA. clear PRALL1 PEA PRA.
    destruct OUTA as [OUTAb OUTAw].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7d8a0] [] 20%N). try clear LXSAME. lx_clear_mem mA.
    (* [comment removed for export] *)
    first [ lazymatch goal with CCl : rw_cells _ _ (SP + -112) (_ :: _) |- _ => rename CCl into CCH end
          | lazymatch goal with FRl : rw_cells _ _ (SP + -128) (_ :: _ :: _ :: _) |- _ =>
              chunk_split FRl 2%nat FRa2 FRr; chunk_split FRr 1%nat CCH FRb2; replace (SP + -128 + 16 + 8) with (SP + -104) in FRb2 by (clear; lia);
              replace (SP + -128 + 16) with (SP + -112) in CCH by (clear; lia) end ].
    replace (SP + -112) with (SP + -128 + 16) in CCH by (clear; lia).
    lazymatch type of CCH with rw_cells _ _ _ [C8 (Z_to_bv 64 ?e)] => replace e with (BUF + (26 + J1)) in CCH by (clear; lia) end.
    assert (OUTwA : wr_at asegs m BUF (Z.of_nat (length bsA))) by (rewrite LBA, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bsA, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTwA WMl) : u8arr asegs mx BUF bsA) as OUT3; clear BYl OUTwA; try clear LXlen end.
    assert (ROF : ro_bytes asegs 147407 (fmt_oom2_l2 ++ [Z_to_bv 8 37])) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
    eapply (evtA_cut asegs AL CS).
    { eapply (vsn_litloop AL IMG ALWF CS CSOK fmt_oom2_l2 (Z_to_bv 8 37) 147407 (J1 + 26) (SP + -128) BUF (26 + J1) (BUF + (n + -1)) bsA);
        first [ exact ROF | exact CCH | exact CRC | exact OUT3 | apply munch_refl | apply wmono_refl | assumption
              | apply litok_all; vm_compute; reflexivity
              | rewrite LBA; exact CRB
              | cbn [length fmt_oom2_l2 map]; clear -Hn LBA SPL SPB LOIMG BH J1a J1b; lia ]. }
    cbn beta. intros ms' (a0B & a1B & bsB & mB & -> & CCHB & OUTB & LENB & PEB & PRB & MUc & WMc & MIB).
    rewrite LBA in MUc. clear CCH OUT3 ROF.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx mB MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    change (Z.of_nat (length fmt_oom2_l2)) with 19 in *. change (147407 + 19) with 147426.
    replace (SP + -128 + 16) with (SP + -112) in CCHB by (clear; lia). replace (BUF + (26 + J1) + 19) with (BUF + (J1 + 45)) in CCHB by (clear; lia).
    assert (LBB : Z.of_nat (length bsB) = n) by (rewrite LENB; exact LBA).
    pose proof (pr_range_extend _ _ _ _ PRALLA PEB PRB ltac:(clear -J1a; lia)) as PRALLB. clear PRALLA PEB PRB.
    destruct OUTB as [OUTBb OUTBw].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7e118] [] 80%N). try clear LXSAME. lx_clear_mem mB.
    (* [comment removed for export] *)
    assert (OUTwC : wr_at asegs m BUF (Z.of_nat (length bsB))) by (rewrite LBB, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bsB, WMl : wmono _ m ?mx', STl : stk _ _ lo (SP + -128), CCl : rw_cells _ _ (SP + -112) [C8 (Z_to_bv 64 ?ce)] |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTwC WMl) : u8arr asegs mx BUF bsB) as OUTuC; clear BYl OUTwC; try clear LXlen;
      replace ce with (BUF + (26 + J1 + 19)) in CCl by (clear; lia);
      assert (LL2 : Z.max J2 0 = J2) by (clear -J2a; lia);
      eapply (evtA_cut asegs AL CS);
      [ eapply (apn_spec AL IMG ALWF CS CSOK v2 10 0 0 0 (SP + -128) lo (SP + -112) BUF (26 + J1 + 19) (BUF + (n + -1)) bsB);
          first [ exact STl | exact CCl | exact OUTuC | exact CRC | assumption
                | rewrite LBB; exact CRB
                | left; reflexivity
                | fold J2; rewrite ?LL2, ?LBB; clear -Hv2 Hn SPL SPB LOIMG BH J1a J1b J2a J2b J3a J3b; lia
                | intros x Hx; apply SCS; clear -Hx SPL; lia ]
      | ] end.
    cbn beta. intros ms' (a1C & a2C & a3C & a4C & a5C & a6C & a7C & bsC & mC & -> & STC & CCHC & OUTC & LENC & PEC & PRC & MUc & WMc & MIC).
    fold J2. fold J2 in CCHC, PRC, MUc. rewrite LL2 in *. rewrite LBB in MUc. clear OUTuC.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx mC MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    ret_lit.
    assert (LBC : Z.of_nat (length bsC) = n) by (rewrite LENC; exact LBB).
    pose proof (pr_range_extend _ _ _ _ PRALLB PEC PRC ltac:(clear -J1a J2a J3a; lia)) as PRALLC. clear PRALLB PEC PRC.
    destruct OUTC as [OUTCb OUTCw].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7d8a0] [] 20%N). try clear LXSAME. lx_clear_mem mC.
    (* [comment removed for export] *)
    first [ lazymatch goal with CCl : rw_cells _ _ (SP + -112) (_ :: _) |- _ => rename CCl into CCH end
          | lazymatch goal with FRl : rw_cells _ _ (SP + -128) (_ :: _ :: _ :: _) |- _ =>
              chunk_split FRl 2%nat FRaD FRr; chunk_split FRr 1%nat CCH FRbD; replace (SP + -128 + 16 + 8) with (SP + -104) in FRbD by (clear; lia);
              replace (SP + -128 + 16) with (SP + -112) in CCH by (clear; lia) end ].
    replace (SP + -112) with (SP + -128 + 16) in CCH by (clear; lia).
    lazymatch type of CCH with rw_cells _ _ _ [C8 (Z_to_bv 64 ?e)] => replace e with (BUF + (26 + J1 + 19 + J2)) in CCH by (clear; lia) end.
    assert (OUTwD : wr_at asegs m BUF (Z.of_nat (length bsC))) by (rewrite LBC, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bsC, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTwD WMl) : u8arr asegs mx BUF bsC) as OUTuD; clear BYl OUTwD; try clear LXlen end.
    assert (ROF : ro_bytes asegs 147429 (fmt_oom2_l3 ++ [Z_to_bv 8 37])) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
    lazymatch goal with |- evtA _ _ _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?cnt) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply (evtA_cut asegs AL CS);
      [ eapply (vsn_litloop AL IMG ALWF CS CSOK fmt_oom2_l3 (Z_to_bv 8 37) 147429 cnt (SP + -128) BUF (26 + J1 + 19 + J2) (BUF + (n + -1)) bsC);
          first [ exact ROF | exact CCH | exact CRC | exact OUTuD | apply munch_refl | apply wmono_refl | assumption
                | apply litok_all; vm_compute; reflexivity
                | rewrite LBC; exact CRB
                | cbn [length fmt_oom2_l3 map]; clear -Hn LBC SPL SPB LOIMG BH J1a J1b J2a J2b J3a J3b; lia ]
      | ] end.
    cbn beta. intros ms' (a0D & a1D & bsD & mD & -> & CCHD & OUTD & LEND & PED & PRD & MUc & WMc & MID).
    rewrite LBC in MUc. clear CCH OUTuD ROF.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx mD MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    change (Z.of_nat (length fmt_oom2_l3)) with 2 in *. change (147429 + 2) with 147431 in *.
    replace (SP + -128 + 16) with (SP + -112) in CCHD by (clear; lia).
    assert (LBD : Z.of_nat (length bsD) = n) by (rewrite LEND; exact LBC).
    pose proof (pr_range_extend _ _ _ _ PRALLC PED PRD ltac:(clear -J1a J2a J3a; lia)) as PRALLD. clear PRALLC PED PRD.
    destruct OUTD as [OUTDb OUTDw].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7e118] [] 80%N). try clear LXSAME. lx_clear_mem mD.
    (* [comment removed for export] *)
    assert (OUTwE : wr_at asegs m BUF (Z.of_nat (length bsD))) by (rewrite LBD, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bsD, WMl : wmono _ m ?mx', STl : stk _ _ lo (SP + -128), CCl : rw_cells _ _ (SP + -112) [C8 (Z_to_bv 64 ?ce)] |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTwE WMl) : u8arr asegs mx BUF bsD) as OUTuE; clear BYl OUTwE; try clear LXlen;
      replace ce with (BUF + (26 + J1 + 19 + J2 + 2)) in CCl by (clear; lia);
      assert (LL3 : Z.max J3 0 = J3) by (clear -J3a; lia);
      eapply (evtA_cut asegs AL CS);
      [ eapply (apn_spec AL IMG ALWF CS CSOK v3 10 0 0 0 (SP + -128) lo (SP + -112) BUF (26 + J1 + 19 + J2 + 2) (BUF + (n + -1)) bsD);
          first [ exact STl | exact CCl | exact OUTuE | exact CRC | assumption
                | rewrite LBD; exact CRB
                | left; reflexivity
                | fold J3; rewrite ?LL3, ?LBD; clear -Hv3 Hn SPL SPB LOIMG BH J1a J1b J2a J2b J3a J3b; lia
                | intros x Hx; apply SCS; clear -Hx SPL; lia ]
      | ] end.
    cbn beta. intros ms' (a1E & a2E & a3E & a4E & a5E & a6E & a7E & bsE & mE & -> & STE & CCHE & OUTE & LENE & PEE & PRE & MUc & WMc & MIE).
    fold J3. fold J3 in CCHE, PRE, MUc. rewrite LL3 in *. rewrite LBD in MUc. clear OUTuE.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx mE MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    ret_lit.
    assert (LBE : Z.of_nat (length bsE) = n) by (rewrite LENE; exact LBD).
    pose proof (pr_range_extend _ _ _ _ PRALLD PEE PRE ltac:(clear -J1a J2a J3a; lia)) as PRALLE. clear PRALLD PEE PRE.
    destruct OUTE as [OUTEb OUTEw].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7d8a0] [] 20%N). try clear LXSAME. lx_clear_mem mE.
    (* [comment removed for export] *)
    first [ lazymatch goal with CCl : rw_cells _ _ (SP + -112) (_ :: _) |- _ => rename CCl into CCH end
          | lazymatch goal with FRl : rw_cells _ _ (SP + -128) (_ :: _ :: _ :: _) |- _ =>
              chunk_split FRl 2%nat FRaF FRr; chunk_split FRr 1%nat CCH FRbF; replace (SP + -128 + 16 + 8) with (SP + -104) in FRbF by (clear; lia);
              replace (SP + -128 + 16) with (SP + -112) in CCH by (clear; lia) end ].
    replace (SP + -112) with (SP + -128 + 16) in CCH by (clear; lia).
    lazymatch type of CCH with rw_cells _ _ _ [C8 (Z_to_bv 64 ?e)] => replace e with (BUF + (26 + J1 + 19 + J2 + 2 + J3)) in CCH by (clear; lia) end.
    assert (OUTwF : wr_at asegs m BUF (Z.of_nat (length bsE))) by (rewrite LBE, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bsE, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTwF WMl) : u8arr asegs mx BUF bsE) as OUTuF; clear BYl OUTwF; try clear LXlen end.
    assert (ROF : ro_bytes asegs 147434 (fmt_oom2_l4 ++ [Z_to_bv 8 0])) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
    lazymatch goal with |- evtA _ _ _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?cnt) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply (evtA_cut asegs AL CS);
      [ eapply (vsn_litloop AL IMG ALWF CS CSOK fmt_oom2_l4 (Z_to_bv 8 0) 147434 cnt (SP + -128) BUF (26 + J1 + 19 + J2 + 2 + J3) (BUF + (n + -1)) bsE);
          first [ exact ROF | exact CCH | exact CRC | exact OUTuF | apply munch_refl | apply wmono_refl | assumption
                | apply litok_all; vm_compute; reflexivity
                | rewrite LBE; exact CRB
                | cbn [length fmt_oom2_l4 map]; clear -Hn LBE SPL SPB LOIMG BH J1a J1b J2a J2b J3a J3b; lia ]
      | ] end.
    cbn beta. intros ms' (a0F & a1F & bsF & mF & -> & CCHF & OUTF & LENF & PEF & PRF & MUc & WMc & MIF).
    rewrite LBE in MUc. clear CCH OUTuF ROF.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx mF MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    change (Z.of_nat (length fmt_oom2_l4)) with 9 in *. change (147434 + 9) with 147443 in *.
    replace (SP + -128 + 16) with (SP + -112) in CCHF by (clear; lia).
    assert (LBF : Z.of_nat (length bsF) = n) by (rewrite LENF; exact LBE).
    pose proof (pr_range_extend _ _ _ _ PRALLE PEF PRF ltac:(clear -J1a J2a J3a; lia)) as PRALLF. clear PRALLE PEF PRF.
    destruct OUTF as [OUTFb OUTFw].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7dc60] [] 30%N). try clear LXSAME. lx_clear_mem mF.
    (* [comment removed for export] *)
    set (len := 56 + J1 + J2 + J3) in *.
    assert (OUTwF : wr_at asegs m BUF (Z.of_nat (length bsF))) by (rewrite LBF, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bsF, WMl : wmono _ m ?mx'
      |- evtA _ _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTwF WMl) : u8arr asegs mx BUF bsF) as OUTG0; clear BYl OUTwF; try clear LXlen;
      pose proof (u8arr_store_ok asegs mx BUF bsF len av OUTG0 ltac:(clear -LBF Hn J1a J1b J2a J2b J3a J3b; subst len; lia) ltac:(subst len; f_equal; clear; lia)) as SOK end.
    zstep. rewrite (le1_lit 0) by (clear; lia).
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u8arr_write asegs mx BUF bsF len (Z_to_bv 8 0) OUTG0 ltac:(clear -LBF Hn J1a J1b J2a J2b J3a J3b; subst len; lia)) as OUTG end.
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace (BUF + len) with E in OUTG by (subst len; clear; lia) end.
    store_done. try clear SOK.
    destruct OUTG as [OUTGb OUTGw].
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 30%N).
    assert (OUTwG : wr_at asegs m BUF (Z.of_nat (length (upd bsF (Z.to_nat len) (Z_to_bv 8 0))))) by (rewrite upd_length, LBF, <- LEN; exact OUTw).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, BYl : bytes_at _ _ BUF _ |- _ =>
      apply evtA_done; lx_exs; cbn zeta; lx_ands;
      [ first [lx_mseq | repeat f_equal; subst len; clear -J1a; lia]
      | assumption
      | exact (conj BYl (wr_at_transport _ _ _ _ _ OUTwG WMl))
      | rewrite upd_length; apply Nat2Z.inj; rewrite LBF, LEN; reflexivity
      | intros i Hi; rewrite nth_error_upd_other by (clear -Hi; subst len; lia); apply PRALLF; subst len; clear -Hi J1a J2a J3a; lia
      | subst len; apply nth_error_upd_same; clear -LBF Hn J1b J2b J3b J1a J2a J3a; lia
      | assumption | exact MUl | exact WMl | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
