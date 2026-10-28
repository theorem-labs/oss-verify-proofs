(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_code_43000_43c04.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_startup_memset () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "RocqVerifyHarness.AgentSubmission.BB.ZStores.zeros"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.regs_agree"; "Stdlib.Lists.List.In"; "memset_clob"].


Definition memset304_ws : list (Z * nat) := ltac2:(CDefT.buildp (gd_tbl_P_startup_memset ()) "(0.(1.$2.$3.)(4.$2.$3.=#1.)(0.(1.$2.$3.)(4.$2.$3.+12?.#1.)(0.(1.$2.$3.)(4.$2.$3.+1.#1.)(0.(1.$2.$3.)(4.$2.$3.+2.#1.)(0.(1.$2.$3.)(4.$2.$3.+12=.#1.)(0.(1.$2.$3.)(4.$2.$3.+12>.#1.)(0.(1.$2.$3.)(4.$2.$3.+3.#1.)(0.(1.$2.$3.)(4.$2.$3.+12<.#1.)(0.(1.$2.$3.)(4.$2.$3.=#4.)(0.(1.$2.$3.)(4.$2.$3.+12<.#4.)(0.(1.$2.$3.)(4.$2.$3.+4.#4.)(0.(1.$2.$3.)(4.$2.$3.+8.#4.)(0.(1.$2.$3.)(4.$2.$3.+124.#4.)(0.(1.$2.$3.)(4.$2.$3.+128.#4.)(0.(1.$2.$3.)(4.$2.$3.+<.#4.)(0.(1.$2.$3.)(4.$2.$3.+10.#4.)(0.(1.$2.$3.)(4.$2.$3.+14.#4.)(0.(1.$2.$3.)(4.$2.$3.+18.#4.)(0.(1.$2.$3.)(4.$2.$3.+114.#4.)(0.(1.$2.$3.)(4.$2.$3.+118.#4.)(0.(1.$2.$3.)(4.$2.$3.+11<.#4.)(0.(1.$2.$3.)(4.$2.$3.+120.#4.)(0.(1.$2.$3.)(4.$2.$3.+18.#8.)(0.(1.$2.$3.)(4.$2.$3.+20.#8.)(0.(1.$2.$3.)(4.$2.$3.+28.#8.)(0.(1.$2.$3.)(4.$2.$3.+30.#8.)(0.(1.$2.$3.)(4.$2.$3.+38.#8.)(0.(1.$2.$3.)(4.$2.$3.+40.#8.)(0.(1.$2.$3.)(4.$2.$3.+48.#8.)(0.(1.$2.$3.)(4.$2.$3.+50.#8.)(0.(1.$2.$3.)(4.$2.$3.+58.#8.)(0.(1.$2.$3.)(4.$2.$3.+60.#8.)(0.(1.$2.$3.)(4.$2.$3.+68.#8.)(0.(1.$2.$3.)(4.$2.$3.+70.#8.)(0.(1.$2.$3.)(4.$2.$3.+78.#8.)(0.(1.$2.$3.)(4.$2.$3.+80.#8.)(0.(1.$2.$3.)(4.$2.$3.+88.#8.)(0.(1.$2.$3.)(4.$2.$3.+90.#8.)(0.(1.$2.$3.)(4.$2.$3.+98.#8.)(0.(1.$2.$3.)(4.$2.$3.+:0.#8.)(0.(1.$2.$3.)(4.$2.$3.+:8.#8.)(0.(1.$2.$3.)(4.$2.$3.+;0.#8.)(0.(1.$2.$3.)(4.$2.$3.+;8.#8.)(0.(1.$2.$3.)(4.$2.$3.+<0.#8.)(0.(1.$2.$3.)(4.$2.$3.+<8.#8.)(0.(1.$2.$3.)(4.$2.$3.+=0.#8.)(0.(1.$2.$3.)(4.$2.$3.+=8.#8.)(0.(1.$2.$3.)(4.$2.$3.+>0.#8.)(0.(1.$2.$3.)(4.$2.$3.+>8.#8.)(0.(1.$2.$3.)(4.$2.$3.+?0.#8.)(0.(1.$2.$3.)(4.$2.$3.+?8.#8.)(0.(1.$2.$3.)(4.$2.$3.+100.#8.)(0.(1.$2.$3.)(4.$2.$3.+108.#8.)(0.(1.$2.$3.)(4.$2.$3.+110.#8.)(5.(1.$2.$3.))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0440?L10575806009.15L1066734905.15 L10677521981.15L10683014269.15L10880343814.15L1099967052.15 L11037362043.15L11109804411.15L12317554279.15L12348959436.15L1297244539.15 L1301383911.15 L13318826941.15L13321282023.15L13371573126.15L1351707782.15 L13638513350.15L13715332684.15L14035657292.15L14394211590.15L14663325051.15L15032543238.15L15847904359.15L15912172871.15L16441816908.15L16478659963.15L16590489341.15L16883081606.15L17945029309.15L18109615308.15L18338617575.15L19224204349.15L19357053543.15L19407344646.15L19556146493.15L19657475910.15L19859674599.15L20326840699.15L20413173638.15L20623331901.15L21193365580.15L21496917068.15L21848286951.15L2200249751.15 L22195845004.15L22555807180.15L22876131788.15L22904173062.15L2336556550.15 L23518339963.15L24374914407.15L24462297913.15L2478969401.15 L25376539879.15L25587676876.15L25679096262.15L25776126331.15L25861891687.15L25985125388.15L26648663628.15L26820787645.15L27028206459.15L27867253607.15L28276543997.15L28940174470.15L2920836153.15 L297653095.15  L30033868748.15L30337653708.15L30554555259.15L31025585209.15L31146041223.15L31327509883.15L31380859239.15L31431150342.15L31681575494.15L31879284967.15L32935429126.15L33355041213.15L33433596665.15L3356231613.15 L33717681853.15L33903549927.15L34263347053.15L34345976699.15L34432607308.15L34835336071.15L34932572039.15L34957601030.15L3508485964.15 L35333882813.15L35490973132.15L35804310226.15L36394254439.15L37182063697.15L37400116199.15L37450669446.15L3783493949.15 L37915057511.15L3807326567.15 L3812000588.15 L38523342540.15L38800139577.15L38878799180.15L38944211949.15L38971201158.15L39138786934.15L39182321996.15L39246613180.15L39386820278.15L39609170749.15L39634477959.15L39924641383.15L39974928390.15L40106570619.15L40206217083.15L40282372791.15L40959818630.15L41880756157.15L42217145533.15L42413773543.15L42924460438.15L42969534412.15L43172264150.15L43273081804.15L43434282087.15L43484605958.15L43504314635.15L43865472379.15L43936411623.15L44101629143.15L44630552349.15L44988627718.15L45566148987.15L45626580157.15L45742424955.15L45927117031.15L45977670278.15L46584087916.15L46944564091.15L46960118973.15L46979304454.15L47228936571.15L47368043596.15L47501005703.15L47719272652.15L47792057789.15L4791010749.15 L48064841612.15L48120168765.15L48145535869.15L48451643239.15L4861348486.15 L49033270139.15L4930636764.15 L49503596678.15L49554689853.15L49703403815.15L49757937531.15L49809968121.15L49955926119.15L50470871933.15L50991074694.15L51193010727.15L51285502331.15L51531700541.15L5173949644.15 L51814235468.15L51944506727.15L5199165245.15 L51994830598.15L52117487948.15L52175546557.15L52251757447.15L52332176957.15L5234848077.15 L52846245670.15L5294708781.15 L53000396422.15L53096638054.15L53379132795.15L53699270205.15L54471133671.15L54589455837.15L545948583.15  L54968657787.15L55018644347.15L55506306310.15L55907059660.15L56436147579.15L56760201158.15L57012166150.15L57071751643.15L57212005543.15L57721090493.15L57813519751.15L57980278759.15L58030573958.15L58081601213.15L58082497853.15L58312603709.15L58582239128.15L59036427014.15L59292264268.15L59596049228.15L59883442348.15L59989069452.15L60319333788.15L60471515751.15L6057807227.15 L60654446796.15L60857863229.15L60957998284.15L60978910075.15L6117332806.15 L61527398278.15L61640115724.15L61727499303.15L61854590073.15L62224989245.15L62302876925.15L62781550662.15L6298035687.15 L62998138599.15L63048458374.15L63245938983.15L63280218813.15L63624378941.15L6388793223.15 L63960507197.15L63999801447.15L64010100877.15L64050092550.15L64295985531.15L65053848966.15L65446206604.15L65949840763.15L66103150844.15L66177983355.15L66490510567.15L6678724487.15 L67134286455.15L67546658822.15L67761174183.15L68132999884.15L6840348861.15 L7303864167.15 L7354446086.15 L779634252.15  L7802060519.15 L791956409.15  L8258191436.15 L8356079750.15 L8603793164.15 L9261350973.15 L9620403660.15 L9751300733.15 L9828385767.15 L984626043.15  L9940703692.15 00000300600900<00?00F00I00L00S00Z00]00d00g00n01101401701>01E01H01K01N01U01\01c01f01i01l01o02602=02@02G02J02M02P02W02Z02]02`02g02n03503<03C03J03Q03T03W03Z03a03d03g03n04504804;04B04I04P04S04V04]04`04c04f04m05405;05>05A05D05G05N05Q05T05[05^05a05d05g05j06106406706>06A06D06G06N06Q06X06[06b06e06l06o07207907@07G07N07Q07X07[07^07a07h07o08208508808?08B08E08H08O08R08U08X08_08b08i08l09309:09=09D09G09N09U09X09[09^09a09d09k09n0:50:80:;0:>0:A0:H0:K0:R0:U0:X0:_0:b0:e0:l0:o0;20;90;<0;?0;F0;I0;L0;S0;V0;Y0;`0;c0;f0;m0<40<;0<>0<A0<H0<K0<N0<Q0<T0<W0<Z0<]0<`0<c0<f0<m0=00=70=:0==0=@0=G0=J0=M0=P0=Q0=X0=[0=b0=i0=l0=o0>20>50><0>?0>F0>M0>T0>[0>b0>i0>l0?30?60?=0?@0?C0?F0?M0?T0?[0?^0?a0?d0?k0@20@50@<0@?0@B0@E0@H0@O0@R0@U0@X0@[0@b0@e0@l0@o0A60A90A@0AC0AJ0AQ0AT0A[0A^0Ae0Al0Ao0B60B90B@0BC0BJ0BM0BT0BW0B^S1dS1dS1dS1dS1dS1d3HnwS1dS1dS1d3HdrS1d3HnwS1dS1d3HdrS1dS1d3HdrS1dS1dS1dS1d3HnwS1d3HnwS1dS1dS1dS1d3HdrS1d3HdrS1d3HnwS1dS1dS1dS1dS1d3HnwS1d3HdrS1dS1d3HdrS1dS1dS1dS1d3HdrS1dS1dS1dS1d3HnwS1d3HnwS1d3HdrS1d3HdrS1d3HnwS1d3HnwS1d3HnwS1dS1dS1dS1d3HdrS1dS1dS1d3HdrS1d3HnwS1dS1dS1d3HdrS1d3HnwS1d3HnwS1dS1dS1d3HdrS1dS1dS1dS1d3HdrS1d3HnwS1d3HnwS1dS1dS1dS1dS1d3HdrS1dS1dS1d3HdrS1dS1dS1dS1dS1dS1d3HdrS1dS1dS1d3HnwS1dS1dS1dS1d3HnwS1dS1d3HnwS1dS1d3HdrS1dS1d3HdrS1dS1dS1d3HdrS1d3HdrS1d3HnwS1d3HnwS1dS1d3HnwS1dS1dS1dS1d3HnwS1d3HnwS1dS1dS1dS1d3HdrS1dS1dS1dS1d3HdrS1dS1dS1dS1d3HdrS1dS1d3HnwS1dS1d3HnwS1d3HdrS1dS1d3HdrS1dS1d3HdrS1d3HdrS1dS1dS1dS1dS1dS1d3HdrS1dS1d3HnwS1dS1dS1dS1dS1d3HnwS1dS1d3HnwS1dS1dS1d3HnwS1dS1dS1d3HdrS1dS1dS1d3HnwS1dS1dS1d3HdrS1dS1dS1d3HdrS1dS1dS1d3HdrS1dS1dS1d3HnwS1d3HnwS1d3HdrS1dS1dS1d3HnwS1dS1dS1dS1dS1dS1dS1dS1dS1dS1dS1d3HdrS1dS1d3HdrS1dS1dS1dS1d3HnwS1dS1dS1dFS1d3HdrS1dS1d3HdrS1d3HdrS1dS1dS1dS1dS1d3HnwS1dS1d3HnwS1d3HnwS1d3HnwS1d3HnwS1d3HnwS1d3HdrS1dS1d3HnwS1dS1d3HnwS1dS1dS1dS1d3HnwS1d3HdrS1d3HnwS1dS1dS1dS1d3HdrS1d3HdrS1dS1d3HdrS1dS1dS1dS1dS1d3HdrS1dS1dS1dS1dS1d3HnwS1dS1d3HnwS1dS1d3HdrS1dS1d3HdrS1dS1d3HdrS1d3HnwS1dS1d3HdrS1dS1d3HnwS1d3HdrS1dS1d3HnwS1dS1d3HnwS1dS1d3HnwS1dS1d3HdrS1dS1d3Hnw". (* [comment removed for export] *)
Lemma memset304_run : ltac2:(CDefT.buildp (gd_tbl_P_startup_memset ()) "Pregs,(6.&5.(7.&40.))Pmem,P,(7.&40.)(8.(7.&8.))Prom,P,(7.&40.)(8.(7.&8.))Pd,(7.&40.)Pret,(7.&40.)P,(9.(7.&40.)(:.R5.(;.&5.+1.$<.))R1.)P,(=.R2.)P,(9.(7.&40.)(:.R7.(;.&5.+:.$<.))R4.)P,(9.(7.&40.)(:.R8.(;.&5.+;.$<.))(>.&40.=))P,(9.(7.&40.)(:.R9.(;.&5.+<.$<.))(>.&40.+130.))P,(9.$2.(?.(10.&40.R7.)+8.)=)P,(11.(12.(10.&40.R8.)+130.)(13.+2.+40.))P,(9.$14.(15.$16.R;.R9.#130.)$17.)(18.(6.&5.(7.&40.))Lregs',(6.&5.(7.&40.))(18.P,(7.&40.)(8.(7.&8.))Lmem',P,(7.&40.)(8.(7.&8.))(19.(1:.$16.(1;.$1<.R?.(;.&40.+46>44.$<.)R>.R=.)(1;.$1<.R2.R;.R1.R=.))(19.(9.P,(7.&40.)(8.(7.&8.))R1.(1=.R>.R<.(1>.#130.)))(1?.Lr,(7.&5.)(20.(7.&5.)R1.$21.)R?.R2.)))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_436f8 D_436f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_436fc D_436fc (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_43700 D_43700 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_43704 D_43704.  (* [comment removed for export] *)
    stw F_43708 D_43708 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_4370c D_4370c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_43710 D_43710 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_43714 D_43714 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_43718 D_43718.  (* [comment removed for export] *)
    stw F_4371c D_4371c (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_43720 D_43720 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_43724 D_43724 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_43728 D_43728 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_4372c D_4372c.  (* [comment removed for export] *)
    stw F_43730 D_43730 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_43734 D_43734 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_43738 D_43738.  (* [comment removed for export] *)
    sn F_4373c D_4373c.  (* [comment removed for export] *)
    sn F_43740 D_43740.  (* [comment removed for export] *)
    stepiv F_43744 D_43744 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_43748 D_43748.  (* [comment removed for export] *)
    sn F_4374c D_4374c.  (* [comment removed for export] *)
    sv F_43750 D_43750 (d).  (* [comment removed for export] *)
    sn F_43754 D_43754.  (* [comment removed for export] *)
    sn F_43758 D_43758.  (* [comment removed for export] *)
    sn F_4375c D_4375c.  (* [comment removed for export] *)
    stw F_43760 D_43760 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_43764 D_43764 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_43768 D_43768 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_4376c D_4376c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_43770 D_43770 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_43774 D_43774 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_43778 D_43778.  (* [comment removed for export] *)
    stw F_4377c D_4377c (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_43780 D_43780 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_43784 D_43784 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_43788 D_43788 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_4378c D_4378c (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_43790 D_43790 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_43794 D_43794 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepiv F_43798 D_43798 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_4379c D_4379c.  (* [comment removed for export] *)
    sn F_437a0 D_437a0.  (* [comment removed for export] *)
    sn F_437a4 D_437a4.  (* [comment removed for export] *)
    stw F_437a8 D_437a8 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437ac D_437ac (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437b0 D_437b0 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437b4 D_437b4 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_437b8 D_437b8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_437bc D_437bc.  (* [comment removed for export] *)
    sv F_437c0 D_437c0 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_437c4 D_437c4.  (* [comment removed for export] *)
    sn F_437c8 D_437c8.  (* [comment removed for export] *)
    sn F_437cc D_437cc.  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_437d0 D_437d0 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d4 D_437d4 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437d8 D_437d8 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_437dc D_437dc (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_437e0 D_437e0.  (* [comment removed for export] *)
    sv F_437e4 D_437e4 (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_437e8 D_437e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_437ec D_437ec ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
