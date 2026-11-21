(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool NArith.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition HEAD : Z := 16180.
Definition FLAGS : Z := 16181.
Definition TIME : Z := 16182.
Definition OS : Z := 16183.
Definition EXLEN : Z := 16184.
Definition EXTRA : Z := 16185.
Definition NAME : Z := 16186.
Definition COMMENT : Z := 16187.
Definition HCRC : Z := 16188.
Definition DICTID : Z := 16189.
Definition DICT : Z := 16190.
Definition TYPE : Z := 16191.
Definition TYPEDO : Z := 16192.
Definition STORED : Z := 16193.
Definition COPY_ : Z := 16194.
Definition COPY : Z := 16195.
Definition TABLE : Z := 16196.
Definition LENLENS : Z := 16197.
Definition CODELENS : Z := 16198.
Definition LEN_ : Z := 16199.
Definition LEN : Z := 16200.
Definition LENEXT : Z := 16201.
Definition DIST : Z := 16202.
Definition DISTEXT : Z := 16203.
Definition MATCH : Z := 16204.
Definition LIT : Z := 16205.
Definition CHECK : Z := 16206.
Definition LENGTH : Z := 16207.
Definition DONE : Z := 16208.
Definition BAD : Z := 16209.
Definition MEM : Z := 16210.
Definition SYNC : Z := 16211.

Definition ENOUGH_LENS : Z := 852.
Definition ENOUGH_DISTS : Z := 592.
Definition MAXBITS : Z := 15.
Inductive codetype : Set := CODES | LENS | DISTS.
Definition DEF_WBITS : Z := 15.
Definition SIZEOF_inflate_state : Z := 7176.

Definition ZSWAP32 (q : Z) : Z :=
  wrap64 (Z.land (Z.shiftr q 24) 255 + Z.land (Z.shiftr q 8) 65280 +
          Z.shiftl (Z.land q 65280) 8 + Z.shiftl (Z.land q 255) 24).


Definition iadler32_upd (adler : Z) (buf : list Z) : Z := adler32_model adler buf.
Definition iadler32_init : Z := 1.
Definition icrc32_upd (crc : Z) (buf : list Z) : Z := crc32_model (wrap32 crc) buf.
Definition icrc32_init : Z := 0.


Definition code_pack (op bits val : Z) : Z := wrap8 op + 256 * wrap8 bits + 65536 * wrap16 val.
Definition code_op (c : Z) : Z := Z.land c 255.
Definition code_bits (c : Z) : Z := Z.land (Z.shiftr c 8) 255.
Definition code_val (c : Z) : Z := Z.land (Z.shiftr c 16) 65535.

Definition lenfix_l : list Z := [
  1888;5244928;1050624;7538708;2033426;7342080;3147776;12585216;
  657168;6293504;2099200;10488064;2048;8390656;4196352;14682368;
  395024;5769216;1574912;9439488;3868435;7866368;3672064;13633792;
  1115921;6817792;2623488;11536640;526336;8914944;4720640;15730944;
  263952;5507072;1312768;14878741;2819859;7604224;3409920;13109504;
  853777;6555648;2361344;11012352;264192;8652800;4458496;15206656;
  526096;6031360;1837056;9963776;5441300;8128512;3934208;14158080;
  1509138;7079936;2885632;12060928;788480;9177088;4982784;16255232;
  198416;5376000;1181696;10684437;2295571;7473152;3278848;12847360;
  722705;6424576;2230272;10750208;133120;8521728;4327424;14944512;
  460560;5900288;1705984;9701632;4392724;7997440;3803136;13895936;
  1246994;6948864;2754560;11798784;657408;9046016;4851712;15993088;
  329488;5638144;1443840;2112;3344147;7735296;3540992;13371648;
  984849;6686720;2492416;11274496;395264;8783872;4589568;15468800;
  591632;6162432;1968128;10225920;6489876;8259584;4065280;14420224;
  1771282;7211008;3016704;12323072;919552;9308160;5113856;16517376;
  1888;5310464;1116160;8587285;2033426;7407616;3213312;12716288;
  657168;6359040;2164736;10619136;67584;8456192;4261888;14813440;
  395024;5834752;1640448;9570560;3868435;7931904;3737600;13764864;
  1115921;6883328;2689024;11667712;591872;8980480;4786176;15862016;
  263952;5572608;1378304;16910352;2819859;7669760;3475456;13240576;
  853777;6621184;2426880;11143424;329728;8718336;4524032;15337728;
  526096;6096896;1902592;10094848;5441300;8194048;3999744;14289152;
  1509138;7145472;2951168;12192000;854016;9242624;5048320;16386304;
  198416;5441536;1247232;12781589;2295571;7538688;3344384;12978432;
  722705;6490112;2295808;10881280;198656;8587264;4392960;15075584;
  460560;5965824;1771520;9832704;4392724;8062976;3868672;14027008;
  1246994;7014400;2820096;11929856;722944;9111552;4917248;16124160;
  329488;5703680;1509376;2112;3344147;7800832;3606528;13502720;
  984849;6752256;2557952;11405568;460800;8849408;4655104;15599872;
  591632;6227968;2033664;10356992;6489876;8325120;4130816;14551296;
  1771282;7276544;3082240;12454144;985088;9373696;5179392;16648448;
  1888;5244928;1050624;7538708;2033426;7342080;3147776;12650752;
  657168;6293504;2099200;10553600;2048;8390656;4196352;14747904;
  395024;5769216;1574912;9505024;3868435;7866368;3672064;13699328;
  1115921;6817792;2623488;11602176;526336;8914944;4720640;15796480;
  263952;5507072;1312768;14878741;2819859;7604224;3409920;13175040;
  853777;6555648;2361344;11077888;264192;8652800;4458496;15272192;
  526096;6031360;1837056;10029312;5441300;8128512;3934208;14223616;
  1509138;7079936;2885632;12126464;788480;9177088;4982784;16320768;
  198416;5376000;1181696;10684437;2295571;7473152;3278848;12912896;
  722705;6424576;2230272;10815744;133120;8521728;4327424;15010048;
  460560;5900288;1705984;9767168;4392724;7997440;3803136;13961472;
  1246994;6948864;2754560;11864320;657408;9046016;4851712;16058624;
  329488;5638144;1443840;2112;3344147;7735296;3540992;13437184;
  984849;6686720;2492416;11340032;395264;8783872;4589568;15534336;
  591632;6162432;1968128;10291456;6489876;8259584;4065280;14485760;
  1771282;7211008;3016704;12388608;919552;9308160;5113856;16582912;
  1888;5310464;1116160;8587285;2033426;7407616;3213312;12781824;
  657168;6359040;2164736;10684672;67584;8456192;4261888;14878976;
  395024;5834752;1640448;9636096;3868435;7931904;3737600;13830400;
  1115921;6883328;2689024;11733248;591872;8980480;4786176;15927552;
  263952;5572608;1378304;16910352;2819859;7669760;3475456;13306112;
  853777;6621184;2426880;11208960;329728;8718336;4524032;15403264;
  526096;6096896;1902592;10160384;5441300;8194048;3999744;14354688;
  1509138;7145472;2951168;12257536;854016;9242624;5048320;16451840;
  198416;5441536;1247232;12781589;2295571;7538688;3344384;13043968;
  722705;6490112;2295808;10946816;198656;8587264;4392960;15141120;
  460560;5965824;1771520;9898240;4392724;8062976;3868672;14092544;
  1246994;7014400;2820096;11995392;722944;9111552;4917248;16189696;
  329488;5703680;1509376;2112;3344147;7800832;3606528;13568256;
  984849;6752256;2557952;11471104;460800;8849408;4655104;15665408;
  591632;6227968;2033664;10422528;6489876;8325120;4130816;14616832;
  1771282;7276544;3082240;12519680;985088;9373696;5179392;16713984].
Definition lenfix_a : arr := arr_of_list lenfix_l.

Definition distfix_l : list Z := [
  66832;16844055;1115411;268502299;328977;67175705;4261141;1073808669;
  197904;33621272;2163988;536937756;591122;134284570;8455446;1344;
  132368;25232663;1639699;402720027;460049;100730137;6358293;1610679581;
  263440;50398488;3212564;805373212;853266;201393434;12649750;1344].
Definition distfix_a : arr := arr_of_list distfix_l.

Definition order_l : list Z := [
  16;17;18;0;8;7;9;6;10;5;11;4;12;3;13;2;14;1;15].
Definition order_a : arr := arr_of_list order_l.

Inductive codeptr : Set := CDyn (ofs : Z) | CLenfix | CDistfix.


Record inflate_state : Type := mkIS {
  is_mode : Z ;
  is_last : Z ;
  is_wrap : Z ;
  is_havedict : Z ;
  is_flags : Z ;
  is_dmax : Z ;
  is_check : Z ;
  is_total : Z ;
  is_head : Z ;
  is_wbits : Z ;
  is_wsize : Z ;
  is_whave : Z ;
  is_wnext : Z ;
  is_window : arr ;
  is_window_blk : option blk ;
  is_hold : Z ;
  is_bits : Z ;
  is_length : Z ;
  is_offset : Z ;
  is_extra : Z ;
  is_lencode : codeptr ;
  is_distcode : codeptr ;
  is_lenbits : Z ;
  is_distbits : Z ;
  is_ncode : Z ;
  is_nlen : Z ;
  is_ndist : Z ;
  is_have : Z ;
  is_next : Z ;
  is_lens : arr ;
  is_work : arr ;
  is_codes : arr ;
  is_sane : Z ;
  is_back : Z ;
  is_was : Z ;
  is_self_blk : blk
}.

Definition iset_mode (s : inflate_state) (v : Z) : inflate_state :=
  mkIS v (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_last (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) v (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_wrap (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) v (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_havedict (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) v (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_flags (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) v (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_dmax (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) v (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_check (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) v (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_total (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) v (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_head (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) v (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_wbits (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) v (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_wsize (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) v (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_whave (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) v (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_wnext (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) v (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_window (s : inflate_state) (v : arr) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) v (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_window_blk (s : inflate_state) (v : option blk) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) v (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_hold (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) v (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_bits (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) v (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_length (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) v (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_offset (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) v (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_extra (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) v (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_lencode (s : inflate_state) (v : codeptr) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) v (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_distcode (s : inflate_state) (v : codeptr) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) v (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_lenbits (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) v (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_distbits (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) v (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_ncode (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) v (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_nlen (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) v (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_ndist (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) v (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_have (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) v (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_next (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) v (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_lens (s : inflate_state) (v : arr) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) v (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_work (s : inflate_state) (v : arr) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) v (is_codes s) (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_codes (s : inflate_state) (v : arr) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) v (is_sane s) (is_back s) (is_was s) (is_self_blk s).
Definition iset_sane (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) v (is_back s) (is_was s) (is_self_blk s).
Definition iset_back (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) v (is_was s) (is_self_blk s).
Definition iset_was (s : inflate_state) (v : Z) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) v (is_self_blk s).
Definition iset_self_blk (s : inflate_state) (v : blk) : inflate_state :=
  mkIS (is_mode s) (is_last s) (is_wrap s) (is_havedict s) (is_flags s) (is_dmax s) (is_check s) (is_total s) (is_head s) (is_wbits s) (is_wsize s) (is_whave s) (is_wnext s) (is_window s) (is_window_blk s) (is_hold s) (is_bits s) (is_length s) (is_offset s) (is_extra s) (is_lencode s) (is_distcode s) (is_lenbits s) (is_distbits s) (is_ncode s) (is_nlen s) (is_ndist s) (is_have s) (is_next s) (is_lens s) (is_work s) (is_codes s) (is_sane s) (is_back s) (is_was s) v.

Definition code_at (s : inflate_state) (p : codeptr) (i : Z) : Z :=
  match p with
  | CDyn ofs => arr_get (is_codes s) (ofs + i)
  | CLenfix => arr_get lenfix_a i
  | CDistfix => arr_get distfix_a i
  end.


Record ilayout : Type := mkLay {
  lay_mode : Z;
  lay_last : Z;
  lay_wrap : Z;
  lay_havedict : Z;
  lay_flags : Z;
  lay_dmax : Z;
  lay_check : Z;
  lay_total : Z;
  lay_head : Z;
  lay_wbits : Z;
  lay_wsize : Z;
  lay_whave : Z;
  lay_wnext : Z;
  lay_window : Z;
  lay_hold : Z;
  lay_bits : Z;
  lay_length : Z;
  lay_offset : Z;
  lay_extra : Z;
  lay_lencode : Z;
  lay_distcode : Z;
  lay_lenbits : Z;
  lay_distbits : Z;
  lay_ncode : Z;
  lay_nlen : Z;
  lay_ndist : Z;
  lay_have : Z;
  lay_next : Z;
  lay_lens : Z;
  lay_work : Z;
  lay_codes : Z;
  lay_sane : Z;
  lay_back : Z;
  lay_was : Z
}.

Definition lay_ref : ilayout :=
  mkLay 8 12 16 20 24 28 32 40 48 56 60 64 68 72 80 88 92 96 100 104 112 120 124 128 132 136 140 144 152 792 1368 7144 7148 7152.
Definition iarr_u16_of (g : Z -> Z) (off n : Z) : arr := arr_init n (fun i => init_u16 g off i).
Definition iarr_u32_of (g : Z -> Z) (off n : Z) : arr := arr_init n (fun i => init_u32 g off i).
Definition iarr_u8_of (g : Z -> Z) (off n : Z) : arr := arr_init n (fun i => init_u8 g off i).

Definition is_of_oracle (lay : ilayout) (g : Z -> Z) (self : blk) : inflate_state :=
  mkIS (init_u32 g (lay_mode lay) 0)
       (swrap32 (init_u32 g (lay_last lay) 0))
       (swrap32 (init_u32 g (lay_wrap lay) 0))
       (swrap32 (init_u32 g (lay_havedict lay) 0))
       (swrap32 (init_u32 g (lay_flags lay) 0))
       (init_u32 g (lay_dmax lay) 0)
       (init_u64 g (lay_check lay) 0)
       (init_u64 g (lay_total lay) 0)
       0
       (init_u32 g (lay_wbits lay) 0)
       (init_u32 g (lay_wsize lay) 0)
       (init_u32 g (lay_whave lay) 0)
       (init_u32 g (lay_wnext lay) 0)
       (arr_make 0 0)
       None
       (init_u64 g (lay_hold lay) 0)
       (init_u32 g (lay_bits lay) 0)
       (init_u32 g (lay_length lay) 0)
       (init_u32 g (lay_offset lay) 0)
       (init_u32 g (lay_extra lay) 0)
       (CDyn 0)
       (CDyn 0)
       (init_u32 g (lay_lenbits lay) 0)
       (init_u32 g (lay_distbits lay) 0)
       (init_u32 g (lay_ncode lay) 0)
       (init_u32 g (lay_nlen lay) 0)
       (init_u32 g (lay_ndist lay) 0)
       (init_u32 g (lay_have lay) 0)
       0
       (iarr_u16_of g (lay_lens lay) 320)
       (iarr_u16_of g (lay_work lay) 288)
       (iarr_u32_of g (lay_codes lay) 1444)
       (swrap32 (init_u32 g (lay_sane lay) 0))
       (swrap32 (init_u32 g (lay_back lay) 0))
       (init_u32 g (lay_was lay) 0)
       self.


Record icall : Type := mkIC {
  ic_input : arr ;
  ic_next_in : Z ;
  ic_avail_in : Z ;
  ic_outbuf : arr ;
  ic_next_out : Z ;
  ic_avail_out : Z ;
  ic_total_in : Z ;
  ic_total_out : Z ;
  ic_adler : Z ;
  ic_data_type : Z ;
  ic_msg : Z
}.

Definition icset_input (s : icall) (v : arr) : icall :=
  mkIC v (ic_next_in s) (ic_avail_in s) (ic_outbuf s) (ic_next_out s) (ic_avail_out s) (ic_total_in s) (ic_total_out s) (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_next_in (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) v (ic_avail_in s) (ic_outbuf s) (ic_next_out s) (ic_avail_out s) (ic_total_in s) (ic_total_out s) (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_avail_in (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) v (ic_outbuf s) (ic_next_out s) (ic_avail_out s) (ic_total_in s) (ic_total_out s) (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_outbuf (s : icall) (v : arr) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) v (ic_next_out s) (ic_avail_out s) (ic_total_in s) (ic_total_out s) (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_next_out (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) (ic_outbuf s) v (ic_avail_out s) (ic_total_in s) (ic_total_out s) (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_avail_out (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) (ic_outbuf s) (ic_next_out s) v (ic_total_in s) (ic_total_out s) (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_total_in (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) (ic_outbuf s) (ic_next_out s) (ic_avail_out s) v (ic_total_out s) (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_total_out (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) (ic_outbuf s) (ic_next_out s) (ic_avail_out s) (ic_total_in s) v (ic_adler s) (ic_data_type s) (ic_msg s).
Definition icset_adler (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) (ic_outbuf s) (ic_next_out s) (ic_avail_out s) (ic_total_in s) (ic_total_out s) v (ic_data_type s) (ic_msg s).
Definition icset_data_type (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) (ic_outbuf s) (ic_next_out s) (ic_avail_out s) (ic_total_in s) (ic_total_out s) (ic_adler s) v (ic_msg s).
Definition icset_msg (s : icall) (v : Z) : icall :=
  mkIC (ic_input s) (ic_next_in s) (ic_avail_in s) (ic_outbuf s) (ic_next_out s) (ic_avail_out s) (ic_total_in s) (ic_total_out s) (ic_adler s) (ic_data_type s) v.

Definition icall_of_zcall (c : ZCall) : icall :=
  mkIC (arr_of_list (zc_input c)) 0 (zlength (zc_input c))
       (arr_make (zc_avail_out c) 0) 0 (zc_avail_out c)
       (zs_total_in (zc_strm c)) (zs_total_out (zc_strm c)) (zs_adler (zc_strm c))
       (zs_data_type (zc_strm c)) (zs_msg (zc_strm c)).

Definition zstrm_of_icall (c : icall) : zstrm :=
  mkZS (ic_total_in c) (ic_total_out c) (ic_adler c) (ic_data_type c) (ic_msg c).
Definition zret_of_icall (c : icall) (rc : Z) : ZRet :=
  mkZRet (ic_next_in c) (arr_slice (ic_outbuf c) 0 (ic_next_out c)) (zstrm_of_icall c) rc.

Record iregs : Type := mkIR {
  ir_next : Z ;
  ir_have : Z ;
  ir_put : Z ;
  ir_left : Z ;
  ir_hold : Z ;
  ir_bits : Z ;
  ir_in : Z ;
  ir_out : Z ;
  ir_ret : Z
}.

Definition irset_next (s : iregs) (v : Z) : iregs :=
  mkIR v (ir_have s) (ir_put s) (ir_left s) (ir_hold s) (ir_bits s) (ir_in s) (ir_out s) (ir_ret s).
Definition irset_have (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) v (ir_put s) (ir_left s) (ir_hold s) (ir_bits s) (ir_in s) (ir_out s) (ir_ret s).
Definition irset_put (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) (ir_have s) v (ir_left s) (ir_hold s) (ir_bits s) (ir_in s) (ir_out s) (ir_ret s).
Definition irset_left (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) (ir_have s) (ir_put s) v (ir_hold s) (ir_bits s) (ir_in s) (ir_out s) (ir_ret s).
Definition irset_hold (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) (ir_have s) (ir_put s) (ir_left s) v (ir_bits s) (ir_in s) (ir_out s) (ir_ret s).
Definition irset_bits (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) (ir_have s) (ir_put s) (ir_left s) (ir_hold s) v (ir_in s) (ir_out s) (ir_ret s).
Definition irset_in (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) (ir_have s) (ir_put s) (ir_left s) (ir_hold s) (ir_bits s) v (ir_out s) (ir_ret s).
Definition irset_out (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) (ir_have s) (ir_put s) (ir_left s) (ir_hold s) (ir_bits s) (ir_in s) v (ir_ret s).
Definition irset_ret (s : iregs) (v : Z) : iregs :=
  mkIR (ir_next s) (ir_have s) (ir_put s) (ir_left s) (ir_hold s) (ir_bits s) (ir_in s) (ir_out s) v.

Record iw : Type := mkW { w_s : inflate_state; w_c : icall; w_r : iregs }.
Definition wset_s (w : iw) (s : inflate_state) : iw := mkW s (w_c w) (w_r w).
Definition wset_c (w : iw) (c : icall) : iw := mkW (w_s w) c (w_r w).
Definition wset_r (w : iw) (r : iregs) : iw := mkW (w_s w) (w_c w) r.

Definition LOAD (w : iw) : iw :=
  let c := w_c w in let s := w_s w in let r := w_r w in
  wset_r w (mkIR (ic_next_in c) (ic_avail_in c) (ic_next_out c) (ic_avail_out c)
                 (is_hold s) (is_bits s) (ir_in r) (ir_out r) (ir_ret r)).

Definition RESTORE (w : iw) : iw :=
  let c := w_c w in let s := w_s w in let r := w_r w in
  let c := icset_next_out c (ir_put r) in
  let c := icset_avail_out c (ir_left r) in
  let c := icset_next_in c (ir_next r) in
  let c := icset_avail_in c (ir_have r) in
  let s := iset_hold s (ir_hold r) in
  let s := iset_bits s (ir_bits r) in
  mkW s c r.


Inductive ares (A : Type) : Type :=
  | ARun (a : A) (w : iw)
  | ALeave (w : iw)
  | ARet (rc : Z) (w : iw).
Arguments ARun {A} _ _.
Arguments ALeave {A} _.
Arguments ARet {A} _ _.

Definition AM (A : Type) : Type := iw -> ares A.

Definition aret {A} (a : A) : AM A := fun w => ARun a w.
Definition abind {A B} (m : AM A) (f : A -> AM B) : AM B :=
  fun w => match m w with
           | ARun a w' => f a w'
           | ALeave w' => ALeave w'
           | ARet rc w' => ARet rc w'
           end.
Definition aleave {A} : AM A := fun w => ALeave w.
Definition areturn {A} (rc : Z) : AM A := fun w => ARet rc w.
Definition aget : AM iw := fun w => ARun w w.
Definition aput (w : iw) : AM unit := fun _ => ARun tt w.
Definition amodify (f : iw -> iw) : AM unit := fun w => ARun tt (f w).
Definition agets {A} (f : iw -> A) : AM A := fun w => ARun (f w) w.

Declare Scope am_scope.
Delimit Scope am_scope with am.
Notation "'do' x <- m ; k" := (abind m (fun x => k))
  (at level 200, x name, m at level 100, k at level 200) : am_scope.
Notation "'let*' x ':=' m 'in' k" := (abind m (fun x => k))
  (at level 200, x pattern, m at level 100, k at level 200) : am_scope.
Notation "m ;; k" := (abind m (fun _ => k))
  (at level 100, right associativity) : am_scope.

Lemma abind_run : forall {A B} (m : AM A) (f : A -> AM B) w,
  abind m f w = match m w with ARun a w' => f a w' | ALeave w' => ALeave w' | ARet rc w' => ARet rc w' end.
Proof. reflexivity. Qed.

Definition gs {A} (f : inflate_state -> A) : AM A := fun w => ARun (f (w_s w)) w.
Definition gc {A} (f : icall -> A) : AM A := fun w => ARun (f (w_c w)) w.
Definition gr {A} (f : iregs -> A) : AM A := fun w => ARun (f (w_r w)) w.
Definition us (f : inflate_state -> inflate_state) : AM unit := fun w => ARun tt (wset_s w (f (w_s w))).
Definition uc (f : icall -> icall) : AM unit := fun w => ARun tt (wset_c w (f (w_c w))).
Definition ur (f : iregs -> iregs) : AM unit := fun w => ARun tt (wset_r w (f (w_r w))).


Record ivariant : Type := mkIV {
  iv_fast : bool ;
  iv_flush_exits : bool ;
  iv_aux : bool ;
  iv_lay : ilayout
}.
Definition ivar_ref : ivariant := mkIV true true true lay_ref.