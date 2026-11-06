(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs ItabUbs RotUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
From Stdlib Require Import PrimString.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require PlanDec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require StrLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Ops GLib GUnp GWin G2 G2Z G2B G3 G3P G4 GRoom G1 G0 G6 GCap GNz GShr GCur GBnd VDestroy GSplit GName GVEnd GInv TdEnter Td PkOps PkEnter PkExit PkStack PkPeek PkFld PkBody PkRegrow PkCap PkInv GPerm.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require Import T_Ubs2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2L Require Import T_Ubs2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require Import T_Ubs2U.
Module C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22).
Definition CUTS : IMap.t template := imap_of [(139%uint63, T_Ubs2U.T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P9VPP>VPP>UPP?UPP@UPPAUPPBUPPCUPPDUPPEUPPFUPPGUPPHUPPIUPPJUPPKUPPLUPPMUPP6VPP7VPP8VPP;UPLXP:VPP;VPP<UPP?VPP@VPPAVPPBVPP:VPP?VPPGVPU;T<Qj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUjLUjKUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk6QQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.

Module C_PKPOP_n_m0k0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PKPOP_n_m0k0).
Definition CUTS : IMap.t template := imap_of [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2U.T_PKPOP_n_m0k0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-33YCRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZLH3;TP<XPP=XPP>XPP6TPP0WPP@XPPAXPPBXPPCXPPDXPPEXPPFXPPGXPPHXPPIXPPJXPP7VPP<UPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNVPPOV0($-)-7WPU9TIQjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUiKULUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(3#.-#%ylQL;;TkHRQyS0.'-%>;UPP>UPP?UPP@UPPAUPLQPCUPPDUPPEUPPFUPPGUPPHUPPIUPPJUPPKUPPLUPPMUPPNUPPOUPP0VPP1VPP=UPP5VPQ1WOOOOOO0#(-$<WP1WPP2WPP3WPP4WPP5VPP5WPP6WPV@V<Qj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wi2V0W9-;'jLUjK@%4-<-#$cyTDM;TSPylD@*,17=#4@#,17=$H5@$-18#@#%1*2%5Vh@$21*2$AU<1*2-#&4WPV<V8Qj3Wi2W01)(-##6V0Wj5Vi2V4:14+@%61)0-#'k>SQySPLRP1WPvq@*/1)322.0#8@%(1)3#L;1&.-#%uqylQ4N;TkDRQ016,%47=@*.16,#L@#02;)@$//9"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PKPOP_n_m0k0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PKPOP_n_m0k0.

Module C_PKPOP_n_m1k1.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PKPOP_n_m1k1).
Definition CUTS : IMap.t template := imap_of [(267%uint63, T_Ubs2U.T_PKHEAD_m1k0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2U.T_PKPOP_n_m1k1).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "YCRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZP<UPP;UPP>UPP?UPP@UPP5VPPCUPPDUPPEUPPFUPPGUPPHUPPIUPPJUPPKUPPLUPPMUPPNUPPOUPP0VPP1VPP=UPP2VPP3VPP4VPPAUPP6VPP7VPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNVPPOVPP0WPP1WPP2WPP4WPV;X3Rj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUjLUjKUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPylDRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T8N;TDO;T@0<TD0<T02<T42<TH5<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZylQ4N;TkDRQySPylDRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;TLK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TH5<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4Zk?SQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PKPOP_n_m1k1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PKPOP_n_m1k1.

Module C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e).
Definition CUTS : IMap.t template := imap_of [(229%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P<UPP6VPP:WPP7VPP9WPU5Wbj3Wj2Wi7V1Wj6Vi=U5Vj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.

Module C_PKHEAD_m1k0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PKHEAD_m1k0).
Definition CUTS : IMap.t template := imap_of [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (207%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e); (288%uint63, T_Ubs2U.T_PKPOP_n_m1k0); (289%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6); (290%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66); (291%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6); (292%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2); (293%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e); (294%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6); (295%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d); (296%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20); (297%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637); (312%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430); (313%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5); (314%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd); (315%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85); (316%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2U.T_PKHEAD_m1k0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "--=YCRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZYD@*$.'#D@#4.'#<@,).+:1+0#8@#$.+$H5@*(.+#8@%4169@**.+@%92$$#L=.'$L9@#3.+-#0P7VPLQA2ZP6VRP3WPA0ZP6VS4#-#T2#--$&7XhP4VPA1ZLPP3WPA4ZP4VPP5VPA0ZPIYhPFXPA1ZPFW2$.(P8YhP50#8%6VU4%<#Q2#--&$<UPP;UPL8B;TP6WPP7WPP8WPP4VPP;WPP<WPP=WPP>WPP?WPP@WPPAWPPBWPPCWPPIUPPJUPPDWPPLUPPMUPQQ0DOOOOOOOOOOWQQH6#1-/&P1VPP2VPP3VPP@UPP5VPP6VQP7VPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNVPPOVPP0WPP1WPLPP2WPLPLPV0Y7Rj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUjLUjKUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPS2.:-#*vqySPySQySPkJRQySP61%8+RPP9WPP:W@#?1%>81$6#h21+)&P6VP@%61$:-#,@UPLQLPP1WPP2WPUKY4R61$2%i0W@'01$4&i;U<@#=1$3,ySPP<UPPEW114?+GWPPHWPPI114?-#:LWPPMWPPNWPPOWPP0XPP1XPP2XPP3XPP4X41$#,5XPLQLL?=T@$%14>#R@-<14<&kCSQ0.<<14>-#*koRySPcyT<?=TSPySS32(7$HH@*(2(7*QP2WPP3W@,.2(9&QQG?61$+@#92)*(@UPP0W02%6#300#+P2WPU2Y;Q?/9&i4VO@&92#+$HH@*%2#+@*.1/0@#82#-@4@2#*#F@;;2#*-#(cyT89<TSPk4H;TQy832)$LD@$12#?@#+1''&QQ@H5#1'LH4>T@#$1';#Y@%>2$-#R@*02$-#Y@%-5(.'LYL?V@&+5('32'-12')-#$P3WPUJY5Rj7W@%:1$<&i1V3@&02)?$LD@$12)?@$9153@%<2*.@*.15112*.#Y@#9386@&@2)7#U@.&2)7#U@%.2)7%UL>@392)7#U@.(2)7#U@#33?%$HN@'/2)@#S@.&2)@#S@%.2)@%SL=@392)@#S@.(2)@#S@#32)@$0K@'/2)@#R@.&2)@#R@%.2)@%RL<@392)@#R@.(2)@#R@(0557@%?8;9@*12)7@%.;?:'LQP3W@&,;?4@/82)8@%=9#;@*52)8@#49#;$HI1#++@I=TSPk@D=9$&#E@&#2*8$LF@&:9$&#S@2/9$&#H@*,2*7#E@&#2*7@#)153@%<2*7@*.151@$$9$&@&?2)7@%?9$&@*12)7@**9$&@/#2)7@%=9$&@*52)7@#49$&%D>>@'.2)@@%?9$&@*12)@@**9$&@/#2)@@%=9$&@*52)@@#19$&@'+2)7@%?9#;@*12)7@**9#;@/#2)7@%=9#;@*52)7@#19#;(cyT8<>1:9&#<@'/3>@@%?9$/@*12*+@*+9$/@/#2*,@%=9$/@*52*,@#49$/$L9@'/2*#@1-3?,#@@@=3?,@6-7,8#A@@=7,8'cyT4;@'/3>7@1-:88#B@@=:88@6-=$&&#C@@==$&&'cyTH619#8#<2#++06>TSPk@E==%<&@$'=2@($3W@#62*@$HC61(/%0E<@&92*@#T@-(2*@51&.91$8@&5=2@6#L@*(=2@6#L@$'=2@621$#@#02*<@#715/@%<2*<@*.15-@#82*<%k@B<2)?*@I;TPFWP31'6(4VPPKW@#/1'622=.%4XP91'#-##P3WPP4WPLLH@##1&:$RZ@%>2)'#U21&:%P4W@*$1&<0.<=2)'51%.#R018&$JW@##1%4#4@#+1%82.*@#(2)3@%76(&=3?:&U7Y7@%>3?6@&42)>$5X115.,7XPP8XPP9X015.-#9<XPP=XPP>XPP?XPP@XPPAXPPBXPPCXPPD51$6#E@$#15.@%<2)&@*015,(kCSQRZ@#'2)&*P7VPRZvq42).@#=3,3&QQ5>61%6@#*699@#016;@&,5%5*U4Y8Rj8W@*(16>$EW@2=16>26:/@#,6:&@&(3-'@%?;;8@*13-'@#%;;8@%=3-'@%7:7+@/#3-'@%=;;3@*52))@#(;;3(P7VPRR@$-3-'#:@#63-'#S@373-'@.>16>2;+4@#&7=4$<K7;++@&(3-0@%?=&-)@*13-0@#%=&-)@%=3-0@%73=8@/#3-0@%==&-#@*52)2@#(=&-#(P7VPRQ@$-3-0#=@#63-0#R@373-0@.>16>2=%:9@#&3-0$@I@&53-0#[@.&3-0#[@&63-0@%73=8@/#3-0#[@.(2)2#[@#,3-0#[@$-3-0#?@#63-00=*+4@323-0@.>16>2=*,)@#&3-0-#'4H>TSPk4I;TQk0I<;;'$8J@%+3.$$4M@&8;;'#V@2>;;'#8@*/3.$$8J@%+2*&@#'15.@%<2*&@*015,@%5;;'#6@(>;;'#9@*23.$@2;16>@#4;;'@&(3-'@%?;;'@*13-'@*9;;'@.-3-'@%=:7)@*52))@%0;;'#;@(>;;'@.03-'@.>16>@#.;;'%L3?@&43-0@%?;;'@*13-0@*9;;'@.-3-0@%=:7)@*52)2@%0;;'#>@(>;;'@.03-0@.>16>@#.;;'-#&02?TSPkLI;TQkH<8@762;1'L@QLQ@#*2;4@#(2;0&LRP42=*72)P3VPX0R3=-'$$Lh@&+80#,LWP2WPU?V9@(,175@$$1'4-#*ySPP8YPPHXPPIXPPJX02'*-#:MXPPNXPPOXPP0YPP1YPP2YPP3YPP4YPP5Y41$1$6Y019%$4V2#*(hL@1<T21%&%P6X1;.2#Q@%:1$;#3017)+P2WPV<V4R@'=1#@%i;U@$#=,/?1=/<6-#/P8YPP5XheqRYL000000000T1171#R01770>'64-#,uqySPylQ82<TkCRQk02<0164-#1lQ@8@TPFX@Qg9ySPk[QySPkMR1#@-#-<B@TLhg<ySPkEZQySPknR0#=-#'D2@TP4Vhg:Lhb5V?18@&0SLR@$(18@31(<=18@@%<1)(@-:19#$@Q@##19$#031-7@-?19$$@Q@%319%$@Q@#)19&)@Qg:L@Q@#&19(%VLT@$(19(#X@#(19(@%<1),@-:19($0S@#$19(#V@.)19($0S@%319($0S@#)19()0Sg:L0S@#&19(%\LX@$(19(#`@#)19(@%;1),@-;19(#V@#$19(#\@.*19(#V@%419(#V@#*19((Vg:L0V@#&19(%hL`@$(19($0Q@#)19)@%;1)-@-;19)#\@#$19)@%;5=2@*919)#\@%419)#\@#*19)(\g:L0\@#&19)&@QL0@$)63=#0@#)63>@%<1)/@-;19+@#$63@#0@.+64##0@%464$#0@#*64%(0hg:L0@#'64'&0SL0@$)64)#0@#)64*@%=1)0@-;19-@#&64,@.+64-#0@%564.#0@#+64/)0@Qg:L0@#(641&0VL0@$)643#0@#*644@1.645@#&646@.,647@%6648@#,649064:@#(64;&0\L0@$)64=#0@#*64>@1.64?@#&64@@.,65#@%665$@#,65%065&@#(65'&0hL0@$*65)@#+65*@1.65+@#&65,@.,65-@%665.@#,65/0650@#(651'0@QL0@$+653@#+654@1.655@#&656@.-657@%6658@#,659065:-#$0hb5VkOR[PFW7=%$%(P4WPRV@%,=;#4%N?T81*4#E1=&;:@%==+;'@*11*3$RX@$.1*'+ySPkDZQkB01)<-#,STcyTD0@TSPk@G;TQk<G0=$3'@#@=%8&#7@#5>48&$LU@&4=%70#32=%<.1=%78%3Y6@&#2/1@&3=;'&6=%7/0=%$<(:XPP;X@#>=%78@#/=%$<@%4=%7(@*>2?((kDSQyS01$<-#&IYPP9YPP:YPP;Y01->-#9>YPP?YPP@YPPAYPPBYPPCYPPDYPPEYPPF52?0#G@#-=%%$'GXPPF3=%%$@%41%#@(/2)7@#?1$(0.)-#&vqPIYPPFXheqRW@$/2?$$7Y@$5=%$<:18@&0SLR@$(18@@#/=%$<@1-19#:9#8219$08-%@-=19$$@Q@%319%@#:=%$<;19(%VLT@$(19(@#/=%$<@1-19(:9#.319(#V@.#19($0S@%319(@#:=%$<;19(%\LX@$(19(@#/=%$<@1.19(99#$319(#\@.$19(#V@%419(@#9=%$<;19(%hL`@$(19(@#0=%$<@1.19)98@8319)@%95=8@*519)#\@%419)@#9=%$<;19)0=%$<@$(19+@#/=%$<@1.19+@#$63@18@-@->19,@%464$@#:=%$<;19,0=%$<@$(19,@#0=%$<@1.19-@#&64,@.%64-0=%$<@%119/@#<=%$<<192%VL0@$)643@#1=%$<@1.192@#&646@.&647@%6648@#<=%$<<192%\L0@$)64=@#1=%$<@1/192@#%64@@.&65#@%665$@#<=%$<<192%hL0@$*65)@#1=%$<@1/193@#%65,@.&65-@%665.@#<=%$<<1931=%$<@$)195@#0=%$<@1/195@#%656@.'657@%6658@#<=%$<21962=5)9#I3=%$@@#)=&+#@$->*1#;=%$@#61=3'0@%;>,'=@*%1*1$kB4>,',$RT@%@=%$>@#$=89*@%;=3%8@&(=8(4@.)=3%8@%71$;@(/181@$&=&*/1>0&.@*==3%8@1(19#@#*=3%8@.&19$@*:=3%8@1(19(@#*=3%8@.&19(@*:=3%8@1)19(@#)=3%8@.'19(@*:=3%8@1)19)@#)=3%8@.'19)@*<=3%8@1)19+@#*=3%8@.'19,@*==3%8@1)19-@#+=3%8@.'19.@+#=3%8@1)192@#+=3%8@.'192@+#=3%8@1*192@#*=3%8@.(192@+#=3%8@1*193@#*=3%8@.(193@+%=3%8@1*195@#+=3%8@.(196@+?=3%8@-=1*3@'2=3%8#<@#6=3%8#S@29=3%8@%5>=$-@.@=3%8@%51%#@(/2)7@$$=&?@#S@+#=3%8@1.19#@#*=3%8@->19$@*:=3%8@1.19(@#*=3%8@->19(@*:=3%8@1/19(@#)=3%8@-?19(@*:=3%8@1/19)@#)=3%8@-?19)@*<=3%8@1/19+@#*=3%8@-?19,@*==3%8@1/19-@#+=3%8@-?19.@+#=3%8@1/192@#+=3%8@-?192@+#=3%8@10192@#*=3%8@-@192@+#=3%8@10193@#*=3%8@-@193@+%=3%8@10195@#+=3%8@-@196@,%=3%8@-/1*11=3%8#S@&7=3%8'cyTDI6>41;@%;=3&#@&(><.<@.)=3&#@%71$;@(/18:@$&=&*81>4@9@#,=3&#:1%,'RUP5X@$01%.71%)%@Uh@%=1%)2'%21%-&3T5R@'@140@%(1%0+cyTDK;TSP0>3->@)+=36)@1(2+)@#*=36)@.&2+*@#&=-4;@%&2++#@361?32+,@%<1%+@*?2+,=1%2@$82+-@'0=4(1@1(2+0@#*=4(1@.&2+0@#&=.&9@%&2+0$0S<2+0@%;1%+@*?2+0=1%2@$82+0@'0=489@1)2+0@#)=489@.'2+0@#%=.67@%'2+0#V<2+0@%;1%+@*@2+0<1%2@$92+0@'0=5+#@1)2+1@#)=5+#@.'2+1@#%=/(5@%'2+1#\<2+1@%;1%+@*@2+1<1%2@$92+1@'2=5;+@1)2+3@#*=5;+@.'2+4@%>9+,#0<9+-@%=1%,@*@2+5@%,9+/@'4=6-4@1)2+6@#+=6-4@.'2+7@%?9+9#0>9+:@.29+;>1%5@$92+:@'6=6=?@1)2+=@#+=6=?@.'2+=@%@9,(>9,)@.39,*@%.9,+@'6=70,@1*2+=@#*=70,@.(2+=@%?9,5>9,6@.39,7@%.9,8@'7=7@7@1*2+>@#*=7@7@.(2+>@%?9-$>9-%@.39-&@%.9-'@'9=83$@1*2+@@#+=83$@.(2,#@%?9-1>9-2@.49-3@%.9-4@(5=9%0@-=1:??=9%0:1&%'RUP4V@%21&'71%@%@Uh@%>1%@@*81;291&)@#71;&#y@%,=96/#?@#6=96/#Q2326@21=96/#Q@2+=96/@%51%#@(/2:6@$$=-27#Q@#0=96/>1%*'RUPFX@$01%,71%'4=+5.@%41%'@(629;@%$1%.@#84$'@(-=:(3@1.2+'@#*=:(3@->2+(@#&=4''@%*2+)5<<222+*@%:1%)@*;2+*=1%0@$82++@'0=:89@1.2+.@#*=:89@->2+.@#&=47#@%*2+.5<<#32+.@%91%)@*;2+.=1%0@$82+.@'0=;*?@1/2+.@#)=;*?@-?2+.@#%=5(=@%+2+.4<;232+.@%91%)@*<2+.<1%0@$92+.@'0=;;'@1/2+/@#)=;;'@-?2+/@#%=589@%+2+/4<;#32+/@%91%)@*<2+/<1%0@$92+/@'2=<--@1/2+1@#*=<--@-?2+2@&$9*@5<:232+2@.,9+$=1%1@$92+3@'3=<=4@1/2+4@#+=<=4@-?2+5@&%9+/6=+4@32+7@.,9+1>1%3@$92+8@'6==/=@1/2+;@#+==/=@-?2+;@&&9+<>9+=@.-9+>@%.9+?@'6==@(@102+;@#*==@(@-@2+;@&%9,+>9,,@.-9,-@%.9,.@'7=>21@102+<@#*=>21@-@2+<@&%9,8>9,9@.-9,:@%.9,;@'9=?$:@102+>@#+=?$:@-@2+?@&%9-'>9-(@..9-)@%.9-*@(9=?5&@-/1:;1=?5&#Q@#&=?5&>1&'3=+48@%.1&)71&$5=+48@-51;2$kC@#&1&+@%+=+46<=@('+8H?TSPk@F0$,%ySS@%-=@(3$1X?=+&,#U@&(=.5?#X@*-34/@#$=.5?#L@%)=@(2@%71$904*0219$$=V@)==,:8#U7=.%*@)=>>98=19&@%<1).@-819'@#*=?60@.+19(@*#>>9<=19,@%<1)2@-819,@#*=?&,@.+19,@*#>>9@>19,@%;1)2@-919,@#)=>4(@.,19,@*#>>:&>19-@%;1)3@-919-@#)=>$$@.,19-@*%>>:*>19/@1*645@#+==1>@.,190@*%>>:.>190@1+64?@#,=<?9@.,192@*)>>:2>196@1,65+@#+=</2@.,196@*)>>:6?196@1+655@#+=;=+@.-196@*)>>::?197@1+65?@#+=;-$@.-197@*+>>:>?199@1+66+@#,=::;@.-19:@';>>;$#L;=9#,@$9=97/%@4A@#*=:*4@.$1*8@%->>;)*D0<TQk@00$4@#@=97:#7@#6=97:#U22/3@&<=97:#5@-'=97:@#%=%&1@&&=('<@*.2?1@#,=('<#L@%)=979@%51$?@(42);@$$='5)#U@#0=97>@#:2?-@'4=9':@#&=%&1@1+19'@#*=9'9@.%19(@*#>>;1@#&=%&1@1+19,@#*=857@.%19,@*#>>;5@#&=%&1@1,19,@#)=8%5@.&19,@*#>>;9@#&=%&1@1,19-@#)=733@.&19-@*%>>;=@#&=%&1@1,19/@#*=7#1@.&190@*%>><#@#'=%&1@1,191@#+=61.@.&192@*)>><'@#'=%&1@1,196@#+=5?)@.&196@*)>><+@#'=%&1@1-196@#*=5/$@.'196@*)>></@#'=%&1@1-197@#*=4<=@.'197@*+>><3@#'=%&1@1-199@#+=4,8@.'19:@'?>><7#L@#+=&,:@$,=3),<=%&58=3:3@-41*61=3:8#U@#&=3:8@#91*.#y@#<=%&39=3)7@&&=3(@#S@1%='$$@#)=3(@@%71$9@(4185@$&=&,(#S7='#>@*7=3(@@1&19'@#*=3(@@.+19(@*;=3(@@1&19,@#*=3(@@.+19,@*;=3(@@1'19,@#)=3(@@.,19,@*;=3(@@1'19-@#)=3(@@.,19-@*==3(@@1'19/@#*=3(@@.,190@*>=3(@@1'191@#+=3(@@.,192@+$=3(@@1'196@#+=3(@@.,196@+$=3(@@1(196@#*=3(@@.-196@+$=3(@@1(197@#*=3(@@.-197@+&=3(@@1(199@#+=3(@@.-19:@+?=3(@@.$1*8@'2=3(@#<@#6=3(@#S@2:=3(@#S@2)=3(@@%51$?@(42);@$$='#>#S@+$=3(@@1,19'@#*=3(@@.%19(@*;=3(@@1,19,@#*=3(@@.%19,@*;=3(@@1-19,@#)=3(@@.&19,@*;=3(@@1-19-@#)=3(@@.&19-@*==3(@@1-19/@#*=3(@@.&190@*>=3(@@1-191@#+=3(@@.&192@+$=3(@@1-196@#+=3(@@.&196@+$=3(@@1.196@#*=3(@@.'196@+$=3(@@1.197@#*=3(@@.'197@+&=3(@@1.199@#+=3(@@.'19:@,%=3(@@-41*61=3(@#S@&7=3(@(cyT8O@@&)=3)+#Q@1%='$-@#)=3)+@%71$9@(418>@$&=&,1#Q7='$)@#%='$':1%/+RUP5XPPMX@$,1%371%.%@Uh@%=1%.2'%21%0#4@(%>35;@%(1%0@#8>4>/@(.=391@1&2+-@#*=391@.+2+.@#&=-7/@%&2+/5>=8,22+0@%<1%0@*?2+0=1%2@$82+1@'1=4+9@1&2+4@#*=4+9@.+2+4@#&=.)-@%&2+45>=8%32+4@%;1%0@*?2+4=1%2@$82+4@'1=4<#@1'2+4@#)=4<#@.,2+4@#%=.9+@%'2+44>=7<32+4@%;1%0@*@2+4<1%2@$92+4@'1=5.+@1'2+5@#)=5.+@.,2+5@#%=/+)@%'2+54>=7532+5@%;1%0@*@2+5<1%2@$92+5@'3=5>3@1'2+7@#*=5>3@.,2+8@%>9+@5>=7.32+8@.29,$=1%3@$92+9@'4=60<@1'2+:@#+=60<@.,2+;@%?9,/#0>9,0@.29,1>1%5@$92+>@'7=7#)@1'2,#@#+=7#)@.,2,#@%@9,<>9,=@.39,>@%.9,?@'7=734@1(2,#@#*=734@.-2,#@%?9-+>9-,@.39--@%.9-.@'8=8%?@1(2,$@#*=8%?@.-2,$@%?9-8>9-9@.39-:@%.9-;@':=86,@1(2,&@#+=86,@.-2,'@%?9.'>9.(@.49.)@%.9.*@(5=9(8@.$1;&?=9(8:1&**RUP4VPRV@%/1&,71&'%@Uh@%>1&'@*81;791&)@#71;+#y@%,=997#?@#6=997#Q232>@22=997#Q@2)=997@%51$?@(42::@$$=-45#Q@#0=997>1%-+RUPFXPP>Y@$,1%171%,4=+7#@%41%,@(629?@%$1%.@#84$0@(.=:+;@1,2++@#*=:+;@.%2+,@#&=4)9@%*2+-5<=122+.@%:1%.@*;2+.=1%0@$82+/@'1=:<#@1,2+2@#*=:<#@.%2+2@#&=495@%*2+25<<@32+2@%91%.@*;2+2=1%0@$82+2@'1=;.)@1-2+2@#)=;.)@.&2+2@#%=5+1@%+2+24<<132+2@%91%.@*<2+2<1%0@$92+2@'1=;>/@1-2+3@#)=;>/@.&2+3@#%=5;-@%+2+34<;@32+3@%91%.@*<2+3<1%0@$92+3@'3=<05@1-2+5@#*=<05@.&2+6@&$9+65<;132+6@.,9+8=1%1@$92+7@'4=<@<@1-2+8@#+=<@<@.&2+9@&%9,%6=+6532+;@.,9,'>1%3@$92+<@'7==3'@1-2+?@#+==3'@.&2+?@&&9,2>9,3@.-9,4@%.9,5@'7=>%0@1.2+?@#*=>%0@.'2+?@&%9,?>9,@@.-9-#@%.9-$@'8=>59@1.2+@@#*=>59@.'2+@@&%9-.>9-/@.-9-0@%.9-1@':=?($@1.2,$@#+=?($@.'2,%@&%9-;>9-<@..9-=@%.9->@(9=?8.@-41:@1=?8.#Q@#&=?8.>1&,3=+6-@%.1&.71&)5=+6-@-51;7$kC@#&1&+@%+=+6+<=@+/$LM0$2$O;0%>$SS2=.8&'LHC;T81;:#V@#/=.78;1*071)?$P311>'-#&42=TP1VPP2VPP3131.&5VPR@%7=,-##001)4&LYP211*$*4WPV0Y7R@)<34<0.<11::51'#71:<@#+=/*,%4WQ@#)1%82.*91%$6=,*3#R@&'=/*1+P2WPU1Y7R@((4''@$+=,*,$6X115.147,$P:12:+@#-46=#E51$6#F@$#15.@%42,$@*815,)kCSQRQR=15.92)/216&2=.41&9WPR@#&=--,;=-,;$DW55*--#$WPLRP5WPX1PQ@#016,@&%=--=216,%6Y8@(,5*4@$+16/$FW@2=16/*P6VRRPvq@##16>@&13,6@%7>4-4@*93,61>4->@&03,6#T@2.3,6@%5>&<-@*=2))#S@#'3,6*P7VPRSvq@%(3,>#T@3?3,>@.>167&P6VT@'-3,>@%754,@*93,>#R@&63,>@&(>8?/@.23,>#R@.(2))#R@#,3,>#R@%*3,>#S@3?3,>@.>1672>*;(@#&8?)%D??@&43-)@@@8>;@@@8>;@4-8>;(cyT8<?0#+$0<@@@3-*@5'3-*(P7VPRQ@%*6'1@@@;9-@'&;9-@@@3,>@@@3,>@8;3,>@@@=$3+@@@=$3+@@@=$3+@@@=$3+@,;=$3+@@@=$3+@@@=$3+@4?=$3+@@@8?%@&%8?%'cyT@;1=$33#82#+#02#+*H:?TSPkN0$>*8C;TQk4C<=/;%&0K;T8>()(#V@#319%,3WPF2100P30192@#;=028%0@<?1)9&P6VU@%>3/>#Z21)=#L@*$1);2.<>1);@#5>'3.@#.1&33#3&X1PT4#/%0PT@&<2,3%IY4@%;1%1@&3>'3.016-@$#42,71$:@#>=16%@#)16-@%<2-(@*.16+1=16/#U@#1='1($@J<2+$$@I@$&2+$22>>$DW:2>>)LPLPLLH@#&1&6@%?5&?(UP2WPL@*)2)?@#%5&=@#9>)*-#>51$2@#+>)*-%LPL@'+4#4#4@*.4#4$EW1156@$=6)7@#.156@%<2),@*,1546=3,7@#-2)**4I;TQk0I<2)0$8J@%'2)0$4M@#&1&:@%?956#V@*.2)0@#%954@#82)0#>@#62)0#R@'.2)0#9@*22)0$8J@%'2)0@#)156@%<2)0@*,15412)0@#(95<42)0)LI;TQkH42)0&kLR]"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PKHEAD_m1k0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PKHEAD_m1k0.

Module C_PKPOP_e_m0k0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PKPOP_e_m0k0).
Definition CUTS : IMap.t template := imap_of [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2U.T_PKPOP_e_m0k0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "--=YCRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZYD@*(.'#L@#0.'$H5@,,.+61+0#8@-+.+#4@%01+4-)#P:WhP@UPA1ZLH3;TPBXPPCXPPDXPP6TPP0WPPFXPPGXPPHXPPIXPPJXPPKXPPLXPPMXPPNXPPOXPPJUPPKUPP0YPP7VPP;UPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNVPPOV0(,-).=WPU9TJQjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUjLUjKUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(3#.-#9ylQL;;TkHRQySPP:WPLQP;WPQ<WOOOOOO0#(-$=WP<WPLPLPLPLPV@Vij9Wj8Wj7Wi6W6Wj5Wi4W4Wj3Wj2Wj1WiBU0WjAUi=U@Uj<Ui;U@$#(<-#$cyTDM;TSPySS1(++P;WhLQP@U<(/-##4WPP6WPV<Vf4'3-#$6V0Wj5ViBU4V0-<&i=U?@$''>-#+k>SQySPLRP<WPvqySRL;'2-#%uqylQ4N;TkDRQ0)3-#847=TSPySQLPP<WPuqRPL000000000Tvq1*)-#8PPBUPPCUPPDUPPEUPPFUPPGUPPHUPPIU41.4-$$LUPPMUPPNUPPOUPP0VPP1VPP2VPP3VPP4VPP@UPP6V01/>@%51/:%<WP3/=&;X1R0/;-#-j0WjOVjNVjMVjLVjKVjJV@&110?@$+1&%(ySPySR81%#@#'1$8@0,1?'@$<121$5V@%?121#;4125&LPP622''-#'V<X5Rj7Wj6Wj5Wj52&:@'%13.@%&2+,-#%PL@QP@UPP<WPM@##2+/%=Vg6,+@%'2+2@#52+*$@8@#+2+*&kERS"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PKPOP_e_m0k0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PKPOP_e_m0k0.

Module C_PKPOP_e_m1k1.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PKPOP_e_m1k1).
Definition CUTS : IMap.t template := imap_of [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2U.T_PKPOP_e_m1k1).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "--=YCRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZYD@*(.'#L@#0.'$H5@,,.+61+0#8@-+.+#4@%01+4-)#P4WhP@UPA1ZLH3;TP<XPP=XPP>XPP6TPPOVPP@XPPAXPPBXPPCXPPDXPPEXPPFXPPGXPPHXPPIXPPJUPPKUPPJXPP6VPP;UPP7VPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNV0(,-).7WPU9TJQjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUjLUjKUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(3#.-$&ylQL;;TkHRQySPP4WPLQL@1<TP1VPP2VPP3VPP4VPP5V0/-@%5/)-#$5WPQ6WOOOOOO0#(-%&WP6WPP2WPLPP3WPLPLPLPV@VIQj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJV@$:1$#-#+iBU0VjAUi=U@Uj<Ui;U@$#02-#$cyTDM;TSPySS1/?&P5Wh>0%$@U@%>0%:/?+V<VCQi2W3@%=.6)j@Ui=U?@$'.9-#+k>SQySPLRP6WPvqySRL;*(-#%uqylQ4N;TkDRQ00.-#847=TSPySQLPP6WPuqRPL000000000Tvq11#$-#8PPBUPPCUPPDUPPEUPPFUPPGUPPHUPPIU41=%-#+LUPPMUPPNUPPOUPP0VP01$@%@UP21-/+P3WPV;X5Q31,0-#$i5VOVj4Vi1V3@$#18;@$+-0(ySPySR8,.@#',%@0,2)#@$11+<'5WPP692&'&<X7Q92%?%i2W31,3%1VO@#>,%@%&2$/%PL@@&52$0'P6WPM71;,316>&=VEQ@&'204@$52$>@#52$6$@8@#+2$6&kERS"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PKPOP_e_m1k1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PKPOP_e_m1k1.

Module C_PKPOP_n_m1k0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PKPOP_n_m1k0).
Definition CUTS : IMap.t template := imap_of [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2U.T_PKPOP_n_m1k0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-33YCRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZLH3;TP<XPP=XPP>XPP6TPP0WPP@XPPAXPPBXPPCXPPDXPPEXPPFXPPGXPPHXPPIXPPJXPP7VPP<UPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNVPPOV0($-)-7WPU9TIQjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUiKULUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(3#.-#%ylQL;;TkHRQyS0.'-&$;UPP>UPP?UPP@UPPAUPPCUPPDUPPEUPPFUPPGUPPHUPPIUPPJUPPKUPPLUPPMUPPNUPPOUPP0VPP1VPP=UPP2VPP3VPP4VPP5VhP6V01#=@%51#9#51&<-$)5WPP6WPV<X5Rj7Wj6Wj5Wi1W4Wj0WjOVjNVjMVjLVjKVjJV@%(1%,'jLUjK@%41%--#$cyTDM;TSPylD@*,1=.#4@#,1=.$H5@$-1=2@#%10#(5VPL@Q@$010&,AUPMOOOOOO0#(-#9WP2WPV=V8Qi4W4Wj3Wj2Wi6V1Wj5Vi2V4@&(1)/-#'k>SQySPLRP1WPvq@*/1)2223>#8@%(1)2'LPQ1W71&.-#%uqylQ4N;TkDRQ016+%@8=@*.16+#L@#02@7@$//9"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PKPOP_n_m1k0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PKPOP_n_m1k0.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6).
Definition CUTS : IMap.t template := imap_of [(298%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P6VPLPPIUPPJUPPKUPPLUPPMUPPNUPPOUPP0VPP1VPP2VPP3VPP4VPP5VPP9WPP7VPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNVPPOVPP0WPP1WPP8WPU:YIQj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUjLUjKUjJUjIUi=UHUj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66).
Definition CUTS : IMap.t template := imap_of [(299%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P4VPP8WPP7WPU;Yaj0Wi5VOVj4Vi=U3Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6).
Definition CUTS : IMap.t template := imap_of [(300%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P5VPP:WPP9WPU<Yaj1Wi6V0Wj5Vi=U4Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2).
Definition CUTS : IMap.t template := imap_of [(301%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P7VPP:WPP9WPU=Yaj3Wi8V2Wj7Vi=U6Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e).
Definition CUTS : IMap.t template := imap_of [(302%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P5VPP:WPP9WPU>Yaj1Wi6V0Wj5Vi=U4Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430).
Definition CUTS : IMap.t template := imap_of [(303%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P5VPP9WPP8WPU?Yaj1Wi6V0Wj5Vi=U4Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5).
Definition CUTS : IMap.t template := imap_of [(304%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P5VPP8WPP7WPU@Yaj1Wi6V0Wj5Vi=U4Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6).
Definition CUTS : IMap.t template := imap_of [(305%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P7VPP:WPP9WPUAYaj3Wi8V2Wj7Vi=U6Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd).
Definition CUTS : IMap.t template := imap_of [(306%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P5VPP9WPP8WPUBYaj1Wi6V0Wj5Vi=U4Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85).
Definition CUTS : IMap.t template := imap_of [(307%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P3VPP6WPP5WPUCYajOVi4VNVj3Vi=U2Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d).
Definition CUTS : IMap.t template := imap_of [(308%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P6VPP9WPP8WPUDYaj2Wi7V1Wj6Vi=U5Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20).
Definition CUTS : IMap.t template := imap_of [(309%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P6VPP9WPP8WPUEYaj2Wi7V1Wj6Vi=U5Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637).
Definition CUTS : IMap.t template := imap_of [(310%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P7VPP:WPP9WPUFYaj3Wi8V2Wj7Vi=U6Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.

Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75).
Definition CUTS : IMap.t template := imap_of [(311%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P3VPP6WPP5WPUGYajOVi4VNVj3Vi=U2Vj<Ui;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSk:SQkIRQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.

Module C_PKPOP_e_m1k0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_PKPOP_e_m1k0).
Definition CUTS : IMap.t template := imap_of [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2U.T_PKPOP_e_m1k0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2U.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "--=YCRLHMS4CNS8CNS<CNS@CNSDCNS05OS<>OSLNOSL20T<A0TDB0T@J0TD?1TDC1TLJ1T0L1T<12T@:2T@;2TL?3T0N3TH:5T0C5T<O6T097T0B7THK7TD08T038T@88TL;8TDG8T0K8T8L8T499THF9T0H9T00:T@1:T4@:TH;;T0A;T4A;T@B;T4C;T8C;T@D;T@E;T@F;T<G;T@G;T4H;T0I;T4I;THI;TLI;T@J;T@K;THK;T0M;T0N;T4N;TDO;T@0<TD0<T02<T42<TDO<TH0@T<1@T@2@T06@T<8@T8B@TH7AT861XL03X4<5Y4F5Y8F5Y@@<Y<G4ZYD@*(.'#L@#0.'$H5@,,.+61+0#8@-+.+#4@%01+4-)#P8WhP@UPA1ZLH3;TP@XPPAXPPBXPP6TPPOVPPDXPPEXPPFXPPGXPPHXPPIXPPJXPPKXPPLXPPMXPPIUPPJUPPNXPP6VPP;UPP7VPP8VPP9VPP:VPP;VPP<VPP=VPP>VPP?VPP@VPPAVPPBVPPCVPPDVPPEVPPFVPPGVPPHVPPIVPPJVPPKVPPLVPPMVPPNV0(,-).;WPU9TJQjIVjHVjGVjFVjEVjDVjCVjBVjAVj@Vj?Vj>Vj=Vj<Vj;Vj:Vj9Vj8Vj7Vj6Vj5Vj4Vj3Vj2Vj1Vj0VjOUjNUjMUjLUjKUjJUjIUjHUjGUjFUjEUjDUjCUjBUjAUj@Uj?Uj>Uj=Uj<Uj;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(3#.-$-ylQL;;TkHRQySPP8WPLQPAUPPBUPPCUPPDUPPEUPPFUPPGUPPHU4/@-$$KUPPLUPPMUPPNUPPOUPP0VPP1VPP2VPP3VPP4VPP5V01#,@%51#(-#$9WPQ:WOOOOOO0#(-%&WP:WPP2WPLPP4WPLPLPLPV@V7Rj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJV@&.1%@-##i=U@Uj<Ui;U@$#1%;-#$cyTDM;TSPySS11%*&P9Wh@$>1%.$@U@%>1%.;1%*-#&4WPV<V2Rj3Wi2W@'*1$()j@Ui=U?@$'1$+-#+k>SQySPLRP:WPvqySRL;+9-#%uqylQ4N;TkDRQ01%>-#847=TSPySQLPP:WPuqRPL000000000Tvq11&401#@110&*P4WPV;Xe31/&-#%i5VOVj4ViAU3V@$.)6(ySPySR8(4@#'(+@0,2,$(P9WPP:22$<(LPV<Xf32$7'i4W4W8135'i=UOV@$?1>&%PL@@(41>''P:WPM81>)*2WPV=V3R2-9@'+2/2@$51>,@#51>$$@8@#+1>$&kERS"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_PKPOP_e_m1k0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_PKPOP_e_m1k0.
